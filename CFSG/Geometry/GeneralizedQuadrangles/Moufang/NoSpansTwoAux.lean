module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.ElationGroup2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Varieties
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Transitive

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

public theorem eq_of_mem_line_of_dist_eq_three (hP : IsGeneralizedPolygon Γ 4) {p K z w : V}
    (hK : Γ.dist p K = 3) (hzK : Γ.Adj K z) (hwK : Γ.Adj K w)
    (hzp : Γ.dist p z = 2) (hwp : Γ.dist p w = 2) : z = w := by
  by_contra hne
  have hzw : Γ.dist z w = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hzK.symm hwK hne
  obtain ⟨N, hN, -⟩ := existsUnique_commonNeighbor_of_pairwise_dist_two hP
    (x := w) (y := z) (z := p) (by rw [dist_comm]; exact hzw)
    (by rw [dist_comm]; exact hwp) (by rw [dist_comm]; exact hzp)
  have hNw : Γ.Adj w N := hN.1
  have hNz : Γ.Adj z N := hN.2.1
  have hNp : Γ.Adj p N := hN.2.2
  let L := commonNeighbor hP hzp
  have hLp : Γ.Adj p L := commonNeighbor_adj_left hP hzp
  have hLz : Γ.Adj z L := commonNeighbor_adj_right hP hzp
  have hNL : N = L := (existsUnique_commonNeighbor hP hzp).unique ⟨hNp, hNz⟩ ⟨hLp, hLz⟩
  have hLw : Γ.Adj w L := by rw [← hNL]; exact hNw
  have hKL : K = L :=
    (existsUnique_commonNeighbor hP hzw).unique ⟨hzK.symm, hwK.symm⟩ ⟨hLz, hLw⟩
  have hadj : Γ.Adj p K := by rw [hKL]; exact hLp
  have h1 : Γ.dist p K = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  omega

public theorem dist_eq_four_of_mem_line_of_ne (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {p K z w : V} (hp : c p = 0) (hKc : c K = 1)
    (hK : Γ.dist p K = 3) (hzK : Γ.Adj K z) (hwK : Γ.Adj K w)
    (hzp : Γ.dist p z = 2) (hzw : z ≠ w) : Γ.dist p w = 4 := by
  have hcw : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hKc hwK
  have heven : Even (Γ.dist p w) := (hP.eq_iff_even_dist c p w).1 (by rw [hp, hcw])
  have hle : Γ.dist p w ≤ 4 := hP.dist_le (by norm_num) p w
  have hne0 : Γ.dist p w ≠ 0 := by
    intro h0
    have hpw : p = w := (hP.connected.dist_eq_zero_iff).mp h0
    have h1 : Γ.dist p K = 1 := by
      rw [hpw]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr hwK.symm
    omega
  by_contra hne4
  have h2 : Γ.dist p w = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact hzw (eq_of_mem_line_of_dist_eq_three hP hK hzK hwK hzp h2)

private theorem ncard_neighborSet_diff_singleton {L b : V} (hb : Γ.Adj L b) :
    (Γ.neighborSet L \ {b}).ncard = (Γ.neighborFinset L).card - 1 := by
  classical
  rw [show Γ.neighborSet L \ {b} = ↑((Γ.neighborFinset L).erase b) by
    ext x
    simp [SimpleGraph.mem_neighborFinset, eq_comm, and_comm]]
  rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (by simpa using hb)]

public theorem ncard_points_of_line_erase {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L b : V} (hL : c L = 1) (hb : Γ.Adj L b) :
    (Γ.neighborSet L \ {b}).ncard = s := by
  rw [ncard_neighborSet_diff_singleton hb, card_neighborFinset_eq_degree, hdeg L,
    if_neg (by rw [hL]; decide)]
  omega

public theorem exists_apartment_at_point (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {p L : V} (hpL : Γ.Adj p L) :
    ∃ v : ZMod 8 → V, IsPolygonApartment Γ 4 v ∧ v 0 = p := by
  obtain ⟨t, ht, ht4, -⟩ := exists_polygonApartment_through_edge (n := 4) (by norm_num) hP hT hpL
  refine ⟨fun j => t (j + 4), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro a b hab
      have h2 : t (a + 4) = t (b + 4) := hab
      exact add_right_cancel (ht.1 h2)
    · intro k
      have h := ht.2 (k + 4)
      have e : ((k + 4 : ZMod 8) + 1) = ((k + 1) + 4 : ZMod 8) := by ring
      rwa [e] at h
  · show t ((0 : ZMod 8) + 4) = p
    rw [show ((0 : ZMod 8) + 4) = 4 by decide]
    exact ht4


section Fixed

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

public theorem noSpansTwo_stabilizer_smul_injective {p y : V} {hy4 : Γ.dist p y = 4}
    {v : ZMod 8 → V}
    {hfree : ∀ (e : ↥(elationGroup H Γ v)) {x : V}, Γ.dist p x = 4 →
      (e : H) • x = x → e = 1}
    (S : Subgroup H) (hSE : S ≤ elationGroup H Γ v) :
    Function.Injective (fun θ : ↥S => (θ : H) • y) := by
  intro a b hab
  have heq : (a : H) • y = (b : H) • y := hab
  let e : ↥(elationGroup H Γ v) :=
    ⟨(b : H)⁻¹ * (a : H),
      (elationGroup H Γ v).mul_mem ((elationGroup H Γ v).inv_mem (hSE b.2)) (hSE a.2)⟩
  have hefix : (e : H) • y = y := by
    show ((b : H)⁻¹ * (a : H)) • y = y
    rw [mul_smul, heq]
    simp
  have he1 : e = 1 := hfree e hy4 hefix
  have hHH : (b : H)⁻¹ * (a : H) = 1 := by
    have := congrArg Subtype.val he1
    simpa [e] using this
  have hEq : (a : H) = (b : H) := by
    calc (a : H) = (b : H) * ((b : H)⁻¹ * (a : H)) := by group
      _ = (b : H) := by rw [hHH, mul_one]
  exact Subtype.ext hEq

public theorem noSpansTwo_stabilizer_line_data
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {p y : V} {hy4 : Γ.dist p y = 4}
    {v : ZMod 8 → V} (hv : IsPolygonApartment Γ 4 v) {hv0 : v 0 = p}
    {hfree : ∀ (e : ↥(elationGroup H Γ v)) {x : V}, Γ.dist p x = 4 →
      (e : H) • x = x → e = 1}
    {N zN : V} (hyN : Γ.Adj y N) (hcN : c N = 1)
    (hdistpN : Γ.dist p N = 3) (hzN : Γ.Adj N zN) (hzNp : Γ.dist p zN = 2) :
    (∀ θ : ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H N),
      (θ : H) • y ∈ Γ.neighborSet N \ {zN}) ∧
    Nat.card ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H N) ≤ s := by
  classical
  let S : Subgroup H := elationGroup H Γ v ⊓ MulAction.stabilizer H N
  have hmaps : ∀ θ : ↥S, (θ : H) • y ∈ Γ.neighborSet N \ {zN} := by
    intro θ
    have hθE : (θ : H) ∈ elationGroup H Γ v := (Subgroup.mem_inf.mp θ.2).1
    have hθN : (θ : H) • N = N :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp θ.2).2
    have hθp : (θ : H) • p = p := by
      have h := elationGroup_le_whorlGroup v hv hθE
      rw [hv0] at h
      exact whorlGroup_fix_self hP hT h
    have hadj : Γ.Adj N ((θ : H) • y) := by
      have h := (GraphAction.adj_smul (θ : H) y N).mpr hyN
      rw [hθN] at h
      exact h.symm
    refine ⟨by simpa using hadj, ?_⟩
    intro hzy
    have hdist : Γ.dist p ((θ : H) • y) = 4 := by
      have h := GPath.dist_smul hP.connected (θ : H) p y
      rw [hθp] at h
      rw [h]
      exact hy4
    rw [hzy, hzNp] at hdist
    omega
  have hSle : Nat.card ↥S ≤ s := by
    let f : ↥S → ↥(Γ.neighborSet N \ {zN}) := fun θ => ⟨(θ : H) • y, hmaps θ⟩
    have hinj : Function.Injective f := by
      intro a b hab
      exact noSpansTwo_stabilizer_smul_injective (p := p) (hy4 := hy4) (v := v) (hfree := hfree)
        S inf_le_left (congrArg Subtype.val hab)
    have hcard := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_coe_set_eq, ncard_points_of_line_erase hdeg hcN hzN] at hcard
    exact hcard
  exact ⟨fun θ => hmaps θ, hSle⟩

public theorem noSpansTwo_rootGroup_path_data
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {L z N L' : V}
    (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hzN : Γ.Adj z N) (hLN : L ≠ N)
    (hL'p : Γ.Adj p L') (hL'L : L' ≠ L) (hcN : c N = 1) :
    rootGroup H Γ p L z ≤ elationGroup H Γ v ∧
      Nat.card ↥(rootGroup H Γ p L z) = s := by
  classical
  have h1v : ∀ x, Γ.dist (v 0) x = 4 → (spanSet Γ (v 0) x).ncard = 2 := by
    intro x hx
    rw [hv0] at hx
    rw [hv0]
    exact h1 x hx
  let qU : GPath Γ 4 := GPath.cons L'
    (GPath.cons p (GPath.cons L (GPath.ofAdj hzN) hzL) hpL) hL'p.symm
  have hq1 : qU 1 = p := rfl
  have hq2 : qU 2 = L := rfl
  have hq3 : qU 3 = z := rfl
  have hq4 : qU 4 = N := rfl
  have hq : qU.NoBack := by
    intro i hi
    have hi2 : i ≤ 2 := by omega
    interval_cases i
    · rw [show qU 0 = L' from rfl, hq2]; exact hL'L
    · rw [hq1, hq3]; exact hzp.symm
    · rw [hq2, hq4]; exact hLN
  have hle : rootGroup H Γ (qU 1) (qU 2) (qU 3) ≤ elationGroup H Γ v :=
    rootGroup_le_elationGroup hP hT c hdeg hst hM v hv (by rw [hv0]; exact hp) h1v
      qU hq (by rw [hv0, hq1]; simp)
  have hcard : Nat.card ↥(rootGroup H Γ (qU 1) (qU 2) (qU 3)) = s := by
    have h := card_rootGroup hP hT hM qU hq
    rw [hq1, hq2, hq3] at h
    have hd : Γ.degree (qU 4) = s + 1 := by
      rw [hq4, hdeg N, if_neg (by rw [hcN]; decide)]
    have hd' : Γ.degree (qU 4) - 1 = s := by rw [hd]; omega
    rw [hd'] at h
    exact h
  exact ⟨by rwa [hq1, hq2, hq3] at hle, by rwa [hq1, hq2, hq3] at hcard⟩

public theorem noSpansTwo_base_data
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    {h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2}
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {y : V} {hy4 : Γ.dist p y = 4}
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    {hfree : ∀ (e : ↥(elationGroup H Γ v)) {x : V}, Γ.dist p x = 4 →
      (e : H) • x = x → e = 1}
    (S : Subgroup H) (hS : S = elationGroup H Γ v ⊓ MulAction.stabilizer H M) :
    S = rootGroup H Γ p L z ∧ Nat.card ↥S = s ∧
      (fun θ : ↥S => (θ : H) • y) '' Set.univ = Γ.neighborSet M \ {z} := by
  classical
  subst hS
  have hcy : c y = 0 := by
    have heven : Even (Γ.dist p y) := by rw [hy4]; norm_num
    have h : c p = c y := (hP.eq_iff_even_dist c p y).2 heven
    rw [hp] at h
    exact h.symm
  have hzp2 : Γ.dist p z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL hzL hzp.symm
  have hcM : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyM
  have hpM : ¬ Γ.Adj p M := by
    intro h
    have hpy : p ≠ y := by
      intro hh
      have h0 : Γ.dist p y = 0 := by rw [hh, SimpleGraph.dist_self]
      omega
    have h2 : Γ.dist p y = 2 := dist_eq_two_of_adj_of_adj_of_ne hP h hyM.symm hpy
    omega
  have hdistpM : Γ.dist p M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hpM (by rw [hp, hcM]; decide)
  have hLM : L ≠ M := by
    intro h
    have hyL : Γ.Adj L y := by rw [h]; exact hyM.symm
    have h2 : Γ.dist p y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hpL hyL (by
        intro hh
        have h0 : Γ.dist p y = 0 := by rw [hh, SimpleGraph.dist_self]
        omega)
    omega
  obtain ⟨L', hL'p, hL'ne⟩ := exists_adj_ne_two hT p L L
  have hL'L : L' ≠ L := fun h => hL'ne.1 h
  obtain ⟨hUleE, hUcard⟩ :=
    noSpansTwo_rootGroup_path_data hP hT c hdeg hst hM hp h1 v hv hv0 hpL hzL hzp hzM hLM
      hL'p hL'L hcM
  let U : Subgroup H := rootGroup H Γ p L z
  have hUleS : U ≤ elationGroup H Γ v ⊓ MulAction.stabilizer H M := by
    refine fun u hu => Subgroup.mem_inf.mpr ⟨hUleE hu, ?_⟩
    exact MulAction.mem_stabilizer_iff.mpr
      ((mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hu).2.2 M hzM)
  haveI hEfin : Fintype ↥(elationGroup H Γ v) :=
    Fintype.ofInjective (fun e : ↥(elationGroup H Γ v) => fun x : V => (e : H) • x)
      (by
        intro e f hef
        apply Subtype.ext
        exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H))
          (fun x => congrFun hef x))
  haveI : Fintype ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H M) :=
    Fintype.ofInjective
      (fun θ : ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H M) =>
        (⟨(θ : H), (Subgroup.mem_inf.mp θ.2).1⟩ : ↥(elationGroup H Γ v)))
      (by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : ↥(elationGroup H Γ v) => (z : H)) hab)
  have hSle : Nat.card ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H M) ≤ s :=
    (noSpansTwo_stabilizer_line_data (p := p) (hy4 := hy4) (hP := hP) (hT := hT) (c := c)
      (hdeg := hdeg) (hv := hv) (hv0 := hv0) (hfree := hfree) (hyN := hyM)
      (hcN := hcM) (hdistpN := hdistpM) (hzN := hzM.symm) (hzNp := hzp2)).2
  have hS_eq_U : (elationGroup H Γ v ⊓ MulAction.stabilizer H M) = U :=
    (Subgroup.eq_of_le_of_card_ge hUleS (by rw [hUcard]; exact hSle)).symm
  have hScard : Nat.card ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H M) = s := by
    rw [hS_eq_U, hUcard]
  have hmaps := (noSpansTwo_stabilizer_line_data (p := p) (hy4 := hy4) (hP := hP) (hT := hT)
    (c := c) (hdeg := hdeg) (hv := hv) (hv0 := hv0) (hfree := hfree) (hyN := hyM)
    (hcN := hcM) (hdistpN := hdistpM) (hzN := hzM.symm) (hzNp := hzp2)).1
  refine ⟨hS_eq_U, hScard, ?_⟩
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro x ⟨θ, -, rfl⟩
    exact hmaps θ
  · rw [ncard_points_of_line_erase hdeg hcM hzM.symm]
    rw [Set.ncard_image_of_injective _
      (noSpansTwo_stabilizer_smul_injective (p := p) (hy4 := hy4) (v := v) (hfree := hfree)
        (elationGroup H Γ v ⊓ MulAction.stabilizer H M) inf_le_left), Set.ncard_univ,
      hScard]


public theorem noSpansTwo_K_data
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {y : V} {hy4 : Γ.dist p y = 4}
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    {g : H} (hgE : g ∈ elationGroup H Γ v) (hgz : g • z ≠ z)
    (K : V) (hK : K = g • M) :
    Γ.dist p K = 3 ∧ c K = 1 ∧ Γ.Adj (g • z) K ∧ Γ.Adj L (g • z) ∧
      Γ.dist p (g • z) = 2 ∧ ¬ Γ.Adj y K ∧ Γ.dist y K = 3 := by
  classical
  have hcy : c y = 0 := by
    have heven : Even (Γ.dist p y) := by rw [hy4]; norm_num
    have h : c p = c y := (hP.eq_iff_even_dist c p y).2 heven
    rw [hp] at h
    exact h.symm
  have hzp2 : Γ.dist p z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL hzL hzp.symm
  have hcM : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyM
  have hgp : g • p = p := by
    have h := elationGroup_le_whorlGroup v hv hgE
    rw [hv0] at h
    exact whorlGroup_fix_self hP hT h
  have hgL : g • L = L := by
    have h := elationGroup_le_whorlGroup v hv hgE
    rw [hv0] at h
    rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h
    exact h L hpL
  have hpM : ¬ Γ.Adj p M := by
    intro h
    have hpy : p ≠ y := by
      intro hh
      have h0 : Γ.dist p y = 0 := by rw [hh, SimpleGraph.dist_self]
      omega
    have h2 : Γ.dist p y = 2 := dist_eq_two_of_adj_of_adj_of_ne hP h hyM.symm hpy
    omega
  have hdistpM : Γ.dist p M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hpM (by rw [hp, hcM]; decide)
  have hdistpK : Γ.dist p K = 3 := by
    have h := GPath.dist_smul hP.connected g p M
    rw [hgp] at h
    rw [hK]
    rw [h]
    exact hdistpM
  have hcK : c K = 1 := by
    have hne : c K ≠ c p := by
      intro heq
      have heven : Even (Γ.dist p K) := (hP.eq_iff_even_dist c p K).1 heq.symm
      obtain ⟨k, hk⟩ := heven
      omega
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c K) with h0 | h1
    · exact absurd (h0.trans hp.symm) hne
    · exact h1
  have hz'K : Γ.Adj (g • z) K := by
    have h := (GraphAction.adj_smul g z M).mpr hzM
    rw [← hK] at h
    exact h
  have hz'L : Γ.Adj L (g • z) := by
    have h := (GraphAction.adj_smul g z L).mpr hzL.symm
    rw [hgL] at h
    exact h.symm
  have hz'p : Γ.dist p (g • z) = 2 := by
    have h := GPath.dist_smul hP.connected g p z
    rw [hgp] at h
    rw [h]
    exact hzp2
  have hyL3 : Γ.dist y L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hpL
  have hyK : ¬ Γ.Adj y K := by
    intro hyK
    let u := proj hP hyL3
    have huL : Γ.Adj L u := proj_adj hP hyL3
    have hyu : Γ.dist y u = 2 := proj_dist hP hyL3
    have huz : u = z := by
      exact (existsUnique_proj hP hyL3).unique ⟨huL, hyu⟩ ⟨hzL, hyz⟩
    have hyz' : Γ.dist y (g • z) = 2 := by
      have hne : y ≠ g • z := by
        intro hh
        have : Γ.Adj L y := by rw [hh]; exact hz'L
        have h1 : Γ.dist y L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr this.symm
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hyK hz'K.symm hne
    have hEq : g • z = u :=
      (existsUnique_proj hP hyL3).unique ⟨hz'L, hyz'⟩ ⟨huL, hyu⟩
    exact hgz (by rw [hEq, huz])
  have hdistyK : Γ.dist y K = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hyK (by rw [hcy, hcK]; decide)
  exact ⟨hdistpK, hcK, hz'K, hz'L, hz'p, hyK, hdistyK⟩


public theorem noSpansTwo_w_data
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {p : V} (hp : c p = 0)
    {y : V} {hy4 : Γ.dist p y = 4}
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    {g : H} (hgz : g • z ≠ z) (K : V) (hK : K = g • M)
    (hdistpM : Γ.dist p M = 3) (hdistpK : Γ.dist p K = 3)
    (hcK : c K = 1) (hz'K : Γ.Adj (g • z) K)
    (hz'L : Γ.Adj L (g • z)) (hz'p : Γ.dist p (g • z) = 2)
    (hyK : ¬ Γ.Adj y K) (hdistyK : Γ.dist y K = 3) :
    ∃ w Mw : V, Γ.Adj K w ∧ Γ.dist y w = 2 ∧ w ≠ g • z ∧
      Γ.Adj y Mw ∧ Γ.Adj w Mw ∧ (∀ u : V, ¬ (Γ.Adj K u ∧ Γ.Adj M u)) ∧ Mw ≠ M := by
  classical
  have hcy : c y = 0 := by
    have heven : Even (Γ.dist p y) := by rw [hy4]; norm_num
    have h : c p = c y := (hP.eq_iff_even_dist c p y).2 heven
    rw [hp] at h
    exact h.symm
  have hzp2 : Γ.dist p z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL hzL hzp.symm
  let w : V := proj hP hdistyK
  have hwK : Γ.Adj K w := proj_adj hP hdistyK
  have hyw : Γ.dist y w = 2 := proj_dist hP hdistyK
  have hyz'4 : Γ.dist y (g • z) = 4 := by
    have hcz' : c (g • z) = 0 := color_eq_zero_of_dist_eq_two hP hp hz'p
    have heven : Even (Γ.dist y (g • z)) :=
      (hP.eq_iff_even_dist c y (g • z)).1 (by rw [hcy, hcz'])
    have hle := hP.dist_le (by norm_num : 4 ≠ 0) y (g • z)
    have hne2 : Γ.dist y (g • z) ≠ 2 := by
      intro h2
      have hEq : g • z = z :=
        (existsUnique_proj hP (dist_eq_three_of_adj_of_dist_eq_four hP hy4 hpL)).unique
          ⟨hz'L, h2⟩ ⟨hzL, hyz⟩
      exact hgz hEq
    have hne0 : Γ.dist y (g • z) ≠ 0 := by
      intro h0
      have hyz' : y = g • z := (hP.connected.preconnected y (g • z)).dist_eq_zero_iff.1 h0
      have hAdj : Γ.Adj L y := by rw [hyz']; exact hz'L
      have h1 : Γ.dist y L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hAdj.symm
      have h3 : Γ.dist y L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hpL
      omega
    obtain ⟨k, hk⟩ := heven
    omega
  have hwne : w ≠ g • z := by
    intro hh
    have h : Γ.dist y (g • z) = 2 := by rw [← hh]; exact hyw
    omega
  have hyL3 : Γ.dist y L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hpL
  let Mw : V := commonNeighbor hP hyw
  have hyMw : Γ.Adj y Mw := commonNeighbor_adj_left hP hyw
  have hwMw : Γ.Adj w Mw := commonNeighbor_adj_right hP hyw
  have hKM_disj : ∀ u : V, ¬ (Γ.Adj K u ∧ Γ.Adj M u) := by
    intro u hu
    have huK : Γ.Adj K u := hu.1
    have huM : Γ.Adj M u := hu.2
    have huz' : u ≠ g • z := by
      intro h
      have h1 : Γ.dist p u = 2 := by rw [h]; exact hz'p
      have hEq : z = u := eq_of_mem_line_of_dist_eq_three hP hdistpM hzM.symm huM hzp2 h1
      exact hgz (h.symm.trans hEq.symm)
    have huz : u ≠ z := by
      intro h
      have h1 : Γ.dist p u = 2 := by rw [h]; exact hzp2
      have hEq : g • z = u :=
        eq_of_mem_line_of_dist_eq_three hP hdistpK hz'K.symm huK hz'p h1
      exact hgz (hEq.trans h)
    have hup4 : Γ.dist p u = 4 :=
      dist_eq_four_of_mem_line_of_ne hP c hp hcK hdistpK hz'K.symm huK hz'p huz'.symm
    have hcu : c u = 0 := by
      have heven : Even (Γ.dist p u) := by rw [hup4]; norm_num
      have h : c p = c u := (hP.eq_iff_even_dist c p u).2 heven
      rw [hp] at h
      exact h.symm
    have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
    have huL : ¬ Γ.Adj u L := by
      intro h
      have hpu : p ≠ u := by
        intro hh
        rw [hh, SimpleGraph.dist_self] at hup4
        omega
      have h2 : Γ.dist p u = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hpL h.symm hpu
      omega
    have huL3 : Γ.dist u L = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c huL (by rw [hcu, hcL]; decide)
    have hzu2 : Γ.dist u z = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP huM.symm hzM.symm huz
    have hz'u2 : Γ.dist u (g • z) = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP huK.symm hz'K.symm huz'
    have hEq : z = g • z :=
      (existsUnique_proj hP huL3).unique ⟨hzL, hzu2⟩ ⟨hz'L, hz'u2⟩
    exact hgz hEq.symm
  have hMw_ne_M : Mw ≠ M := by
    intro h
    have hwM : Γ.Adj M w := by rw [← h]; exact hwMw.symm
    exact hKM_disj w ⟨hwK, hwM⟩
  exact ⟨w, Mw, hwK, hyw, hwne, hyMw, hwMw, hKM_disj, hMw_ne_M⟩


public theorem noSpansTwo_Lw_data
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {p : V} (hp : c p = 0)
    {y : V} {hy4 : Γ.dist p y = 4}
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    {g : H} {K w Mw : V} (hKM_disj : ∀ u : V, ¬ (Γ.Adj K u ∧ Γ.Adj M u))
    (hdistpK : Γ.dist p K = 3) (hz'K : Γ.Adj (g • z) K)
    (hz'L : Γ.Adj L (g • z)) (hdistpM : Γ.dist p M = 3)
    (hMw_ne_M : Mw ≠ M) (hyMw : Γ.Adj y Mw) (hwMw : Γ.Adj w Mw) :
    ∃ zw Lw : V, Γ.Adj Mw zw ∧ Γ.dist p zw = 2 ∧ Γ.Adj p Lw ∧ Γ.Adj zw Lw ∧
      Lw ≠ L ∧ Γ.dist Lw M = 4 ∧ Γ.dist p Mw = 3 ∧ Lw ≠ Mw := by
  classical
  have hcy : c y = 0 := by
    have heven : Even (Γ.dist p y) := by rw [hy4]; norm_num
    have h : c p = c y := (hP.eq_iff_even_dist c p y).2 heven
    rw [hp] at h
    exact h.symm
  have hzp2 : Γ.dist p z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL hzL hzp.symm
  have hpMw : ¬ Γ.Adj p Mw := by
    intro h
    have hpy : p ≠ y := by
      intro hh
      have h0 : Γ.dist p y = 0 := by rw [hh, SimpleGraph.dist_self]
      omega
    have h2 : Γ.dist p y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP h hyMw.symm hpy
    omega
  have hcMw : c Mw = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyMw
  have hdistpMw : Γ.dist p Mw = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hpMw (by rw [hp, hcMw]; decide)
  let zw : V := proj hP hdistpMw
  have hzwMw : Γ.Adj Mw zw := proj_adj hP hdistpMw
  have hzwp : Γ.dist p zw = 2 := proj_dist hP hdistpMw
  let Lw : V := commonNeighbor hP hzwp
  have hpLw : Γ.Adj p Lw := commonNeighbor_adj_left hP hzwp
  have hzwLw : Γ.Adj zw Lw := commonNeighbor_adj_right hP hzwp
  have hcLw : c Lw = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpLw
  have hcM : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyM
  have hpM : ¬ Γ.Adj p M := by
    intro h
    have h1 : Γ.dist p M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  have hyL3 : Γ.dist y L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hpL
  have hLw_ne_L : Lw ≠ L := by
    intro h
    have hzwL : Γ.Adj zw L := by rw [← h]; exact hzwLw
    have hyzw : Γ.dist y zw = 2 := by
      have hyne : y ≠ zw := by
        intro hh
        have h1 : Γ.Adj L y := by rw [hh]; exact hzwL.symm
        have h2 : Γ.dist y L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1.symm
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hyMw hzwMw hyne
    have hzw_eq : zw = z :=
      (existsUnique_proj hP hyL3).unique ⟨hzwL.symm, hyzw⟩ ⟨hzL, hyz⟩
    have hMw_eq_M : Mw = M :=
      (existsUnique_commonNeighbor hP hyz).unique
        ⟨hyMw, by rw [← hzw_eq]; exact hzwMw.symm⟩ ⟨hyM, hzM⟩
    exact hMw_ne_M hMw_eq_M
  have hdistLwM : Γ.dist Lw M = 4 := by
    have hLM_ne : Lw ≠ M := by
      intro h
      exact hpM (by rw [← h]; exact hpLw)
    have heven : Even (Γ.dist Lw M) :=
      (hP.eq_iff_even_dist c Lw M).1 (by rw [hcLw, hcM])
    have hle : Γ.dist Lw M ≤ 4 := by
      have h1 : Γ.dist Lw M ≤ Γ.dist Lw p + Γ.dist p M := hP.connected.dist_triangle
      have h2 : Γ.dist Lw p = 1 := by
        rw [SimpleGraph.dist_comm]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hpLw
      rw [h2, hdistpM] at h1
      omega
    have hne0 : Γ.dist Lw M ≠ 0 := by
      intro h
      exact hLM_ne ((hP.connected.dist_eq_zero_iff).1 h)
    have hne2 : Γ.dist Lw M ≠ 2 := by
      intro h2
      obtain ⟨u, huM, hu1⟩ :=
        hP.exists_adj_dist_succ (y := Lw) (v := M) (by rw [h2]; norm_num)
      have huLw : Γ.Adj Lw u := by
        have h1 : Γ.dist Lw u = 1 := by omega
        exact SimpleGraph.dist_eq_one_iff_adj.mp h1
      have hup : u ≠ p := by
        intro hh
        exact hpM (by rw [← hh]; exact huM.symm)
      have hup2 : Γ.dist p u = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hpLw huLw hup.symm
      have hu_eq_z : z = u :=
        eq_of_mem_line_of_dist_eq_three hP hdistpM hzM.symm huM hzp2 hup2
      have hzLw : Γ.Adj z Lw := by
        rw [hu_eq_z]
        exact huLw.symm
      have hLw_eq_L : Lw = L :=
        (existsUnique_commonNeighbor hP hzp2).unique ⟨hpLw, hzLw⟩ ⟨hpL, hzL.symm⟩
      exact hLw_ne_L hLw_eq_L
    obtain ⟨k, hk⟩ := heven
    omega
  have hLwMw : Lw ≠ Mw := by
    intro h
    exact hpMw (by rw [← h]; exact hpLw)
  exact ⟨zw, Lw, hzwMw, hzwp, hpLw, hzwLw, hLw_ne_L, hdistLwM, hdistpMw, hLwMw⟩

end Fixed

end CFSG.Geometry.GeneralizedQuadrangles
