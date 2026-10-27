module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwoAux
public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Closure

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

section Fixed

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

private theorem sw_data
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {y : V} {hy4 : Γ.dist p y = 4}
    {zw Mw Lw : V} (hpLw : Γ.Adj p Lw) (hzwLw : Γ.Adj zw Lw)
    (hzwp : Γ.dist p zw = 2) (hLwMw : Lw ≠ Mw)
    (hyMw : Γ.Adj y Mw) (hzwMw : Γ.Adj Mw zw)
    (hcMw : c Mw = 1) (hdistpMw : Γ.dist p Mw = 3)
    {hfree : ∀ (e : ↥(elationGroup H Γ v)) {x : V}, Γ.dist p x = 4 →
      (e : H) • x = x → e = 1} :
    (elationGroup H Γ v ⊓ MulAction.stabilizer H Mw = rootGroup H Γ p Lw zw) ∧
    Nat.card ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) = s ∧
    (fun θ : ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) => (θ : H) • y) ''
        Set.univ = Γ.neighborSet Mw \ {zw} := by
  classical
  obtain ⟨L'', hL''p, hL''ne⟩ := exists_adj_ne_two hT p Lw Lw
  have hL''Lw : L'' ≠ Lw := fun h => hL''ne.1 h
  have hzwp' : zw ≠ p := by
    intro h
    rw [h, SimpleGraph.dist_self] at hzwp
    omega
  obtain ⟨hUwleE, hUwcard⟩ :=
    noSpansTwo_rootGroup_path_data hP hT c hdeg hst hM hp h1 v hv hv0 hpLw hzwLw.symm hzwp'
      hzwMw.symm hLwMw hL''p hL''Lw hcMw
  have hUwleSw : rootGroup H Γ p Lw zw ≤
      elationGroup H Γ v ⊓ MulAction.stabilizer H Mw := by
    refine fun u hu => Subgroup.mem_inf.mpr ⟨hUwleE hu, ?_⟩
    exact MulAction.mem_stabilizer_iff.mpr
      ((mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hu).2.2 Mw hzwMw.symm)
  haveI hEfin : Fintype ↥(elationGroup H Γ v) :=
    Fintype.ofInjective (fun e : ↥(elationGroup H Γ v) => fun x : V => (e : H) • x)
      (by
        intro e f hef
        apply Subtype.ext
        exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H))
          (fun x => congrFun hef x))
  haveI : Fintype ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) :=
    Fintype.ofInjective
      (fun θ : ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) =>
        (⟨(θ : H), (Subgroup.mem_inf.mp θ.2).1⟩ : ↥(elationGroup H Γ v)))
      (by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : ↥(elationGroup H Γ v) => (z : H)) hab)
  have hSwle : Nat.card ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) ≤ s :=
    (noSpansTwo_stabilizer_line_data (p := p) (hy4 := hy4) (hP := hP) (hT := hT) (c := c)
      (hdeg := hdeg) (hv := hv) (hv0 := hv0) (hfree := hfree) (hyN := hyMw)
      (hcN := hcMw) (hdistpN := hdistpMw) (hzN := hzwMw) (hzNp := hzwp)).2
  have hSw_eq_Uw : (elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) =
      rootGroup H Γ p Lw zw :=
    (Subgroup.eq_of_le_of_card_ge hUwleSw (by rw [hUwcard]; exact hSwle)).symm
  have hSwcard : Nat.card ↥(elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) = s := by
    rw [hSw_eq_Uw, hUwcard]
  have hmaps := (noSpansTwo_stabilizer_line_data (p := p) (hy4 := hy4) (hP := hP) (hT := hT)
    (c := c) (hdeg := hdeg) (hv := hv) (hv0 := hv0) (hfree := hfree) (hyN := hyMw)
    (hcN := hcMw) (hdistpN := hdistpMw) (hzN := hzwMw) (hzNp := hzwp)).1
  refine ⟨hSw_eq_Uw, hSwcard, ?_⟩
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro x ⟨θ, -, rfl⟩
    exact hmaps θ
  · rw [ncard_points_of_line_erase hdeg hcMw hzwMw]
    rw [Set.ncard_image_of_injective _
      (noSpansTwo_stabilizer_smul_injective (p := p) (hy4 := hy4) (v := v) (hfree := hfree)
        (elationGroup H Γ v ⊓ MulAction.stabilizer H Mw) inf_le_left), Set.ncard_univ,
      hSwcard]


private theorem b_exists
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hM : MoufangCondition H Γ 4) (hT : IsThick Γ) {p : V} (hp : c p = 0)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {y : V} {hy4 : Γ.dist p y = 4}
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    {hfree : ∀ (e : ↥(elationGroup H Γ v)) {x : V}, Γ.dist p x = 4 →
      (e : H) • x = x → e = 1}
    {g : H} (hgE : g ∈ elationGroup H Γ v) (hgz : g • z ≠ z)
    {K w Mw : V} (hK : K = g • M) (hwK : Γ.Adj K w) (hw4 : Γ.dist p w = 4)
    (hwMw : Γ.Adj w Mw) (hwne : w ≠ g • z)
    {zw : V} (hzwMw : Γ.Adj Mw zw) (hzwp : Γ.dist p zw = 2)
    (S Sw : Subgroup H) (hS : S = elationGroup H Γ v ⊓ MulAction.stabilizer H M)
    (hSw : Sw = elationGroup H Γ v ⊓ MulAction.stabilizer H Mw)
    (hS_eq_U : S = rootGroup H Γ p L z)
    (hS_orbit : (fun θ : ↥S => (θ : H) • y) '' Set.univ =
      Γ.neighborSet M \ {z})
    (hSw_orbit : (fun θ : ↥Sw => (θ : H) • y) '' Set.univ =
      Γ.neighborSet Mw \ {zw}) :
    ∃ (a : ↥S) (b : ↥Sw), (b : H) = g * (a : H) ∧
      (b : H) • M = K ∧ (b : H) • z = g • z ∧ (b : H) • y = w := by
  classical
  have hzp2 : Γ.dist p z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL hzL hzp.symm
  have hgpinv : g⁻¹ • p = p := by
    have hgp : g • p = p := by
      have h := elationGroup_le_whorlGroup v hv hgE
      rw [hv0] at h
      exact whorlGroup_fix_self hP hT h
    calc g⁻¹ • p = g⁻¹ • (g • p) := by rw [hgp]
      _ = p := by simp
  let m : V := g⁻¹ • w
  have hgm : g • m = w := by
    show g • (g⁻¹ • w) = w
    simp
  have hmM : Γ.Adj M m := by
    have h := (GraphAction.adj_smul g⁻¹ K w).mpr hwK
    have hK' : g⁻¹ • K = M := by
      rw [hK]
      simp
    rwa [hK'] at h
  have hmz : m ≠ z := by
    intro h
    apply hwne
    rw [← hgm, h]
  have hm4 : Γ.dist p m = 4 := by
    have h := GPath.dist_smul hP.connected g⁻¹ p w
    rw [hgpinv] at h
    rw [h]
    exact hw4
  have hmset : m ∈ Γ.neighborSet M \ {z} := ⟨hmM, hmz⟩
  have hmimg : m ∈ (fun a : ↥S => (a : H) • y) '' Set.univ := by
    rw [hS_orbit]
    exact hmset
  obtain ⟨a, -, hay⟩ := hmimg
  have hwmwif : w ∈ Γ.neighborSet Mw \ {zw} := by
    refine ⟨by simpa using hwMw.symm, ?_⟩
    intro h
    have h1 : Γ.dist p w = Γ.dist p zw := by rw [h]
    rw [hzwp] at h1
    rw [hw4] at h1
    omega
  have hwimg : w ∈ (fun b : ↥Sw => (b : H) • y) '' Set.univ := by
    rw [hSw_orbit]
    exact hwmwif
  obtain ⟨b, -, hby⟩ := hwimg
  have haS : (a : H) ∈ S := a.2
  have haS' : (a : H) ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H M := by
    rw [← hS]
    exact haS
  have haE : (a : H) ∈ elationGroup H Γ v := (Subgroup.mem_inf.mp haS').1
  have haM : (a : H) • M = M :=
    MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp haS').2
  have haz : (a : H) • z = z := by
    have haU : (a : H) ∈ rootGroup H Γ p L z := by rw [← hS_eq_U]; exact haS
    exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp haU).2.1 z hzL
  have hbS' : (b : H) ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H Mw := by
    rw [← hSw]
    exact b.2
  have hbE : (b : H) ∈ elationGroup H Γ v := (Subgroup.mem_inf.mp hbS').1
  have hga_y : (g * (a : H)) • y = w := by
    rw [mul_smul]
    rw [show (a : H) • y = m from hay]
    exact hgm
  have hbga : (b : H) = g * (a : H) := by
    let e : ↥(elationGroup H Γ v) :=
      ⟨(b : H)⁻¹ * (g * (a : H)),
        (elationGroup H Γ v).mul_mem ((elationGroup H Γ v).inv_mem hbE)
          ((elationGroup H Γ v).mul_mem hgE haE)⟩
    have hefix : (e : H) • y = y := by
      show ((b : H)⁻¹ * (g * (a : H))) • y = y
      rw [mul_smul, hga_y, ← hby, ← mul_smul]
      simp
    have he1 : e = 1 := hfree e hy4 hefix
    have hHH : (b : H)⁻¹ * (g * (a : H)) = 1 := by
      have := congrArg Subtype.val he1
      simpa [e] using this
    exact inv_mul_eq_one.mp hHH
  have hbM : (b : H) • M = K := by
    rw [hbga, mul_smul, haM, hK]
  have hbz : (b : H) • z = g • z := by
    rw [hbga, mul_smul, haz]
  exact ⟨a, b, hbga, hbM, hbz, hby⟩


private theorem b_normalizes
    (hP : IsGeneralizedPolygon Γ 4) {p y M : V} {v : ZMod 8 → V}
    {g : H} (hgE : g ∈ elationGroup H Γ v)
    (hnorm : ∀ s : H, s ∈ elationGroup H Γ v → s • M = M →
      g * s * g⁻¹ ∈ elationGroup H Γ v ∧ (g * s * g⁻¹) • M = M)
    (S Sw : Subgroup H) (hS : S = elationGroup H Γ v ⊓ MulAction.stabilizer H M)
    (a : ↥S) (b : ↥Sw) (hbga : (b : H) = g * (a : H))
    {K w Mw : V} (hbM : (b : H) • M = K) (hby : (b : H) • y = w)
    (hyM : Γ.Adj y M) (hwMw : Γ.Adj w Mw) :
    (∀ σ : H, σ ∈ S → (b : H)⁻¹ * σ * (b : H) ∈ S) ∧
      (∀ σ : H, σ ∈ S → Γ.dist K (σ • Mw) ≤ 2) := by
  classical
  have haS : (a : H) ∈ S := a.2
  haveI hEfin : Fintype ↥(elationGroup H Γ v) :=
    Fintype.ofInjective (fun e : ↥(elationGroup H Γ v) => fun x : V => (e : H) • x)
      (by
        intro e f hef
        apply Subtype.ext
        exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H))
          (fun x => congrFun hef x))
  haveI hSfin : Fintype ↥S :=
    Fintype.ofInjective (fun θ : ↥S =>
        (⟨(θ : H), by
          have hθ : (θ : H) ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H M := by
            rw [← hS]
            exact θ.2
          exact (Subgroup.mem_inf.mp hθ).1⟩ : ↥(elationGroup H Γ v)))
      (by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ↥(elationGroup H Γ v) => (z : H)) hxy)
  have hg_map_le : Subgroup.map (MulAut.conj g) S ≤ S := by
    rintro x ⟨s, hs, rfl⟩
    have hs' : s ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H M := by
      rw [← hS]
      exact hs
    have hsE : s ∈ elationGroup H Γ v := (Subgroup.mem_inf.mp hs').1
    have hsM : s • M = M :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hs').2
    have hmem : g * s * g⁻¹ ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H M :=
      Subgroup.mem_inf.mpr ⟨(hnorm s hsE hsM).1,
        MulAction.mem_stabilizer_iff.mpr (hnorm s hsE hsM).2⟩
    rw [hS]
    show (MulAut.conj g) s ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H M
    rw [MulAut.conj_apply]
    exact hmem
  have hg_map_eq : Subgroup.map (MulAut.conj g) S = S := by
    refine Subgroup.eq_of_le_of_card_ge hg_map_le ?_
    exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm
  have hginv_norm : ∀ σ : H, σ ∈ S → g⁻¹ * σ * g ∈ S := by
    intro σ hσ
    have hmem : σ ∈ Subgroup.map (MulAut.conj g) S := by
      rw [hg_map_eq]
      exact hσ
    rw [Subgroup.mem_map] at hmem
    obtain ⟨s, hs, hseq⟩ := hmem
    have heq : g⁻¹ * σ * g = s := by
      rw [← hseq]
      show g⁻¹ * (g * s * g⁻¹) * g = s
      group
    rwa [heq]
  have hbconj : ∀ σ : H, σ ∈ S → (b : H)⁻¹ * σ * (b : H) ∈ S := by
    intro σ hσ
    have h1 : g⁻¹ * σ * g ∈ S := hginv_norm σ hσ
    rw [hbga]
    have heq : (g * (a : H))⁻¹ * σ * (g * (a : H)) =
        (a : H)⁻¹ * (g⁻¹ * σ * g) * (a : H) := by group
    rw [heq]
    exact S.mul_mem (S.mul_mem (S.inv_mem haS) h1) haS
  have hK_meets : ∀ σ : H, σ ∈ S → Γ.dist K (σ • Mw) ≤ 2 := by
    intro σ hσ
    have htS : (b : H)⁻¹ * σ * (b : H) ∈ S := hbconj σ hσ
    have htM : Γ.Adj M (((b : H)⁻¹ * σ * (b : H)) • y) := by
      have htMfix : ((b : H)⁻¹ * σ * (b : H)) • M = M := by
        have ht' : ((b : H)⁻¹ * σ * (b : H)) ∈
            elationGroup H Γ v ⊓ MulAction.stabilizer H M := by
          rw [← hS]
          exact htS
        exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp ht').2
      have h := (GraphAction.adj_smul ((b : H)⁻¹ * σ * (b : H)) y M).mpr hyM
      rw [htMfix] at h
      exact h.symm
    have hxK : Γ.Adj K (σ • w) := by
      have hx_eq : σ • w = (b : H) • (((b : H)⁻¹ * σ * (b : H)) • y) := by
        calc σ • w = σ • ((b : H) • y) := by rw [hby]
          _ = (σ * (b : H)) • y := by rw [← mul_smul]
          _ = ((b : H) * ((b : H)⁻¹ * σ * (b : H))) • y := by
              congr 1
              group
          _ = (b : H) • (((b : H)⁻¹ * σ * (b : H)) • y) := by rw [← mul_smul]
      rw [hx_eq]
      have h := (GraphAction.adj_smul (b : H) M
        (((b : H)⁻¹ * σ * (b : H)) • y)).mpr htM
      rw [hbM] at h
      exact h
    have hxMw : Γ.Adj (σ • Mw) (σ • w) := by
      have h := (GraphAction.adj_smul σ w Mw).mpr hwMw
      exact h.symm
    by_cases hEq : K = σ • Mw
    · rw [hEq, SimpleGraph.dist_self]; omega
    · have h2 : Γ.dist K (σ • Mw) = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hxK hxMw.symm hEq
      omega
  exact ⟨hbconj, hK_meets⟩


private theorem span_mem
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {y : V} {hy4 : Γ.dist p y = 4}
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    {g : H} {K w Mw zw Lw : V} (hK : K = g • M)
    (hdistpK : Γ.dist p K = 3) (hz'K : Γ.Adj (g • z) K)
    (hz'L : Γ.Adj L (g • z)) (hdistpM : Γ.dist p M = 3)
    (hpLw : Γ.Adj p Lw) (hLw_ne_L : Lw ≠ L) (hzwLw : Γ.Adj zw Lw)
    (hzwMw : Γ.Adj Mw zw) (hzwp : Γ.dist p zw = 2) (hyMw : Γ.Adj y Mw)
    (hdistpMw : Γ.dist p Mw = 3) (hdistLwM : Γ.dist Lw M = 4)
    (S : Subgroup H) (hS : S = elationGroup H Γ v ⊓ MulAction.stabilizer H M)
    (hS_orbit : (fun θ : ↥S => (θ : H) • y) '' Set.univ =
      Γ.neighborSet M \ {z})
    (hK_meets : ∀ σ : H, σ ∈ S → Γ.dist K (σ • Mw) ≤ 2) :
    K ∈ spanSet Γ Lw M := by
  classical
  intro N hN
  rw [mem_traceSet] at hN
  obtain ⟨hNLw, hNM⟩ := hN
  rw [SimpleGraph.dist_comm] at hNLw hNM
  obtain ⟨u, huLw, huN1⟩ :=
    hP.exists_adj_dist_succ (y := N) (v := Lw) (by rw [hNLw]; norm_num)
  obtain ⟨vN, hvM, hvN1⟩ :=
    hP.exists_adj_dist_succ (y := N) (v := M) (by rw [hNM]; norm_num)
  have huN : Γ.Adj N u := by
    have h1 : Γ.dist N u = 1 := by omega
    exact SimpleGraph.dist_eq_one_iff_adj.mp h1
  have hvN : Γ.Adj N vN := by
    have h1 : Γ.dist N vN = 1 := by omega
    exact SimpleGraph.dist_eq_one_iff_adj.mp h1
  have hzp2 : Γ.dist p z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpL hzL hzp.symm
  by_cases hvz : vN = z
  ·
    have hup : u = p := by
      by_contra hup
      have hcLw : c Lw = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpLw
      have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
      have h4 : Γ.dist u z = 4 := by
        have h := dist_eq_four_of_mem_two_lines hP c (L := Lw) (W := L) (z := p)
          (z1 := z) (z2 := u) hLw_ne_L hcLw hcL hpLw.symm hpL.symm hzL hzp huLw hup
        rwa [SimpleGraph.dist_comm] at h
      have huz : u ≠ z := by
        intro h
        have hLw_eq_L : Lw = L :=
          (existsUnique_commonNeighbor hP hzp2).unique
            ⟨hpLw, by rw [← h]; exact huLw.symm⟩ ⟨hpL, hzL.symm⟩
        exact hLw_ne_L hLw_eq_L
      have h2 : Γ.dist u z = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP huN.symm (by rw [← hvz]; exact hvN) huz
      omega
    have hN_eq_L : N = L :=
      (existsUnique_commonNeighbor hP hzp2).unique
        ⟨by rw [← hup]; exact huN.symm, by rw [← hvz]; exact hvN.symm⟩
        ⟨hpL, hzL.symm⟩
    have hKL : Γ.dist K L = 2 := by
      have hKLne : K ≠ L := by
        intro h
        rw [h] at hdistpK
        have h1 : Γ.dist p L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpL
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hz'K.symm hz'L.symm hKLne
    rw [hN_eq_L]
    omega
  ·
    have hvz' : z ≠ vN := fun h => hvz h.symm
    have hv4 : Γ.dist p vN = 4 :=
      dist_eq_four_of_mem_line_of_ne hP c hp (color_eq_one_of_adj_of_color_eq_zero
        (by
          have heven : Even (Γ.dist p y) := by rw [hy4]; norm_num
          have h : c p = c y := (hP.eq_iff_even_dist c p y).2 heven
          rw [hp] at h
          exact h.symm) hyM) hdistpM hzM.symm hvM hzp2 hvz'
    have hvset : vN ∈ Γ.neighborSet M \ {z} := ⟨by simpa using hvM, hvz⟩
    have hvimg : vN ∈ (fun a : ↥S => (a : H) • y) '' Set.univ := by
      rw [hS_orbit]
      exact hvset
    obtain ⟨a, -, hay⟩ := hvimg
    have haS : (a : H) ∈ S := a.2
    have haS' : (a : H) ∈ elationGroup H Γ v ⊓ MulAction.stabilizer H M := by
      rw [← hS]
      exact haS
    have haE : (a : H) ∈ elationGroup H Γ v := (Subgroup.mem_inf.mp haS').1
    have hap : (a : H) • p = p := by
      have h := elationGroup_le_whorlGroup v hv haE
      rw [hv0] at h
      exact whorlGroup_fix_self hP hT h
    have haLw : (a : H) • Lw = Lw := by
      have h := elationGroup_le_whorlGroup v hv haE
      rw [hv0] at h
      rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h
      exact h Lw hpLw
    have hay4 : Γ.dist p ((a : H) • y) = 4 := by
      have h := GPath.dist_smul hP.connected (a : H) p y
      rw [hap] at h
      rw [h]
      exact hy4
    have hcay : c ((a : H) • y) = 0 := by
      have heven : Even (Γ.dist p ((a : H) • y)) := by rw [hay4]; norm_num
      have h : c p = c ((a : H) • y) :=
        (hP.eq_iff_even_dist c p ((a : H) • y)).2 heven
      rw [hp] at h
      exact h.symm
    have hnot : ¬ Γ.Adj ((a : H) • y) Lw := by
      intro h
      have h2 : Γ.dist Lw M = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP h.symm
          (by rw [show (a : H) • y = vN from hay]; exact hvM.symm) (by
          intro hh
          rw [hh, SimpleGraph.dist_self] at hdistLwM
          omega)
      omega
    have hayLw : Γ.dist ((a : H) • y) Lw = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hnot
        (by rw [hcay, color_eq_one_of_adj_of_color_eq_zero hp hpLw]; decide)
    have hyzw2 : Γ.dist y zw = 2 := by
      have hyne : y ≠ zw := by
        intro h
        rw [h] at hy4
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hyMw hzwMw hyne
    have hazw2 : Γ.dist ((a : H) • y) ((a : H) • zw) = 2 := by
      rw [GPath.dist_smul hP.connected (a : H) y zw]
      exact hyzw2
    have hazwLw : Γ.Adj Lw ((a : H) • zw) := by
      have h := (GraphAction.adj_smul (a : H) zw Lw).mpr hzwLw
      rw [haLw] at h
      exact h.symm
    have hvN' : Γ.Adj N ((a : H) • y) := by
      rw [show (a : H) • y = vN from hay]
      exact hvN
    have huzw : u = (a : H) • zw := by
      have hne : u ≠ (a : H) • y := by
        intro h
        have hAdj : Γ.Adj Lw ((a : H) • y) := by rw [← h]; exact huLw
        exact hnot hAdj.symm
      have hau2 : Γ.dist ((a : H) • y) u = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hvN'.symm huN hne.symm
      exact ((existsUnique_proj hP hayLw).unique ⟨hazwLw, hazw2⟩ ⟨huLw, hau2⟩).symm
    have hN_eq : N = (a : H) • Mw := by
      have hne : (a : H) • y ≠ u := by
        intro h
        have hAdj : Γ.Adj Lw ((a : H) • y) := by rw [h]; exact huLw
        exact hnot hAdj.symm
      have hdist : Γ.dist ((a : H) • y) u = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hvN'.symm huN hne
      refine (existsUnique_commonNeighbor hP hdist).unique ?_ ?_
      · exact ⟨hvN'.symm, huN.symm⟩
      · exact ⟨(GraphAction.adj_smul (a : H) y Mw).mpr hyMw,
          by rw [huzw]; exact (GraphAction.adj_smul (a : H) zw Mw).mpr hzwMw.symm⟩
    rw [hN_eq]
    exact hK_meets a haS


public theorem normalizer_stabilizer_fixes
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (h2 : ∀ L M, Γ.Adj p L → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2)
    (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v) (hv0 : v 0 = p)
    {y : V} (hy4 : Γ.dist p y = 4)
    {L z M : V} (hpL : Γ.Adj p L) (hzL : Γ.Adj L z) (hzp : z ≠ p)
    (hyz : Γ.dist y z = 2) (hyM : Γ.Adj y M) (hzM : Γ.Adj z M)
    (hEcard : Nat.card ↥(elationGroup H Γ v) = s * t * s)
    (hfree : ∀ (e : ↥(elationGroup H Γ v)) {x : V}, Γ.dist p x = 4 →
      (e : H) • x = x → e = 1)
    {g : H} (hgE : g ∈ elationGroup H Γ v)
    (hnorm : ∀ s : H, s ∈ elationGroup H Γ v → s • M = M →
      g * s * g⁻¹ ∈ elationGroup H Γ v ∧ (g * s * g⁻¹) • M = M) :
    g • z = z := by
  classical
  let E : Subgroup H := elationGroup H Γ v
  let S : Subgroup H := E ⊓ MulAction.stabilizer H M
  have hSdef : S = elationGroup H Γ v ⊓ MulAction.stabilizer H M := rfl
  obtain ⟨hS_eq_U, hScard, hS_orbit⟩ :=
    noSpansTwo_base_data (hP := hP) (hT := hT) (c := c) (hdeg := hdeg) (hst := hst)
      (hM := hM) (hp := hp) (h1 := h1) (v := v) (hv := hv) (hv0 := hv0)
      (hy4 := hy4) (hpL := hpL) (hzL := hzL) (hzp := hzp) (hyz := hyz)
      (hyM := hyM) (hzM := hzM) (hfree := hfree) S hSdef
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
  by_contra hgz
  let K : V := g • M
  have hK : K = g • M := rfl
  obtain ⟨hdistpK, hcK, hz'K, hz'L, hz'p, hyK, hdistyK⟩ :=
    noSpansTwo_K_data (hP := hP) (hT := hT) (c := c) (hdeg := hdeg) (hM := hM)
      (hp := hp) (v := v) (hv := hv) (hv0 := hv0) (hy4 := hy4) (hpL := hpL)
      (hzL := hzL) (hzp := hzp) (hyz := hyz) (hyM := hyM) (hzM := hzM)
      (hgE := hgE) (hgz := hgz) K hK
  obtain ⟨w, Mw, hwK, hyw, hwne, hyMw, hwMw, hKM_disj, hMw_ne_M⟩ :=
    noSpansTwo_w_data (hP := hP) (c := c) (hp := hp) (hy4 := hy4) (hpL := hpL)
      (hzL := hzL) (hzp := hzp) (hyz := hyz) (hyM := hyM) (hzM := hzM)
      (hgz := hgz) (K := K) (hK := hK) (hdistpM := hdistpM) (hdistpK := hdistpK)
      (hcK := hcK) (hz'K := hz'K) (hz'L := hz'L) (hz'p := hz'p) (hyK := hyK)
      (hdistyK := hdistyK)
  have hw4 : Γ.dist p w = 4 :=
    dist_eq_four_of_mem_line_of_ne hP c hp hcK hdistpK hz'K.symm hwK hz'p hwne.symm
  obtain ⟨zw, Lw, hzwMw, hzwp, hpLw, hzwLw, hLw_ne_L, hdistLwM, hdistpMw, hLwMw⟩ :=
    noSpansTwo_Lw_data (hP := hP) (c := c) (hp := hp) (hy4 := hy4) (hpL := hpL)
      (hzL := hzL) (hzp := hzp) (hyz := hyz) (hyM := hyM) (hzM := hzM)
      (hKM_disj := hKM_disj) (hdistpK := hdistpK) (hz'K := hz'K) (hz'L := hz'L)
      (hdistpM := hdistpM) (hMw_ne_M := hMw_ne_M) (hyMw := hyMw) (hwMw := hwMw)
  have hcMw : c Mw = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyMw
  obtain ⟨hSw_eq_Uw, hSwcard, hSw_orbit⟩ :=
    sw_data (hP := hP) (hT := hT) (c := c) (hdeg := hdeg) (hst := hst)
      (hM := hM) (hp := hp) (h1 := h1) (v := v) (hv := hv) (hv0 := hv0)
      (hy4 := hy4) (hpLw := hpLw) (hzwLw := hzwLw) (hzwp := hzwp)
      (hLwMw := hLwMw) (hyMw := hyMw) (hzwMw := hzwMw) (hcMw := hcMw)
      (hdistpMw := hdistpMw) (hfree := hfree)
  let Sw : Subgroup H := elationGroup H Γ v ⊓ MulAction.stabilizer H Mw
  have hSwdef : Sw = elationGroup H Γ v ⊓ MulAction.stabilizer H Mw := rfl
  obtain ⟨a, b, hbga, hbM, hbz, hby⟩ :=
    b_exists (hP := hP) (c := c) (hdeg := hdeg) (hM := hM) (hT := hT) (hp := hp)
      (v := v) (hv := hv) (hv0 := hv0) (hy4 := hy4) (hpL := hpL) (hzL := hzL)
      (hzp := hzp) (hyz := hyz) (hyM := hyM) (hzM := hzM) (hfree := hfree)
      (hgE := hgE) (hgz := hgz) (hK := hK) (hwK := hwK) (hw4 := hw4)
      (hwMw := hwMw) (hwne := hwne) (hzwMw := hzwMw) (hzwp := hzwp)
      (S := S) (Sw := Sw) (hS := hSdef) (hSw := hSwdef)
      (hS_eq_U := hS_eq_U) (hS_orbit := hS_orbit) (hSw_orbit := hSw_orbit)
  obtain ⟨hbconj, hK_meets⟩ :=
    b_normalizes (hP := hP) (p := p) (v := v) (hgE := hgE) (hnorm := hnorm)
      (S := S) (Sw := Sw) (hS := hSdef) (a := a) (b := b) (hbga := hbga)
      (hbM := hbM) (hby := hby) (hyM := hyM) (hwMw := hwMw)
  have hK_span : K ∈ spanSet Γ Lw M :=
    span_mem (hP := hP) (hT := hT) (c := c) (hdeg := hdeg) (hM := hM) (hp := hp)
      (v := v) (hv := hv) (hv0 := hv0) (hy4 := hy4) (hpL := hpL) (hzL := hzL)
      (hzp := hzp) (hyz := hyz) (hyM := hyM) (hzM := hzM) (hK := hK) (w := w)
      (hdistpK := hdistpK) (hz'K := hz'K) (hz'L := hz'L) (hdistpM := hdistpM)
      (hpLw := hpLw) (hLw_ne_L := hLw_ne_L) (hzwLw := hzwLw) (hzwMw := hzwMw)
      (hzwp := hzwp) (hyMw := hyMw) (hdistpMw := hdistpMw)
      (hdistLwM := hdistLwM) (S := S) (hS := hSdef) (hS_orbit := hS_orbit)
      (hK_meets := hK_meets)
  have hKLw_ne : K ≠ Lw := by
    intro h
    rw [h] at hdistpK
    have h1 : Γ.dist p Lw = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpLw
    omega
  have hKM_ne : K ≠ M := by
    intro h
    exact hKM_disj z ⟨by rw [h]; exact hzM.symm, hzM.symm⟩
  have hLwM_ne : Lw ≠ M := by
    intro h
    rw [h, SimpleGraph.dist_self] at hdistLwM
    omega
  have hsub : ({K, Lw, M} : Set V) ⊆ spanSet Γ Lw M := by
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact hK_span
    · exact left_mem_spanSet hdistLwM
    · exact right_mem_spanSet hdistLwM
  have hcard3 : ({K, Lw, M} : Set V).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨K, Lw, M, hKLw_ne, hKM_ne, hLwM_ne, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard3] at hle
  have h2c := h2 Lw M hpLw hdistLwM
  omega

end Fixed

end CFSG.Geometry.GeneralizedQuadrangles
