module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderChar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open Module

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def dispOf (g : V ≃ₗ[k] V) : Submodule k V := LinearMap.range ((g : V →ₗ[k] V) - 1)

theorem mem_dispOf {g : V ≃ₗ[k] V} {v : V} : v ∈ dispOf g ↔ ∃ u, g u - u = v := by
  simp [dispOf, LinearMap.mem_range]

theorem sub_mem_dispOf (g : V ≃ₗ[k] V) (u : V) : g u - u ∈ dispOf g := mem_dispOf.2 ⟨u, rfl⟩

theorem commGL_le_iff {X : Subgroup (V ≃ₗ[k] V)} {Z : Submodule k V} :
    commGL X ⊤ ≤ Z ↔ X ≤ trivMod Z := by
  constructor
  · intro h x hx w
    exact h (Submodule.subset_span ⟨x, hx, w, Submodule.mem_top, rfl⟩)
  · intro h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, u, -, rfl⟩
    exact h hx u

theorem dispOf_le_commGL {X : Subgroup (V ≃ₗ[k] V)} {g : V ≃ₗ[k] V} (hg : g ∈ X) :
    dispOf g ≤ commGL X ⊤ := by
  intro v hv
  obtain ⟨u, rfl⟩ := mem_dispOf.1 hv
  exact Submodule.subset_span ⟨g, hg, u, Submodule.mem_top, rfl⟩

theorem commGL_zpowers (g : V ≃ₗ[k] V) : commGL (Subgroup.zpowers g) ⊤ = dispOf g :=
  le_antisymm (commGL_le_iff.2 (Subgroup.zpowers_le.2 fun w => sub_mem_dispOf g w))
    (dispOf_le_commGL (Subgroup.mem_zpowers g))

theorem le_trivMod_commGL (X : Subgroup (V ≃ₗ[k] V)) : X ≤ trivMod (commGL X ⊤) :=
  commGL_le_iff.1 le_rfl

theorem fixed_of_disp_of_pow_three [CharP k 2] {a : V ≃ₗ[k] V} (ha3 : a ^ 3 = 1) {w : V}
    (hw : w ∈ dispOf a) (hfix : a w = w) : w = 0 := by
  obtain ⟨u, rfl⟩ := mem_dispOf.1 hw
  have h3 : ∀ v, a (a (a v)) = v := fun v => by
    have := congrArg (fun e : V ≃ₗ[k] V => e v) ha3
    simpa [pow_succ] using this
  have h1 : a (a u - u) = a u - u := hfix
  rw [map_sub] at h1
  have h2 : a (a u) = -u := by
    have : a (a u) = (a u - u) + a u := sub_eq_iff_eq_add.1 h1
    rw [this, sub_add_eq_add_sub, char_two_add_self k, zero_sub]
  have h4 : u = - a u := by
    have := h3 u
    rw [h2, map_neg] at this
    exact this.symm
  have h5 : a u = -u := by
    have := congrArg Neg.neg h4
    simpa using this.symm
  rw [h5, ← neg_add', char_two_add_self k, neg_zero]

theorem irreducible_of_rank_two [CharP k 2] (hk : Nat.card k = 2) [Module.Finite k V]
    {a : V ≃ₗ[k] V} (ha3 : a ^ 3 = 1) (hr : finrank k (dispOf a) = 2)
    (U : Submodule k V) (hU : U ≤ dispOf a) (hinv : ∀ u ∈ U, a u ∈ U) :
    U = ⊥ ∨ U = dispOf a := by
  have hle : finrank k U ≤ 2 := hr ▸ Submodule.finrank_mono hU
  rcases Nat.lt_or_ge (finrank k U) 2 with hlt | hge
  · rcases (by omega : finrank k U = 0 ∨ finrank k U = 1) with h0 | h1
    · left; exact Submodule.finrank_eq_zero.1 h0
    · exfalso
      obtain ⟨⟨u, hu⟩, hu0, hspan⟩ := finrank_eq_one_iff'.1 h1
      obtain ⟨c, hc⟩ := hspan ⟨a u, hinv u hu⟩
      have hc' : c • u = a u := congrArg Subtype.val hc
      have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
      have hc0 : c ≠ 0 := by
        intro h
        rw [h, zero_smul] at hc'
        exact hu0' (a.injective (by rw [← hc', map_zero]))
      have hc1 := eq_one_of_ne_zero_of_card_two k hk hc0
      rw [hc1, one_smul] at hc'
      exact hu0' (fixed_of_disp_of_pow_three ha3 (hU hu) hc'.symm)
  · right
    exact Submodule.eq_of_le_of_finrank_eq hU (by omega)

theorem isPGroup_of_le {G : Type*} [Group G] {p : ℕ} {B A : Subgroup G} (hB : IsPGroup p B)
    (hAB : A ≤ B) : IsPGroup p A := by
  intro g
  obtain ⟨n, hn⟩ := hB ⟨g.1, hAB g.2⟩
  exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩

theorem eq_one_of_sq_of_isPGroup_three {G : Type*} [Group G] {B : Subgroup G} (hB : IsPGroup 3 B)
    {g : G} (hg : g ∈ B) (h2 : g * g = 1) : g = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 hB ⟨g, hg⟩
  have hn' : orderOf g = 3 ^ n := (Subgroup.orderOf_coe (⟨g, hg⟩ : B)).trans hn
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rw [hn'] at hdvd
  rcases n with _ | n
  · rw [pow_zero] at hn'
    exact orderOf_eq_one_iff.1 hn'
  · exfalso
    have h3 : 3 ∣ 2 := (dvd_pow_self 3 (Nat.succ_ne_zero n)).trans hdvd
    omega

theorem natCard_le_of_dvd {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G) {N m : ℕ}
    (hdvd : Nat.card G ∣ N) (hN : ¬ 3 ^ (m + 1) ∣ N) : Nat.card G ≤ 3 ^ m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hG.exists_card_eq
  rw [hj] at hdvd ⊢
  by_contra hlt
  have hmj : m + 1 ≤ j := by
    by_contra h
    exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact hN ((pow_dvd_pow 3 hmj).trans hdvd)

theorem comm_of_isPGroup_three_card_le {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (h9 : Nat.card G ≤ 9) : ∀ a b : G, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hG.exists_card_eq
  have hm2 : m ≤ 2 := by
    by_contra h
    have h27 : 27 ≤ 3 ^ m := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m
  · have h1 : Nat.card G = 1 := by simpa using hm
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 h1
    intro a b
    exact Subsingleton.elim _ _
  · have : IsCyclic G := isCyclic_of_prime_card (p := 3) (by simpa using hm)
    intro a b
    exact (inferInstance : IsMulCommutative G).is_comm.comm a b
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (by simpa using hm)).is_comm.comm

theorem mul_self_eq_one_of_trivMod [CharP k 2] {W : Submodule k V} {g : V ≃ₗ[k] V}
    (hg : g ∈ trivMod W) (hfix : ∀ w ∈ W, g w = w) : g * g = 1 := by
  ext v
  have h2 : g (g v - v) = g v - v := hfix _ (hg v)
  rw [map_sub] at h2
  have h3 : g (g v) = (g v - v) + g v := sub_eq_iff_eq_add.1 h2
  show g (g v) = v
  rw [h3, sub_add_eq_add_sub, char_two_add_self k, zero_sub, neg_eq_self_of_char_two_module k]

theorem eq_one_of_trivMod_of_pGroup [CharP k 2] {B : Subgroup (V ≃ₗ[k] V)} (hB : IsPGroup 3 B)
    {W : Submodule k V} (hBW : B ≤ trivMod W) {g : V ≃ₗ[k] V} (hg : g ∈ B)
    (hfix : ∀ w ∈ W, g w = w) : g = 1 :=
  eq_one_of_sq_of_isPGroup_three hB hg (mul_self_eq_one_of_trivMod (hBW hg) hfix)

theorem card_dvd_of_trivMod [CharP k 2] {A : Subgroup (V ≃ₗ[k] V)} (hA : IsPGroup 3 A)
    {W : Submodule k V} (hAW : A ≤ trivMod W) : Nat.card A ∣ Nat.card (W ≃ₗ[k] W) := by
  have hW : ∀ g : A, ∀ w ∈ W, A.subtype g w ∈ W := fun g w hw => by
    have h1 : g.1 w - w ∈ W := hAW g.2 w
    simpa using W.add_mem h1 hw
  refine Subgroup.card_dvd_of_injective (resHom A.subtype W hW) ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hker : g ∈ (resHom A.subtype W hW).ker := hg
  rw [ker_resHom, mem_centSub] at hker
  exact Subtype.ext (eq_one_of_trivMod_of_pGroup hA hAW g.2 fun w hw => hker w hw)

theorem natCard_linearEquiv_eq [Finite k] [Module.Finite k V] {d : ℕ} (hd : finrank k V = d) :
    Nat.card (V ≃ₗ[k] V) = ∏ i : Fin d, (Nat.card k ^ d - Nat.card k ^ (i : ℕ)) := by
  have : Fintype k := Fintype.ofFinite k
  let b := Module.finBasisOfFinrankEq k V hd
  have h1 : Nat.card (V ≃ₗ[k] V) = Nat.card (Matrix.GeneralLinearGroup (Fin d) k) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, Nat.card_eq_fintype_card (α := k)]


theorem binary_three_group_rank_two_elements_commute [Module.Finite k V] (hk : Nat.card k = 2)
    {B : Subgroup (V ≃ₗ[k] V)} (hB : IsPGroup 3 B) {a b : V ≃ₗ[k] V} (ha : a ∈ B) (hb : b ∈ B)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hra : finrank k (dispOf a) = 2) (hrb : finrank k (dispOf b) = 2) :
    a * b = b * a := by
  have := charP_two_of_card_two k hk
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Finite V := Module.finite_of_finite k
  have : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨W, hW⟩ : ∃ W : Submodule k V, W = dispOf a ⊔ dispOf b := ⟨_, rfl⟩
  have haW : dispOf a ≤ W := hW ▸ le_sup_left
  have hbW : dispOf b ≤ W := hW ▸ le_sup_right
  have hWle : finrank k W ≤ 4 := by
    have := Submodule.finrank_add_le_finrank_add_finrank (dispOf a) (dispOf b)
    rw [← hW] at this
    omega
  have hWge : 2 ≤ finrank k W := hra ▸ Submodule.finrank_mono haW
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (V ≃ₗ[k] V), A = Subgroup.closure {a, b} := ⟨_, rfl⟩
  have haA : a ∈ A := hA ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbA : b ∈ A := hA ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hAB : A ≤ B := by
    rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have hAW : A ≤ trivMod W := by
    rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact fun w => haW (sub_mem_dispOf _ w)
    · exact fun w => hbW (sub_mem_dispOf _ w)
  have hA3 : IsPGroup 3 A := isPGroup_of_le hB hAB
  have hdvd := card_dvd_of_trivMod hA3 hAW
  have hN : ¬ 27 ∣ Nat.card (W ≃ₗ[k] W) := by
    rcases (by omega : finrank k W = 2 ∨ finrank k W = 3 ∨ finrank k W = 4) with h | h | h <;>
      rw [natCard_linearEquiv_eq h, hk] <;> norm_num [Fin.prod_univ_succ]
  have h9 : Nat.card A ≤ 3 ^ 2 := natCard_le_of_dvd hA3 hdvd (by simpa using hN)
  have hcomm := comm_of_isPGroup_three_card_le hA3 (by simpa using h9)
  exact congrArg Subtype.val (hcomm ⟨a, haA⟩ ⟨b, hbA⟩)

theorem binary_three_group_rank_two_generated_isElementaryAbelian [Module.Finite k V]
    (hk : Nat.card k = 2) {B : Subgroup (V ≃ₗ[k] V)} (hB : IsPGroup 3 B)
    {S : Set (V ≃ₗ[k] V)} (hSB : S ⊆ B)
    (hS : ∀ s ∈ S, orderOf s = 3 ∧ finrank k (dispOf s) = 2) :
    CFSG.IsElementaryAbelian 3 (Subgroup.closure S) := by
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
    binary_three_group_rank_two_elements_commute hk hB (hSB hs) (hSB ht) (hS s hs).1 (hS t ht).1
      (hS s hs).2 (hS t ht).2
  have hpair : S.Pairwise Commute := fun s hs t ht _ => hcomm s hs t ht
  have : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hpair
  have hall : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact Subtype.ext (hall a a.2 b b.2)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
    show (x : V ≃ₗ[k] V) ^ 3 = 1
    refine Subgroup.closure_induction (p := fun y _ => y ^ 3 = 1) ?_ ?_ ?_ ?_ x.2
    · intro s hs
      rw [← (hS s hs).1]
      exact pow_orderOf_eq_one s
    · exact one_pow 3
    · intro y z hy hz hy3 hz3
      have hyz : Commute y z := hall y hy z hz
      rw [hyz.mul_pow, hy3, hz3, one_mul]
    · intro y hy hy3
      rw [inv_pow, hy3, inv_one]

theorem isCompl_commGL_fixGL_of_odd [CharP k 2] (D : Subgroup (V ≃ₗ[k] V)) [Finite D]
    (hodd : Odd (Nat.card D)) : IsCompl (commGL D ⊤) (fixGL D) := by
  classical
  have := Fintype.ofFinite D
  let p : V →ₗ[k] V := ∑ d : D, ((d : V ≃ₗ[k] V) : V →ₗ[k] V)
  have hp : ∀ v, p v = ∑ d : D, (d : V ≃ₗ[k] V) v := fun v => by simp [p, LinearMap.sum_apply]
  have hp1 : ∀ x ∈ D, ∀ v, p (x v) = p v := by
    intro x hx v
    rw [hp, hp]
    exact Equiv.sum_comp (Equiv.mulRight (⟨x, hx⟩ : D)) (fun d : D => (d : V ≃ₗ[k] V) v)
  have hp2 : ∀ x ∈ D, ∀ v, x (p v) = p v := by
    intro x hx v
    rw [hp, map_sum]
    exact Equiv.sum_comp (Equiv.mulLeft (⟨x, hx⟩ : D)) (fun d : D => (d : V ≃ₗ[k] V) v)
  have hcard : ((Fintype.card D : ℕ) : k) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_eq_one_of_odd_char_two k hodd
  have hp3 : ∀ w, (∀ x ∈ D, x w = w) → p w = w := by
    intro w hw
    rw [hp]
    have : ∀ d : D, (d : V ≃ₗ[k] V) w = w := fun d => hw d d.2
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, hcard, one_smul]
  have hgen : ∀ x ∈ D, ∀ u, x u - u ∈ commGL D ⊤ := fun x hx u =>
    Submodule.subset_span ⟨x, hx, u, Submodule.mem_top, rfl⟩
  have hp4 : ∀ v, v - p v ∈ commGL D ⊤ := by
    intro v
    have h1 : v - p v = ∑ d : D, (v - (d : V ≃ₗ[k] V) v) := by
      rw [hp, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul k, hcard, one_smul]
    rw [h1]
    refine Submodule.sum_mem _ fun d _ => ?_
    have := (commGL D ⊤).neg_mem (hgen d d.2 v)
    simpa using this
  have hp5 : ∀ w ∈ commGL D ⊤, p w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, u, -, rfl⟩ := hw
      show p (x u - u) = 0
      rw [map_sub, hp1 x hx u, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, hx, smul_zero]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro w hw1 hw2
    calc w = p w := (hp3 w hw2).symm
      _ = 0 := hp5 w hw1
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    exact Submodule.mem_sup.2 ⟨v - p v, hp4 v, p v, fun x hx => hp2 x hx v, by abel⟩


theorem binary_three_group_rank_two_generators_disjoint_natural_planes
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite k V] (hk : Nat.card k = 2)
    (L : ι → Subgroup (V ≃ₗ[k] V)) (hL : Function.Injective L)
    (hcyc : ∀ i, IsCyclic (L i)) (hord : ∀ i, Nat.card (L i) = 3)
    (hD : IsPGroup 3 (⨆ i, L i : Subgroup (V ≃ₗ[k] V)))
    (hrk : ∀ i, finrank k (commGL (L i) ⊤) = 2) :
    (∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧ iSupIndep L ∧
    iSupIndep (fun i => commGL (L i) ⊤) ∧
    commGL (⨆ i, L i) ⊤ = ⨆ i, commGL (L i) ⊤ ∧
    IsCompl (commGL (⨆ i, L i) ⊤) (fixGL (⨆ i, L i)) ∧
    (∀ i, ∀ U : Submodule k V, U ≤ commGL (L i) ⊤ → (∀ x ∈ L i, ∀ u ∈ U, x u ∈ U) →
      U = ⊥ ∨ U = commGL (L i) ⊤) ∧
    (∀ i j, i ≠ j → ∀ x ∈ L i, ∀ v ∈ commGL (L j) ⊤, x v = v) ∧
    (∀ i, ∀ x ∈ L i, ∀ v ∈ fixGL (⨆ i, L i), x v = v) ∧
    (∀ g ∈ (⨆ i, L i : Subgroup (V ≃ₗ[k] V)),
      (∀ w ∈ commGL (⨆ i, L i) ⊤, g w = w) → g = 1) := by
  classical
  have := charP_two_of_card_two k hk
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Finite V := Module.finite_of_finite k
  have : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup (V ≃ₗ[k] V), D = ⨆ i, L i := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  have hLD : ∀ i, L i ≤ D := fun i => hDdef ▸ le_iSup L i
  have hgen : ∀ i, ∃ a : V ≃ₗ[k] V, L i = Subgroup.zpowers a ∧ orderOf a = 3 := by
    intro i
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L i)
    have h1 : L i = Subgroup.zpowers (g : V ≃ₗ[k] V) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
        exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
      · intro hx
        exact (Subgroup.zpowers_le.2 g.2) hx
    refine ⟨g, h1, ?_⟩
    have := Nat.card_zpowers (g : V ≃ₗ[k] V)
    rw [← h1, hord i] at this
    exact this.symm
  choose a haL ha3 using hgen
  have haLi : ∀ i, a i ∈ L i := fun i => haL i ▸ Subgroup.mem_zpowers (a i)
  have haD : ∀ i, a i ∈ D := fun i => hLD i (haLi i)
  have hI : ∀ i, commGL (L i) ⊤ = dispOf (a i) := fun i => by rw [haL i, commGL_zpowers]
  have hrk' : ∀ i, finrank k (dispOf (a i)) = 2 := fun i => (hI i) ▸ hrk i
  have ha3' : ∀ i, a i ^ 3 = 1 := fun i => by rw [← ha3 i]; exact pow_orderOf_eq_one _
  have hcommgen : ∀ i j, a i * a j = a j * a i := fun i j =>
    binary_three_group_rank_two_elements_commute hk hD (haD i) (haD j) (ha3 i) (ha3 j)
      (hrk' i) (hrk' j)
  have hcomm : ∀ i j, ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x := by
    intro i j x hx y hy
    rw [haL i] at hx
    rw [haL j] at hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow (hcommgen i j) n m).eq
  have hDcent : ∀ i, ∀ x ∈ D, a i * x = x * a i := by
    intro i x hx
    have : D ≤ Subgroup.centralizer {a i} := by
      rw [hDdef]
      refine iSup_le fun j => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm i j _ (haLi i) y hy
    exact Subgroup.mem_centralizer_iff.1 (this hx) (a i) rfl
  have hIinv : ∀ i, ∀ x ∈ D, ∀ v ∈ dispOf (a i), x v ∈ dispOf (a i) := by
    intro i x hx v hv
    obtain ⟨u, rfl⟩ := mem_dispOf.1 hv
    have hc : a i (x u) = x (a i u) := congrArg (fun e : V ≃ₗ[k] V => e u) (hDcent i x hx)
    have : x (a i u - u) = a i (x u) - x u := by rw [map_sub, hc]
    rw [this]
    exact sub_mem_dispOf _ _
  have hirr : ∀ i, ∀ U : Submodule k V, U ≤ dispOf (a i) → (∀ u ∈ U, a i u ∈ U) →
      U = ⊥ ∨ U = dispOf (a i) := fun i U hU hinv =>
    irreducible_of_rank_two hk (ha3' i) (hrk' i) U hU hinv
  have hdisj : ∀ i j, i ≠ j → dispOf (a i) ⊓ dispOf (a j) = ⊥ := by
    intro i j hij
    rcases hirr i (dispOf (a i) ⊓ dispOf (a j)) inf_le_left
      (fun u hu => ⟨hIinv i (a i) (haD i) u hu.1, hIinv j (a i) (haD i) u hu.2⟩) with h | h
    · exact h
    · exfalso
      have hle : dispOf (a i) ≤ dispOf (a j) := h.symm.le.trans inf_le_right
      have heq : dispOf (a i) = dispOf (a j) :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hrk' i, hrk' j])
      have hE : L i ⊔ L j ≤ trivMod (dispOf (a i)) := by
        refine sup_le ?_ ?_
        · rw [haL i]; exact Subgroup.zpowers_le.2 fun w => sub_mem_dispOf _ w
        · rw [haL j]; exact Subgroup.zpowers_le.2 fun w => heq ▸ sub_mem_dispOf _ w
      have hE3 : IsPGroup 3 (L i ⊔ L j : Subgroup (V ≃ₗ[k] V)) :=
        isPGroup_of_le hD (sup_le (hLD i) (hLD j))
      have hdvd := card_dvd_of_trivMod hE3 hE
      have h6 : Nat.card (dispOf (a i) ≃ₗ[k] dispOf (a i)) = 6 := by
        rw [natCard_linearEquiv_eq (hrk' i), hk]; norm_num [Fin.prod_univ_succ]
      rw [h6] at hdvd
      have hle3 : Nat.card (L i ⊔ L j : Subgroup (V ≃ₗ[k] V)) ≤ 3 ^ 1 :=
        natCard_le_of_dvd hE3 hdvd (by norm_num)
      have hEi : L i = L i ⊔ L j :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hord i]; simpa using hle3)
      have hEj : L j = L i ⊔ L j :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hord j]; simpa using hle3)
      exact hij (hL (hEi.trans hEj.symm))
  have hcent : ∀ i j, i ≠ j → ∀ x ∈ L j, ∀ v ∈ dispOf (a i), x v = v := by
    intro i j hij x hx v hv
    have h1 : x v - v ∈ dispOf (a i) := (dispOf (a i)).sub_mem (hIinv i x (hLD j hx) v hv) hv
    have h2 : x v - v ∈ dispOf (a j) := by
      rw [← hI j]
      exact Submodule.subset_span ⟨x, hx, v, Submodule.mem_top, rfl⟩
    have h3 : x v - v ∈ dispOf (a i) ⊓ dispOf (a j) := ⟨h1, h2⟩
    rw [hdisj i j hij, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  have hindI : iSupIndep (fun i => commGL (L i) ⊤) := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    have hle : (⨆ j, ⨆ (_ : j ≠ i), commGL (L j) ⊤) ≤
        LinearMap.ker ((a i : V →ₗ[k] V) - 1) := by
      refine iSup₂_le fun j hj => ?_
      intro w hw
      rw [hI j] at hw
      have := hcent j i hj (a i) (haLi i) w hw
      simp [LinearMap.mem_ker, this]
    have hfix : a i v = v := by
      have := hle hv2
      simpa [LinearMap.mem_ker, sub_eq_zero] using this
    have hv1' : v ∈ dispOf (a i) := by rw [← hI i]; exact hv1
    exact (Submodule.mem_bot k).2 (fixed_of_disp_of_pow_three (ha3' i) hv1' hfix)
  have hindL : iSupIndep L := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hle : (⨆ j, ⨆ (_ : j ≠ i), L j) ≤
        centSub (MonoidHom.id (V ≃ₗ[k] V)) (dispOf (a i)) := by
      refine iSup₂_le fun j hj => ?_
      intro y hy v hv
      exact hcent i j (Ne.symm hj) y hy v hv
    have hfix := hle hx2
    have hxL : x ∈ L i := hx1
    have hx1' : x = 1 := eq_one_of_trivMod_of_pGroup (isPGroup_of_le hD (hLD i))
      (W := dispOf (a i)) (by rw [← hI i]; exact le_trivMod_commGL (L i)) hxL
      (fun v hv => hfix v hv)
    exact Subgroup.mem_bot.2 hx1'
  have hW : commGL D ⊤ = ⨆ i, commGL (L i) ⊤ := by
    refine le_antisymm ?_ (iSup_le fun i => ?_)
    · rw [commGL_le_iff, hDdef]
      refine iSup_le fun i => ?_
      exact commGL_le_iff.1 (le_iSup (fun i => commGL (L i) ⊤) i)
    · exact commGL_le_iff.2 ((hLD i).trans (le_trivMod_commGL D))
  have hodd : Odd (Nat.card D) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  refine ⟨fun i j _ x hx y hy => hcomm i j x hx y hy, hindL, hindI, hW,
    isCompl_commGL_fixGL_of_odd D hodd, ?_, ?_, ?_,
    fun g hg hfix => eq_one_of_trivMod_of_pGroup hD (le_trivMod_commGL D) hg hfix⟩
  · intro i U hU hinv
    rw [hI i] at hU ⊢
    exact hirr i U hU (fun u hu => hinv (a i) (haLi i) u hu)
  · intro i j hij x hx v hv
    rw [hI j] at hv
    exact hcent j i (Ne.symm hij) x hx v hv
  · intro i x hx v hv
    exact hv x (hLD i hx)

end CFSG.QuasithinUnique.Setup.Offender
