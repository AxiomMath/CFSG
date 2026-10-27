module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.ClassicalInvolution

open scoped MatrixGroups commutatorElement

structure IsClassicalSL2 (F : Type*) [Field F] {G : Type*} [Group G] (J : Subgroup G) (d : G) :
    Prop where
  nonempty_mulEquiv : Nonempty (J ≃* SL(2, F))
  mem : d ∈ J
  orderOf_eq_two : orderOf d = 2
  le_centralizer : J ≤ Subgroup.centralizer ({d} : Set G)
  centralizer_le_normalizer : Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (J : Set G)

@[expose] def IsTightPair {G : Type*} [Group G] (J K : Subgroup G) : Prop :=
  Odd (Nat.card (J ⊓ K : Subgroup G))

theorem IsTightPair.symm {G : Type*} [Group G] {J K : Subgroup G} (h : IsTightPair J K) :
    IsTightPair K J := by
  unfold IsTightPair at h ⊢
  rwa [inf_comm]

section SL2

variable {F : Type*} [Field F]

private theorem exists_ne_zero_sq_ne_one [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  have hall : ∀ a : F, a ≠ 0 → a ^ 2 = 1 := by
    intro a ha
    by_contra h
    exact hcon ⟨a, ha, h⟩
  have hsub : (Set.univ : Set F) ⊆ (({0, 1, -1} : Finset F) : Set F) := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h := hall a ha
      rw [pow_two] at h
      rcases mul_self_eq_one_iff.mp h with h | h <;> simp [h]
  have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_univ, Set.ncard_coe_finset] at hle
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  omega

theorem sl2_isPerfect [Finite F] (h4 : 4 ≤ Nat.card F) : Group.IsPerfect SL(2, F) := by
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one h4
  exact ⟨Matrix.SL2.commutator_eq_top ha hasq⟩

theorem mem_center_sl2_iff (x : SL(2, F)) :
    x ∈ Subgroup.center SL(2, F) ↔ x = 1 ∨ x = -1 := by
  have hneg : ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1) :=
    CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix F
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hx⟩
    simp only [Fintype.card_fin, pow_two] at hr
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hx]
      simp
    · right
      apply Subtype.ext
      rw [← hx, hneg]
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, hneg.symm⟩

theorem sl2_neg_one_ne_one [Finite F] (hodd : Odd (Nat.card F)) : (-1 : SL(2, F)) ≠ 1 :=
  CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F
    (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd)

theorem sl2_orderOf_neg_one [Finite F] (hodd : Odd (Nat.card F)) :
    orderOf (-1 : SL(2, F)) = 2 :=
  CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F
    (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd)

theorem sl2_orderOf_eq_two_iff [Finite F] (hodd : Odd (Nat.card F)) (x : SL(2, F)) :
    orderOf x = 2 ↔ x = -1 :=
  CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F
    (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) x

theorem sl2_natCard_center [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card (Subgroup.center SL(2, F)) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨-1, (mem_center_sl2_iff _).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    exact sl2_neg_one_ne_one hodd (congrArg Subtype.val h).symm
  · ext ⟨x, hx⟩
    rcases (mem_center_sl2_iff x).mp hx with rfl | rfl <;> simp

theorem sl2_normal_cases [Finite F] (h4 : 4 ≤ Nat.card F) (N : Subgroup SL(2, F)) (hN : N.Normal) :
    N = ⊥ ∨ N = Subgroup.center SL(2, F) ∨ N = ⊤ := by
  classical
  have : IsSimpleGroup PSL(2, F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let q : SL(2, F) →* PSL(2, F) := QuotientGroup.mk' (Subgroup.center SL(2, F))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hnorm : (N.map q).Normal := hN.map q hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map q) with h | h
  · have hle : N ≤ Subgroup.center SL(2, F) := by
      intro x hx
      have hx' : q x ∈ N.map q := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).mp hx'
    by_cases hneg : (-1 : SL(2, F)) ∈ N
    · right
      left
      refine le_antisymm hle ?_
      intro x hx
      rcases (mem_center_sl2_iff x).mp hx with rfl | rfl
      · exact N.one_mem
      · exact hneg
    · left
      refine (Subgroup.eq_bot_iff_forall N).mpr fun x hx => ?_
      rcases (mem_center_sl2_iff x).mp (hle hx) with rfl | rfl
      · rfl
      · exact absurd hx hneg
  · right
    right
    have hmap : ∀ x : SL(2, F), ∃ n ∈ N, n⁻¹ * x ∈ Subgroup.center SL(2, F) := by
      intro x
      have hx : q x ∈ N.map q := by rw [h]; trivial
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.eq_one_iff]
      change q (n⁻¹ * x) = 1
      rw [map_mul, map_inv, hnx, inv_mul_cancel]
    have hperf := sl2_isPerfect h4
    have hcomm : commutator SL(2, F) ≤ N := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
      obtain ⟨n₁, hn₁, hz₁⟩ := hmap x
      obtain ⟨n₂, hn₂, hz₂⟩ := hmap y
      obtain ⟨z₁, hz₁c, rfl⟩ : ∃ z ∈ Subgroup.center SL(2, F), x = n₁ * z :=
        ⟨n₁⁻¹ * x, hz₁, by group⟩
      obtain ⟨z₂, hz₂c, rfl⟩ : ∃ z ∈ Subgroup.center SL(2, F), y = n₂ * z :=
        ⟨n₂⁻¹ * y, hz₂, by group⟩
      have hcen₁ : ⁅z₁, n₂ * z₂⁆ = 1 :=
        commutatorElement_eq_one_iff_commute.mpr ((Subgroup.mem_center_iff.mp hz₁c _).symm)
      have hcen₂ : ⁅n₁, z₂⁆ = 1 :=
        commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hz₂c _)
      have e1 : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂ * z₂⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, hcen₁]
        simp
      have e2 : ⁅n₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj, hcen₂]
        simp
      rw [e1, e2, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact hcomm

theorem sl2_normal_odd [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F)
    (N : Subgroup SL(2, F)) (hN : N.Normal) (hNodd : Odd (Nat.card N)) : N = ⊥ :=
  CFSG.Semidihedral.OddLinearNormals.normal_odd_specialLinear_eq_bot F hodd h3 N hN hNodd

end SL2

section Equiv

variable {F : Type*} [Field F] [Finite F] {P : Type*} [Group P]

theorem isPerfect_of_equiv_sl2 (h4 : 4 ≤ Nat.card F) (e : P ≃* SL(2, F)) : Group.IsPerfect P :=
  have := sl2_isPerfect h4
  Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

omit [Finite F] in
theorem mem_center_iff_of_equiv_sl2 (e : P ≃* SL(2, F)) (x : P) :
    x ∈ Subgroup.center P ↔ e x ∈ Subgroup.center SL(2, F) := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, h g']
  · intro h g
    apply e.injective
    rw [map_mul, map_mul, h (e g)]

theorem orderOf_eq_two_iff_of_equiv_sl2 (hodd : Odd (Nat.card F)) (e : P ≃* SL(2, F)) (x : P) :
    orderOf x = 2 ↔ x = e.symm (-1) := by
  rw [← MulEquiv.orderOf_eq e x, sl2_orderOf_eq_two_iff hodd, e.eq_symm_apply]

theorem normal_cases_of_equiv_sl2 (h4 : 4 ≤ Nat.card F) (e : P ≃* SL(2, F)) (N : Subgroup P)
    (hN : N.Normal) : N = ⊥ ∨ N = Subgroup.center P ∨ N = ⊤ := by
  have hN' : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  have hback : (N.map e.toMonoidHom).comap e.toMonoidHom = N :=
    Subgroup.comap_map_eq_self_of_injective e.injective N
  rcases sl2_normal_cases h4 _ hN' with h | h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp h
  · right
    left
    rw [← hback, h]
    ext x
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    exact (mem_center_iff_of_equiv_sl2 e x).symm
  · right
    right
    rw [← hback, h, Subgroup.comap_top]

theorem normal_odd_of_equiv_sl2 (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F)
    (e : P ≃* SL(2, F)) (N : Subgroup P) (hN : N.Normal) (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  have hN' : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  have hodd' : Odd (Nat.card (N.map e.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp
    (sl2_normal_odd hodd h3 _ hN' hodd')

theorem natCard_center_of_equiv_sl2 (hodd : Odd (Nat.card F)) (e : P ≃* SL(2, F)) :
    Nat.card (Subgroup.center P) = 2 := by
  have hmap : (Subgroup.center P).map e.toMonoidHom = Subgroup.center SL(2, F) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_center_iff_of_equiv_sl2 e x).mp hx
    · intro hy
      refine ⟨e.symm y, (mem_center_iff_of_equiv_sl2 e _).mpr (by simpa using hy), by simp⟩
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap,
    sl2_natCard_center hodd]

theorem natCard_conj_range_of_equiv_sl2 (hodd : Odd (Nat.card F)) (e : P ≃* SL(2, F)) :
    Nat.card (MulAut.conj : P →* MulAut P).range * 2 = Nat.card P := by
  have hker : (MulAut.conj : P →* MulAut P).ker = Subgroup.center P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have := DFunLike.congr_fun h g
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · intro h
      ext g
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h g).symm
  have := Subgroup.card_ker_mul_card_range (MulAut.conj : P →* MulAut P)
  rw [hker, natCard_center_of_equiv_sl2 hodd e] at this
  omega

end Equiv

namespace IsClassicalSL2

variable {F : Type*} [Field F] [Finite F] {G : Type*} [Group G] {J : Subgroup G} {d : G}

theorem isPerfect (h : IsClassicalSL2 F J d) (h4 : 4 ≤ Nat.card F) : Group.IsPerfect J := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact isPerfect_of_equiv_sl2 h4 e

theorem eq_of_orderOf_eq_two (h : IsClassicalSL2 F J d) (hodd : Odd (Nat.card F)) {t : G}
    (htJ : t ∈ J) (ht : orderOf t = 2) : t = d := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  have h1 : (⟨t, htJ⟩ : J) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rwa [Subgroup.orderOf_mk])
  have h2 : (⟨d, h.mem⟩ : J) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rw [Subgroup.orderOf_mk, h.orderOf_eq_two])
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem mem_center (h : IsClassicalSL2 F J d) (hodd : Odd (Nat.card F)) :
    (⟨d, h.mem⟩ : J) ∈ Subgroup.center J := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  rw [mem_center_iff_of_equiv_sl2 e]
  have h2 : (⟨d, h.mem⟩ : J) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rw [Subgroup.orderOf_mk, h.orderOf_eq_two])
  rw [h2, MulEquiv.apply_symm_apply]
  exact (mem_center_sl2_iff _).mpr (Or.inr rfl)

theorem normal_cases (h : IsClassicalSL2 F J d) (h4 : 4 ≤ Nat.card F) (N : Subgroup J)
    (hN : N.Normal) : N = ⊥ ∨ N = Subgroup.center J ∨ N = ⊤ := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact normal_cases_of_equiv_sl2 h4 e N hN

theorem normal_odd_eq_bot (h : IsClassicalSL2 F J d) (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) (N : Subgroup J) (hN : N.Normal) (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact normal_odd_of_equiv_sl2 hodd h3 e N hN hNodd

omit [Finite F] in
theorem natCard_eq (h : IsClassicalSL2 F J d) : Nat.card J = Nat.card SL(2, F) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact Nat.card_congr e.toEquiv

private theorem mem_map_conj_iff' {J : Subgroup G} {g x : G} :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  rw [Subgroup.mem_map_equiv]
  simp

omit [Finite F] in
theorem conj (h : IsClassicalSL2 F J d) (g : G) :
    IsClassicalSL2 F (J.map (MulAut.conj g).toMonoidHom) (g * d * g⁻¹) where
  nonempty_mulEquiv := by
    obtain ⟨e⟩ := h.nonempty_mulEquiv
    exact ⟨(Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e⟩
  mem := ⟨d, h.mem, rfl⟩
  orderOf_eq_two := by
    rw [← h.orderOf_eq_two]
    exact MulEquiv.orderOf_eq (MulAut.conj g) d
  le_centralizer := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hjd : j * d = d * j := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hj)
    calc (MulAut.conj g).toMonoidHom j * (g * d * g⁻¹)
        = g * (j * d) * g⁻¹ := by simp [MulAut.conj_apply, mul_assoc]
      _ = g * (d * j) * g⁻¹ := by rw [hjd]
      _ = (g * d * g⁻¹) * (MulAut.conj g).toMonoidHom j := by simp [MulAut.conj_apply, mul_assoc]
  centralizer_le_normalizer := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hy' : g⁻¹ * y * g ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * d = g⁻¹ * (y * (g * d * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * d * g⁻¹) * y) * g := by rw [hy]
        _ = d * (g⁻¹ * y * g) := by group
    have hN := Subgroup.mem_normalizer_iff.mp (h.centralizer_le_normalizer hy')
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_map_conj_iff', mem_map_conj_iff', hN (g⁻¹ * x * g)]
    have : g⁻¹ * y * g * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g := by group
    rw [this]

end IsClassicalSL2

theorem IsTightPair.ne_of_orderOf_eq_two {G : Type*} [Group G] {J K : Subgroup G} {d e : G}
    (h : IsTightPair J K) (hd : d ∈ J) (he : e ∈ K) (hord : orderOf d = 2) : d ≠ e := by
  rintro rfl
  have hdvd : 2 ∣ Nat.card (J ⊓ K : Subgroup G) := by
    have := Subgroup.orderOf_dvd_natCard (J ⊓ K) (x := d) ⟨hd, he⟩
    rwa [hord] at this
  exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hdvd)

end CFSG.ClassicalInvolution
