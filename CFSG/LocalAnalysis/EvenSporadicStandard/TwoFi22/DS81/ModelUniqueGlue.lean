module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueCard

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace UniqueGlue

theorem card_map_mul_card_ker_subgroupOf {G N : Type*} [Group G] [Group N] (f : G →* N)
    (H : Subgroup G) : Nat.card (H.map f) * Nat.card (f.ker.subgroupOf H) = Nat.card H := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rwa [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, mul_comm] at h

theorem isPGroup_two_of_forall_sq {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ x ∈ H, x ^ 2 = 1) : IsPGroup 2 H := fun x => ⟨1, Subtype.ext (by simp [h x x.2])⟩

theorem sq_eq_one_of_mem_map {G N : Type*} [Group G] [Group N] (f : G →* N) (H : Subgroup G)
    (h : ∀ x ∈ H, x ^ 2 = 1) : ∀ y ∈ H.map f, y ^ 2 = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, h x hx, map_one]

theorem hom_word_mem_of_eVec_mem {G : Type*} [Group G] (ψ : Multiplicative Word →* G)
    (K : Subgroup G) (h : ∀ i, ψ (eVec i) ∈ K) (w : Multiplicative Word) : ψ w ∈ K := by
  have key : ∀ v : Word, ψ (Multiplicative.ofAdd v) ∈ K := by
    intro v
    rw [← Finset.univ_sum_single v]
    refine Finset.sum_induction _ (fun v : Word => ψ (Multiplicative.ofAdd v) ∈ K) ?_ ?_ ?_
    · intro a b ha hb
      rw [ofAdd_add, map_mul]
      exact K.mul_mem ha hb
    · simp
    · intro i _
      have hv : v i = 0 ∨ v i = 1 := by
        have : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        exact this _
      rcases hv with hv | hv
      · rw [hv]
        simp
      · rw [hv]
        exact h i
  have := key (Multiplicative.toAdd w)
  rwa [ofAdd_toAdd] at this

section Cover


theorem fjQ_mem_E0 (i : Fin 23) : fjQ i ∈ E0 :=
  Subgroup.mem_subgroupOf.2 ⟨eVec i, fjHom_eVec i⟩

theorem ker_piC_le_E0 : piC.ker ≤ E0 := by
  rw [ker_piC, center_C, Subgroup.zpowers_le]
  rw [E0, Subgroup.mem_subgroupOf]
  refine ⟨eVec 0, ?_⟩
  rw [fjHom_eVec, fjPt_zero]
  rfl

theorem piC_mem_map_E0 (c : Cd) : piC c ∈ E0.map piC ↔ c ∈ E0 := by
  have h : (E0.map piC).comap piC = E0 := by
    rw [Subgroup.comap_map_eq, sup_eq_left.2 ker_piC_le_E0]
  rw [← Subgroup.mem_comap, h]

theorem card_map_piC_E0 : Nat.card (E0.map piC) = 2 ^ 10 := by
  have h := card_map_mul_card_ker_subgroupOf piC E0
  have h2 : Nat.card (piC.ker.subgroupOf E0) = 2 := by
    rw [← card_ker_piC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe ker_piC_le_E0).toEquiv
  rw [h2, E0_card] at h
  omega

theorem two_pow_ten_le_card_map_piC {B : Subgroup Cd} (hB : Nat.card B = 2 ^ 11) :
    2 ^ 10 ≤ Nat.card (B.map piC) := by
  have h := card_map_mul_card_ker_subgroupOf piC B
  have : Finite piC.ker := Nat.finite_of_card_ne_zero (by rw [card_ker_piC]; norm_num)
  have hk : Nat.card (piC.ker.subgroupOf B) ≤ 2 := by
    rw [← card_ker_piC]
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, x.2⟩) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  rw [hB] at h
  generalize Nat.card (B.map piC) = m at h ⊢
  generalize Nat.card (piC.ker.subgroupOf B) = k at h hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · omega
  · omega

theorem map_piC_le_normalizer {B : Subgroup Cd} (hB : B ≤ normalizer (E0 : Set Cd)) :
    B.map piC ≤ normalizer ((E0.map piC : Subgroup CFSG.Sporadic.Fi22.J) :
      Set CFSG.Sporadic.Fi22.J) :=
  (Subgroup.map_mono hB).trans (Subgroup.le_normalizer_map piC)

end Cover

section Sylow


theorem exists_conj_sup_mem_slvl_zero {E B : Subgroup CFSG.Sporadic.Fi22.J}
    (hE : ∀ x ∈ E, x ^ 2 = 1) (hB : ∀ x ∈ B, x ^ 2 = 1)
    (hBE : B ≤ normalizer (E : Set CFSG.Sporadic.Fi22.J)) :
    ∃ g : CFSG.Sporadic.Fi22.J, ∀ x ∈ E ⊔ B, g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.slvl 0 := by
  obtain ⟨Q, hQ⟩ := ((isPGroup_two_of_forall_sq hE).to_sup_of_normal_left'
    (isPGroup_two_of_forall_sq hB) hBE).exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_into_slvl Q
  exact ⟨g, fun x hx => hg x (hQ hx)⟩

end Sylow

section Points


theorem conj_mem_D_fi22 (g : CFSG.Sporadic.Fi22.J) {x : CFSG.Sporadic.Fi22.J}
    (hx : x ∈ CFSG.Sporadic.Fi22.D) : g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.D :=
  (show IsConj CFSG.Sporadic.Fi22.a x from hx).trans (isConj_iff.2 ⟨g, rfl⟩)

theorem piC_fjQ_mem_D {i : Fin 23} (hi : i ≠ 0) : piC (fjQ i) ∈ CFSG.Sporadic.Fi22.D := by
  rw [fjQ_eq_ofStar hi]
  exact piC_ofStar_mem_D _

theorem piC_fjQ_zero : piC (fjQ 0) = 1 := by
  have h : fjQ 0 = dCd := Subtype.ext fjPt_zero
  rw [h, piC_dCd]

theorem exists_pt_of_mem_D_slvl {g : CFSG.Sporadic.Fi22.J}
    (hg : ∀ x ∈ E0.map piC, g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.slvl 0)
    {x : CFSG.Sporadic.Fi22.J} (hxD : x ∈ CFSG.Sporadic.Fi22.D)
    (hxS : x ∈ CFSG.Sporadic.Fi22.slvl 0) :
    ∃ i : Fin 23, i ≠ 0 ∧ g * piC (fjQ i) * g⁻¹ = x := by
  let f : {i : Fin 23 // i ≠ 0} → {y : CFSG.Sporadic.Fi22.J //
      y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ CFSG.Sporadic.Fi22.slvl 0} := fun i =>
    ⟨g * piC (fjQ i.1) * g⁻¹, conj_mem_D_fi22 g (piC_fjQ_mem_D i.2),
      hg _ (Subgroup.mem_map_of_mem _ (fjQ_mem_E0 i.1))⟩
  have hinj : Function.Injective f := by
    intro i j h
    have h' := congrArg Subtype.val h
    have h'' : piC (fjQ i.1) = piC (fjQ j.1) := mul_left_cancel (mul_right_cancel h')
    rw [fjQ_eq_ofStar i.2, fjQ_eq_ofStar j.2] at h''
    have hij : fjPt i.1 = fjPt j.1 := congrArg Subtype.val (ofStar_injective_of_piC h'')
    by_contra hne
    exact fjPt_ne (fun e => hne (Subtype.ext e)) hij
  have hcard : Nat.card {y : CFSG.Sporadic.Fi22.J //
      y ∈ CFSG.Sporadic.Fi22.D ∧ y ∈ CFSG.Sporadic.Fi22.slvl 0} ≤
      Nat.card {i : Fin 23 // i ≠ 0} := by
    refine card_D_slvl_le.trans ?_
    rw [Nat.card_eq_fintype_card]
    exact le_of_eq (by decide)
  obtain ⟨⟨i, hi⟩, hfi⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨x, hxD, hxS⟩
  have h := congrArg Subtype.val hfi
  exact ⟨i, hi, h⟩

theorem closure_D_slvl_eq {g : CFSG.Sporadic.Fi22.J}
    (hg : ∀ x ∈ E0.map piC, g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.slvl 0) :
    Subgroup.closure {x : CFSG.Sporadic.Fi22.J |
      x ∈ CFSG.Sporadic.Fi22.D ∧ x ∈ CFSG.Sporadic.Fi22.slvl 0} =
      (E0.map piC).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxD, hxS⟩
    obtain ⟨i, -, rfl⟩ := exists_pt_of_mem_D_slvl hg hxD hxS
    exact ⟨piC (fjQ i), Subgroup.mem_map_of_mem _ (fjQ_mem_E0 i), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 he
    have hew : e = ⟨fjHom w, fjHom_mem_Cd w⟩ := Subtype.ext hw.symm
    have key := hom_word_mem_of_eVec_mem ((MulAut.conj g).toMonoidHom.comp fjProj)
      (Subgroup.closure {x : CFSG.Sporadic.Fi22.J |
        x ∈ CFSG.Sporadic.Fi22.D ∧ x ∈ CFSG.Sporadic.Fi22.slvl 0}) (fun i => ?_) w
    · rw [hew]
      exact key
    · rw [MonoidHom.comp_apply, fjProj_eVec]
      by_cases hi : i = 0
      · rw [hi, piC_fjQ_zero, map_one]
        exact one_mem _
      · exact subset_closure ⟨conj_mem_D_fi22 g (piC_fjQ_mem_D hi),
          hg _ (Subgroup.mem_map_of_mem _ (fjQ_mem_E0 i))⟩

end Points

end UniqueGlue

open UniqueGlue in
theorem E0_unique_of_cp
    (cp : ∀ A : Subgroup CFSG.Sporadic.Fi22.J, A ≤ CFSG.Sporadic.Fi22.slvl 0 →
      (∀ a ∈ A, a ^ 2 = 1) → 2 ^ 10 ≤ Nat.card A →
      Nat.card (Subgroup.closure {x : CFSG.Sporadic.Fi22.J |
        x ∈ CFSG.Sporadic.Fi22.D ∧ x ∈ CFSG.Sporadic.Fi22.slvl 0}) = 2 ^ 10 →
      A ≤ Subgroup.closure {x : CFSG.Sporadic.Fi22.J |
        x ∈ CFSG.Sporadic.Fi22.D ∧ x ∈ CFSG.Sporadic.Fi22.slvl 0}) :
    ∀ B : Subgroup ↥CFSG.Sporadic.Fi23.Cd,
      B ≤ Subgroup.normalizer (E0 : Set ↥CFSG.Sporadic.Fi23.Cd) →
      (∀ b ∈ B, b ^ 2 = 1) → Nat.card B = 2 ^ 11 → B = E0 := by
  intro B hBN hBsq hBcard
  obtain ⟨g, hg⟩ := exists_conj_sup_mem_slvl_zero (sq_eq_one_of_mem_map piC E0 E0_sq)
    (sq_eq_one_of_mem_map piC B hBsq) (map_piC_le_normalizer hBN)
  have hgE : ∀ x ∈ E0.map piC, g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.slvl 0 := fun x hx =>
    hg x (Subgroup.mem_sup_left hx)
  have hgB : ∀ x ∈ B.map piC, g * x * g⁻¹ ∈ CFSG.Sporadic.Fi22.slvl 0 := fun x hx =>
    hg x (Subgroup.mem_sup_right hx)
  have hcl := closure_D_slvl_eq hgE
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hA := cp ((B.map piC).map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_ (by
    rw [hcl, Subgroup.card_map_of_injective hinj, card_map_piC_E0])
  · rw [hcl] at hA
    have hBE : B ≤ E0 := fun b hb => (piC_mem_map_E0 b).1
      ((Subgroup.map_le_map_iff_of_injective hinj).1 hA (Subgroup.mem_map_of_mem _ hb))
    have : Finite E0 := Nat.finite_of_card_ne_zero (by rw [E0_card]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge hBE (by rw [E0_card, hBcard])
  · rintro _ ⟨x, hx, rfl⟩
    exact hgB x hx
  · exact sq_eq_one_of_mem_map _ _ (sq_eq_one_of_mem_map piC B hBsq)
  · rw [Subgroup.card_map_of_injective hinj]
    exact two_pow_ten_le_card_map_piC hBcard

end CFSG.EvenSporadicStandard.TwoFi22.DS81
