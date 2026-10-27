module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecB
public import CFSG.ClassicalInvolution.Asc77.AscE184Graph

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE184Sect

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem exists_of_mem_RSet_sectionFamily (hA : IsPGroup 2 ↥A) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ RSet (sectionFamily Ω A)) :
    ∃ J ∈ sectionMembers Ω A, R₀ ∈ fixedSylows A J := by
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR₀
  obtain ⟨J, hJ, rfl⟩ := hM
  exact ⟨J, hJ, (isSylow2In_secMember_iff hA hJ.2).mp hRM⟩

theorem mem_RSet_of_mem_RSet_sectionFamily (hA : IsPGroup 2 ↥A) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ RSet (sectionFamily Ω A)) : R₀ ∈ RSet Ω := by
  obtain ⟨J, hJ, hT⟩ := exists_of_mem_RSet_sectionFamily hA hR₀
  exact mem_RSet_of_isSylow2In hJ.1 hT.1

theorem mem_USet_of_mem_USet_sectionFamily (hA : IsPGroup 2 ↥A) {U : Subgroup G}
    (hU : U ∈ USet (sectionFamily Ω A)) : U ∈ USet Ω := by
  obtain ⟨R₀, hR₀, hUR, hcyc, hidx⟩ := hU
  exact ⟨R₀, mem_RSet_of_mem_RSet_sectionFamily hA hR₀, hUR, hcyc, hidx⟩

theorem isUniqueInvolution_of_secMember (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {J : Subgroup G} (hJ : J ∈ sectionMembers Ω A) {z : G}
    (hz : IsUniqueInvolution (secMember A J) z) : IsUniqueInvolution J z := by
  obtain ⟨z₀, hz₀⟩ := hΩ.exists_uniqueInvolution hp hq hJ.1
  have hz₀A := isUniqueInvolution_secMember hp hΩ hA hJ.1 hJ.2 hz₀
  have : z = z₀ := hz.eq hz₀A
  exact this ▸ hz₀

theorem mem_twinSet_of_secMember (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {K L : Subgroup G} (hK : K ∈ sectionMembers Ω A)
    (hL : L ∈ sectionMembers Ω A)
    (h : secMember A L ∈ twinSet (sectionFamily Ω A) (secMember A K)) : L ∈ twinSet Ω K := by
  obtain ⟨-, z, hzK, hzL⟩ := h
  exact ⟨hL.1, z, isUniqueInvolution_of_secMember hp hq hΩ hA hK hzK,
    isUniqueInvolution_of_secMember hp hq hΩ hA hL hzL⟩

theorem secMember_mem_twinSet (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A)
    {K L : Subgroup G} (hK : K ∈ sectionMembers Ω A) (hL : L ∈ sectionMembers Ω A)
    (h : L ∈ twinSet Ω K) :
    secMember A L ∈ twinSet (sectionFamily Ω A) (secMember A K) := by
  obtain ⟨-, z, hzK, hzL⟩ := h
  exact ⟨secMember_mem_sectionFamily hL, z, isUniqueInvolution_secMember hp hΩ hA hK.1 hK.2 hzK,
    isUniqueInvolution_secMember hp hΩ hA hL.1 hL.2 hzL⟩

theorem mem_omegaNbr_of_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {K J : Subgroup G} (hK : K ∈ sectionMembers Ω A)
    (hJ : J ∈ sectionMembers Ω A)
    (h : secMember A J ∈ omegaNbr (sectionFamily Ω A) (secMember A K)) : J ∈ omegaNbr Ω K := by
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  obtain ⟨J', hJ', hTfix⟩ := exists_of_mem_RSet_sectionFamily hA hT
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJ'.1 hTfix.1)
  have hTJG : T ≤ J := hTJ.trans (secMember_le_left A J)
  have hJJ' : J = J' := hΩ.eq_of_le_of_le hJ.1 hJ'.1 hTfix.1.2.1 (by omega) hTJG hTfix.1.1
  subst hJJ'
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK.1
  have hzA := isUniqueInvolution_secMember hp hΩ hA hK.1 hK.2 hz
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hTN' : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK.1 hJ.1 (Ne.symm hJK) hz hTJG hTfix.1.2.1
      (by omega) hTc
  exact ⟨hJ.1, hJK, T, mem_RSet_of_isSylow2In hJ.1 hTfix.1, hTJG, hTN'⟩

theorem mem_omegaStarNbr_of_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) {K J : Subgroup G}
    (hK : K ∈ sectionMembers Ω A) (hJ : J ∈ sectionMembers Ω A)
    (h : secMember A J ∈ omegaStarNbr (sectionFamily Ω A) (secMember A K)) :
    J ∈ omegaStarNbr Ω K := by
  obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  have hUΩ : U ∈ USet Ω := mem_USet_of_mem_USet_sectionFamily hA hU
  obtain ⟨R₀, hR₀, J', hJ', hR₀J', hUR₀, hcyc, hcard, h4⟩ := hΩ.exists_data_of_mem_USet hp hUΩ
  have hU2 : IsPGroup 2 U := hΩ.isPGroup_of_mem_USet hp hUΩ
  have hUJG : U ≤ J := hUJ.trans (secMember_le_left A J)
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK.1
  have hzA := isUniqueInvolution_secMember hp hΩ hA hK.1 hK.2 hz
  have hUc : U ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hUN' : U ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK.1 hJ.1 (Ne.symm hJK) hz hUJG hU2 (by omega) hUc
  exact ⟨hJ.1, hJK, U, hUΩ, hUJG, hUN'⟩

theorem dstarAdj_of_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) {K J : Subgroup G} (hK : K ∈ sectionMembers Ω A)
    (hJ : J ∈ sectionMembers Ω A)
    (h : dstarAdj (sectionFamily Ω A) (secMember A K) (secMember A J)) : dstarAdj Ω K J := by
  rcases h.2 with h1 | h1
  · exact ⟨hJ.1, Or.inl (mem_omegaStarNbr_of_sectionFamily hp hq hΩ hA hK hJ h1)⟩
  · exact ⟨hJ.1, Or.inr (mem_omegaStarNbr_of_sectionFamily hp hq hΩ hA hJ hK h1)⟩

theorem mem_dstarComp_of_dstarComp_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) {K : Subgroup G}
    (hK : K ∈ sectionMembers Ω A) {L : Subgroup G}
    (hL : L ∈ dstarComp (sectionFamily Ω A) (secMember A K)) :
    ∀ M ∈ sectionMembers Ω A, secMember A M = L → M ∈ dstarComp Ω K := by
  induction hL with
  | refl =>
    intro M hM hMK
    rw [eq_of_secMember_eq hp hΩ hA hM hK hMK]
    exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b c
    intro M hM hMc
    have hbΛ : b ∈ sectionFamily Ω A := by
      rcases dstarComp_subset_insert _ hab with h | h
      · rw [h]
        exact secMember_mem_sectionFamily hK
      · exact h
    obtain ⟨M₀, hM₀, rfl⟩ := hbΛ
    have h1 := ih M₀ hM₀ rfl
    rw [← hMc] at hbc
    exact h1.tail (dstarAdj_of_sectionFamily hp hq hΩ hA hM₀ hM hbc)

omit [Finite G] in
theorem conjSub_sectionHull_le (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x ∈ Subgroup.centralizer (A : Set G)) :
    conjSub x (sectionHull Ω A) ≤ sectionHull Ω A := by
  unfold sectionHull conjSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hL => ?_
  exact le_iSup₂_of_le _ (conjSub_mem_sectionFamily hΩ hx hL) le_rfl

omit [Finite G] in
theorem le_normalizer_sectionHull (hΩ : HypOmegaMod p f Ω) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (sectionHull Ω A : Set G) := by
  intro x hx
  refine mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (conjSub_sectionHull_le hΩ hx) ?_)
  have := conjSub_mono (n := x)
    (conjSub_sectionHull_le hΩ ((Subgroup.centralizer (A : Set G)).inv_mem hx))
  rwa [conjSub_conjSub_inv] at this

end CFSG.ClassicalInvolution.Asc77.AscE184Sect
