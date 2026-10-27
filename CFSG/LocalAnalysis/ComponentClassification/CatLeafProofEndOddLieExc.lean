module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieInner
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieToralE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieToralE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieTwisted
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormD4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormTwE6

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.FooteLit
  CFSG.LieType.Ree CFSG.Walter.Ree.Model
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem false_of_ree_dihedral
    {X : Type} [Group X] {n p f : ℕ} (hL : LieModel X .twistedG2 n p f) {D : Subgroup X}
    (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h8 : 8 ≤ Nat.card D) : False := by
  have hRT : ReeTitsModel X .twistedG2 p f := by
    rcases hL with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  obtain ⟨hfin, -, hp3, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier X p f hRT
  subst hp3
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hRT
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := ReeTag.G2.reeGamma K a' with hΓ
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, hE8, -, ⟨P, hP⟩, -⟩ := small_Ree_prime_field_involution_fusion a' K hK' w₀ hw₀
  let eP : P ≃* smallReeE8 a' K w₀ :=
    ((P : Subgroup Γ).equivMapOfInjective Γ.subtype Γ.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  have hPc : ∀ x y : P, x * y = y * x := fun x y => eP.injective (by
    rw [map_mul, map_mul]
    exact hE8.toIsMulCommutative.is_comm.comm _ _)
  obtain ⟨m, hm, ⟨eD⟩⟩ := hD
  have hDcard : Nat.card D = 2 ^ m := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, ← pow_succ']
    congr 1
    omega
  have hm3 : 3 ≤ m := by
    by_contra h
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hDp : IsPGroup 2 D := IsPGroup.of_card hDcard
  obtain ⟨S, hS⟩ := (hDp.map E.toMonoidHom).exists_le_sylow
  have hSc : ∀ x y : S, x * y = y * x := fun x y => (Sylow.equiv S P).injective (by
    rw [map_mul, map_mul]
    exact hPc _ _)
  have : Fact (2 < 2 ^ (m - 1)) := ⟨by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩
  set r := eD.symm (DihedralGroup.r 1) with hr
  set s := eD.symm (DihedralGroup.sr 0) with hs
  have hrs : r * s ≠ s * r := by
    intro h
    have h' := congrArg eD h
    rw [map_mul, map_mul, hr, hs, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add] at h'
    exact ZMod.neg_one_ne_one (DihedralGroup.sr.inj h')
  let ι : D →* S := (E.toMonoidHom.comp D.subtype).codRestrict (S : Subgroup Γ) fun x =>
    hS ⟨x, x.2, rfl⟩
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (E.injective (congrArg Subtype.val hxy))
  exact hrs (hι (by rw [map_mul, map_mul, hSc]))

theorem false_of_oddExceptional_footeComponent
    {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {τ : StatedLieTag} {n p f : ℕ}
    (hτ : τ ∈ Burgoyne.oddExceptionalTags) (hτ' : τ ≠ .twistedG2) (hp2 : p ≠ 2)
    (hL : LieModel X τ n p f) {z : X} {K : Subgroup X} (hK : IsTwoComponentAt z K)
    (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hF : FooteFamilyType K) : False := by
  have hcases : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨
      τ = .trialityD4 := by
    revert hτ hτ'
    cases τ <;> decide
  have hn0 : n = 0 := by
    rcases hL with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
    · exact h
    · exact h
    · exact h
  subst hn0
  have hzZ := not_mem_center_of_footeComponent hX hK hs hF
  have hαo := orderOf_mulAut_conj_of_not_mem_center hK.1 hzZ
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_quat (τ := .G2) (fun F _ _ hF α hα L hL =>
        odd_G2_F4_E8_all_involution_fixed_p_components .G2 (Or.inl rfl) F hF α hα 2
          Nat.prime_two L hL) oddExcInnerDiagQuatForm_G2 hm.1.1 hp2
      (hm.2 : UntwistedChevalleyModel X .G2 (p ^ f)) hK hs hF
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_quat (τ := .F4) (fun F _ _ hF α hα L hL =>
        odd_G2_F4_E8_all_involution_fixed_p_components .F4 (Or.inr (Or.inl rfl)) F hF α hα 2
          Nat.prime_two L hL) oddExcInnerDiagQuatForm_F4 hm.1.1 hp2
      (hm.2 : UntwistedChevalleyModel X .F4 (p ^ f)) hK hs hF
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_quat (τ := .E6) (fun F _ _ hF α hα L hL =>
        odd_E6_all_involution_fixed_p_components F hF α hα 2 Nat.prime_two L hL)
      oddExcInnerDiagQuatForm_E6 hm.1.1 hp2
      (hm.2 : UntwistedChevalleyModel X .E6 (p ^ f)) hK hs hF
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_quat (τ := .E7) (fun F _ _ hF α hα L hL =>
        odd_E7_all_involution_fixed_p_components F hF α hα 2 Nat.prime_two L hL)
      oddExcInnerDiagQuatForm_E7 hm.1.1 hp2
      (hm.2 : UntwistedChevalleyModel X .E7 (p ^ f)) hK hs hF
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_quat (τ := .E8) (fun F _ _ hF α hα L hL =>
        odd_G2_F4_E8_all_involution_fixed_p_components .E8 (Or.inr (Or.inr rfl)) F hF α hα 2
          Nat.prime_two L hL) oddExcInnerDiagQuatForm_E8 hm.1.1 hp2
      (hm.2 : UntwistedChevalleyModel X .E8 (p ^ f)) hK hs hF
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_conj_quat
      (oddTwistedE6InnerSLForm_holds X p f hm.1.1 hp2 hm.1 hL (MulAut.conj z) hαo ⟨z, rfl⟩).1
      (oddTwistedE6InnerQuatForm_holds X p f hm.1.1 hp2 hm.1 hL (MulAut.conj z) hαo ⟨z, rfl⟩)
      hK hs hF
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_conj_quat
      (oddTrialityInnerSLForm_holds X p f hm.1.1 hp2 hm.1 hL (MulAut.conj z) hαo ⟨z, rfl⟩).1
      (oddTrialityInnerQuatForm_holds X p f hm.1.1 hp2 hm.1 hL (MulAut.conj z) hαo ⟨z, rfl⟩)
      hK hs hF

theorem false_of_oddExceptional_footeConfig
    {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {τ : StatedLieTag} {n p f : ℕ}
    (hτ : τ ∈ Burgoyne.oddExceptionalTags) (hp2 : p ≠ 2) (hL : LieModel X τ n p f) {z : X}
    {K D : Subgroup X} (hK : IsTwoComponentAt z K) (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hF : FooteFamilyType K) (hD : AschbacherTheorem3.IsDihedralTwoGroup D)
    (h8 : 8 ≤ Nat.card D) : False := by
  by_cases hτ' : τ = .twistedG2
  · subst hτ'
    exact false_of_ree_dihedral hL hD h8
  · exact false_of_oddExceptional_footeComponent hX hτ hτ' hp2 hL hK hs hF

theorem endOddLieInputFor_oddExceptional
    : Sol78.F514.EndOddLieInputFor Burgoyne.oddExceptionalTags := by
  intro X _ _ hX τ n p f hτ _ hp2 _ hL z _ K _ D hK _ hs hF _ _ _ _ _ _ _ _ hD h8 _ _
  exact (false_of_oddExceptional_footeConfig hX hτ hp2 hL hK hs hF hD h8).elim

end CFSG.ComponentClassification.CatLeafProof
