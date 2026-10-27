module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpOrderL2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpCard
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecConf

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem fixed_component_models {K : Type} [Field K] [Finite K] {n p f' : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f') (hadm : StatedLieAdmissible .PSp n p f')
    (hn : 3 ≤ n) {α : MulAut (StatedProj (StatedSp n K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L)
    (hZ : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z * z = 1 → z = 1) :
    CentralModel p .PSL n f' L ∨ CentralModel p .PSU n f' L ∨
      (Even n ∧ CentralModel p .PSp (n / 2) (2 * f') L) ∨
        ∃ j, f' = 2 * j ∧ CentralModel p .PSp n j L := by
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK) (by omega : 2 ≤ n)).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  ·
    have hαA : α = conjAut n K A := by rw [hα, hσ, map_one, mul_one]
    subst hαA
    have hA : orderOf (conjAut n K A) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
    rcases inner_psp_component_cases hp hp2 hK hadm hn A hA hL with
      ⟨z, hzL, hzc, hzz, hz1⟩ | h | h | h
    · exact absurd (hZ z hzL hzc hzz) hz1
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  ·
    exact Or.inr (Or.inr (Or.inr
      (field_psp_component_model (by omega) hp hp2 hadm.2.1 hK A σ hα hσ2 hσ d hd hL)))

theorem false_of_fixed_twoComponent {K : Type} [Field K] [Finite K] {n p f' f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f')
    (hadm : StatedLieAdmissible .PSp n p f') (hn : 3 ≤ n) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    {α : MulAut (StatedProj (StatedSp n K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {L : Subgroup (fixedSubgroup α)} (hL : IsPComponent 2 L)
    (hX : (LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f ∧ n ≠ 4) ∨
      (LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p (2 * f) ∧ n = 4)) : False := by
  have hf' : 1 ≤ f' := hadm.2.1
  have hq : IsQuasisimple L := CatalogueBSymplecticB.odd_symplectic_involution_fixed_p_components
    p f' hp hp2 hf' K hK n (by omega) α hα2 hα1 2 Nat.prime_two L hL
  have hsub : L.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hL
    exact h
  have hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := by
    rcases hX with ⟨h, -⟩ | ⟨h, -⟩
    · exact GSThmB.X10Rec.isSimpleGroup_of_lieModel_psp h5 h
    · exact isSimpleGroup_of_lieModel_psl (by norm_num) h
  have hZO := GSThmB.X10Rec.center_eq_pPrimeCore hq hs
  have hZ : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z * z = 1 → z = 1 := by
    intro z hzL hzc hzz
    exact congrArg Subtype.val (eq_one_of_mem_center hZO (z := ⟨z, hzL⟩)
      (mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm) (Subtype.ext hzz))
  have hY : ∀ {t : StatedLieTag} {m e : ℕ}, LieModel (L ⧸ pPrimeCore 2 L) t m p e →
      LieModel (L ⧸ center L) t m p e := fun h =>
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO).symm h
  rcases fixed_component_models hp hp2 hK hadm hn hα2 hα1 ⟨hq, hsub⟩ hZ with
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨he, -, h⟩ | ⟨j, hj, -, h⟩
  ·
    rcases hX with ⟨hX, hn4⟩ | ⟨hX, rfl⟩
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inl rfl) (Or.inr (Or.inr rfl)) hp2
        (by omega) (by norm_num) h (hY hX)
      exact false_of_card_psl_psp4 hp hp2 hf hf' hn hn4 h1 h2 hv
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inl rfl) (Or.inl rfl) hp2
        (by norm_num) (by norm_num) h (hY hX)
      exact false_of_card_psl4_l2 hp hp2 hf hf' h1 h2 hv
  ·
    rcases hX with ⟨hX, hn4⟩ | ⟨hX, rfl⟩
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inl rfl))
        (Or.inr (Or.inr rfl)) hp2 (by omega) (by norm_num) h (hY hX)
      exact false_of_card_psu_psp4 hp hp2 hf hf' hn hn4 h1 h2 hv
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inl rfl)) (Or.inl rfl) hp2
        (by norm_num) (by norm_num) h (hY hX)
      exact false_of_card_psu4_l2 hp hp2 hf hf' h1 h2 hv
  ·
    rcases hX with ⟨hX, hn4⟩ | ⟨hX, rfl⟩
    · have hm : 3 ≤ n / 2 := by
        obtain ⟨k, hk⟩ := he
        omega
      obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inr rfl))
        (Or.inr (Or.inr rfl)) hp2 (by omega) (by norm_num) h (hY hX)
      exact false_of_card_psp_psp4 hp hp2 hf (by omega) hm h1 h2 hv
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inr rfl)) (Or.inl rfl) hp2
        (by norm_num) (by norm_num) h (hY hX)
      exact false_of_card_psp_l2 hp hp2 hf (by omega) (by norm_num) h1 h2 hv
  ·
    have hj1 : 1 ≤ j := by omega
    rcases hX with ⟨hX, -⟩ | ⟨hX, rfl⟩
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inr rfl))
        (Or.inr (Or.inr rfl)) hp2 (by omega) (by norm_num) h (hY hX)
      exact false_of_card_psp_psp4 hp hp2 hf hj1 hn h1 h2 hv
    · obtain ⟨h1, h2, hv⟩ := lieOrder_of_two_lieModels (Or.inr (Or.inr rfl)) (Or.inl rfl) hp2
        (by norm_num) (by norm_num) h (hY hX)
      exact false_of_card_psp_l2 hp hp2 hf hj1 (by norm_num) h1 h2 hv

theorem cf81X10RowSpHigh : GSThmB.CF81X10RowSpHigh := by
  intro N _ _ n p f' f hp hp2 hn hadm hN hf h5 α hα2 hα1 L hL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel' hadm hN
  have hα₀2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα₀1 : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  let Φ := Sporadic.HeldB.fixedSubgroupCongr e α
  have hL₀ := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Φ hL
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  have htr : ∀ {t : StatedLieTag} {m e' : ℕ}, LieModel (L ⧸ pPrimeCore 2 L) t m p e' →
      LieModel (L.map Φ.toMonoidHom ⧸ pPrimeCore 2 (L.map Φ.toMonoidHom)) t m p e' := fun h =>
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)) h
  refine ⟨fun hX => ?_, fun h4 hX => ?_⟩
  · by_contra h4
    exact false_of_fixed_twoComponent hp hp2 hK hadm hn hf h5 hα₀2 hα₀1 hL₀
      (Or.inl ⟨htr hX, h4⟩)
  · exact false_of_fixed_twoComponent hp hp2 hK hadm hn hf h5 hα₀2 hα₀1 hL₀
      (Or.inr ⟨htr hX, h4⟩)

end CFSG.ComponentClassification.CatLeafProof.X10Sp
