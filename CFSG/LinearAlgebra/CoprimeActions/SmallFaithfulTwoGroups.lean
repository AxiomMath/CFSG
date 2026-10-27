module

public import CFSG.LinearAlgebra.CoprimeActions.IrreduciblePrimeNormalizerImage
public import CFSG.LinearAlgebra.CoprimeActions.SmallModuleSpecialTwoGroup
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoFaithfulDimensionBound
public import CFSG.LargeExtraspecial.CyclicCenter
public import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreducibleFiniteCenterCyclic
public import CFSG.GroupTheory.CoprimeActionSupport.PrimeConjugationImage
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutomizerWidth
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOrderWidth
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
import all CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow

public section

namespace CFSG.LinearAlgebra.CoprimeActions.SmallFaithfulTwoGroups

theorem not_orderOf_le_two {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    ¬ orderOf (2 : ZMod q) ≤ 2 := by
  intro h
  haveI : Fact q.Prime := ⟨hq⟩
  have h2' : ((2 : ℕ) : ZMod q) ≠ 0 := fun hz => by
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 hz); omega
  have h2'' : (2 : ZMod q) ≠ 0 := by simpa using h2'
  have hpos : 0 < orderOf (2 : ZMod q) :=
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2'')) (by omega)
  have h3 : ¬ (q ∣ 3) := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have h3' : ((3 : ℕ) : ZMod q) ≠ 0 := fun hz => h3 ((ZMod.natCast_eq_zero_iff _ _).1 hz)
  interval_cases hk : orderOf (2 : ZMod q)
  · have h1 := orderOf_eq_one_iff.1 hk
    have : (1 : ZMod q) = 0 := by linear_combination h1
    exact one_ne_zero this
  · have h1 := pow_orderOf_eq_one (2 : ZMod q)
    rw [hk] at h1
    apply h3'
    push_cast
    linear_combination h1

theorem special_transfer {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center A = commutator A ∧ Subgroup.center A = frattini A) :
    Subgroup.center B = commutator B ∧ Subgroup.center B = frattini B := by
  have hc : (commutator A).map (e : A →* B) = commutator B := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      ← commutator_def]
  have hf : (frattini A).map (e : A →* B) = frattini B := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · intro b hb
      have := frattini_le_comap_frattini_of_surjective (φ := (e.symm : B →* A)) e.symm.surjective hb
      exact ⟨e.symm b, this, by simp⟩
  have hz : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  constructor
  · rw [← hz, ← hc, h.1]
  · rw [← hz, ← hf, h.2]

theorem false_of_dim_le_three {F : Type*} [Field F] [IsAlgClosed F] (hF : (2 : F) ≠ 0)
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (τ : Representation F H W) (hτ : Function.Injective τ)
    (hdim : Module.finrank F W ≤ 3)
    (E D : Subgroup H) (hE : E ≠ ⊥) (hE2 : IsPGroup 2 E)
    (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) (hD : Nat.card D = q) (hED : ⁅E, D⁆ = E) :
    False := by
  classical
  have hlt : Module.finrank F W < q := by omega
  obtain ⟨J, _, _, W', _, _, _, _, τ, Q, X, hτ, hWV, hQ, hQ2, hX, hQX, hirr⟩ :=
    IrreduciblePrimeNormalizerImage.exists_image τ hτ E D hE hE2 q hD hq hq3 hED hF
      hlt
  haveI : Small.{0} J := inferInstance
  let e : Shrink.{0} J ≃* J := Shrink.mulEquiv
  let τ' : Representation F (Shrink.{0} J) W' := τ.comp e.toMonoidHom
  have hτ' : Function.Injective τ' := hτ.comp e.injective
  let Q' : Subgroup (Shrink.{0} J) := Q.map (e.symm : J →* Shrink.{0} J)
  let X' : Subgroup (Shrink.{0} J) := X.map (e.symm : J →* Shrink.{0} J)
  have hQ'ne : Q' ≠ ⊥ := by
    intro h
    apply hQ
    have := Subgroup.map_injective (f := (e.symm : J →* Shrink.{0} J)) e.symm.injective
      (h.trans (Subgroup.map_bot _).symm)
    exact this
  have hQ'2 : IsPGroup 2 Q' := hQ2.map _
  have hX' : Nat.card X' = q := by
    rw [← hX]
    exact Subgroup.card_map_of_injective e.symm.injective
  have hQX' : ⁅Q', X'⁆ = Q' := by
    simp only [Q', X']
    rw [← Subgroup.map_commutator, hQX]
  have hXN' : X' ≤ Subgroup.normalizer (Q' : Set (Shrink.{0} J)) := by
    have := Subgroup.normalizer_commutator_ge_right Q' X'
    rwa [hQX'] at this
  have hW'q : Module.finrank F W' < q := by omega
  obtain ⟨hspec, -⟩ := SmallModuleSpecialTwoGroup.special_and_center hF τ' hτ' q hq
    hq3 hW'q X' Q' hX' hQ'ne hQ'2 hXN' hQX'
  unfold CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.IsSpecialPGroup at hspec
  obtain ⟨h1, h2⟩ := hspec
  have hZC : Subgroup.center Q' = commutator Q' :=
    Subgroup.map_injective Q'.subtype_injective h1
  have hZF : Subgroup.center Q' = frattini Q' :=
    Subgroup.map_injective Q'.subtype_injective h2
  let eQ : Q' ≃* Q := (MulEquiv.subgroupMap (e.symm : J ≃* Shrink.{0} J) Q).symm
  obtain ⟨hZC2, hZF2⟩ := special_transfer eQ ⟨hZC, hZF⟩
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  let σ : Representation F Q W' := τ.comp Q.subtype
  have hσ : Function.Injective σ := fun a b h => Subtype.ext (hτ h)
  haveI : IsCyclic (Subgroup.center Q) :=
    CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreducibleFiniteCenterCyclic.cyclic_center σ hσ hirr
  have hext := CFSG.LargeExtraspecial.isExtraspecialPGroup_of_cyclic_center Nat.prime_two hQ2 hZC2 hZF2 this
  obtain ⟨w, hw0, hcard⟩ :=
    CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOrderWidth.exists_width Q hext
  have hcard' : Nat.card Q = 2 ^ (1 + 2 * w) := by rw [hcard]; ring_nf
  have hlow := CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoFaithfulDimensionBound.dimension_lower_bound
    hF hext hcard' σ hσ
  have hw : w ≤ 1 := by
    by_contra h
    push Not at h
    have : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h
    omega
  obtain ⟨C, hC⟩ := CFSG.GroupTheory.CoprimeActionSupport.PrimeConjugationImage.exists_subgroup
    hq Q X hQ hX hQX
  have := CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutomizerWidth.order_le_twice_width
    hext hcard' hq (by omega) C hC
  exact not_orderOf_le_two hq hq3 (this.trans (by omega))

end CFSG.LinearAlgebra.CoprimeActions.SmallFaithfulTwoGroups
