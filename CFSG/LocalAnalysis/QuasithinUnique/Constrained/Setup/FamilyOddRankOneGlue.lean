module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.RankThree.Chevalley.OddRankOneReeTitsModels
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem oddRankOneChevalley
    : OddRankOneChevalleyProp := by
  intro S _ _ hS t p f _ h
  exact CFSG.RankThree.Chevalley.odd_rank_one_Chevalley_exceptional_model_is_binary_triality S hS t
    p f h

theorem oddRankOneReeTits
    : OddRankOneReeTitsProp := by
  intro S _ _ hS t p f _
  exact CFSG.RankThree.Chevalley.odd_rank_one_excludes_all_Ree_Tits_models S hS t p f

theorem trialityTwoHasRankTwo
    : TrialityTwoHasRankTwoProp := by
  intro S _ _ hmod
  obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩, rfl⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 3 := hK
  have hσe : ∀ c, σ' c = c ^ (2 ^ 1) := hσ
  have hK3 : Nat.card K = 2 ^ (3 * 1) := by rw [hK']; norm_num
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  obtain ⟨-, -, -, -, -, -, -, ⟨e2⟩⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) le_rfl K hK' σ' hσe
  obtain ⟨-, E, hE, hEcard⟩ :=
    CFSG.RankThree.Chevalley.even_triality_commuting_rank_one_product_and_elementary_nine K
      σ'.toRingHom (fun c => CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq (q := 2 ^ 1) hK' hσe c)
  let φ : S ≃* graphFixedRootGroup TwistTag.D4 K σ'.toRingHom := e.trans e2
  let Ψ : ↥E →* S := φ.symm.toMonoidHom.comp E.subtype
  have hΨ : Function.Injective Ψ := φ.symm.injective.comp E.subtype_injective
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => mul_comm' a b
  have hpow : ∀ a : ↥E, a ^ 3 = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 E) a
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm hpow
    (by rw [hEcard]; norm_num) Ψ hΨ le_top

end CFSG.QuasithinUnique.Setup.Family
