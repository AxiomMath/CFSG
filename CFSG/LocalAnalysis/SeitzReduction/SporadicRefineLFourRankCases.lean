module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourRankA8
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHS
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem hs_card_lt_of_mul_self
    {S : Type} [Group S] (e : S ≃* NativeSporadic.HS)
    {E : Subgroup S} (hE : ∀ x ∈ E, x * x = 1) : Nat.card E < 32 := by
  have h : QuasithinUnique.Lin2.RankCert.ElemAbelianLt S 32 :=
    QuasithinUnique.Lin2.RankCert.ElemAbelianLt.of_mulEquiv (Y := NativeSporadic.HS) e
      QuasithinUnique.Lin2.hs_native_rank'
  refine h E ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_mul_self hE a.2 b.2)⟩⟩, fun x hx => ?_⟩
  rw [sq]
  exact hE x hx

theorem card_mulAut_dvd_of_lieModel_psl_four_two {X : Type} [Group X]
    (h : LieModel X .PSL 4 2 1) : Nat.card (MulAut X) ∣ 40320 := by
  obtain ⟨φ⟩ := (ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).1 h
  have : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  have hXc : Nat.card X = 20160 := by
    rw [Nat.card_congr φ.toEquiv]
    exact card_alternatingGroup_eight
  have hZ : center X = ⊥ := by
    obtain ⟨eS⟩ := nonempty_equiv_SL_four_of_lieModel h
    exact center_eq_bot_of_mulEquiv_SL_four (Nat.card_zmod 2) eS
  rw [RankOne.card_mulAut_of_center_eq_bot hZ, hXc, show (40320 : ℕ) = 20160 * 2 by norm_num]
  exact Nat.mul_dvd_mul_left _
    (ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six
      (by norm_num) φ)

section SuzFive


theorem suz_not_lieModel_psl_four_two {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Suz) {σ : MulAut S} (hcard : Nat.card (fixedSubgroup σ) = 1209600)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hfree : FixedCentralizerTwoFree σ D) :
    ¬ LieModel (D ⧸ center D) .PSL 4 2 1 := by
  intro hDm
  have hq : Nat.card (D ⧸ center D) = 20160 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hDcard : Nat.card D = 20160 * Nat.card (center D) := by
    rw [← hq]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hN : D.Normal := normal_of_isComponent_of_twoFree hD hfree h2
  have : Group.IsPerfect D := hD.1.1
  have hdvd := card_dvd_card_centralizer_mul_card_mulAut (H := fixedSubgroup σ) (D := D)
  have hdvd' : 1209600 ∣ Nat.card (centralizer (D : Set (fixedSubgroup σ))) * 40320 :=
    hcard ▸ hdvd.trans (Nat.mul_dvd_mul_left _ (card_mulAut_dvd_of_lieModel_psl_four_two hDm))
  rw [show (1209600 : ℕ) = 30 * 40320 by norm_num] at hdvd'
  have h30 : 30 ∣ Nat.card (centralizer (D : Set (fixedSubgroup σ))) :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 40320) hdvd'
  have h5 : 5 ∣ Nat.card (centralizer (D : Set (fixedSubgroup σ))) :=
    (by norm_num : (5 : ℕ) ∣ 30).trans h30
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := centralizer (D : Set (fixedSubgroup σ))) 5 h5
  have hy' : orderOf ((y : fixedSubgroup σ) : S) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hK : D.map (fixedSubgroup σ).subtype ≤ centralizer {((y : fixedSubgroup σ) : S)} := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_iff.mp y.2 d hd)
  have hKcard : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
    card_map_of_injective (fixedSubgroup σ).subtype_injective
  have h20160 : 20160 ∣ Nat.card (D.map (fixedSubgroup σ).subtype) := by
    rw [hKcard, hDcard]
    exact Dvd.intro _ rfl
  rcases suz_card_dvd_of_le_centralizer e hy' hK with h | h
  · exact absurd (h20160.trans h) (by norm_num)
  · exact absurd (h20160.trans h) (by norm_num)

end SuzFive

section ONTransport


theorem on_outer_not_lieModel_psl_four_two {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.ON) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hfree : FixedCentralizerTwoFree σ D) : ¬ LieModel (D ⧸ center D) .PSL 4 2 1 := by
  intro hDm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card (D ⧸ center D) = 20160 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hDcard : Nat.card D = 20160 * Nat.card (center D) := by
    rw [← hq]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 6) (G := D)
    (by rw [hDcard]; exact Dvd.dvd.mul_right (by norm_num) _)
  have hKp : IsPGroup 2 K := IsPGroup.of_card hK
  have hKZ : K ⊓ center D = ⊥ := inf_center_eq_bot_of_twoFree hfree hKp
  set ι : K →* S := (fixedSubgroup σ).subtype.comp (D.subtype.comp K.subtype) with hι
  have hιinj : Function.Injective ι :=
    (fixedSubgroup σ).subtype_injective.comp (D.subtype_injective.comp K.subtype_injective)
  have hT₀card : Nat.card ι.range = 64 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hιinj, Subgroup.card_top, hK]
    norm_num
  have hfix : ∀ x ∈ ι.range, σ x = x := by
    rintro _ ⟨k, rfl⟩
    exact ((k : D) : fixedSubgroup σ).2
  obtain ⟨q, hqT, hqo, W, hWT, hWcard, hWq⟩ :=
    on_outer_exists_of_fix_card_sixtyfour e hσ hout hT₀card hfix
  obtain ⟨qK, rfl⟩ := hqT
  set W' : Subgroup K := W.comap ι with hW'
  have hW'card : Nat.card W' = 32 := by
    rw [← Subgroup.card_map_of_injective hιinj, hW', Subgroup.map_comap_eq_self hWT, hWcard]
  have hqKo : orderOf qK = 4 := by rw [← orderOf_injective ι hιinj, hqo]
  have hW'q : ∀ w ∈ W', w * qK = qK * w := fun w hw =>
    hιinj (by rw [map_mul, map_mul]; exact hWq _ hw)
  obtain ⟨eS⟩ := nonempty_equiv_SL_four_of_lieModel hDm
  set ψ : K →* D ⧸ center D := (QuotientGroup.mk' (center D)).comp K.subtype with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : (k : D) ∈ center D := by
      have h0 : (QuotientGroup.mk' (center D)) (k : D) = 1 := hk
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    have h2 : (k : D) ∈ K ⊓ center D := mem_inf.mpr ⟨k.2, h1⟩
    rw [hKZ, mem_bot] at h2
    exact Subtype.ext h2
  have hxo : orderOf (ψ qK) = 4 := by rw [orderOf_injective ψ hψinj, hqKo]
  have hTp : IsPGroup 2 ((⊤ : Subgroup K).map ψ) := (IsPGroup.of_card (n := 6)
    (by rw [Subgroup.card_top, hK])).map ψ
  have h16 := card_le_sixteen_of_mulEquiv_SL_four (Nat.card_zmod 2) eS hTp
    (mem_map_of_mem ψ (mem_top qK)) hxo (map_mono (le_top : W' ≤ ⊤)) (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, hW'q w hw])
  rw [Subgroup.card_map_of_injective hψinj, hW'card] at h16
  omega

end ONTransport

end CFSG.SeitzReduction.SporadicRefine
