module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.Milestones.ASVolI.I2Covers
import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fixed
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentKpIrred
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc5
import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_commute_mem_coset (hp2 : p ≠ 2) {J : Subgroup G} {b : G} {k : ℕ}
    (hbk : b ^ (p ^ k) = 1) (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hb : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J) {x : G} (hx : x ∈ J) :
    ∃ n ∈ pCoreOf 2 J, b * (x * n) = x * n * b := by
  have hp : p.Prime := Fact.out
  have hN : ∀ n ∈ pCoreOf 2 J, b * n * b⁻¹ ∈ pCoreOf 2 J := fun n hn =>
    CFSG.ASVolI.burnsideI22P5_pCoreOf_conj J b (Subgroup.mem_normalizer_iff.mp hbJ) hn
  have hxJ : ∀ h : G, h ∈ J ↔ x⁻¹ * h * x⁻¹⁻¹ ∈ J := fun h =>
    ⟨fun hh => J.mul_mem (J.mul_mem (J.inv_mem hx) hh) (J.inv_mem (J.inv_mem hx)), fun hh => by
      have := J.mul_mem (J.mul_mem hx hh) (J.inv_mem hx)
      simpa [mul_assoc] using this⟩
  have hg : x⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 J := by
    have := CFSG.ASVolI.burnsideI22P5_pCoreOf_conj J x⁻¹ hxJ (hb x hx)
    simpa [mul_assoc] using this
  have hNp : ¬ p ∣ Nat.card (pCoreOf 2 J) := by
    intro hdvd
    have h2 : IsPGroup 2 ↥(pCoreOf 2 J) := CFSG.pCore_isPGroup.map _
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [hm] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨n, hn, he⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.Sec13.fixed_in_coset (pCoreOf 2 J) b x k hbk hN hg hNp
  refine ⟨n, hn, ?_⟩
  calc b * (x * n) = b * (x * n) * b⁻¹ * b := by group
    _ = x * n * b := by rw [he]

theorem surjective_inf_quot (hp2 : p ≠ 2) {J C : Subgroup G} {b : G} {k : ℕ}
    (hbk : b ^ (p ^ k) = 1) (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hb : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J) (hC : ∀ x : G, b * x = x * b → x ∈ C) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp
      (Subgroup.inclusion (inf_le_right : C ⊓ J ≤ J))) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨n, hn, hc⟩ := exists_commute_mem_coset hp2 hbk hbJ hb x.2
  have hnJ : n ∈ J := Subgroup.map_subtype_le _ hn
  refine ⟨⟨(x : G) * n, hC _ hc, J.mul_mem x.2 hnJ⟩, ?_⟩
  obtain ⟨n', hn', rfl⟩ := hn
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  convert (CFSG.pCore 2 ↥J).inv_mem hn' using 1
  exact Subtype.ext (by simp)

theorem hasNormalPComplement_quot_of_inf (hp2 : p ≠ 2) {J C : Subgroup G} {b : G} {k : ℕ}
    (hbk : b ^ (p ^ k) = 1) (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hb : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J) (hC : ∀ x : G, b * x = x * b → x ∈ C)
    (h : CFSG.HasNormalPComplement p ↥(C ⊓ J)) :
    CFSG.HasNormalPComplement p (↥J ⧸ CFSG.pCore 2 ↥J) :=
  hasNormalPComplement_of_surjective' _ (surjective_inf_quot hp2 hbk hbJ hb hC) h

theorem not_hasNormalPComplement_inf (hp2 : p ≠ 2) {J L C : Subgroup G} {b : G} {k : ℕ}
    (hbk : b ^ (p ^ k) = 1) (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hb : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J) (hC : ∀ x : G, b * x = x * b → x ∈ C)
    (hJL : J ≤ L) (hJ : ¬ CFSG.HasNormalPComplement p (↥J ⧸ CFSG.pCore 2 ↥J)) :
    ¬ CFSG.HasNormalPComplement p ↥(C ⊓ L) := fun h =>
  hJ (hasNormalPComplement_quot_of_inf hp2 hbk hbJ hb hC
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5.hasNormalPComplement_of_injective
      (Subgroup.inclusion (inf_le_inf_left C hJL)) (Subgroup.inclusion_injective _) h))

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
