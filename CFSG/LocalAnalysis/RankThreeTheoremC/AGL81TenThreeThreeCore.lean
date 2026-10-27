module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def KFactParabolicW : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), Open.IsQuasisimple ↥Y →
    pCoreOf 2 Y = ⊥ → IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    ∀ b : A, Odd (orderOf b) → b ∈ normalizer (Y : Set A) → b ∈ normalizer (P : Set A) →
      (∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
          wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) →
      ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index ∨ ∀ y ∈ Y, b * y = y * b

@[expose] def TenThreeThreeAt (Φ : Subgroup G → Subgroup G → Subgroup G → Prop) : Prop :=
  ∀ (M H L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M (pCoreOf 2 H) →
    normalizer (pCoreOf 2 H : Set G) = H → pCoreOf 2 M ≤ pCoreOf 2 H →
    IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal → Φ M (pCoreOf 2 H) L →
    ∀ b ∈ H ⊓ M, Odd (orderOf b) →
      (∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
      ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L ∨
        ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M

variable {G}

theorem not_two_dvd_relIndex_of_isParabolicTwo {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (h : IsParabolicTwo Y P) : ¬ 2 ∣ P.relIndex Y := by
  obtain ⟨hPY, T, hT, hN⟩ := h
  have hTP : T ≤ P := fun t ht => hN ⟨hT.1 ht, le_normalizer ht⟩
  have e := relIndex_mul_relIndex T P Y hTP hPY
  intro h2
  exact hT.2.2 (show 2 ∣ T.relIndex Y from e ▸ dvd_mul_of_dvd_right h2 _)

theorem pCoreOf_barM_eq_bot {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) :
    pCoreOf 2 (barM M L) = ⊥ := by
  have h := CZeroLift.pCore_eq_bot_of_isSubnormal hL.component.2.1
    (pCore_quotient_pCore_eq_bot' 2)
  unfold pCoreOf
  rw [h, Subgroup.map_bot]

theorem bar_action {M H L : Subgroup G} (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {b : G}
    (hb : b ∈ H ⊓ M) (hbo : Odd (orderOf b))
    (hbJ : ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) :
    Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ ∈ normalizer (barM M L : Set _) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ ∈ normalizer (barM M (H ⊓ L) : Set _) ∧
      ∀ w (hw : w ∈ barM M (H ⊓ L)), QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M (H ⊓ L))) ⟨w, hw⟩ ∈
          wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L))) →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ * w *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩)⁻¹ * w⁻¹ ∈
            pCoreOf 2 (barM M (H ⊓ L)) := by
  have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
  have hbM : b ∈ M := hb.2
  have hbL : b ∈ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLM).mp hLn hbM
  have hbX : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := (mem_normalizer_iff.mp (le_normalizer hb.1 : b ∈ normalizer (H : Set G)) x)
    have h2 := mem_normalizer_iff.mp hbL x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  refine ⟨hbo.of_dvd_nat
    ((orderOf_map_dvd _ _).trans (Subgroup.orderOf_coe (⟨b, hbM⟩ : ↥M)).symm.dvd),
    mem_normalizer_barM hbM hbL, mem_normalizer_barM hbM hbX,
    fun w hw hwW => commutator_mem_of_wSup hXM hbM hbX hbJ hw hwW⟩

theorem tenThreeThreeAt_of_parabolic (hKF : KFactParabolicW) :
    TenThreeThreeAt G (fun M S L => NineThreeTwo M S L) := by
  intro M H L _ _ hNH hMS hL hLn h2 b hb hbo hbJ
  have hLM : L ≤ M := hL.le
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  obtain ⟨hcl, hpar, -⟩ := h2
  rw [hNS] at hpar
  set P := barM M (H ⊓ L) with hP
  obtain ⟨hbbo, hbLbar, hbP, hW⟩ := bar_action hLM hLn hb hbo hbJ
  set bb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩ with hbb
  rcases hKF _ (barM M L) P hL.component.2.2 (pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent)
      hcl hpar bb hbbo hbLbar hbP hW with hodd | hcen
  · left
    have hk : L ⊓ pCoreOf 2 M ≤ H := fun x hx =>
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hMS hx.2)
    exact not_two_dvd_relIndex_jZero hLM hk (not_two_dvd_relIndex_of_isParabolicTwo hpar) hodd
  · right
    exact commutator_mem_pCoreOf_of_centralizes hLM hb.2 hcen

theorem concl_of_forall {M H L B : Subgroup G}
    (h : ∀ b ∈ B, ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L ∨
      ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    (∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
      ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L := by
  by_cases hodd : ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L
  · exact Or.inr hodd
  · exact Or.inl fun b hb => (h b hb).resolve_left hodd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
