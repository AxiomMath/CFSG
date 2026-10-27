module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenParabolicOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open scoped commutatorElement

@[expose] def TenThreeThree.KFactParabolicCommNA : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P B : Subgroup A) (p : ℕ), p.Prime → p ≠ 2 →
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    IsPGroup p ↥B → B ≤ Subgroup.normalizer (Y : Set A) →
    B ≤ Subgroup.normalizer (P : Set A) →
    (∀ b ∈ B, ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) →
    (∀ c ∈ ⁅B, B⁆, ∀ y ∈ Y, c * y = y * c) ∨ 4 ≤ Open.pRank p Y

variable {G : Type} [Group G] [Finite G]

namespace ParabolicComm

theorem commutatorElement_mem {M : Subgroup G} {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    ⁅a, b⁆ ∈ M :=
  M.commutator_le_self (Subgroup.commutator_mem_commutator ha hb)

theorem mk_commutator_mem {M B : Subgroup G} (hBM : B ≤ M) {b₁ b₂ : G} (h₁ : b₁ ∈ B)
    (h₂ : b₂ ∈ B) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨⁅b₁, b₂⁆, commutatorElement_mem (hBM h₁) (hBM h₂)⟩ ∈
      ⁅barM M B, barM M B⁆ := by
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      ⟨⁅b₁, b₂⁆, commutatorElement_mem (hBM h₁) (hBM h₂)⟩ =
      ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b₁, hBM h₁⟩,
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b₂, hBM h₂⟩⁆ := by
    rw [← map_commutatorElement]
    rfl
  rw [e]
  exact Subgroup.commutator_mem_commutator ⟨⟨b₁, hBM h₁⟩, h₁, rfl⟩ ⟨⟨b₂, hBM h₂⟩, h₂, rfl⟩

theorem forall_mem_commutator {M B L : Subgroup G} (hBM : B ≤ M)
    (hc : ∀ c ∈ ⁅barM M B, barM M B⁆, ∀ y ∈ barM M L, c * y = y * c) :
    ∀ c ∈ ⁅B, B⁆, ∃ hcM : c ∈ M, ∀ y ∈ barM M L,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hcM⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hcM⟩ := by
  let C' : Subgroup G := ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype
  have hle : ⁅B, B⁆ ≤ C' := by
    rw [Subgroup.commutator_le]
    intro b₁ h₁ b₂ h₂
    refine ⟨⟨⁅b₁, b₂⁆, commutatorElement_mem (hBM h₁) (hBM h₂)⟩, ?_, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc _ (mk_commutator_mem hBM h₁ h₂) y hy).symm
  intro c hc'
  obtain ⟨m, hm, rfl⟩ := hle hc'
  refine ⟨m.2, fun y hy => ?_⟩
  simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hm
  exact (hm y hy).symm

end ParabolicComm

theorem commutator_comm_le_of_cases_na (hK : KFactParabolicCommNA) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {M H L B : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLn : (L.subgroupOf M).Normal) (hM3 : Open.pRank p M ≤ 3) (hBHM : B ≤ H ⊓ M)
    (hB : IsPGroup p B) (hI : (cZero (H ⊓ L)).Nonempty)
    (hBJ : ∀ b ∈ B, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    (hcases : ∀ b ∈ B, (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        IsParabolicTwo (barM M L) (barM M (H ⊓ L)))) :
    ⁅⁅B, B⁆, L⁆ ≤ pCoreOf 2 L := by
  have hLM : L ≤ M := hL.le
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hBM : B ≤ M := fun b hb => (hBHM hb).2
  have hCB : ⁅B, B⁆ ≤ B := B.commutator_le_self
  have hCM : ⁅B, B⁆ ≤ M := hCB.trans hBM
  by_cases hall : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M
  · exact commutator_le_pCoreOf_of_forall hLM hCM hMn fun c hc => hall c (hCB hc)
  obtain ⟨b₀, hb₀, hb₀'⟩ : ∃ b ∈ B, ¬ ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M :=
    Classical.by_contradiction fun h => hall fun b hb => Classical.by_contradiction fun h' =>
      h ⟨b, hb, h'⟩
  obtain ⟨hcl, hpar⟩ := (hcases b₀ hb₀).resolve_left hb₀'
  have hact := fun b (hb : b ∈ B) =>
    bar_action hLM hLn (hBHM hb) (odd_orderOf_of_isPGroup hp hp2 hB hb) (hBJ b hb)
  have hBp : IsPGroup p ↥(barM M B) := hB.of_surjective _ (barHom_surjective M B hBM)
  have hnab : ∃ x ∈ barM M (H ⊓ L), ∃ y ∈ barM M (H ⊓ L),
      x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 (barM M (H ⊓ L)) := by
    obtain ⟨I₀, hI₀⟩ := hI
    obtain ⟨u, hu, v, hv, huv⟩ := exists_comm_not_mem_pCoreOf_of_cZero hI₀
    have hIX : I₀ ≤ H ⊓ L := hI₀.le
    have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, hXM (hIX hu)⟩, ⟨⟨u, hXM (hIX hu)⟩, hIX hu, rfl⟩,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hXM (hIX hv)⟩, ⟨⟨v, hXM (hIX hv)⟩, hIX hv, rfl⟩,
      fun h => huv (comm_mem_pCoreOf_of_bar hXM hIX hu hv h)⟩
  have hkey := hK (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) (barM M (H ⊓ L)) (barM M B) p hp hp2
    hL.component.2.2 (pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent) hcl hpar hnab hBp
    (by
      rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩
      exact (hact b hb).2.1)
    (by
      rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩
      exact (hact b hb).2.2.1)
    (by
      rintro _ ⟨⟨b, hbM⟩, hb, rfl⟩ w hw hwW
      exact (hact b hb).2.2.2 w hw hwW)
  rcases hkey with hc | h4
  · refine commutator_le_pCoreOf_of_forall hLM hCM hMn fun c hc' => ?_
    obtain ⟨hcM, hcL⟩ := ParabolicComm.forall_mem_commutator hBM hc c hc'
    exact commutator_mem_pCoreOf_of_centralizes hLM hcM hcL
  · exact absurd (h4.trans ((pRank_barM_le hp hp2 _).trans hM3)) (by norm_num)

theorem agl81ElevenElevenParabolicComm_of (hC : AGL81TenThreeThreeCasesCfg G)
    (hK : KFactParabolicCommNA) (h10C : AGL81TenOneCZero G) (h91 : AGL81TenNineOneCfg G) :
    AGL81ElevenElevenParabolicComm G := by
  intro hS p P M H Q K hd L hL hLn B hBHM hB hBJ _
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  exact commutator_comm_le_of_cases_na hK hp hp2 hL hLn (pRank_le_three_of_escape hS hd) hBHM hB
    (h10C hS p P M H Q K hd L hL (h91 hS p P M H Q K hd L hL)) hBJ
    fun b hb => hC hS p P M H Q K hd L hL hLn b (hBHM hb)
      (odd_orderOf_of_isPGroup hp hp2 hB hb) (hBJ b hb)

end CFSG.LocalAnalysis.RankThreeTheoremC
