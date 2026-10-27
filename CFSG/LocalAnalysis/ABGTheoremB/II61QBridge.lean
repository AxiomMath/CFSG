module

public import CFSG.LocalAnalysis.ABGTheoremB.CoverCentralizer
public import CFSG.GroupTheory.ABGLocalTools.QGroupPStability
import CFSG.GroupTheory.QuasiDihedralFusion.SimpleNormal

public section

namespace CFSG.ABGTheoremB.Setting

open CFSG.ABGQGroups CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

variable {G : Type u} [Group G] (σ : Setting G)

private theorem pCore_ne_bot_of_isPLocal {r : ℕ} {H : Subgroup G} (hH : IsPLocal r H) :
    CFSG.pCore r H ≠ ⊥ := by
  obtain ⟨R, hR1, hRp, rfl⟩ := hH
  have hRle : R ≤ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer
  have hn : (R.subgroupOf (Subgroup.normalizer (R : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mpr le_rfl
  have hle : R.subgroupOf (Subgroup.normalizer (R : Set G)) ≤
      CFSG.pCore r (Subgroup.normalizer (R : Set G)) :=
    le_sSup ⟨hn, hRp.comap_subtype⟩
  intro hbot
  apply hR1
  rw [eq_bot_iff]
  intro g hg
  have hmem : (⟨g, hRle hg⟩ : Subgroup.normalizer (R : Set G)) ∈
      CFSG.pCore r (Subgroup.normalizer (R : Set G)) := hle hg
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

theorem familyL_pCore_ne_bot {r : ℕ} {H : Subgroup G} (hH : H ∈ σ.familyL r) :
    CFSG.pCore r H ≠ ⊥ :=
  pCore_ne_bot_of_isPLocal hH.1

variable [Finite G]

theorem not_dvd_q_of_ne_p (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) (hrp : r ≠ σ.p) :
    ¬ r ∣ σ.q := fun h =>
  hrp ((Nat.prime_dvd_prime_iff_eq hr hσ.p_prime).mp (hr.dvd_of_dvd_pow h))

theorem familyL_isQGroup (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime)
    (hdiv : r ∣ Nat.card σ.ON) {H : Subgroup G} (hH : H ∈ σ.familyL r) : IsQGroup H :=
  (σ.familyL_properties hσ hII hr hdiv hH).1.1

theorem familyL_qGroupStanding (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) {H : Subgroup G} (hH : H ∈ σ.familyL r)
    (hO : CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H) :
    QGroupStanding r σ.q H := by
  obtain ⟨hQ, -, -, ⟨P, hP⟩, -, -⟩ := σ.familyL_properties hσ hII hr hdiv hH
  exact ⟨hQ, hσ.five_lt_q, ⟨σ.height, hσ.sylow.of_le P (hP.trans inf_le_left)⟩, hO⟩

theorem familyL_qGroupStabilityFacts (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) {H : Subgroup G} (hH : H ∈ σ.familyL r) :
    QGroupStabilityFacts σ.q H := by
  obtain ⟨J, hJn, ⟨F, hF, hFin, hq, he⟩, h2⟩ :=
    σ.exists_normal_isPGroup_centralizer_of_mem_familyL hσ hII hr hdiv hH
  exact ⟨⟨J, F, hF, hFin, hJn, hq, he, h2⟩⟩

theorem II61Q_of_qGroup (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H := by
  intro r hr hdiv hrp H hH hO
  have : Fact r.Prime := ⟨hr⟩
  exact isPStable_of_qGroup (σ.prime_ne_two_of_dvd_ON hr hdiv)
    (σ.familyL_qGroupStanding hσ hII hr hdiv hH hO) (σ.not_dvd_q_of_ne_p hσ hr hrp)
    (σ.familyL_pCore_ne_bot hH) (σ.familyL_qGroupStabilityFacts hσ hII hr hdiv hH)

end CFSG.ABGTheoremB.Setting
