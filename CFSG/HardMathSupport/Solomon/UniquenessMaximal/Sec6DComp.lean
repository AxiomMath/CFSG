module

public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G]

theorem mem_barX_iff {p : ℕ} {X K : Subgroup G} {z : ↥X ⧸ GLAPPrimeCore p ↥X} :
    z ∈ barX p X K ↔ ∃ x : ↥X, (x : G) ∈ K ∧ QuotientGroup.mk' (GLAPPrimeCore p ↥X) x = z := by
  unfold barX
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).2 hx, rfl⟩

theorem barX_gLBConj_le (p : ℕ) {C : Subgroup G} {j : G} (hj : j ∈ C) (T : Subgroup G) :
    barX p C (GLBConj j T) ≤
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hj⟩) (barX p C T) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : (c : G) ∈ GLBConj j T := (Subgroup.mem_subgroupOf).1 hc
  rw [mem_gLBConj, ← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹, ?_, rfl⟩
  show (⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹ : ↥C) ∈ T.subgroupOf C
  rw [Subgroup.mem_subgroupOf]
  simpa using mem_gLBConj.1 hc'

theorem barX_gLBConj_of_mem (p : ℕ) {M : Subgroup G} {g : G} (hg : g ∈ M) (K : Subgroup G) :
    barX p M (GLBConj g K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) (barX p M K) := by
  refine le_antisymm (barX_gLBConj_le p hg K) ?_
  have h := barX_gLBConj_le p (M.inv_mem hg) (GLBConj g K)
  rw [gLBConj_inv_gLBConj] at h
  have h2 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) h
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨g⁻¹, M.inv_mem hg⟩ : ↥M) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, gLBConj_gLBConj_inv] at h2
  exact h2

variable [Finite G]

theorem gLBConj_X_of_mem {X : Subgroup G} {g : G} (hg : g ∈ X) : GLBConj g X = X :=
  mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)

theorem comp_conj {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) {g : G} (hg : g ∈ X) :
    GLAPComponent p X (GLBConj g K) := by
  have := glaPComponent_gLBConj hK g
  rwa [gLBConj_X_of_mem hg] at this

theorem le_normalizer_of_ne {p : ℕ} {X K K' : Subgroup G} (hK : GLAPComponent p X K)
    (hK' : GLAPComponent p X K') (hne : K ≠ K') : K ≤ Subgroup.normalizer (K' : Set G) := by
  intro g hg
  have hgX : g ∈ X := hK.1 hg
  have hbar : barX p X K ≠ barX p X K' := fun h => hne (glaPComponent_unique hK hK' h)
  have hcomm : ⁅barX p X K, barX p X K'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK.2.2.1 hK'.2.2.1 hbar
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hg' : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ ∈ barX p X K :=
    mem_barX_iff.2 ⟨⟨g, hgX⟩, hg, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 (hcen hg')
  have hconj : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩) (barX p X K') =
      barX p X K' := by
    set gb := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ with hgb
    ext z
    rw [mem_gLBConj]
    constructor
    · intro hw
      generalize hw' : gb * z * gb⁻¹ = w at hw
      have h1 : w * gb = gb * w := hc w hw
      have hz : z = gb⁻¹ * (w * gb) := by rw [← hw']; group
      rw [h1] at hz
      have : z = w := by rw [hz]; group
      rw [this]; exact hw
    · intro hz
      have h1 : z * gb = gb * z := hc z hz
      have e : gb * z * gb⁻¹ = z := by rw [← h1]; group
      rw [e]; exact hz
  have hK'g : GLAPComponent p X (GLBConj g K') := comp_conj hK' hgX
  have hbar' : barX p X (GLBConj g K') = barX p X K' := by
    rw [barX_gLBConj_of_mem p hgX K', hconj]
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hK'g hK' hbar')

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
