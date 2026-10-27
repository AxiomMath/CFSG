module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.E27Lie.CocycleCount
public import CFSG.HardMathSupport.Lang.Triality.HeightCoord
public import CFSG.LieType.Chevalley.C2E6BruhatBuilding
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

variable {G : Type*} [Group G] {β : MulAut G} {N : ℕ → Subgroup G} {d : ℕ}
  {A : ℕ → Type*} [∀ k, CommGroup (A k)] {Φ : ∀ k, N k →* A k} {τ : ∀ k, A k →* A k} {b : ℕ → ℕ}

theorem cocycleProd_twistedConj (hβ3 : β ^ 3 = 1) (y w : G) :
    cocycleProd β (w⁻¹ * y * β w) = w⁻¹ * cocycleProd β y * w := by
  have h3 : ∀ x, β (β (β x)) = x := fun x => by
    have := congrArg (fun φ : MulAut G => φ x) hβ3
    simpa [pow_succ] using this
  simp only [cocycleProd, map_mul, map_inv, h3]
  group

theorem CocycleData.exists_kill_step (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) {m y : G}
    (hm : m ∈ N 0) (hmy : m⁻¹ * y ∈ N k) {c : A k} (hc : c ∈ (Φ k).range)
    (hcob : Φ k ⟨m⁻¹ * y, hmy⟩ = c * (τ k c)⁻¹) :
    ∃ w ∈ N k, m⁻¹ * (w⁻¹ * y * β w) ∈ N (k + 1) := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hc
  obtain ⟨hX, hΦX⟩ := h.conj k hk m⁻¹ (inv_mem hm) x⁻¹
  have hβx : β (x : G) ∈ N k := h.stable k (x : G) x.2
  have hPΦ : Φ k (⟨m⁻¹ * ((x⁻¹ : N k) : G) * (m⁻¹)⁻¹, hX⟩ * ⟨m⁻¹ * y, hmy⟩ *
      ⟨β (x : G), hβx⟩ : N k) = 1 := by
    rw [map_mul, map_mul, hΦX, map_inv, h.act k hk x, hx, hcob]
    group
  refine ⟨(x : G), x.2, ?_⟩
  have heq : m⁻¹ * ((x : G)⁻¹ * y * β (x : G)) =
      ((⟨m⁻¹ * ((x⁻¹ : N k) : G) * (m⁻¹)⁻¹, hX⟩ * ⟨m⁻¹ * y, hmy⟩ *
        ⟨β (x : G), hβx⟩ : N k) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [heq]
  exact h.ker k hk _ hPΦ

theorem CocycleData.norm_eq_one (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) {m y : G}
    (hm : m ∈ N 0) (hmc : cocycleProd β m = 1) (hyc : cocycleProd β y = 1)
    (hmy : m⁻¹ * y ∈ N k) :
    Φ k ⟨m⁻¹ * y, hmy⟩ * τ k (Φ k ⟨m⁻¹ * y, hmy⟩) * τ k (τ k (Φ k ⟨m⁻¹ * y, hmy⟩)) = 1 := by
  obtain ⟨hX, hΦ⟩ := h.corr_mem hk hm ⟨m⁻¹ * y, hmy⟩
  have hcorr : CocycleData.corr β m (m⁻¹ * y) = 1 := by
    have h1 := CocycleData.cocycleProd_eq (β := β) m (m⁻¹ * y)
    rw [mul_inv_cancel_left, hyc, hmc, mul_one] at h1
    exact h1.symm
  have h1 : (⟨CocycleData.corr β m (m⁻¹ * y), hX⟩ : N k) = 1 := Subtype.ext hcorr
  rw [h1, map_one] at hΦ
  exact hΦ.symm

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
