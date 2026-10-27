module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSubGen
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

omit [Finite X] in
theorem EndB.mk_commutatorElement {M : Subgroup X} {a b : X} (ha : a ∈ M) (hb : b ∈ M)
    (hab : ⁅a, b⁆ ∈ M) :
    (QuotientGroup.mk ⟨⁅a, b⁆, hab⟩ : ↥M ⧸ pPrimeCore 2 ↥M) =
      ⁅(QuotientGroup.mk ⟨a, ha⟩ : ↥M ⧸ pPrimeCore 2 ↥M), QuotientGroup.mk ⟨b, hb⟩⁆ := by
  have heq : (⟨⁅a, b⁆, hab⟩ : ↥M) = ⁅(⟨a, ha⟩ : ↥M), ⟨b, hb⟩⁆ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [heq]
  exact map_commutatorElement (QuotientGroup.mk' _) _ _

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem not_mem_commutator_W
    (hJ : JLayer hs π) (hπi : Function.Injective π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ ⁅W, W⁆ := by
  have hle : ⁅W, W⁆ ≤ preimageOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j)) := by
    rw [commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hWM ha) (hWM hb)) (inv_mem (hWM ha))) (inv_mem (hWM hb))
    rw [mem_preimageOf hab, mk_commutatorElement (hWM ha) (hWM hb) hab]
    exact hJ.commutator_mem_A hQ _ _
  intro h
  have h1 := hle h
  rw [mem_preimageOf (mem_centralizer_singleton_iff.mpr rfl)] at h1
  exact hJ.betaBar_not_mem_A hπi h1

theorem z_mem_commutator_W' (hs : Setting46e t L p f S w z V i j) {W : Subgroup X}
    (hDW : S ⊓ L ≤ W) : z ∈ ⁅W, W⁆ := by
  obtain ⟨c, hc, hcz⟩ := hs.setup.exists_commutator_sq_eq_z
  rw [← hcz]
  exact pow_mem (commutator_mono hDW hDW hc) 2

theorem exists_y [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) (hJ : JLayer hs π)
    (hπi : Function.Injective π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ∃ y ∈ normalizer (W : Set X), y ∉ W ∧ y ^ 2 ∈ W ∧ IsPGroup 2 ↥(W ⊔ zpowers y) ∧
      y ∉ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ∧
      y * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y⁻¹ =
        w ^ (orderOf w / 2) * t ^ i * z ^ j * z ∧ y * z * y⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  have hDW : S ⊓ L ≤ W := (le_sup_right.trans le_sup_left).trans (hs.beta.lt.le.trans hUW)
  have hnot := hJ.not_isSylowOf_W hnab hFC hKC hI hKF hcent hW htW
  obtain ⟨y, hyN, hyW, hy2, hy2grp⟩ := exists_mem_normalizer_sq_mem hW.isPGroup hnot
  have hyM : y ∉ centralizer ({β} : Set X) := by
    intro hyM
    have hle : W ⊔ zpowers y ≤ centralizer ({β} : Set X) := sup_le hW.le (zpowers_le.mpr hyM)
    have := hW.eq_of_le le_sup_left hle hy2grp
    exact hyW (this ▸ mem_sup_right (mem_zpowers y))
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzM : z ∈ centralizer ({β} : Set X) := K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβz : β * z = z * β := (mem_centralizer_singleton_iff.mp hzM).symm
  have hyβ := conj_mem_zW y hyN β hβZ
  have hcomm := conj_mem_commutator' (N := normalizer (W : Set X)) conj_mem_W conj_mem_W
  have hyb : y * β * y⁻¹ = β * z := by
    rcases mem_closure_pair hβ2 hz2 hβz (hZle hyβ) with h | h | h | h
    · exfalso
      apply hs.beta.ne_one
      have hb1 : β = 1 := by
        calc β = y⁻¹ * (y * β * y⁻¹) * y := by group
          _ = 1 := by rw [h]; group
      exact hb1
    · exfalso
      apply hyM
      rw [mem_centralizer_singleton_iff]
      calc y * β = (y * β * y⁻¹) * y := by group
        _ = β * y := by rw [h]
    · exfalso
      apply hJ.not_mem_commutator_W hπi hQ hW.le
      have := hcomm y⁻¹ (inv_mem hyN) z (z_mem_commutator_W' hs hDW)
      rwa [← h, show y⁻¹ * (y * β * y⁻¹) * y⁻¹⁻¹ = β by group] at this
    · exact h
  refine ⟨y, hyN, hyW, hy2, hy2grp, hyM, hyb, ?_⟩
  have hy2β : y ^ 2 * β = β * y ^ 2 := mem_centralizer_singleton_iff.mp (hW.le hy2)
  have hy2β' : (y * y) * β = β * (y * y) := by rw [← sq]; exact hy2β
  have h1 : y * (β * z) * y⁻¹ = β := by
    rw [← hyb]
    calc y * (y * β * y⁻¹) * y⁻¹ = ((y * y) * β) * (y * y)⁻¹ := by group
      _ = β := by rw [hy2β']; group
  have h2 : y * (β * z) * y⁻¹ = (y * β * y⁻¹) * (y * z * y⁻¹) := by group
  rw [h2, hyb] at h1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  calc y * z * y⁻¹ = (β * z)⁻¹ * ((β * z) * (y * z * y⁻¹)) := by group
    _ = (β * z)⁻¹ * β := by rw [h1]
    _ = z := by rw [mul_inv_rev, hzinv]; group

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
