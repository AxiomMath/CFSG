module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Hyp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.normalizer_W (h : CampbellHyp X K R P) :
    X ≤ normalizer (omegaCenter (K ⊓ pCoreOf 2 X) : Set A) :=
  normalizer_omegaCenter (normalizer_inf_of_normalizes h.K_normal (normalizer_pCoreOf X))

theorem CampbellHyp.commutator_W_le (h : CampbellHyp X K R P) :
    ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ≤ omegaCenter (K ⊓ pCoreOf 2 X) := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have hn := h.normalizer_W (h.K_le hk)
  have h1 : k * w * k⁻¹ ∈ omegaCenter (K ⊓ pCoreOf 2 X) :=
    (Subgroup.mem_normalizer_iff.1 hn w).1 hw
  have h2 : ⁅w, k⁆ = w * (k * w * k⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact (omegaCenter (K ⊓ pCoreOf 2 X)).mul_mem hw
    ((omegaCenter (K ⊓ pCoreOf 2 X)).inv_mem h1)

theorem wFacts_Q_le_inf (h : CampbellHyp X K R P) :
    CFSG.Quasithin.c134Q X K ≤ K ⊓ pCoreOf 2 X := by
  unfold CFSG.Quasithin.c134Q
  rw [Subgroup.commutator_le]
  intro o ho k hk
  have hoX : o ∈ X := pCoreOf_le_self X ho
  have hkX : k ∈ X := h.K_le hk
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : o * k * o⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (h.K_normal hoX) k).1 hk
    rw [commutatorElement_def]
    exact K.mul_mem h1 (K.inv_mem hk)
  · have h1 : k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_pCoreOf X hkX) o⁻¹).1
        ((pCoreOf 2 X).inv_mem ho)
    have h2 : ⁅o, k⁆ = o * (k * o⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact (pCoreOf 2 X).mul_mem ho h1

theorem CampbellHyp.commutator_W_le_center_Q (h : CampbellHyp X K R P) :
    ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ≤
      CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K) := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have hwQ : w ∈ pCoreOf 2 X := (Subgroup.mem_inf.1 (omegaCenter_le _ hw)).2
  have hQ : ⁅w, k⁆ ∈ CFSG.Quasithin.c134Q X K := Subgroup.commutator_mem_commutator hwQ hk
  have hW : ⁅w, k⁆ ∈ omegaCenter (K ⊓ pCoreOf 2 X) :=
    h.commutator_W_le (Subgroup.commutator_mem_commutator hw hk)
  have hcent : ⁅w, k⁆ ∈ Subgroup.centralizer (CFSG.Quasithin.c134Q X K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact ((mem_omegaCenter.1 hW).2.1 q (wFacts_Q_le_inf h hq)).symm
  unfold CFSG.Quasithin.centerOf
  exact Subgroup.mem_inf.2 ⟨hQ, hcent⟩

theorem CampbellHyp.normalizer_B0 (h : CampbellHyp X K R P) :
    X ≤ normalizer ((⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ : Subgroup A) : Set A) :=
  normalizer_commutator_of_normalizes h.normalizer_W h.K_normal
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem commW_mem_pCore (h : CampbellHyp X K R P) {z : A} (hz : z ∈ omegaCenter R) :
    z ∈ pCoreOf 2 X ∧ ∀ q ∈ pCoreOf 2 X, q * z = z * q := by
  obtain ⟨hzR, hzC, -⟩ := mem_omegaCenter.1 hz
  have hcomm : ∀ q ∈ pCoreOf 2 X, q * z = z * q := fun q hq =>
    (hzC q (h.pCore_X_le_R hq)).symm
  exact ⟨h.charTwo ⟨h.R_le hzR, Subgroup.mem_centralizer_iff.2 hcomm⟩, hcomm⟩

theorem commW_conj_mem (h : CampbellHyp X K R P) {z k : A} (hz : z ∈ omegaCenter R)
    (hk : k ∈ X) :
    k * z * k⁻¹ ∈ pCoreOf 2 X ∧ ∀ q ∈ pCoreOf 2 X, q * (k * z * k⁻¹) = (k * z * k⁻¹) * q := by
  obtain ⟨hzQ, hzC⟩ := commW_mem_pCore h hz
  have hn := normalizer_pCoreOf X hk
  refine ⟨(Subgroup.mem_normalizer_iff.1 hn z).1 hzQ, fun q hq => ?_⟩
  have hq' : k⁻¹ * q * k ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff''.1 hn q).1 hq
  have hcomm := hzC _ hq'
  calc q * (k * z * k⁻¹) = k * ((k⁻¹ * q * k) * z) * k⁻¹ := by group
    _ = k * (z * (k⁻¹ * q * k)) * k⁻¹ := by rw [hcomm]
    _ = (k * z * k⁻¹) * q := by group

theorem commW_c_mem_W (h : CampbellHyp X K R P) {z k : A} (hz : z ∈ omegaCenter R)
    (hk : k ∈ K) : z⁻¹ * (k * z * k⁻¹) ∈ omegaCenter (K ⊓ pCoreOf 2 X) := by
  have hzR : z ∈ R := omegaCenter_le R hz
  have hz2 : z ^ 2 = 1 := (mem_omegaCenter.1 hz).2.2
  have hzX : z ∈ X := h.R_le hzR
  obtain ⟨hzQ, hzC⟩ := commW_mem_pCore h hz
  obtain ⟨hyQ, hyC⟩ := commW_conj_mem h hz (h.K_le hk)
  have hcK : z⁻¹ * (k * z * k⁻¹) ∈ K := by
    have h1 : z⁻¹ * k * z ∈ K := (Subgroup.mem_normalizer_iff''.1 (h.K_normal hzX) k).1 hk
    have h2 : z⁻¹ * (k * z * k⁻¹) = (z⁻¹ * k * z) * k⁻¹ := by group
    rw [h2]
    exact K.mul_mem h1 (K.inv_mem hk)
  have hcQ : z⁻¹ * (k * z * k⁻¹) ∈ pCoreOf 2 X :=
    (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hzQ) hyQ
  have hcC : ∀ q ∈ pCoreOf 2 X, q * (z⁻¹ * (k * z * k⁻¹)) = (z⁻¹ * (k * z * k⁻¹)) * q := by
    intro q hq
    exact ((Commute.inv_right (hzC q hq : Commute q z)).mul_right
      (hyC q hq : Commute q (k * z * k⁻¹))).eq
  have hc2 : (z⁻¹ * (k * z * k⁻¹)) ^ 2 = 1 := by
    have hcomm : Commute z⁻¹ (k * z * k⁻¹) :=
      Commute.inv_left (hyC z hzQ : Commute z (k * z * k⁻¹))
    rw [hcomm.mul_pow, inv_pow, hz2, conj_pow, hz2]
    group
  exact mem_omegaCenter.2 ⟨⟨hcK, hcQ⟩, fun x hx => (hcC x hx.2).symm, hc2⟩

theorem CampbellHyp.commutator_W_ne_bot (h : CampbellHyp X K R P) :
    ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆ ≠ ⊥ := by
  intro hbot
  have hKW : ∀ w ∈ omegaCenter (K ⊓ pCoreOf 2 X), ∀ k ∈ K, w * k = k * w := by
    intro w hw k hk
    have hmem := Subgroup.commutator_mem_commutator hw hk
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hKgen := closure_odd_of_perfect h.K_perfect
  have hcent : ∀ z ∈ omegaCenter R, ∀ k ∈ K, k * z * k⁻¹ = z := by
    intro z hz
    refine centralizes_of_odd_generation hKgen (fun k hk _ => ?_)
    have hcW := commW_c_mem_W h hz hk
    obtain ⟨-, hzC⟩ := commW_mem_pCore h hz
    obtain ⟨hcX, -, hc2⟩ := mem_omegaCenter.1 hcW
    refine ⟨hc2, ?_, ?_⟩
    · rw [mul_inv_eq_iff_eq_mul]
      exact (hKW _ hcW k hk).symm
    · exact (hzC _ hcX.2).symm
  have hKP : K ≤ P := by
    intro k hk
    refine h.cent_le ⟨h.K_le hk, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    have := hcent z hz k hk
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hQP : pCoreOf 2 X ≤ P := (h.pCore_X_le_R).trans h.R_le_P
  have hXP : X ≤ P := h.X_eq.le.trans (sup_le hKP hQP)
  exact not_le_of_gt h.P_lt_X hXP
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
