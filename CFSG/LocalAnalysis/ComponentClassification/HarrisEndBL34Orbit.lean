module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Model
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.not_conj_tbeta (hKF : AutPSL2FusionInput) (hs : Setting46e t L p f S w z V i j)
    (htz : ∀ c : X, c * t * c⁻¹ ≠ t * z)
    (hz' : ∀ c : X, c * t * c⁻¹ ≠ z)
    (hβz' : ∀ c : X, c * t * c⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j * z) (c : X) :
    c * t * c⁻¹ ≠ t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  intro hc
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have htV : t ∈ V := hs.le_V (hs.standing.t_mem hs.sylow)
  set O := {y : X | ∃ v ∈ V, v * t * v⁻¹ = y} with hO
  have hOV : O.ncard ∣ Nat.card V := by
    rw [hO, ncard_conj_orbit V htV]
    exact Subgroup.relIndex_dvd_card _ _
  have hX : ∀ g : X, g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} → g * t * g⁻¹ ∈ O := by
    intro g hg
    have hV' : IsSylowOf 2 V (⊤ ⊓ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :
        Set X)) := by
      rw [top_inf_eq]
      exact hs.sylow_V
    obtain ⟨v, hv, hvt⟩ := hs.setup.exists_conj_W hKF le_top hV' (mem_top g) hg
    exact ⟨v, hv, hvt⟩
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hβX : β ∈ closure {t, w ^ (orderOf w / 2), z} := beta_mem_X i j
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X hβX
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzM : z ∈ centralizer ({β} : Set X) := K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβz : β * z = z * β := (mem_centralizer_singleton_iff.mp hzM).symm
  have ht1 : t ≠ 1 := by
    intro h
    have := hs.standing.config.orderOf_eq
    rw [h, orderOf_one] at this
    norm_num at this
  have hsub : O ⊆ {t, t * β, t * (β * z)} := by
    rintro y ⟨v, hv, rfl⟩
    have hyX : v * t * v⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
      (mem_normalizer_iff.mp (hs.setup.normalizer_T_le_normalizer_X (hs.sylow_V.le hv)) t).mp htX
    rcases hs.setup.mem_closure_beta_z_or hβX hs.beta.not_mem hyX with h | h
    · exfalso
      rcases mem_closure_pair hβ2 hz2 hβz h with h | h | h | h
      · apply ht1
        calc t = v⁻¹ * (v * t * v⁻¹) * v := by group
          _ = 1 := by rw [h]; group
      · exact hs.beta.not_conj v h
      · exact hz' v h
      · exact hβz' v h
    · rcases mem_closure_pair hβ2 hz2 hβz h with h | h | h | h
      · left
        calc v * t * v⁻¹ = t * (t⁻¹ * (v * t * v⁻¹)) := by group
          _ = t := by rw [h, mul_one]
      · right; left
        calc v * t * v⁻¹ = t * (t⁻¹ * (v * t * v⁻¹)) := by group
          _ = t * β := by rw [h]
      · exfalso
        apply htz v
        calc v * t * v⁻¹ = t * (t⁻¹ * (v * t * v⁻¹)) := by group
          _ = t * z := by rw [h]
      · right; right
        calc v * t * v⁻¹ = t * (t⁻¹ * (v * t * v⁻¹)) := by group
          _ = t * (β * z) := by rw [h]
  have hsup : ({t, t * β, t * (β * z)} : Set X) ⊆ O := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, one_mem _, by group⟩
    · rw [← hc]
      exact hX c (by rw [hc]; exact mul_mem htX hβX)
    · obtain ⟨v, hv, -, -, hvt⟩ := hs.beta.exists_mem
      rcases hvt with h | h
      · exact absurd h (htz v)
      · exact ⟨v, (mem_inf.mp hv).1, by rw [h, mul_assoc]⟩
  have heq : O = {t, t * β, t * (β * z)} := Set.Subset.antisymm hsub hsup
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    norm_num at this
  have hβ1 : β ≠ 1 := hs.beta.ne_one
  have hβz1 : β * z ≠ 1 := by
    intro h
    apply hs.beta.not_mem
    have hβeq : w ^ (orderOf w / 2) * t ^ i * z ^ j = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hβeq]
    exact inv_mem (mem_sup_right hs.lemma45.z_mem.1)
  have h3 : O.ncard = 3 := by
    rw [heq, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · intro h
      apply hz1
      have := mul_left_cancel h
      calc z = β⁻¹ * (β * z) := by group
        _ = 1 := by rw [← this]; group
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨fun h => hβ1 ?_, fun h => hβz1 ?_⟩
      · calc β = t⁻¹ * (t * β) := by group
          _ = 1 := by rw [← h]; group
      · calc β * z = t⁻¹ * (t * (β * z)) := by group
          _ = 1 := by rw [← h]; group
  obtain ⟨k, hk⟩ := hs.sylow_V.isPGroup.exists_card_eq
  rw [h3, hk] at hOV
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hOV)
  norm_num at this

end CFSG.ComponentClassification.HarrisLit
