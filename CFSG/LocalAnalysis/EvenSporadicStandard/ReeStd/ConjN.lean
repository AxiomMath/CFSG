module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.StageN
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem conj_N_eq (hS : 2 ∣ S.index) {x : G} (hx : x ∈ S) (hxΛ : x ∉ Λ) :
    ∃ n ∈ normalizer (S : Set G), x = n * H.z * n⁻¹ := by
  obtain ⟨n₀, hn₀, hmove⟩ := h.exists_move hS
  obtain ⟨hx₀S, hx₀Λ⟩ := h.N_conj_z_mem hn₀
  obtain ⟨σ, hσ, hσN⟩ := h.exists_sigma
  obtain ⟨φ, hφ7, hφfree, hφpow⟩ := h.exists_sigma_aut hσ hσN
  have hz2 : ∀ i : ℕ, σ ^ i * H.z = H.z * σ ^ i := hσ.pow_comm_z
  have hl₀Λ : H.z * (n₀ * H.z * n₀⁻¹) ∈ Λ := h.z_mul_mem_Λ hx₀S hx₀Λ
  have hl₀sq : ¬ ∃ m : Λ, (⟨_, hl₀Λ⟩ : Λ) = m * m := by
    rintro ⟨m, hm⟩
    obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl (one_mem Λ) m.2
    apply hmove s hs
    have : H.z * (n₀ * H.z * n₀⁻¹) = m.1 * m.1 := congrArg Subtype.val hm
    calc n₀ * H.z * n₀⁻¹ = H.z * (H.z * (n₀ * H.z * n₀⁻¹)) := by
          rw [← mul_assoc, H.z_mul_self, one_mul]
      _ = H.z * (m.1 * m.1) := by rw [this]
      _ = s * H.z * s⁻¹ := by simpa using hseq.symm
  have key : ∀ l ∈ Λ, ∃ n ∈ normalizer (S : Set G), H.z * l = n * H.z * n⁻¹ := by
    intro l hl
    rcases J1Std.cosets_exhaust (fun a b => Subtype.ext (h.comm a.2 b.2)) φ hφ7 hφfree
      h.card_sq_eq_one hl₀sq ⟨l, hl⟩ with ⟨m, hm⟩ | ⟨i, m, hm⟩
    · obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl (one_mem Λ) m.2
      refine ⟨s, le_normalizer hs, ?_⟩
      have : l = m.1 * m.1 := congrArg Subtype.val hm
      rw [this]
      simpa using hseq.symm
    · set L' : Λ := (φ ^ i) ⟨_, hl₀Λ⟩ with hL'
      have hL'val : (L' : G) = σ ^ i * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹ := hφpow i _
      have hlval : l = (L' : G) * (m.1 * m.1) := congrArg Subtype.val hm
      obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl L'.2 m.2
      have hzL : H.z * (L' : G) = (σ ^ i * n₀) * H.z * (σ ^ i * n₀)⁻¹ := by
        rw [hL'val]
        have hc := hz2 i
        calc H.z * (σ ^ i * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹)
            = (H.z * σ ^ i) * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹ := by group
          _ = (σ ^ i * H.z) * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹ := by rw [hc]
          _ = σ ^ i * (H.z * H.z) * (n₀ * H.z * n₀⁻¹) * (σ ^ i)⁻¹ := by group
          _ = (σ ^ i * n₀) * H.z * (σ ^ i * n₀)⁻¹ := by rw [H.z_mul_self]; group
      refine ⟨s * (σ ^ i * n₀), mul_mem (le_normalizer hs) (mul_mem (pow_mem hσN i) hn₀), ?_⟩
      calc H.z * l = H.z * (L' : G) * (m.1 * m.1) := by rw [hlval, mul_assoc]
        _ = s * (H.z * (L' : G)) * s⁻¹ := hseq.symm
        _ = s * ((σ ^ i * n₀) * H.z * (σ ^ i * n₀)⁻¹) * s⁻¹ := by rw [hzL]
        _ = s * (σ ^ i * n₀) * H.z * (s * (σ ^ i * n₀))⁻¹ := by group
  obtain ⟨n, hn, hnx⟩ := key (H.z * x) (h.z_mul_mem_Λ hx hxΛ)
  exact ⟨n, hn, by rw [← hnx, ← mul_assoc, H.z_mul_self, one_mul]⟩

end Stage

end CFSG.EvenSporadicStandard.ReeStd
