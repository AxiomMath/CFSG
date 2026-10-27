module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Tau
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMA6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}

theorem sec8t84a1_autL (h6 : Asc82Tab6M) (hctx : Sec8Ctx G t L S z g B) :
    Nat.card ↥(autIn L B) = 360 ∧
      ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 →
        ∃ n ∈ L ⊓ normalizer (B : Set G), n * b * n⁻¹ = b' := by
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  have hBL : B ≤ L := fun b hb => (hctx.B_le hb).1
  obtain ⟨P0, hP0, hBP0⟩ := sec68_exists_sylow_ge (H := L)
    (CFSG.Open.IsElemAbelian.isPGroup hctx.B_e16.1) hBL
  obtain ⟨haut, htrans, -⟩ := h6.aut_B G L hLM P0 hP0 B hBP0 hctx.B_e16
  exact ⟨sec9m_card_A6 haut, htrans⟩

theorem sec8t84a1_range_bot_or_top (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B)
    (τ : ↥(Nsub8 t B ⊓ centralizer (B : Set G)) →* ↥B)
    (hτ : ∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) :
    τ.range = ⊥ ∨ τ.range = ⊤ := by
  by_cases hbot : τ.range = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    have hnt : ∃ v ∈ τ.range, v ≠ 1 := by
      rw [Subgroup.eq_bot_iff_forall] at hbot
      push Not at hbot
      exact hbot
    obtain ⟨v, hv, hv1⟩ := hnt
    obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.mp hv
    rw [Subgroup.eq_top_iff']
    intro b
    by_cases hb : b = 1
    · rw [hb]; exact τ.range.one_mem
    · obtain ⟨n, hn, hnconj⟩ := (sec8t84a1_autL h6 hctx).2 (v : G) v.2
        (fun h => hv1 (Subtype.ext h)) (b : G) b.2 (fun h => hb (Subtype.ext h))
      have hn' := sec8t84a1_L_norm_le hctx hn
      have hnN : n ∈ Nsub8 t B := hn'.1
      have hnt' : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp hn'.2
      have hx'N : n * (x₀ : G) * n⁻¹ ∈ Nsub8 t B ⊓ centralizer (B : Set G) :=
        sec8t84a1_C_normal h8B hctx n hnN x₀ x₀.2
      let x' : ↥(Nsub8 t B ⊓ centralizer (B : Set G)) :=
        ⟨n * (x₀ : G) * n⁻¹, hx'N⟩
      have hτx' : τ x' = b := by
        apply Subtype.ext
        calc ((τ x' : ↥B) : G) = (x' : G) * t * (x' : G)⁻¹ * t⁻¹ := hτ x'
          _ = n * ((x₀ : G) * t * (x₀ : G)⁻¹ * t⁻¹) * n⁻¹ := sec8t84a1_tau_conj hnt'
          _ = n * ((v : ↥B) : G) * n⁻¹ := by rw [← hτ x₀, hx₀]
          _ = (b : G) := hnconj
      exact MonoidHom.mem_range.mpr ⟨x', hτx'⟩

end CFSG.OddStandard.SmallF3.Omega
