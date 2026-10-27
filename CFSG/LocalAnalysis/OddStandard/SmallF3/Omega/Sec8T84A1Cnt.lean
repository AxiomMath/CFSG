module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Orb
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNFr
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMAut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMGrp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}

theorem sec8t84a1_range_ne_bot (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B)
    (τ : ↥(Nsub8 t B ⊓ centralizer (B : Set G)) →* ↥B)
    (hτ : ∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) :
    τ.range ≠ ⊥ := by
  intro hbot
  obtain ⟨h2tr, -⟩ := h8B G t L S z g B hctx
  have hB16 : Nat.card B = 16 := by rw [hctx.B_e16.2]; norm_num
  have htX : t ∈ cosetSet t B := ⟨1, B.one_mem, by simp⟩
  have hX16 : (cosetSet t B).ncard = 16 := sec9n_ncard_coset hB16
  let N : Subgroup G := Nsub8 t B
  let Nt : Subgroup G := N ⊓ centralizer ({t} : Set G)
  have hcardN : Nat.card ↥N = 16 * Nat.card ↥Nt := by
    have h := sec9f_card_stab h2tr htX (by rw [hX16]; norm_num)
    rw [hX16] at h
    simpa only [N, Nt] using h
  have hNnorm : N ≤ normalizer (B : Set G) := sec8t84a1_N_le_normalizer h8B hctx
  let ρ : ↥N →* MulAut ↥B := B.normalizerMonoidHom.comp (Subgroup.inclusion hNnorm)
  let Nt' : Subgroup ↥N := Nt.subgroupOf N
  have hker : ρ.ker ≤ Nt' := by
    intro x hx
    have hx1 : B.normalizerMonoidHom (Subgroup.inclusion hNnorm x) = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxC : (x : G) ∈ centralizer (B : Set G) := by
      have h2 : Subgroup.inclusion hNnorm x ∈ B.normalizerMonoidHom.ker :=
        MonoidHom.mem_ker.mpr hx1
      rw [Subgroup.normalizerMonoidHom_ker] at h2
      have h3 : ((Subgroup.inclusion hNnorm x : ↥(normalizer (B : Set G))) : G)
          ∈ centralizer (B : Set G) := Subgroup.mem_subgroupOf.mp h2
      rwa [Subgroup.coe_inclusion] at h3
    have hxCmem : (x : G) ∈ N ⊓ centralizer (B : Set G) := ⟨x.2, hxC⟩
    have hτ1 : τ ⟨(x : G), hxCmem⟩ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hbot]
      exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hxCmem⟩, rfl⟩
    have hτval : ((τ ⟨(x : G), hxCmem⟩ : ↥B) : G) = 1 := by
      rw [hτ1, Subgroup.coe_one]
    have hcomm : (x : G) * t = t * (x : G) := by
      have h := hτ ⟨(x : G), hxCmem⟩
      rw [hτval] at h
      have h1 : (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1 := h.symm
      calc (x : G) * t = ((x : G) * t * (x : G)⁻¹ * t⁻¹) * t * (x : G) := by group
        _ = 1 * t * (x : G) := by rw [h1]
        _ = t * (x : G) := by group
    have hxcent : (x : G) ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxcent⟩
  let Ht : Subgroup (MulAut ↥B) := autIn L B
  have hHt : Ht ≤ Nt'.map ρ := by
    intro φ hφ
    obtain ⟨x, hxL, hxnorm, hxφ⟩ := sec9m_mem_autIn.mp hφ
    have hxNt : x ∈ Nt := sec8t84a1_L_norm_le hctx ⟨hxL, hxnorm⟩
    have hxN : x ∈ N := hxNt.1
    have hxcent : x ∈ centralizer ({t} : Set G) := hxNt.2
    have hxNt' : (⟨x, hxN⟩ : ↥N) ∈ Nt' :=
      Subgroup.mem_subgroupOf.mpr ⟨hxN, hxcent⟩
    have hρx : ρ ⟨x, hxN⟩ = φ := by
      refine MulEquiv.ext (fun b => Subtype.ext ?_)
      have h1 : ((ρ ⟨x, hxN⟩) b : G) = x * (b : G) * x⁻¹ := by
        change ((B.normalizerMonoidHom (Subgroup.inclusion hNnorm ⟨x, hxN⟩)) b : G) = _
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      rw [h1, hxφ b]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hxNt', hρx⟩
  have hHtcard : Nat.card ↥Ht = 360 := (sec8t84a1_autL h6 hctx).1
  have h360 : 360 ∣ Nat.card ↥Ht := by rw [hHtcard]
  have hidx : Nt'.index = 16 := by
    have h1 : Nat.card ↥Nt' * Nt'.index = Nat.card ↥N :=
      Subgroup.card_mul_index (H := Nt')
    have h2 : Nat.card ↥Nt' = Nat.card ↥Nt :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Nt ≤ N)).toEquiv
    rw [h2, hcardN] at h1
    rw [mul_comm (16 : ℕ) (Nat.card ↥Nt)] at h1
    haveI : Nonempty ↥Nt := ⟨1⟩
    exact Nat.mul_left_cancel (Nat.card_pos) h1
  have hΓ : Nat.card (MulAut ↥B) = 20160 := sec9m_card_mulAut hctx.B_e16
  exact sec9f_count_contra ρ Nt' hker hidx Ht hHt h360 hΓ

theorem sec8t84a1_range_top (h8B : Asc82Lemma8B) (h6 : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B)
    (τ : ↥(Nsub8 t B ⊓ centralizer (B : Set G)) →* ↥B)
    (hτ : ∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) :
    τ.range = ⊤ :=
  (sec8t84a1_range_bot_or_top h8B h6 hctx τ hτ).resolve_left
    (sec8t84a1_range_ne_bot h8B h6 hctx τ hτ)

end CFSG.OddStandard.SmallF3.Omega
