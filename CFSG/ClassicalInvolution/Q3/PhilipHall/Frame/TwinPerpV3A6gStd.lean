module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gAbel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eShape
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1ParWr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_mem_aeBar8 vq_compl vq_empty vq_mul_self zBar_eq_vq)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (conjSub_ofPerm_memBar conjSub_ofPerm_ae6AE8 mkQ_ofPerm_inv card_aeBarOver natCard_conjSub
    mem_aeSubOver_of_mkQ_mem e29Sub_le)

@[expose] def α₀ : Finset (Fin 8) := {0, 1, 2, 3}

@[expose] def β₀ : Finset (Fin 8) := {0, 1, 4, 5}

@[expose] def γ₀ : Finset (Fin 8) := {2, 3, 4, 5}

theorem card_α₀ : α₀.card = 4 := by decide
theorem card_β₀ : β₀.card = 4 := by decide
theorem vq_α₀_mul_β₀ : vq α₀ * vq β₀ = vq γ₀ := by
  rw [vq_mul]
  congr 1

@[expose] def six : List (Finset (Fin 8)) := [α₀, α₀ᶜ, β₀, β₀ᶜ, γ₀, γ₀ᶜ]

theorem six_planes : ∀ δ ∈ six, δ ∈ affinePlanes := by decide +kernel

theorem mem_six_of_vq {δ : Finset (Fin 8)}
    (hz : vq δ = vq α₀ ∨ vq δ = vq β₀ ∨ vq δ = vq α₀ * vq β₀) : δ ∈ six := by
  rw [vq_α₀_mul_β₀] at hz
  unfold six
  have key : ∀ S : Finset (Fin 8), vq δ = vq S → δ = S ∨ δ = Sᶜ := by
    intro S h
    rcases vq_eq_iff.mp h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, compl_compl])
  rcases hz with hz | hz | hz
  · rcases key _ hz with rfl | rfl <;> simp
  · rcases key _ hz with rfl | rfl <;> simp
  · rcases key _ hz with rfl | rfl <;> simp

@[expose] def sw : Equiv.Perm (Fin 8) := Equiv.swap 6 7

@[expose] noncomputable def sQ : AEQ 8 := mkQ 8 (ofPerm sw)

@[expose] noncomputable def X3 : Subgroup (AEQ 8) := conjSub sQ e29Sub

theorem sw_inv : sw⁻¹ = sw := Equiv.swap_inv _ _

theorem sQ_inv : sQ⁻¹ = sQ := by
  unfold sQ
  rw [mkQ_ofPerm_inv, sw_inv]

theorem permQ_sQ : permQ 8 sQ = sw := rfl

theorem sw_map_six : ∀ δ ∈ six, δ.map sw.toEmbedding = δ := by decide +kernel

theorem sw_map_α₀ : α₀.map sw.toEmbedding = α₀ := sw_map_six _ (by simp [six])
theorem sw_map_β₀ : β₀.map sw.toEmbedding = β₀ := sw_map_six _ (by simp [six])
theorem sw_comm_σ₀ : sw * σ₀ * sw⁻¹ = σ₀ := by
  rw [sw_inv]
  exact Equiv.ext (by decide +kernel)

theorem sQ_conj_vq (S : Finset (Fin 8)) : sQ * vq S * sQ⁻¹ = vq (S.map sw.toEmbedding) := by
  rw [conj_vq, permQ_sQ]

theorem sQ_conj_vq_α₀ : sQ * vq α₀ * sQ⁻¹ = vq α₀ := by rw [sQ_conj_vq, sw_map_α₀]
theorem sQ_conj_vq_β₀ : sQ * vq β₀ * sQ⁻¹ = vq β₀ := by rw [sQ_conj_vq, sw_map_β₀]

theorem conjSub_sQ_aeBar8 : conjSub sQ aeBar8 = aeBar8 := conjSub_ofPerm_ae6AE8 sw

theorem e29Sub_le_aeBar8 : e29Sub ≤ aeBar8 := e29Sub_le

theorem card_agl32 : Nat.card agl32 = 1344 := by
  have hbij : Function.Bijective (fun p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ×
      (Fin 3 → ZMod 2) => (⟨aperm p.1 p.2, aperm_mem_agl32 p.1 p.2⟩ : agl32)) := by
    constructor
    · rintro ⟨A, b⟩ ⟨A', b'⟩ hAb
      have hv : aperm A b = aperm A' b' := congrArg Subtype.val hAb
      obtain ⟨h1, h2⟩ := aperm_inj hv
      rw [h1, h2]
    · rintro ⟨σ, hσ⟩
      obtain ⟨A, b, hAb⟩ := exists_aperm_eq hσ
      exact ⟨(A, b), Subtype.ext hAb⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, card_sl3Two, Nat.card_fun]
  simp

theorem card_e29Sub : Nat.card e29Sub = 86016 := by
  have h := card_aeBarOver agl32 (fun σ hσ => Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign σ hσ))
  unfold e29Sub
  rw [h, card_agl32]

theorem mem_agl32_of_dec {σ : Equiv.Perm (Fin 8)}
    (h : ∀ s ∈ affinePlanes, s.map σ.toEmbedding ∈ affinePlanes ∧ s.map σ⁻¹.toEmbedding ∈ affinePlanes) :
    σ ∈ agl32 := h

theorem e29Sub_ne_X3 : e29Sub ≠ X3 := by
  intro h
  set ρ : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * Equiv.swap 5 6 with hρ
  have hρa : ρ ∈ agl32 := mem_agl32_of_dec (by rw [hρ]; decide +kernel)
  have hρe : ρ ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign ρ hρa)
  have hg : mkQ 8 (ofPerm ρ) ∈ e29Sub := mkQ_ofPerm_mem_aeBarOver hρa hρe
  rw [h] at hg
  have h1 : sQ⁻¹ * mkQ 8 (ofPerm ρ) * sQ ∈ e29Sub := mem_conjSub_iff.mp hg
  have h2 : sQ⁻¹ * mkQ 8 (ofPerm ρ) * sQ = mkQ 8 (ofPerm (sw⁻¹ * ρ * sw)) := by
    rw [sQ_inv, sw_inv]
    unfold sQ
    rw [← map_mul, ← map_mul, ofPerm_mul, ofPerm_mul]
  rw [h2] at h1
  have h3 := mem_aeSubOver_of_mkQ_mem h1
  have h4 : sw⁻¹ * ρ * sw ∈ agl32 := h3.2
  rw [sw_inv] at h4
  have h5 := (h4 {0, 2, 4, 6} (by decide)).1
  revert h5
  rw [hρ]
  unfold sw
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
