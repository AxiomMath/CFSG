module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.HashR

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ}

theorem bfsSet_enc_iff (L : List (Perm (Fin n))) (r : ℕ) :
    (∀ σ : Perm (Fin n), RN.enc σ ∈ bfsSet (L.map RN.enc) r ↔
      σ ∈ ball (fun σ => L.map (σ * ·)) {1} r) ∧
    ∀ x ∈ bfsSet (L.map RN.enc) r, ∃ σ : Perm (Fin n), RN.enc σ = x := by
  have hball : RN.enc '' ball (fun σ => L.map (σ * ·)) {1} r =
      ball (fun x => (L.map RN.enc).map (x * ·)) {1} r := by
    refine ball_image RN.enc (fun σ => ?_) ?_ r
    · simp only [List.map_map]
      exact List.map_congr_left fun g _ => RN.enc_mul σ g
    · rw [Set.image_singleton, RN.enc_one]
  refine ⟨fun σ => ?_, fun x hx => ?_⟩
  · rw [mem_bfsSet_iff, ← hball]
    exact ⟨fun ⟨τ, hτ, e⟩ => by rwa [← RN.enc_inj e], fun h => ⟨σ, h, rfl⟩⟩
  · rw [mem_bfsSet_iff, ← hball] at hx
    obtain ⟨τ, -, e⟩ := hx
    exact ⟨τ, e⟩

end CFSG.KC.LQT.M24Snd

end
