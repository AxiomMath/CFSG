module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Sort
public import CFSG.Certificates.Kernel.LocalQTM24Snd.Act

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.KC.LQT.P

variable {n : ℕ}

theorem rounds_code_iff (hn : n ≤ 32) (L : List (Perm (Fin n))) (r : ℕ) :
    (∀ σ : Perm (Fin n), P.code σ ∈
        (rounds (fun x => (L.map P.code).map (mul n x)) r [one n] [one n]).1 ↔
      σ ∈ ball (fun σ => L.map (σ * ·)) {1} r) ∧
    ∀ c ∈ (rounds (fun x => (L.map P.code).map (mul n x)) r [one n] [one n]).1,
      ∃ σ : Perm (Fin n), P.code σ = c := by
  have hinv := bfsC_inv n (L.map P.code) r
  have hball : P.code '' ball (fun σ => L.map (σ * ·)) {1} r =
      ball (fun x => (L.map P.code).map (mul n x)) {one n} r := by
    refine ball_image P.code (fun σ => ?_) ?_ r
    · simp only [List.map_map]
      exact List.map_congr_left fun g _ => (P.code_mul hn σ g).symm
    · rw [Set.image_singleton, P.code_one]
  refine ⟨fun σ => ⟨fun h => ?_, fun h => ?_⟩, fun c hc => ?_⟩
  · have h' := hinv.sub _ h
    rw [← hball] at h'
    obtain ⟨τ, hτ, e⟩ := h'
    rwa [← P.code_inj hn e]
  · exact hinv.sup _ (hball ▸ ⟨σ, h, rfl⟩)
  · have h' := hinv.sub c hc
    rw [← hball] at h'
    obtain ⟨τ, -, e⟩ := h'
    exact ⟨τ, e⟩

theorem rounds_closed (hn : n ≤ 32) (L : List (Perm (Fin n))) (r : ℕ) (p : ℕ → Bool)
    (hF : (rounds (fun x => (L.map P.code).map (mul n x)) r [one n] [one n]).2 = [])
    (hp : ∀ c ∈ (rounds (fun x => (L.map P.code).map (mul n x)) r [one n] [one n]).1,
      p c = true) :
    ∀ σ ∈ Subgroup.closure {t | t ∈ L}, p (P.code σ) = true := by
  have hinv := bfsC_inv n (L.map P.code) r
  set S := (rounds (fun x => (L.map P.code).map (mul n x)) r [one n] [one n]).1 with hS
  have hcl := hinv.closed (F := {x | x ∈ (rounds (fun x => (L.map P.code).map (mul n x)) r
    [one n] [one n]).2}) (fun x hx => by rw [hF] at hx; exact absurd hx List.not_mem_nil)
  have h1 : (1 : Perm (Fin n)) ∈ {σ : Perm (Fin n) | P.code σ ∈ S} := by
    change P.code (1 : Perm (Fin n)) ∈ S
    rw [← P.code_one]
    exact hinv.sup _ (ball_mono (Nat.zero_le r) (mem_ball_zero (Set.mem_singleton _)))
  have hP : ∀ x ∈ {σ : Perm (Fin n) | P.code σ ∈ S}, ∀ t ∈ L,
      x * t ∈ {σ : Perm (Fin n) | P.code σ ∈ S} := by
    intro x hx t ht
    change P.code (x * t) ∈ S
    rw [← P.code_mul hn]
    exact hcl _ hx _ (List.mem_map.2 ⟨P.code t, List.mem_map_of_mem ht, rfl⟩)
  intro σ hσ
  exact hp _ (closure_le_of_closed L _ h1 hP σ hσ)

end CFSG.KC.LQT.M24Snd

end
