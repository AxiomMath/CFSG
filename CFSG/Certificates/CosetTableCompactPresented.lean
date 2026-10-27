module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.CosetTableCompact

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

@[expose] def cyclicCheckC {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List ℕ)
    (k cap n : ℕ) : Bool :=
  u.all (fun c => decide (c < 2 * m)) && (codes ws).contains (List.replicate k u).flatten &&
    decide ((cap + 2) * (2 * m + 1) ≤ 2 ^ 32) &&
    checkC (mkParams (2 * m) (invArr m) (codes ws) [u]) cap n

theorem cyclicCheck_of_cyclicCheckC {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List ℕ)
    {k cap n : ℕ} (h : cyclicCheckC ws u k cap n = true) : cyclicCheck ws u k cap n = true := by
  unfold cyclicCheckC at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨hu, hk⟩, hcap⟩, hc⟩ := h
  have hc' : check (mkParams (2 * m) (invArr m) (codes ws) [u]) cap n = true := by
    rw [← checkC_eq n hcap]
    exact hc
  simp only [cyclicCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem]
  exact ⟨⟨hu, hk⟩, hc'⟩

theorem card_le_of_cyclicCheckC {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List ℕ)
    {k cap n : ℕ} (hk0 : 0 < k) (h : cyclicCheckC ws u k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * k :=
  card_le_of_cyclicCheck ws u hk0 (cyclicCheck_of_cyclicCheckC ws u h)

end CFSG.CosetTable
