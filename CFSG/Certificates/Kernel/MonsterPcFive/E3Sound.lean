module

public import CFSG.Certificates.Kernel.MonsterPcFive.Card
public import Certificates.Data.Kernel.MonsterPcFive.E3

public section

namespace CFSG.KC.MonPcFive

variable {G : Type*} [Group G] {u2 u1 : G} {b : Fin 6 → G} {x : G}

theorem V9.beq_eq {v w : V9} (h : v.beq w = true) : v = w := by
  unfold V9.beq at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  cases v
  cases w
  simp only at h0 h1 h2
  subst h0 h1
  rw [RV.beq_eq h2]

theorem tripV_sound [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) (hs : sigOK () = true)
    (hx : x ≠ 1) {t a c : V9} (ht : t.red) (ha : a.red) (hc : c.red) (h : tripV t a c = true) :
    let T := psi u2 u1 b x t
    let A := psi u2 u1 b x a
    let B := psi u2 u1 b x c
    T * A = A * T ∧ T * B = B * T ∧ A * B = B * A ∧ T ^ 5 = 1 ∧ A ^ 5 = 1 ∧ B ^ 5 = 1 ∧
      ∀ i < 5, ∀ j < 5, ∀ l < 5, T ^ i * A ^ j * B ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0 := by
  intro T A B
  unfold tripV at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hta, htb⟩, hab⟩, ot⟩, oa⟩, ob⟩, hind⟩ := h
  have comm : ∀ {v w : V9}, v.red → w.red → (mulV v w).beq (mulV w v) = true →
      psi u2 u1 b x v * psi u2 u1 b x w = psi u2 u1 b x w * psi u2 u1 b x v := by
    intro v w hv hw e
    rw [H.psi_mul C hv hw, H.psi_mul C hw hv, V9.beq_eq e]
  have ord : ∀ {v : V9}, v.red → ord5 v = true → psi u2 u1 b x v ^ 5 = 1 := by
    intro v hv e
    rw [H.psi_pow C hv, V9.beq_eq e, psi_one]
  refine ⟨comm ht ha hta, comm ht hc htb, comm ha hc hab, ord ht ot, ord ha oa, ord hc ob, ?_⟩
  intro i hi j hj l hl e
  have hi' := allBelow_spec (allBelow_spec (allBelow_spec hind i hi) j hj) l hl
  rw [Bool.or_eq_true] at hi'
  rcases hi' with h0 | h1
  · simp only [Bool.and_eq_true, Nat.beq_eq] at h0
    exact ⟨h0.1.1, h0.1.2, h0.2⟩
  · exfalso
    have hv : (mulV (mulV (powV t i) (powV a j)) (powV c l)).red := mulV_red _ _
    have e2 : psi u2 u1 b x (mulV (mulV (powV t i) (powV a j)) (powV c l)) = 1 := by
      rw [← H.psi_mul C (mulV_red _ _) (powV_red _ _), ← H.psi_mul C (powV_red _ _) (powV_red _ _),
        ← H.psi_pow C ht, ← H.psi_pow C ha, ← H.psi_pow C hc]
      exact e
    have := psi_eq_one H C hs hx hv e2
    rw [this] at h1
    exact absurd h1 (by decide)

end CFSG.KC.MonPcFive

end
