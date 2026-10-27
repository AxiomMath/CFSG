module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Elem

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem mem_iff_of_map_conj {H : Subgroup G} {n : G}
    (h : H.map (MulAut.conj n⁻¹).toMonoidHom = H) (x : G) : x ∈ H ↔ n⁻¹ * x * n ∈ H := by
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    have : s = x := by
      have h2 : n⁻¹ * s * n = n⁻¹ * x * n := by simpa [MulAut.conj_apply] using hsx
      simpa using h2
    rwa [this] at hs

namespace Cfg

variable {d : Datum A} (K : Cfg d)

include K

local macro "dnorm " K:term : tactic =>
  `(tactic| simp only [mul_assoc, ($K).sort_pq, ($K).sort_tq, ($K).sort_tp, canc_q,
    ($K).canc_p, ($K).canc_t, ($K).pi_q, ($K).tau_q, ($K).tau_pi, q_mul_self,
    ($K).pi_sq, ($K).tau_sq, one_mul, mul_one])

theorem R1_le_S : K.c.R1 ≤ d.S := by
  unfold Chart2.R1
  rw [closure_le]
  rintro x (rfl | rfl | rfl | rfl | rfl)
  · exact K.q_mem_S
  · exact K.pi_mem_S
  · exact K.tau_mem_S
  · exact K.mu_mem_S
  · exact K.lam_mem_S

theorem R2_le_S : K.c.R2 ≤ d.S := by
  unfold Chart2.R2
  rw [closure_le]
  rintro x (rfl | rfl | rfl | rfl | rfl)
  · exact K.q_mem_S
  · exact K.pi_mem_S
  · exact K.tau_mem_S
  · exact K.ze_mem_S
  · exact K.xi_mem_S

theorem S_eq_sup : d.S = K.c.R1 ⊔ K.c.R2 := by
  refine le_antisymm ?_ (sup_le K.R1_le_S K.R2_le_S)
  rw [← K.c.gen, closure_le]
  have h1 : K.c.R1 ≤ K.c.R1 ⊔ K.c.R2 := le_sup_left
  have h2 : K.c.R2 ≤ K.c.R1 ⊔ K.c.R2 := le_sup_right
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact h1 (subset_closure (by simp))
  · exact h1 (subset_closure (by simp))
  · exact h1 (subset_closure (by simp))
  · exact h1 (subset_closure (by simp))
  · exact h1 (subset_closure (by simp))
  · exact h2 (subset_closure (by simp))
  · exact h2 (subset_closure (by simp))

theorem rootless {x : G} (hx : x ∈ K.c.D) (hx1 : x ≠ 1) (hroot : ∀ s ∈ d.S, s * s ≠ x) :
    x = d.q := by
  have hga := K.g_act
  simp only [GAct, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false] at hga
  obtain ⟨hgq, hgpi, -⟩ := hga
  have hgroot : ∀ y s : G, s ∈ d.S → s * s = y → cj s K.g * cj s K.g = cj y K.g := by
    intro y s _ h
    rw [← cj_mul, h]
  have hSg : ∀ s ∈ d.S, cj s K.g ∈ d.S := fun s hs => by
    simpa [cj] using K.g_norm s hs
  have hπ : ∃ s ∈ d.S, s * s = K.c.pi := by
    obtain ⟨s, hs, h⟩ := K.sf.root_pi
    exact ⟨s, hs, by rw [← pow_two]; exact h⟩
  have hqπ : ∃ s ∈ d.S, s * s = d.q * K.c.pi := by
    obtain ⟨s, hs, h⟩ := K.sf.root_qpi
    exact ⟨s, hs, by rw [← pow_two]; exact h⟩
  have hτ : ∃ s ∈ d.S, s * s = K.c.tau := by
    obtain ⟨s, hs, h⟩ := K.sf.root_tau
    exact ⟨s, hs, by rw [← pow_two]; exact h⟩
  have hqτ : ∃ s ∈ d.S, s * s = d.q * K.c.tau := by
    obtain ⟨s, hs, h⟩ := K.sf.root_qtau
    exact ⟨s, hs, by rw [← pow_two]; exact h⟩
  by_contra hne
  rcases K.D_cases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx1 rfl
  · exact hne rfl
  · obtain ⟨s, hs, h⟩ := hπ; exact hroot s hs h
  · obtain ⟨s, hs, h⟩ := hqπ; exact hroot s hs h
  · obtain ⟨s, hs, h⟩ := hτ; exact hroot s hs h
  · obtain ⟨s, hs, h⟩ := hqτ; exact hroot s hs h
  ·
    obtain ⟨s, hs, h⟩ := hqπ
    refine hroot _ (hSg s hs) ?_
    rw [hgroot _ s hs h, cj_mul, hgq, hgpi]
    dnorm K
  ·
    obtain ⟨s, hs, h⟩ := hπ
    refine hroot _ (hSg s hs) ?_
    rw [hgroot _ s hs h, hgpi]
    dnorm K

theorem R1_ne_R2 : K.c.R1 ≠ K.c.R2 := by
  intro h
  have h1 : K.c.R1 ⊓ K.c.R2 = K.c.R1 := by rw [← h, inf_idem]
  have := K.sf.inf_R
  rw [h1] at this
  have h2 := K.sf.card_R1
  rw [this, K.sf.card_D] at h2
  omega

theorem map_R_perm {g : G} (h1 : K.c.R1.map (MulAut.conj g).toMonoidHom ≤ d.X)
    (h2 : K.c.R2.map (MulAut.conj g).toMonoidHom ≤ d.X) :
    (K.c.R1.map (MulAut.conj g).toMonoidHom = K.c.R1 ∧
        K.c.R2.map (MulAut.conj g).toMonoidHom = K.c.R2) ∨
      (K.c.R1.map (MulAut.conj g).toMonoidHom = K.c.R2 ∧
        K.c.R2.map (MulAut.conj g).toMonoidHom = K.c.R1) := by
  have key : ∀ H : Subgroup G, (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) → (∀ a ∈ H, a * a = 1) →
      Nat.card H = 32 → H.map (MulAut.conj g).toMonoidHom ≤ d.X →
      (H.map (MulAut.conj g).toMonoidHom = K.c.R1 ∨
        H.map (MulAut.conj g).toMonoidHom = K.c.R2) := by
    intro H hc hs hcard hle
    refine K.elemAb32 hle ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show (MulAut.conj g) a * (MulAut.conj g) b = (MulAut.conj g) b * (MulAut.conj g) a
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      show (MulAut.conj g) a * (MulAut.conj g) a = 1
      rw [← map_mul, hs a ha, map_one]
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hcard
  have hne : K.c.R1.map (MulAut.conj g).toMonoidHom ≠ K.c.R2.map (MulAut.conj g).toMonoidHom :=
    fun h => K.R1_ne_R2 (Subgroup.map_injective (MulAut.conj g).injective h)
  have a1 := key K.c.R1 K.sf.R1_comm K.sf.R1_sq K.sf.card_R1 h1
  have a2 := key K.c.R2 K.sf.R2_comm K.sf.R2_sq K.sf.card_R2 h2
  rcases a1 with e1 | e1 <;> rcases a2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hne

theorem map_S_D_eq {g : G} (h1 : K.c.R1.map (MulAut.conj g).toMonoidHom ≤ d.X)
    (h2 : K.c.R2.map (MulAut.conj g).toMonoidHom ≤ d.X) :
    d.S.map (MulAut.conj g).toMonoidHom = d.S ∧ K.c.D.map (MulAut.conj g).toMonoidHom = K.c.D := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [K.S_eq_sup, Subgroup.map_sup, ← K.sf.inf_R, Subgroup.map_inf_eq _ _ _ hinj]
  rcases K.map_R_perm h1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; exact ⟨rfl, rfl⟩
  · rw [e1, e2]; exact ⟨sup_comm _ _, inf_comm _ _⟩

theorem weakly_closed (g : G) (h : d.S.map (MulAut.conj g).toMonoidHom ≤ d.X) :
    d.S.map (MulAut.conj g).toMonoidHom = d.S :=
  (K.map_S_D_eq ((Subgroup.map_mono K.R1_le_S).trans h) ((Subgroup.map_mono K.R2_le_S).trans h)).1

theorem map_S_D_of_normalizer {n : G} (hn : n ∈ normalizer (d.X : Set G)) :
    d.S.map (MulAut.conj n⁻¹).toMonoidHom = d.S ∧
      K.c.D.map (MulAut.conj n⁻¹).toMonoidHom = K.c.D := by
  have hle : ∀ H : Subgroup G, H ≤ d.S → H.map (MulAut.conj n⁻¹).toMonoidHom ≤ d.X := by
    rintro H hH _ ⟨r, hr, rfl⟩
    have := (mem_normalizer_iff''.1 hn r).1 (d.S_le_X (hH hr))
    simpa [MulAut.conj_apply] using this
  exact K.map_S_D_eq (hle _ K.R1_le_S) (hle _ K.R2_le_S)

theorem cj_q_of_map {n : G} (h : d.S.map (MulAut.conj n⁻¹).toMonoidHom = d.S) : cj d.q n = d.q := by
  have hS := mem_iff_of_map_conj h
  have hqS : cj d.q n ∈ d.S := (hS _).1 K.q_mem_S
  have hD : cj d.q n ∈ K.c.D := by
    refine K.mem_D_of_central hqS fun s hs => ?_
    have hs' : n * s * n⁻¹ ∈ d.S := by
      refine (hS (n * s * n⁻¹)).2 ?_
      have e : n⁻¹ * (n * s * n⁻¹) * n = s := by group
      rw [e]; exact hs
    have hc : (n * s * n⁻¹) * d.q = d.q * (n * s * n⁻¹) := K.D_central K.q_mem_D hs'
    calc s * cj d.q n = n⁻¹ * ((n * s * n⁻¹) * d.q) * n := by unfold cj; group
      _ = n⁻¹ * (d.q * (n * s * n⁻¹)) * n := by rw [hc]
      _ = cj d.q n * s := by unfold cj; group
  refine K.rootless hD ?_ ?_
  · intro h1
    have h1' : n⁻¹ * d.q * n = 1 := h1
    have : d.q = 1 := by
      calc d.q = n * (n⁻¹ * d.q * n) * n⁻¹ := by group
        _ = 1 := by rw [h1']; group
    exact (q_ne_one d) this
  · intro s hs hss
    have hs' : n * s * n⁻¹ ∈ d.S := by
      refine (hS (n * s * n⁻¹)).2 ?_
      have e : n⁻¹ * (n * s * n⁻¹) * n = s := by group
      rw [e]; exact hs
    have : (n * s * n⁻¹) ^ 2 = d.q := by
      have e : (n * s * n⁻¹) ^ 2 = n * (s * s) * n⁻¹ := by rw [pow_two]; group
      rw [e, hss]
      have e2 : n * cj d.q n * n⁻¹ = d.q := by unfold cj; group
      exact e2
    exact K.sf.no_root_q _ hs' this

theorem X_sylow_G : IsSylowOf 2 d.X (⊤ : Subgroup G) :=
  d.X_sylow_G K.h fun _ hn => K.cj_q_of_map (K.map_S_D_of_normalizer hn).1

theorem fuse_D {x y : G} (hx : x ∈ K.c.D) (hy : y ∈ K.c.D) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (d.S : Set G), cj x n = y := by
  have hc : ∀ z ∈ K.c.D, z ∈ d.S ∧ z ∈ centralizer (d.S : Set G) := fun z hz =>
    ⟨K.D_le_S hz, mem_centralizer_iff.2 fun s hs => K.D_central hz hs⟩
  exact fuse_of_weaklyClosed K.X_sylow_G d.S_le_X K.weakly_closed (hc x hx) (hc y hy) hxy

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
