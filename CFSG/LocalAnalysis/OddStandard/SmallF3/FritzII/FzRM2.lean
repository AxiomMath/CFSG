module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private def fzrAux_V {G : Type*} [Group G] (s l : G) : Set G := {1, s, l, l * s}

private lemma fzrAux_V_mul {G : Type*} [Group G] {s l : G}
    (hss : s * s = 1) (hll : l * l = 1) (hsl : s * l = l * s) :
    ∀ v ∈ fzrAux_V s l, ∀ w ∈ fzrAux_V s l, v * w ∈ fzrAux_V s l := by
  have h_s_ls : s * (l * s) = l := by rw [← mul_assoc, hsl, mul_assoc, hss, mul_one]
  have h_ls_s : (l * s) * s = l := by rw [mul_assoc, hss, mul_one]
  have h_ls_l : (l * s) * l = s := by rw [mul_assoc, hsl, ← mul_assoc, hll, one_mul]
  have h_l_ls : l * (l * s) = s := by rw [← mul_assoc, hll, one_mul]
  have h_ls_ls : (l * s) * (l * s) = 1 := by rw [mul_assoc, h_s_ls, hll]
  intro v hv w hw
  simp only [fzrAux_V, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw ⊢
  rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
    (simp only [hss, hll, hsl, h_s_ls, h_ls_s, h_ls_l, h_l_ls, h_ls_ls, one_mul, mul_one,
      true_or, or_true, or_false, false_or])

private lemma fzrAux_V_inv {G : Type*} [Group G] {s l : G}
    (hss : s * s = 1) (hll : l * l = 1) (hsl : s * l = l * s) :
    ∀ v ∈ fzrAux_V s l, v⁻¹ ∈ fzrAux_V s l := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hl_inv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  intro v hv
  simp only [fzrAux_V, Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl
  · simp
  · rw [hs_inv]; simp
  · rw [hl_inv]; simp
  · rw [mul_inv_rev, hs_inv, hl_inv, hsl]; simp

private lemma fzrAux_V_subset_T {G : Type*} [Group G] {s l : G} {T : Subgroup G}
    (hsT : s ∈ T) (hlT : l ∈ T) : fzrAux_V s l ⊆ T := by
  intro v hv
  simp only [fzrAux_V, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact T.one_mem
  · exact hsT
  · exact hlT
  · exact T.mul_mem hlT hsT

private def fzrAux_M {G : Type*} [Group G] (P : Subgroup G) (s l : G)
    (hNor : ∀ v ∈ fzrAux_V s l, ∀ p ∈ P, v * p * v⁻¹ ∈ P)
    (hss : s * s = 1) (hll : l * l = 1) (hsl : s * l = l * s) : Subgroup G where
  carrier := {m | ∃ p ∈ P, ∃ v, v ∈ fzrAux_V s l ∧ m = p * v}
  one_mem' := ⟨1, P.one_mem, 1, by simp [fzrAux_V], by rw [mul_one]⟩
  mul_mem' := by
    rintro a b ⟨p, hp, v, hv, rfl⟩ ⟨p', hp', w, hw, rfl⟩
    refine ⟨p * (v * p' * v⁻¹), P.mul_mem hp (hNor v hv p' hp'), v * w,
      fzrAux_V_mul hss hll hsl v hv w hw, ?_⟩
    calc p * v * (p' * w)
        = p * (v * (p' * w)) := by rw [mul_assoc p v (p'*w)]
      _ = p * ((v * p') * w) := by rw [← mul_assoc v p' w]
      _ = p * (((v * p' * v⁻¹) * v) * w) := by
            rw [show (v * p' * v⁻¹) * v = v * p' by
              rw [mul_assoc, inv_mul_cancel, mul_one]]
      _ = p * ((v * p' * v⁻¹) * (v * w)) := by rw [mul_assoc (v*p'*v⁻¹) v w]
      _ = p * (v * p' * v⁻¹) * (v * w) := by rw [← mul_assoc p (v*p'*v⁻¹) (v*w)]
  inv_mem' := by
    rintro a ⟨p, hp, v, hv, rfl⟩
    refine ⟨v⁻¹ * p⁻¹ * v, ?_, v⁻¹, fzrAux_V_inv hss hll hsl v hv, ?_⟩
    · simpa using hNor v⁻¹ (fzrAux_V_inv hss hll hsl v hv) p⁻¹ (P.inv_mem hp)
    · calc (p * v)⁻¹ = v⁻¹ * p⁻¹ := by rw [mul_inv_rev]
        _ = (v⁻¹ * p⁻¹ * v) * v⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]

private lemma fzrAux_dich_Q {G : Type*} [Group G] {P Q M : Subgroup G} {t : G}
    (hPM : P ≤ M) (hQP : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P) :
    ∀ q ∈ Q, q ∈ M ∨ t * q ∈ M := by
  intro q hq
  rcases hQP q hq with h | h
  · exact Or.inl (hPM h)
  · exact Or.inr (hPM h)

private lemma fzrAux_dich_tauQ {G : Type*} [Group G] {P Q M : Subgroup G} {t tau s : G}
    (hPM : P ≤ M) (hsM : s ∈ M)
    (hQP : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P)
    (ht2 : t * t = 1) (hst : s * t = t * s) (hτ : tau = s ∨ tau = t * s) :
    ∀ q ∈ Q, tau * q ∈ M ∨ t * (tau * q) ∈ M := by
  intro q hq
  rcases hQP q hq with hqP | hqP
  · rcases hτ with h | h
    · rw [h]; exact Or.inl (M.mul_mem hsM (hPM hqP))
    · rw [h]; refine Or.inr ?_
      have hI1 : t * (t * s * q) = s * q := by
        calc t * (t * s * q) = (t * (t * s)) * q := by rw [← mul_assoc t (t*s) q]
          _ = ((t * t) * s) * q := by rw [← mul_assoc t t s]
          _ = s * q := by rw [ht2, one_mul]
      rw [hI1]
      exact M.mul_mem hsM (hPM hqP)
  · rcases hτ with h | h
    · rw [h]; refine Or.inr ?_
      have hI2 : t * (s * q) = s * (t * q) := by
        calc t * (s * q) = (t * s) * q := by rw [← mul_assoc t s q]
          _ = (s * t) * q := by rw [← hst]
          _ = s * (t * q) := by rw [mul_assoc]
      rw [hI2]
      exact M.mul_mem hsM (hPM hqP)
    · rw [h]; refine Or.inl ?_
      have hI3 : (t * s) * q = s * (t * q) := by
        calc (t * s) * q = (s * t) * q := by rw [← hst]
          _ = s * (t * q) := by rw [mul_assoc]
      rw [hI3]
      exact M.mul_mem hsM (hPM hqP)

private lemma fzrAux_dich_lQ {G : Type*} [Group G] {P Q M : Subgroup G} {t l : G}
    (hPM : P ≤ M) (hlM : l ∈ M)
    (hQP : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P) (htl : t * l = l * t) :
    ∀ q ∈ Q, l * q ∈ M ∨ t * (l * q) ∈ M := by
  intro q hq
  rcases hQP q hq with hqP | hqP
  · exact Or.inl (M.mul_mem hlM (hPM hqP))
  · refine Or.inr ?_
    have hI4 : t * (l * q) = l * (t * q) := by
      calc t * (l * q) = (t * l) * q := by rw [← mul_assoc t l q]
        _ = (l * t) * q := by rw [htl]
        _ = l * (t * q) := by rw [mul_assoc]
    rw [hI4]
    exact M.mul_mem hlM (hPM hqP)

private lemma fzrAux_dich_ltauQ {G : Type*} [Group G] {P Q M : Subgroup G} {t tau s l : G}
    (hPM : P ≤ M) (hsM : s ∈ M) (hlM : l ∈ M)
    (hQP : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P)
    (ht2 : t * t = 1) (hst : s * t = t * s) (htl : t * l = l * t)
    (hτ : tau = s ∨ tau = t * s) :
    ∀ q ∈ Q, l * tau * q ∈ M ∨ t * (l * tau * q) ∈ M := by
  intro q hq
  rcases hQP q hq with hqP | hqP
  · rcases hτ with h | h
    · rw [h]; exact Or.inl (M.mul_mem (M.mul_mem hlM hsM) (hPM hqP))
    · rw [h]; refine Or.inr ?_
      have hI5 : t * (l * (t * s) * q) = l * s * q := by
        calc t * (l * (t * s) * q) = (t * (l * (t * s))) * q := by
              rw [← mul_assoc t (l * (t*s)) q]
          _ = ((t * l) * (t * s)) * q := by rw [← mul_assoc t l (t * s)]
          _ = ((l * t) * (t * s)) * q := by rw [htl]
          _ = (l * (t * (t * s))) * q := by rw [mul_assoc l t (t * s)]
          _ = (l * ((t * t) * s)) * q := by rw [← mul_assoc t t s]
          _ = (l * s) * q := by rw [ht2, one_mul]
          _ = l * s * q := rfl
      rw [hI5]
      exact M.mul_mem (M.mul_mem hlM hsM) (hPM hqP)
  · rcases hτ with h | h
    · rw [h]; refine Or.inr ?_
      have hI6 : t * (l * s * q) = l * s * (t * q) := by
        calc t * (l * s * q) = (t * (l * s)) * q := by rw [← mul_assoc t (l*s) q]
          _ = ((t * l) * s) * q := by rw [← mul_assoc t l s]
          _ = ((l * t) * s) * q := by rw [htl]
          _ = (l * (t * s)) * q := by rw [mul_assoc l t s]
          _ = (l * (s * t)) * q := by rw [← hst]
          _ = ((l * s) * t) * q := by rw [← mul_assoc l s t]
          _ = (l * s) * (t * q) := by rw [mul_assoc (l*s) t q]
      rw [hI6]
      exact M.mul_mem (M.mul_mem hlM hsM) (hPM hqP)
    · rw [h]; refine Or.inl ?_
      have hI7 : (l * (t * s)) * q = l * s * (t * q) := by
        calc (l * (t * s)) * q = (l * (s * t)) * q := by rw [← hst]
          _ = ((l * s) * t) * q := by rw [← mul_assoc l s t]
          _ = (l * s) * (t * q) := by rw [mul_assoc (l*s) t q]
      rw [hI7]
      exact M.mul_mem (M.mul_mem hlM hsM) (hPM hqP)

theorem fzr_index2_M {G : Type} [Group G] [Finite G] {T P Q : Subgroup G} {t tau s l : G}
    (hPQ : P ≤ Q) (hQT : Q ≤ T) (hTP : ∀ g ∈ T, ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (hP : Nat.card P = 64) (hT : Nat.card T = 512)
    (hQP : ∀ q ∈ Q, q ∈ P ∨ t * q ∈ P)
    (hTQ : ∀ g ∈ T, g ∈ Q ∨ tau⁻¹ * g ∈ Q ∨ l⁻¹ * g ∈ Q ∨ (l * tau)⁻¹ * g ∈ Q)
    (ht : t ∈ T) (htau : tau ∈ T) (hl : l ∈ T)
    (ht2 : t * t = 1) (htau2 : tau * tau = 1) (hl2 : l * l = 1)
    (httau : t * tau = tau * t) (htl : t * l = l * t) (htaul : tau * l = l * tau)
    (hs : s = tau ∨ s = t * tau) :
    ∃ M : Subgroup G, M ≤ T ∧ M.relIndex T = 2 ∧ P ≤ M ∧ s ∈ M ∧ l ∈ M ∧ t ∉ M ∧
      ∀ m ∈ M, ∃ p ∈ P, m = p ∨ m = p * s ∨ m = p * l ∨ m = p * (l * s) := by
  have hll : l * l = 1 := hl2
  have hsT : s ∈ T := by
    rcases hs with h | h
    · rw [h]; exact htau
    · rw [h]; exact T.mul_mem ht htau
  have hss : s * s = 1 := by
    rcases hs with h | h
    · rw [h]; exact htau2
    · rw [h]
      simpa [pow_two, ht2, htau2] using (show Commute t tau from httau).mul_pow 2
  have hst : s * t = t * s := by
    rcases hs with h | h
    · rw [h]; exact httau.symm
    · rw [h]
      exact ((Commute.refl t).mul_left httau.symm).eq
  have hsl : s * l = l * s := by
    rcases hs with h | h
    · rw [h]; exact htaul
    · rw [h]
      exact ((show Commute t l from htl).mul_left (show Commute tau l from htaul)).eq
  have hτ : tau = s ∨ tau = t * s := by
    rcases hs with h | h
    · exact Or.inl h.symm
    · right; rw [h, ← mul_assoc, ht2, one_mul]
  have hNor : ∀ v ∈ fzrAux_V s l, ∀ p ∈ P, v * p * v⁻¹ ∈ P :=
    fun v hv p hp => hTP v (fzrAux_V_subset_T hsT hl hv) p hp
  let M : Subgroup G := fzrAux_M P s l hNor hss hll hsl
  have hMT : M ≤ T := by
    rintro m ⟨p, hp, v, hv, rfl⟩
    exact T.mul_mem (hQT (hPQ hp)) (fzrAux_V_subset_T hsT hl hv)
  have hPM : P ≤ M := by
    intro p hp
    exact ⟨p, hp, 1, by simp [fzrAux_V], by rw [mul_one]⟩
  have hsM : s ∈ M := by
    refine ⟨1, P.one_mem, s, ?_, ?_⟩
    · simp [fzrAux_V]
    · rw [one_mul]
  have hlM : l ∈ M := by
    refine ⟨1, P.one_mem, l, ?_, ?_⟩
    · simp [fzrAux_V]
    · rw [one_mul]
  have hM_form : ∀ m ∈ M, ∃ p ∈ P, m = p ∨ m = p * s ∨ m = p * l ∨ m = p * (l * s) := by
    intro m hm
    rcases hm with ⟨p, hp, v, hv, rfl⟩
    simp only [fzrAux_V, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨p, hp, Or.inl (by rw [mul_one])⟩
    · exact ⟨p, hp, Or.inr (Or.inl rfl)⟩
    · exact ⟨p, hp, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨p, hp, Or.inr (Or.inr (Or.inr rfl))⟩
  have hcardM : Nat.card M ≤ 256 := by
    let rep : Bool × Bool → G := fun x =>
      match x with
      | (false, false) => 1
      | (false, true) => s
      | (true, false) => l
      | (true, true) => l * s
    have hrepV : ∀ i, rep i ∈ fzrAux_V s l := by
      rintro ⟨b1, b2⟩
      cases b1 <;> cases b2 <;> simp [rep, fzrAux_V]
    let f : P × (Bool × Bool) → M := fun x =>
      ⟨x.1 * rep x.2, ⟨x.1, x.1.2, rep x.2, hrepV x.2, rfl⟩⟩
    have hf : Function.Surjective f := by
      intro m
      obtain ⟨p, hp, h | h | h | h⟩ := hM_form m m.2
      · exact ⟨(⟨p, hp⟩, (false, false)), by apply Subtype.ext; simpa [f, rep] using h.symm⟩
      · exact ⟨(⟨p, hp⟩, (false, true)), by apply Subtype.ext; simpa [f, rep] using h.symm⟩
      · exact ⟨(⟨p, hp⟩, (true, false)), by apply Subtype.ext; simpa [f, rep] using h.symm⟩
      · exact ⟨(⟨p, hp⟩, (true, true)), by apply Subtype.ext; simpa [f, rep] using h.symm⟩
    have hcardBB : Nat.card (Bool × Bool) = 4 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
    have hle := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, hcardBB, hP] at hle
    have hmul : (64 : ℕ) * 4 = 256 := by decide
    rwa [hmul] at hle
  have ht_notMem : t ∉ M := by
    intro htM
    have htauM : tau ∈ M := by
      rcases hτ with h | h
      · rw [h]; exact hsM
      · rw [h]; exact M.mul_mem htM hsM
    have hTM : T ≤ M := by
      intro g hg
      rcases hTQ g hg with hQ | hQ | hQ | hQ
      · rcases hQP g hQ with h | h
        · exact hPM h
        · have hg_eq : g = t * (t * g) := by rw [← mul_assoc, ht2, one_mul]
          rw [hg_eq]; exact M.mul_mem htM (hPM h)
      · have hg_eq : g = tau * (tau⁻¹ * g) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
        rcases hQP (tau⁻¹ * g) hQ with h | h
        · rw [hg_eq]; exact M.mul_mem htauM (hPM h)
        · have hq_eq : tau⁻¹ * g = t * (t * (tau⁻¹ * g)) := by
            rw [← mul_assoc, ht2, one_mul]
          rw [hg_eq, hq_eq]
          exact M.mul_mem htauM (M.mul_mem htM (hPM h))
      · have hg_eq : g = l * (l⁻¹ * g) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
        rcases hQP (l⁻¹ * g) hQ with h | h
        · rw [hg_eq]; exact M.mul_mem hlM (hPM h)
        · have hq_eq : l⁻¹ * g = t * (t * (l⁻¹ * g)) := by
            rw [← mul_assoc, ht2, one_mul]
          rw [hg_eq, hq_eq]
          exact M.mul_mem hlM (M.mul_mem htM (hPM h))
      · have hg_eq : g = (l * tau) * ((l * tau)⁻¹ * g) := by
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        rcases hQP ((l * tau)⁻¹ * g) hQ with h | h
        · rw [hg_eq]; exact M.mul_mem (M.mul_mem hlM htauM) (hPM h)
        · have hq_eq : (l * tau)⁻¹ * g = t * (t * ((l * tau)⁻¹ * g)) := by
            rw [← mul_assoc, ht2, one_mul]
          rw [hg_eq, hq_eq]
          exact M.mul_mem (M.mul_mem hlM htauM) (M.mul_mem htM (hPM h))
    have h512 : Nat.card T ≤ Nat.card M := Subgroup.card_le_of_le hTM
    rw [hT] at h512
    have hcontra : (512 : ℕ) ≤ 256 := le_trans h512 hcardM
    exact absurd hcontra (by decide)
  have hcover : ∀ g ∈ T, g ∈ M ∨ t * g ∈ M := by
    intro g hg
    rcases hTQ g hg with hQ | hQ | hQ | hQ
    · exact fzrAux_dich_Q hPM hQP g hQ
    · have hg_eq : g = tau * (tau⁻¹ * g) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hg_eq]
      exact fzrAux_dich_tauQ hPM hsM hQP ht2 hst hτ (tau⁻¹ * g) hQ
    · have hg_eq : g = l * (l⁻¹ * g) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hg_eq]
      exact fzrAux_dich_lQ hPM hlM hQP htl (l⁻¹ * g) hQ
    · have hg_eq : g = (l * tau) * ((l * tau)⁻¹ * g) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hg_eq]
      exact fzrAux_dich_ltauQ hPM hsM hlM hQP ht2 hst htl hτ ((l * tau)⁻¹ * g) hQ
  refine ⟨M, hMT, ?_, hPM, hsM, hlM, ht_notMem, hM_form⟩
  rw [Subgroup.relIndex_eq_two_iff']
  refine ⟨t, ht, fun b hb => ?_⟩
  rw [xor_iff_or_and_not_and]
  refine ⟨(hcover b hb).elim Or.inr Or.inl, ?_⟩
  rintro ⟨htb, hbM⟩
  exact ht_notMem (by simpa [mul_assoc] using M.mul_mem htb (M.inv_mem hbM))

end CFSG.OddStandard.SmallF3.FritzII
