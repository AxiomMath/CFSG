module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Rel2
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih0

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

@[expose] def D1 (a a' t : G) : Subgroup G := zpowers (a * a'⁻¹) ⊔ zpowers t

@[expose] def D2 (a a' b b' t : G) : Subgroup G := zpowers (a * a') ⊔ zpowers (b * b' * t)

theorem commute_sup_sup {r₁ s₁ r₂ s₂ : G} (h11 : r₁ * r₂ = r₂ * r₁) (h12 : r₁ * s₂ = s₂ * r₁)
    (h21 : s₁ * r₂ = r₂ * s₁) (h22 : s₁ * s₂ = s₂ * s₁) :
    ∀ g ∈ zpowers r₁ ⊔ zpowers s₁, ∀ g' ∈ zpowers r₂ ⊔ zpowers s₂, g * g' = g' * g := by
  have key : ∀ g₀ : G, g₀ * r₂ = r₂ * g₀ → g₀ * s₂ = s₂ * g₀ →
      ∀ g' ∈ zpowers r₂ ⊔ zpowers s₂, g₀ * g' = g' * g₀ := by
    intro g₀ hr hs g' hg'
    have hle : zpowers r₂ ⊔ zpowers s₂ ≤ centralizer ({g₀} : Set G) := by
      refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
      · exact hr.symm
      · exact hs.symm
    have := mem_centralizer_singleton_iff.1 (hle hg')
    exact this.symm
  intro g hg g' hg'
  have hle : zpowers r₁ ⊔ zpowers s₁ ≤ centralizer ((zpowers r₂ ⊔ zpowers s₂ : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_iff]
    · intro g'' hg''
      exact (key r₁ h11 h12 g'' hg'').symm
    · intro g'' hg''
      exact (key s₁ h21 h22 g'' hg'').symm
  exact ((mem_centralizer_iff.1 (hle hg)) g' hg').symm

theorem card_sup_of_commute {H K : Subgroup G} [Finite G] (hcomm : ∀ g ∈ H, ∀ g' ∈ K, g * g' = g' * g)
    (hinf : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let f : H × K →* G := (H.subtype).noncommCoprod K.subtype (fun p q => hcomm _ p.2 _ q.2)
  have happ : ∀ (p : H) (q : K), f (p, q) = (p : G) * q := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨p, q⟩ hpq
    rw [MonoidHom.mem_ker, happ] at hpq
    have hmem : (p : G) ∈ H ⊓ K := by
      refine ⟨p.2, ?_⟩
      have : (p : G) = ((q : G))⁻¹ := eq_inv_of_mul_eq_one_left hpq
      rw [this]
      exact K.inv_mem q.2
    rw [hinf, mem_bot] at hmem
    have hp : p = 1 := Subtype.ext hmem
    rw [hmem, one_mul] at hpq
    have hq : q = 1 := Subtype.ext hpq
    rw [hp, hq]
    exact one_mem _
  have hrange : f.range = H ⊔ K := by
    apply le_antisymm
    · rintro _ ⟨⟨p, q⟩, rfl⟩
      rw [happ]
      exact mul_mem (mem_sup_left p.2) (mem_sup_right q.2)
    · refine sup_le ?_ ?_
      · intro p hp
        exact ⟨(⟨p, hp⟩, 1), by rw [happ]; simp⟩
      · intro q hq
        exact ⟨(1, ⟨q, hq⟩), by rw [happ]; simp⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem commute_of_conj {x y : G} (h : x * y * x⁻¹ = y) : x * y = y * x := mul_inv_eq_iff_eq_mul.1 h

theorem eq_one_or_pow_half {δ : G} {M : ℕ} (hδ : orderOf δ = 2 * M) {i : ℕ} (h : δ ^ i * δ ^ i = 1) :
    δ ^ i = 1 ∨ δ ^ i = δ ^ M := by
  have h2 : δ ^ (2 * i) = 1 := by rw [two_mul, pow_add]; exact h
  have h3 : 2 * M ∣ 2 * i := hδ ▸ orderOf_dvd_of_pow_eq_one h2
  have h4 : M ∣ i := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  obtain ⟨k, rfl⟩ := h4
  have hM : δ ^ (2 * M) = 1 := hδ ▸ pow_orderOf_eq_one δ
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [show M * (2 * m) = 2 * M * m by ring, pow_mul, hM, one_pow]
  · right
    rw [show M * (2 * m + 1) = 2 * M * m + M by ring, pow_add, pow_mul, hM, one_pow, one_mul]

namespace Rel

variable {a b a' b' t : G} {M : ℕ}

theorem card_D2 (h : Rel a b a' b' t M) : Nat.card ↥(D2 a a' b b' t) = 2 * (2 * M) := by
  have : NeZero (2 * M) := ⟨by have := h.one_le; omega⟩
  exact card_dihedral_sup (2 * M) (a * a') (b * b' * t) h.orderOf_dl2 h.s2_sq h.s2_dl2
    h.s2_not_mem_dl2

theorem commute_dl1_a (h : Rel a b a' b' t M) : Commute (a * a'⁻¹) a :=
  Commute.mul_left (Commute.refl a) h.commute_a_a'.inv_right.symm

theorem commute_dl1_a' (h : Rel a b a' b' t M) : Commute (a * a'⁻¹) a' :=
  Commute.mul_left h.commute_a_a' (Commute.refl a').inv_left

theorem commute_dl2_a (h : Rel a b a' b' t M) : Commute (a * a') a :=
  Commute.mul_left (Commute.refl a) h.commute_a_a'.symm

theorem commute_dl1_dl2 (h : Rel a b a' b' t M) : Commute (a * a'⁻¹) (a * a') :=
  Commute.mul_right h.commute_dl1_a h.commute_dl1_a'

theorem D1_D2_comm (h : Rel a b a' b' t M) :
    ∀ g ∈ D1 a a' t, ∀ g' ∈ D2 a a' b b' t, g * g' = g' * g := by
  refine commute_sup_sup h.commute_dl1_dl2.eq ?_ ?_ ?_
  · have := commute_of_conj h.s2_dl1
    exact this.symm
  · exact commute_of_conj h.t_dl2
  · exact commute_of_conj h.t_s2

theorem commute_a_dl1_pow (h : Rel a b a' b' t M) (i : ℕ) : Commute a ((a * a'⁻¹) ^ i) :=
  (Commute.mul_right (Commute.refl a) h.commute_a_a'.inv_right).pow_right i

theorem commute_a_dl2_pow (h : Rel a b a' b' t M) (j : ℕ) : Commute a ((a * a') ^ j) :=
  (Commute.mul_right (Commute.refl a) h.commute_a_a').pow_right j

theorem t_dl1_pow (h : Rel a b a' b' t M) (i : ℕ) :
    t * (a * a'⁻¹) ^ i * t⁻¹ = ((a * a'⁻¹) ^ i)⁻¹ := by
  rw [← conj_pow, h.t_dl1, inv_pow]

theorem t_dl2_pow (h : Rel a b a' b' t M) (j : ℕ) : t * (a * a') ^ j * t⁻¹ = (a * a') ^ j := by
  rw [← conj_pow, h.t_dl2]

theorem aN_ne_one' (h : Rel a b a' b' t M) : a ^ (2 * M) ≠ 1 := h.qg.aN_ne_one (by have := h.one_le; omega)

theorem rot_rot (h : Rel a b a' b' t M) {i j : ℕ} (e : (a * a'⁻¹) ^ i = (a * a') ^ j) :
    (a * a'⁻¹) ^ i = 1 := by
  have h1 : t * (a * a'⁻¹) ^ i * t⁻¹ = ((a * a'⁻¹) ^ i)⁻¹ := h.t_dl1_pow i
  have h2 : t * (a * a') ^ j * t⁻¹ = (a * a') ^ j := h.t_dl2_pow j
  rw [e, h2] at h1
  have hsq : (a * a') ^ j * (a * a') ^ j = 1 := by
    nth_rewrite 1 [h1]; exact inv_mul_cancel _
  rcases eq_one_or_pow_half h.orderOf_dl2 hsq with h3 | h3
  · rw [e, h3]
  · exfalso
    have hsq' : (a * a'⁻¹) ^ i * (a * a'⁻¹) ^ i = 1 := by rw [e]; exact hsq
    rcases eq_one_or_pow_half h.orderOf_dl1 hsq' with h4 | h4
    · apply h.dl2_M_ne_one
      rw [← h3, ← e, h4]
    · have h5 : (a * a'⁻¹) ^ M = (a * a') ^ M := by rw [← h4, e, h3]
      rw [h.dl2_M] at h5
      exact h.aN_ne_one' (mul_left_cancel (h5.symm.trans (mul_one _).symm))

theorem D1_inf_D2 (h : Rel a b a' b' t M) : D1 a a' t ⊓ D2 a a' b b' t = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  rw [mem_bot]
  have : NeZero (2 * M) := ⟨by have := h.one_le; omega⟩
  have hr1 : (a * a'⁻¹) ^ (2 * M) = 1 := h.orderOf_dl1 ▸ pow_orderOf_eq_one _
  have hr2 : (a * a') ^ (2 * M) = 1 := h.orderOf_dl2 ▸ pow_orderOf_eq_one _
  obtain ⟨i, hi⟩ := (mem_dihedral_iff (2 * M) hr1 h.t_sq h.t_dl1).1 hg1
  obtain ⟨j, hj⟩ := (mem_dihedral_iff (2 * M) hr2 h.s2_sq h.s2_dl2).1 hg2
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · rw [hi]; exact h.rot_rot (hi.symm.trans hj)
  ·
    exfalso
    have e : (b * b' * t) * (a * a') ^ j = (a * a'⁻¹) ^ i := by rw [← hj, hi]
    have e2 : b * b' * t = (a * a'⁻¹) ^ i * ((a * a') ^ j)⁻¹ := eq_mul_inv_of_mul_eq e
    apply h.s2_not_comm_a
    rw [e2]
    exact (h.commute_a_dl1_pow i).mul_right (h.commute_a_dl2_pow j).inv_right
  · exfalso
    have e : t * (a * a'⁻¹) ^ i = (a * a') ^ j := by rw [← hi, hj]
    have e2 : t = (a * a') ^ j * ((a * a'⁻¹) ^ i)⁻¹ := eq_mul_inv_of_mul_eq e
    apply h.t_not_comm_a
    rw [e2]
    exact (h.commute_a_dl2_pow j).mul_right (h.commute_a_dl1_pow i).inv_right
  · exfalso
    have e : t * (a * a'⁻¹) ^ i = (b * b' * t) * (a * a') ^ j := by rw [← hi, hj]
    have e1 := h.t_dl1_pow i
    have e2 := h.t_dl2_pow j
    have e3 : ((a * a'⁻¹) ^ i)⁻¹ = (b * b') * (a * a') ^ j := by
      rw [← e1]
      calc t * (a * a'⁻¹) ^ i * t⁻¹ = (b * b' * t) * (a * a') ^ j * t⁻¹ := by rw [e]
        _ = (b * b') * (t * (a * a') ^ j * t⁻¹) := by simp only [mul_assoc]
        _ = (b * b') * (a * a') ^ j := by rw [e2]
    have e4 : b * b' = ((a * a'⁻¹) ^ i)⁻¹ * ((a * a') ^ j)⁻¹ := eq_mul_inv_of_mul_eq e3.symm
    apply h.b0_not_comm_a
    rw [e4]
    exact (h.commute_a_dl1_pow i).inv_right.mul_right (h.commute_a_dl2_pow j).inv_right

end Rel

theorem mem_sup_iff_of_commute {H K : Subgroup G} (hcomm : ∀ g ∈ H, ∀ g' ∈ K, g * g' = g' * g) {g : G} :
    g ∈ H ⊔ K ↔ ∃ p ∈ H, ∃ q ∈ K, g = p * q := by
  constructor
  · intro hg
    let L : Subgroup G :=
      { carrier := {g | ∃ p ∈ H, ∃ q ∈ K, g = p * q}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
        mul_mem' := by
          rintro _ _ ⟨p, hp, q, hq, rfl⟩ ⟨p', hp', q', hq', rfl⟩
          refine ⟨p * p', mul_mem hp hp', q * q', mul_mem hq hq', ?_⟩
          have h1 : p' * q = q * p' := hcomm p' hp' q hq
          calc p * q * (p' * q') = p * (q * p') * q' := by simp only [mul_assoc]
            _ = p * (p' * q) * q' := by rw [h1]
            _ = p * p' * (q * q') := by simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨p, hp, q, hq, rfl⟩
          refine ⟨p⁻¹, H.inv_mem hp, q⁻¹, K.inv_mem hq, ?_⟩
          have h1 : p⁻¹ * q⁻¹ = q⁻¹ * p⁻¹ := hcomm p⁻¹ (H.inv_mem hp) q⁻¹ (K.inv_mem hq)
          rw [mul_inv_rev, h1] }
    have : H ⊔ K ≤ L := sup_le (fun p hp => ⟨p, hp, 1, one_mem _, (mul_one p).symm⟩)
      (fun q hq => ⟨1, one_mem _, q, hq, (one_mul q).symm⟩)
    exact this hg
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact mul_mem (mem_sup_left hp) (mem_sup_right hq)

theorem conj_mem_of_gens {r s : G} (a : G) (hr : a * r * a⁻¹ ∈ zpowers r ⊔ zpowers s)
    (hs : a * s * a⁻¹ ∈ zpowers r ⊔ zpowers s) :
    ∀ g ∈ zpowers r ⊔ zpowers s, a * g * a⁻¹ ∈ zpowers r ⊔ zpowers s := by
  have : zpowers r ⊔ zpowers s ≤ (zpowers r ⊔ zpowers s).comap (MulAut.conj a).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le]
    · exact hr
    · exact hs
  exact fun g hg => this hg

theorem mem_sup_zpowers_iff {K : Subgroup G} {a : G} (hconj : ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hsq : a * a ∈ K) {g : G} : g ∈ K ⊔ zpowers a ↔ g ∈ K ∨ ∃ k ∈ K, g = k * a := by
  constructor
  · intro hg
    let L : Subgroup G :=
      { carrier := {g | g ∈ K ∨ ∃ k ∈ K, g = k * a}
        one_mem' := Or.inl (one_mem _)
        mul_mem' := by
          rintro g₁ g₂ (h1 | ⟨k₁, hk₁, rfl⟩) (h2 | ⟨k₂, hk₂, rfl⟩)
          · exact Or.inl (mul_mem h1 h2)
          · exact Or.inr ⟨g₁ * k₂, mul_mem h1 hk₂, by rw [mul_assoc]⟩
          · refine Or.inr ⟨k₁ * (a * g₂ * a⁻¹), mul_mem hk₁ (hconj _ h2), ?_⟩
            group
          · refine Or.inl ?_
            have : k₁ * a * (k₂ * a) = k₁ * (a * k₂ * a⁻¹) * (a * a) := by group
            rw [this]
            exact mul_mem (mul_mem hk₁ (hconj _ hk₂)) hsq
        inv_mem' := by
          rintro _ (h1 | ⟨k, hk, rfl⟩)
          · exact Or.inl (K.inv_mem h1)
          · refine Or.inr ⟨((a * a)⁻¹) * (a * k⁻¹ * a⁻¹), mul_mem (K.inv_mem hsq) (hconj _ (K.inv_mem hk)), ?_⟩
            group }
    have : K ⊔ zpowers a ≤ L := by
      refine sup_le (fun k hk => Or.inl hk) ?_
      rw [zpowers_le]
      exact Or.inr ⟨1, one_mem _, (one_mul a).symm⟩
    exact this hg
  · rintro (hg | ⟨k, hk, rfl⟩)
    · exact mem_sup_left hg
    · exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_zpowers a))

namespace Rel

variable {a b a' b' t : G} {M : ℕ}

theorem a_t_a_inv (h : Rel a b a' b' t M) : a * t * a⁻¹ = (a * a'⁻¹) * t := by
  have : t * a⁻¹ = a'⁻¹ * t := by
    have h1 : a' * t = t * a := h.ta.symm
    calc t * a⁻¹ = a'⁻¹ * (a' * t) * a⁻¹ := by group
      _ = a'⁻¹ * (t * a) * a⁻¹ := by rw [h1]
      _ = a'⁻¹ * t := by group
  calc a * t * a⁻¹ = a * (t * a⁻¹) := by rw [mul_assoc]
    _ = a * (a'⁻¹ * t) := by rw [this]
    _ = (a * a'⁻¹) * t := by rw [mul_assoc]

theorem a_s2_a_inv (h : Rel a b a' b' t M) : a * (b * b' * t) * a⁻¹ = (a * a') * (b * b' * t) := by
  have h1 : t * a⁻¹ = a'⁻¹ * t := by
    have h1 : a' * t = t * a := h.ta.symm
    calc t * a⁻¹ = a'⁻¹ * (a' * t) * a⁻¹ := by group
      _ = a'⁻¹ * (t * a) * a⁻¹ := by rw [h1]
      _ = a'⁻¹ * t := by group
  have e2 : (b * b') * a'⁻¹ = a' * (b * b') := by simpa using h.b0_zpow_a' (-1)
  calc a * (b * b' * t) * a⁻¹ = a * (b * b') * (t * a⁻¹) := by simp only [mul_assoc]
    _ = a * (b * b') * (a'⁻¹ * t) := by rw [h1]
    _ = a * ((b * b') * a'⁻¹) * t := by simp only [mul_assoc]
    _ = a * (a' * (b * b')) * t := by rw [e2]
    _ = (a * a') * (b * b' * t) := by simp only [mul_assoc]

theorem dl1_mem_D1 (a a' t : G) : a * a'⁻¹ ∈ D1 a a' t := mem_sup_left (mem_zpowers _)

theorem t_mem_D1 (a a' t : G) : t ∈ D1 a a' t := mem_sup_right (mem_zpowers _)

theorem dl2_mem_D2 (a a' b b' t : G) : a * a' ∈ D2 a a' b b' t := mem_sup_left (mem_zpowers _)

theorem s2_mem_D2 (a a' b b' t : G) : b * b' * t ∈ D2 a a' b b' t := mem_sup_right (mem_zpowers _)

theorem a_conj_D1 (h : Rel a b a' b' t M) : ∀ g ∈ D1 a a' t, a * g * a⁻¹ ∈ D1 a a' t := by
  refine conj_mem_of_gens a ?_ ?_
  · rw [mul_inv_eq_iff_eq_mul.2 h.commute_dl1_a.symm.eq]
    exact dl1_mem_D1 a a' t
  · rw [h.a_t_a_inv]
    exact mul_mem (dl1_mem_D1 a a' t) (t_mem_D1 a a' t)

theorem a_conj_D2 (h : Rel a b a' b' t M) : ∀ g ∈ D2 a a' b b' t, a * g * a⁻¹ ∈ D2 a a' b b' t := by
  refine conj_mem_of_gens a ?_ ?_
  · rw [mul_inv_eq_iff_eq_mul.2 h.commute_dl2_a.symm.eq]
    exact dl2_mem_D2 a a' b b' t
  · rw [h.a_s2_a_inv]
    exact mul_mem (dl2_mem_D2 a a' b b' t) (s2_mem_D2 a a' b b' t)

theorem a_conj_sup (h : Rel a b a' b' t M) :
    ∀ g ∈ D1 a a' t ⊔ D2 a a' b b' t, a * g * a⁻¹ ∈ D1 a a' t ⊔ D2 a a' b b' t := by
  have : D1 a a' t ⊔ D2 a a' b b' t ≤
      (D1 a a' t ⊔ D2 a a' b b' t).comap (MulAut.conj a).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro g hg
      exact mem_sup_left (h.a_conj_D1 g hg)
    · intro g hg
      exact mem_sup_right (h.a_conj_D2 g hg)
  exact fun g hg => this hg

theorem a_sq_mem (h : Rel a b a' b' t M) : a * a ∈ D1 a a' t ⊔ D2 a a' b b' t := by
  have : a * a = (a * a'⁻¹) * (a * a') := by
    calc a * a = a * (a'⁻¹ * a') * a := by group
      _ = a * a'⁻¹ * (a' * a) := by group
      _ = (a * a'⁻¹) * (a * a') := by rw [← h.c_aa]
  rw [this]
  exact mul_mem (mem_sup_left (dl1_mem_D1 a a' t)) (mem_sup_right (dl2_mem_D2 a a' b b' t))

theorem commute_s2_dl1 (h : Rel a b a' b' t M) : Commute (b * b' * t) (a * a'⁻¹) :=
  commute_of_conj h.s2_dl1

theorem a_not_mem_sup (h : Rel a b a' b' t M) : a ∉ D1 a a' t ⊔ D2 a a' b b' t := by
  intro ha
  rw [mem_sup_iff_of_commute h.D1_D2_comm] at ha
  obtain ⟨p, hp, q, hq, hpq⟩ := ha
  have : NeZero (2 * M) := ⟨by have := h.one_le; omega⟩
  have hr1 : (a * a'⁻¹) ^ (2 * M) = 1 := h.orderOf_dl1 ▸ pow_orderOf_eq_one _
  have hr2 : (a * a') ^ (2 * M) = 1 := h.orderOf_dl2 ▸ pow_orderOf_eq_one _
  obtain ⟨i, hi⟩ := (mem_dihedral_iff (2 * M) hr1 h.t_sq h.t_dl1).1 hp
  obtain ⟨j, hj⟩ := (mem_dihedral_iff (2 * M) hr2 h.s2_sq h.s2_dl2).1 hq
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj] at hpq
  ·
    have hA : a = a ^ ((i + j : ℕ) : ℤ) * a' ^ ((j : ℤ) - i) := by
      calc a = (a * a'⁻¹) ^ i * (a * a') ^ j := hpq
        _ = (a * a'⁻¹) ^ (i : ℤ) * (a * a') ^ (j : ℤ) := by rw [zpow_natCast, zpow_natCast]
        _ = (a ^ (i : ℤ) * a' ^ (-(i : ℤ))) * (a ^ (j : ℤ) * a' ^ (j : ℤ)) := by
          rw [h.dl1_zpow, h.dl2_zpow]
        _ = a ^ (i : ℤ) * (a' ^ (-(i : ℤ)) * a ^ (j : ℤ)) * a' ^ (j : ℤ) := by
          simp only [mul_assoc]
        _ = a ^ (i : ℤ) * (a ^ (j : ℤ) * a' ^ (-(i : ℤ))) * a' ^ (j : ℤ) := by
          rw [← h.comm_zpow j (-(i : ℤ))]
        _ = a ^ ((i + j : ℕ) : ℤ) * a' ^ ((j : ℤ) - i) := by
          rw [show a ^ (i : ℤ) * (a ^ (j : ℤ) * a' ^ (-(i : ℤ))) * a' ^ (j : ℤ) =
              a ^ (i : ℤ) * a ^ (j : ℤ) * (a' ^ (-(i : ℤ)) * a' ^ (j : ℤ)) by simp only [mul_assoc],
            ← zpow_add, ← zpow_add]
          push_cast
          congr 2
          ring
    have h2 : a ^ (-((i + j : ℕ) : ℤ)) * a = a' ^ ((j : ℤ) - i) := by
      nth_rewrite 2 [hA]
      rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    have h3 : a ^ (-((i + j : ℕ) : ℤ) + 1) = a' ^ ((j : ℤ) - i) := by
      rw [zpow_add, zpow_one]; exact h2
    have d1 := h.dvd_of_zpow_eq_a h3
    have d2 := h.dvd_of_zpow_eq_a' h3
    have h2M : (2 : ℤ) ∣ ((2 * M : ℕ) : ℤ) := ⟨M, by push_cast; ring⟩
    have e1 := dvd_trans h2M d1
    have e2 := dvd_trans h2M d2
    push_cast at e1 e2
    omega
  ·
    have e2 : b * b' * t = ((a * a'⁻¹) ^ i)⁻¹ * a * ((a * a') ^ j)⁻¹ := by
      calc b * b' * t = ((a * a'⁻¹) ^ i)⁻¹ * ((a * a'⁻¹) ^ i * ((b * b' * t) * (a * a') ^ j)) *
            ((a * a') ^ j)⁻¹ := by group
        _ = ((a * a'⁻¹) ^ i)⁻¹ * a * ((a * a') ^ j)⁻¹ := by rw [← hpq]
    apply h.s2_not_comm_a
    rw [e2]
    exact (((h.commute_a_dl1_pow i).inv_right).mul_right (Commute.refl a)).mul_right
      (h.commute_a_dl2_pow j).inv_right
  ·
    have e2 : t = a * ((a * a') ^ j)⁻¹ * ((a * a'⁻¹) ^ i)⁻¹ := by
      calc t = (t * (a * a'⁻¹) ^ i * (a * a') ^ j) * ((a * a') ^ j)⁻¹ * ((a * a'⁻¹) ^ i)⁻¹ := by
            group
        _ = a * ((a * a') ^ j)⁻¹ * ((a * a'⁻¹) ^ i)⁻¹ := by rw [← hpq]
    apply h.t_not_comm_a
    rw [e2]
    exact ((Commute.refl a).mul_right (h.commute_a_dl2_pow j).inv_right).mul_right
      (h.commute_a_dl1_pow i).inv_right
  ·
    have hXS : (b * b' * t) * (a * a'⁻¹) ^ i = (a * a'⁻¹) ^ i * (b * b' * t) :=
      (h.commute_s2_dl1.pow_right i).eq
    have hts : t * (b * b' * t) = b * b' := by
      calc t * (b * b' * t) = (t * (b * b')) * t := (mul_assoc _ _ _).symm
        _ = (b * b') * (t * t) := by rw [h.t_b0]; simp only [mul_assoc]
        _ = b * b' := by rw [h.t_sq, mul_one]
    have e1 : a = (b * b') * (a * a'⁻¹) ^ i * (a * a') ^ j := by
      calc a = t * (a * a'⁻¹) ^ i * ((b * b' * t) * (a * a') ^ j) := hpq
        _ = t * (((a * a'⁻¹) ^ i * (b * b' * t)) * (a * a') ^ j) := by simp only [mul_assoc]
        _ = t * (((b * b' * t) * (a * a'⁻¹) ^ i) * (a * a') ^ j) := by rw [hXS]
        _ = (t * (b * b' * t)) * (a * a'⁻¹) ^ i * (a * a') ^ j := by simp only [mul_assoc]
        _ = (b * b') * (a * a'⁻¹) ^ i * (a * a') ^ j := by rw [hts]
    have e2 : b * b' = a * ((a * a') ^ j)⁻¹ * ((a * a'⁻¹) ^ i)⁻¹ := by
      calc b * b' = ((b * b') * (a * a'⁻¹) ^ i * (a * a') ^ j) * ((a * a') ^ j)⁻¹ *
            ((a * a'⁻¹) ^ i)⁻¹ := by group
        _ = a * ((a * a') ^ j)⁻¹ * ((a * a'⁻¹) ^ i)⁻¹ := by rw [← e1]
    apply h.b0_not_comm_a
    rw [e2]
    exact ((Commute.refl a).mul_right (h.commute_a_dl2_pow j).inv_right).mul_right
      (h.commute_a_dl1_pow i).inv_right

end Rel

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
