module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BQuot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123

open Subgroup

variable {Y : Type} [Group Y] {J₁ J₂ : Subgroup Y}

theorem mem_sup_iff_of_comm (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) {x : Y} :
    x ∈ J₁ ⊔ J₂ ↔ ∃ a ∈ J₁, ∃ b ∈ J₂, a * b = x := by
  constructor
  · intro hx
    let S : Subgroup Y :=
      { carrier := {x | ∃ a ∈ J₁, ∃ b ∈ J₂, a * b = x}
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          exact ⟨a * a', J₁.mul_mem ha ha', b * b', J₂.mul_mem hb hb', by
            calc a * a' * (b * b') = a * (a' * b) * b' := by simp only [mul_assoc]
              _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
              _ = a * b * (a' * b') := by simp only [mul_assoc]⟩
        one_mem' := ⟨1, J₁.one_mem, 1, J₂.one_mem, mul_one 1⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, J₁.inv_mem ha, b⁻¹, J₂.inv_mem hb, by rw [hc a ha b hb, mul_inv_rev]⟩ }
    have hle : J₁ ⊔ J₂ ≤ S := by
      apply sup_le
      · intro a ha
        exact ⟨a, ha, 1, J₂.one_mem, mul_one a⟩
      · intro b hb
        exact ⟨1, J₁.one_mem, b, hb, one_mul b⟩
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact (J₁ ⊔ J₂).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem q_eq_one_of_mem_inf (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (Q₁ : A5Quot J₁) {x : Y}
    (hx₁ : x ∈ J₁) (hx₂ : x ∈ J₂) : Q₁.q ⟨x, hx₁⟩ = 1 := by
  exact Q₁.central_ker ⟨x, hx₁⟩ fun b => Subtype.ext (hc b.1 b.2 x hx₂).symm

theorem q_order_five (Q : A5Quot J₁) {t : Y} (ht : t ∈ J₁) (ho : orderOf t = 5) :
    Q.q ⟨t, ht⟩ ^ 5 = 1 ∧ Q.q ⟨t, ht⟩ ≠ 1 := by
  have h5 : (⟨t, ht⟩ : ↥J₁) ^ 5 = 1 := by
    apply Subtype.ext
    have h := pow_orderOf_eq_one t
    rw [ho] at h
    simpa using h
  refine ⟨?_, fun h1 => ?_⟩
  · rw [← map_pow, h5, map_one]
  · have hcop := Q.ker_coprime ⟨t, ht⟩ h1
    rw [Subgroup.orderOf_mk, ho] at hcop
    have h55 : Nat.gcd 5 5 = 1 := hcop
    rw [Nat.gcd_self] at h55
    omega

theorem q_eq_one_of_mul_mem (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (Q₁ : A5Quot J₁) {t₁ t₂ : Y}
    (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5) {W : Subgroup Y} (hW : IsPGroup 2 W)
    (hd : t₁ * t₂ ∈ normalizer (W : Set Y)) {a b : Y} (ha : a ∈ J₁) (hb : b ∈ J₂) (hab : a * b ∈ W) :
    Q₁.q ⟨a, ha⟩ = 1 := by
  obtain ⟨hc5, hc1⟩ := q_order_five Q₁ ht₁ ho₁
  obtain ⟨H, hHmem⟩ : ∃ H : Subgroup A5, ∀ h : A5, h ∈ H ↔
      ∃ (a' b' : Y) (ha' : a' ∈ J₁) (hb' : b' ∈ J₂), a' * b' ∈ W ∧ Q₁.q ⟨a', ha'⟩ = h := by
    refine ⟨{ carrier := {h | ∃ (a' b' : Y) (ha' : a' ∈ J₁) (hb' : b' ∈ J₂), a' * b' ∈ W ∧
                Q₁.q ⟨a', ha'⟩ = h}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun h => Iff.rfl⟩
    · rintro _ _ ⟨a', b', ha', hb', hab', rfl⟩ ⟨a'', b'', ha'', hb'', hab'', rfl⟩
      refine ⟨a' * a'', b' * b'', J₁.mul_mem ha' ha'', J₂.mul_mem hb' hb'', ?_, ?_⟩
      · have e : a' * a'' * (b' * b'') = (a' * b') * (a'' * b'') := by
          have h1 : a'' * b' = b' * a'' := hc a'' ha'' b' hb'
          calc a' * a'' * (b' * b'') = a' * (a'' * b') * b'' := by group
            _ = a' * (b' * a'') * b'' := by rw [h1]
            _ = (a' * b') * (a'' * b'') := by group
        rw [e]
        exact W.mul_mem hab' hab''
      · exact map_mul Q₁.q ⟨a', ha'⟩ ⟨a'', ha''⟩
    · exact ⟨1, 1, J₁.one_mem, J₂.one_mem, by simpa using W.one_mem, map_one _⟩
    · rintro _ ⟨a', b', ha', hb', hab', rfl⟩
      refine ⟨a'⁻¹, b'⁻¹, J₁.inv_mem ha', J₂.inv_mem hb', ?_, ?_⟩
      · have e : a'⁻¹ * b'⁻¹ = (a' * b')⁻¹ := by
          have h1 : a' * b' = b' * a' := hc a' ha' b' hb'
          calc a'⁻¹ * b'⁻¹ = (b' * a')⁻¹ := by group
            _ = (a' * b')⁻¹ := by rw [h1]
        rw [e]
        exact W.inv_mem hab'
      · exact map_inv Q₁.q ⟨a', ha'⟩
  have hH2 : IsPGroup 2 H := by
    rintro ⟨h, hh⟩
    obtain ⟨a', b', ha', hb', hab', rfl⟩ := (hHmem h).1 hh
    obtain ⟨n, hn⟩ := hW ⟨a' * b', hab'⟩
    have hn' : (a' * b') ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have hcomm : Commute a' b' := hc a' ha' b' hb'
    have h1 : a' ^ (2 ^ n) * b' ^ (2 ^ n) = 1 := by rw [← hcomm.mul_pow]; exact hn'
    have h2 : a' ^ (2 ^ n) ∈ J₂ := by
      have : a' ^ (2 ^ n) = (b' ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact J₂.inv_mem (J₂.pow_mem hb' _)
    have h3 := q_eq_one_of_mem_inf hc Q₁ (J₁.pow_mem ha' (2 ^ n)) h2
    have h4 : (⟨a' ^ (2 ^ n), J₁.pow_mem ha' (2 ^ n)⟩ : ↥J₁) = (⟨a', ha'⟩ : ↥J₁) ^ (2 ^ n) := rfl
    rw [h4, map_pow] at h3
    simpa using h3
  have hHn : ∀ h ∈ H, Q₁.q ⟨t₁, ht₁⟩ * h * (Q₁.q ⟨t₁, ht₁⟩)⁻¹ ∈ H := by
    intro h hh
    obtain ⟨a', b', ha', hb', hab', rfl⟩ := (hHmem h).1 hh
    rw [hHmem]
    have ht₁a : t₁ * a' * t₁⁻¹ ∈ J₁ := J₁.mul_mem (J₁.mul_mem ht₁ ha') (J₁.inv_mem ht₁)
    have ht₂b : t₂ * b' * t₂⁻¹ ∈ J₂ := J₂.mul_mem (J₂.mul_mem ht₂ hb') (J₂.inv_mem ht₂)
    refine ⟨t₁ * a' * t₁⁻¹, t₂ * b' * t₂⁻¹, ht₁a, ht₂b, ?_, ?_⟩
    · have e : t₁ * a' * t₁⁻¹ * (t₂ * b' * t₂⁻¹) = (t₁ * t₂) * (a' * b') * (t₁ * t₂)⁻¹ := by
        have h1 : t₂ * a' = a' * t₂ := (hc a' ha' t₂ ht₂).symm
        have h2 : (t₂ * b' * t₂⁻¹) * t₁⁻¹ = t₁⁻¹ * (t₂ * b' * t₂⁻¹) :=
          (hc t₁⁻¹ (J₁.inv_mem ht₁) _ ht₂b).symm
        calc t₁ * a' * t₁⁻¹ * (t₂ * b' * t₂⁻¹)
            = t₁ * a' * (t₁⁻¹ * (t₂ * b' * t₂⁻¹)) := by group
          _ = t₁ * a' * ((t₂ * b' * t₂⁻¹) * t₁⁻¹) := by rw [h2]
          _ = t₁ * (a' * t₂) * (b' * t₂⁻¹ * t₁⁻¹) := by group
          _ = t₁ * (t₂ * a') * (b' * t₂⁻¹ * t₁⁻¹) := by rw [h1]
          _ = (t₁ * t₂) * (a' * b') * (t₁ * t₂)⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 hd _).1 hab'
    · have e : (⟨t₁ * a' * t₁⁻¹, ht₁a⟩ : ↥J₁) = ⟨t₁, ht₁⟩ * ⟨a', ha'⟩ * ⟨t₁, ht₁⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
  have hbot := a5_two_subgroup hc5 hc1 hH2 hHn
  have hmem : Q₁.q ⟨a, ha⟩ ∈ H := (hHmem _).2 ⟨a, b, ha, hb, hab, rfl⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem commutes_d_of_mem_W (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (Q₁ : A5Quot J₁) (Q₂ : A5Quot J₂)
    {t₁ t₂ : Y} (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5) (ho₂ : orderOf t₂ = 5)
    {W : Subgroup Y} (hW : IsPGroup 2 W) (hd : t₁ * t₂ ∈ normalizer (W : Set Y)) {v : Y} (hv : v ∈ W)
    (hvJ : v ∈ J₁ ⊔ J₂) : v * (t₁ * t₂) = (t₁ * t₂) * v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hc).1 hvJ
  have h1 : Q₁.q ⟨a, ha⟩ = 1 := q_eq_one_of_mul_mem hc Q₁ ht₁ ht₂ ho₁ hW hd ha hb hv
  have hc' : ∀ b ∈ J₂, ∀ a ∈ J₁, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hd' : t₂ * t₁ ∈ normalizer (W : Set Y) := by rwa [← hc t₁ ht₁ t₂ ht₂]
  have hv' : b * a ∈ W := by rwa [← hc a ha b hb]
  have h2 : Q₂.q ⟨b, hb⟩ = 1 := q_eq_one_of_mul_mem hc' Q₂ ht₂ ht₁ ho₂ hW hd' hb ha hv'
  have ha' := Q₁.ker_central ⟨a, ha⟩ h1
  have hb' := Q₂.ker_central ⟨b, hb⟩ h2
  have e1 : a * t₁ = t₁ * a := congrArg Subtype.val (ha' ⟨t₁, ht₁⟩)
  have e2 : b * t₂ = t₂ * b := congrArg Subtype.val (hb' ⟨t₂, ht₂⟩)
  have e3 : b * t₁ = t₁ * b := (hc t₁ ht₁ b hb).symm
  have e4 : a * t₂ = t₂ * a := hc a ha t₂ ht₂
  calc a * b * (t₁ * t₂) = a * (b * t₁) * t₂ := by group
    _ = a * (t₁ * b) * t₂ := by rw [e3]
    _ = (a * t₁) * (b * t₂) := by group
    _ = (t₁ * a) * (t₂ * b) := by rw [e1, e2]
    _ = t₁ * (a * t₂) * b := by group
    _ = t₁ * (t₂ * a) * b := by rw [e4]
    _ = (t₁ * t₂) * (a * b) := by group

theorem not_centralizes (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (Q₁ : A5Quot J₁) {t₁ t₂ : Y}
    (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5) :
    ∃ a ∈ J₁, a * (t₁ * t₂) ≠ (t₁ * t₂) * a := by
  by_contra hne
  push_neg at hne
  have hcent : Q₁.q ⟨t₁, ht₁⟩ = 1 := by
    apply Q₁.central_ker ⟨t₁, ht₁⟩
    intro b
    apply Subtype.ext
    show t₁ * b.1 = b.1 * t₁
    have h1 := hne b.1 b.2
    have h2 := hc b.1 b.2 t₂ ht₂
    have key : b.1 * t₁ * t₂ = t₁ * b.1 * t₂ := by
      calc b.1 * t₁ * t₂ = b.1 * (t₁ * t₂) := by rw [mul_assoc]
        _ = t₁ * t₂ * b.1 := h1
        _ = t₁ * (t₂ * b.1) := by rw [mul_assoc]
        _ = t₁ * (b.1 * t₂) := by rw [h2]
        _ = t₁ * b.1 * t₂ := by rw [mul_assoc]
    exact (mul_right_cancel key).symm
  exact (q_order_five Q₁ ht₁ ho₁).2 hcent

theorem q_commute_of_commute_d (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (Q₁ : A5Quot J₁) {t₁ t₂ : Y}
    (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) {a b : Y} (ha : a ∈ J₁) (hb : b ∈ J₂)
    (h : (a * b) * (t₁ * t₂) = (t₁ * t₂) * (a * b)) :
    Q₁.q ⟨a, ha⟩ * Q₁.q ⟨t₁, ht₁⟩ = Q₁.q ⟨t₁, ht₁⟩ * Q₁.q ⟨a, ha⟩ := by
  have hbt₁ : t₁ * b = b * t₁ := hc t₁ ht₁ b hb
  have hat₂ : a * t₂ = t₂ * a := hc a ha t₂ ht₂
  have e1 : a * t₁ * (b * t₂) = a * b * (t₁ * t₂) := by
    rw [mul_assoc a t₁, ← mul_assoc t₁ b t₂, hbt₁, mul_assoc b t₁ t₂, ← mul_assoc a b]
  have e3 : t₁ * a * (t₂ * b) = t₁ * t₂ * (a * b) := by
    rw [mul_assoc t₁ a, ← mul_assoc a t₂ b, hat₂, mul_assoc t₂ a b, mul_assoc t₁ t₂ (a * b)]
  have hx : (t₁ * a)⁻¹ * (a * t₁) * (b * t₂) = t₂ * b := by
    rw [mul_assoc (t₁ * a)⁻¹ (a * t₁) (b * t₂), e1, h, ← e3, inv_mul_cancel_left]
  have hxeq : (t₁ * a)⁻¹ * (a * t₁) = t₂ * b * (b * t₂)⁻¹ := eq_mul_inv_of_mul_eq hx
  have hxJ₁ : (t₁ * a)⁻¹ * (a * t₁) ∈ J₁ :=
    J₁.mul_mem (J₁.inv_mem (J₁.mul_mem ht₁ ha)) (J₁.mul_mem ha ht₁)
  have hxJ₂ : (t₁ * a)⁻¹ * (a * t₁) ∈ J₂ := by
    rw [hxeq]
    exact J₂.mul_mem (J₂.mul_mem ht₂ hb) (J₂.inv_mem (J₂.mul_mem hb ht₂))
  have hq := q_eq_one_of_mem_inf hc Q₁ hxJ₁ hxJ₂
  have hsub : (⟨(t₁ * a)⁻¹ * (a * t₁), hxJ₁⟩ : ↥J₁) =
      (⟨t₁, ht₁⟩ * ⟨a, ha⟩)⁻¹ * (⟨a, ha⟩ * ⟨t₁, ht₁⟩) := rfl
  rw [hsub] at hq
  simp only [map_mul, map_inv] at hq
  exact (inv_mul_eq_one.1 hq).symm

theorem tbaux_five_split {J : Subgroup Y} (Q : A5Quot J) {t a : Y} (ht : t ∈ J) (ha : a ∈ J)
    (ho : orderOf t = 5)
    (hcomm : Q.q ⟨a, ha⟩ * Q.q ⟨t, ht⟩ = Q.q ⟨t, ht⟩ * Q.q ⟨a, ha⟩) :
    ∃ (k : ℕ) (w : Y), w ∈ J ∧ a = t ^ k * w ∧ (∀ b ∈ J, w * b = b * w) ∧
      Nat.Coprime (orderOf w) 5 := by
  obtain ⟨h5, hne⟩ := q_order_five Q ht ho
  obtain ⟨k, hk⟩ := a5_centralizer (Q.q ⟨t, ht⟩) (Q.q ⟨a, ha⟩) h5 hne hcomm
  set T : ↥J := ⟨t, ht⟩
  set A : ↥J := ⟨a, ha⟩
  set W : ↥J := (T ^ (k : ℕ))⁻¹ * A with hW
  have hqW : Q.q W = 1 := by
    rw [hW, map_mul, map_inv, map_pow, hk]
    exact inv_mul_cancel _
  refine ⟨k, (W : Y), W.2, ?_, ?_, ?_⟩
  · have h1 : A = T ^ (k : ℕ) * W := by rw [hW]; exact (mul_inv_cancel_left _ _).symm
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · intro b hb
    have h3 := Q.ker_central W hqW ⟨b, hb⟩
    exact congrArg Subtype.val h3
  · have h4 := Q.ker_coprime W hqW
    rwa [← Subgroup.orderOf_coe] at h4

theorem five_elem_mem (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (Q₁ : A5Quot J₁) (Q₂ : A5Quot J₂)
    {t₁ t₂ : Y} (ht₁ : t₁ ∈ J₁) (ht₂ : t₂ ∈ J₂) (ho₁ : orderOf t₁ = 5) (ho₂ : orderOf t₂ = 5)
    {z : Y} (hz : z ∈ J₁ ⊔ J₂) (hzd : z * (t₁ * t₂) = (t₁ * t₂) * z) (hz5 : z ^ 5 = 1) :
    z ∈ zpowers t₁ ⊔ zpowers t₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hc).1 hz
  have hc' : ∀ a ∈ J₂, ∀ b ∈ J₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hab : a * b = b * a := hc a ha b hb
  have htt : t₁ * t₂ = t₂ * t₁ := hc t₁ ht₁ t₂ ht₂
  have h1 := q_commute_of_commute_d hc Q₁ ht₁ ht₂ ha hb hzd
  have h2 := q_commute_of_commute_d hc' Q₂ ht₂ ht₁ hb ha
    (by rw [← hab, ← htt]; exact hzd)
  obtain ⟨k₁, z₁, hz₁J, ha_eq, hz₁c, hz₁o⟩ := tbaux_five_split Q₁ ht₁ ha ho₁ h1
  obtain ⟨k₂, z₂, hz₂J, hb_eq, hz₂c, hz₂o⟩ := tbaux_five_split Q₂ ht₂ hb ho₂ h2
  have hs₁ : t₁ ^ k₁ ∈ J₁ := J₁.pow_mem ht₁ k₁
  have hs₂ : t₂ ^ k₂ ∈ J₂ := J₂.pow_mem ht₂ k₂
  have c_s₁s₂ : Commute (t₁ ^ k₁) (t₂ ^ k₂) := hc _ hs₁ _ hs₂
  have c_s₁z₁ : Commute (t₁ ^ k₁) z₁ := (hz₁c _ hs₁).symm
  have c_s₁z₂ : Commute (t₁ ^ k₁) z₂ := hc _ hs₁ _ hz₂J
  have c_s₂z₁ : Commute (t₂ ^ k₂) z₁ := (hc _ hz₁J _ hs₂).symm
  have c_s₂z₂ : Commute (t₂ ^ k₂) z₂ := (hz₂c _ hs₂).symm
  have c_z₁z₂ : Commute z₁ z₂ := hc _ hz₁J _ hz₂J
  have hS : Commute (t₁ ^ k₁ * t₂ ^ k₂) (z₁ * z₂) :=
    (c_s₁z₁.mul_right c_s₁z₂).mul_left (c_s₂z₁.mul_right c_s₂z₂)
  have hzeq : a * b = (t₁ ^ k₁ * t₂ ^ k₂) * (z₁ * z₂) := by
    rw [ha_eq, hb_eq]
    calc (t₁ ^ k₁ * z₁) * (t₂ ^ k₂ * z₂) = t₁ ^ k₁ * (z₁ * t₂ ^ k₂) * z₂ := by
          simp only [mul_assoc]
      _ = t₁ ^ k₁ * (t₂ ^ k₂ * z₁) * z₂ := by rw [c_s₂z₁.eq.symm]
      _ = (t₁ ^ k₁ * t₂ ^ k₂) * (z₁ * z₂) := by simp only [mul_assoc]
  have hp₁ : (t₁ ^ k₁) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← ho₁, pow_orderOf_eq_one, one_pow]
  have hp₂ : (t₂ ^ k₂) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← ho₂, pow_orderOf_eq_one, one_pow]
  have hw5 : (z₁ * z₂) ^ 5 = 1 := by
    rw [hzeq, hS.mul_pow, c_s₁s₂.mul_pow, hp₁, hp₂, one_mul, one_mul] at hz5
    exact hz5
  have hcop : Nat.Coprime (orderOf (z₁ * z₂)) 5 :=
    Nat.Coprime.coprime_dvd_left c_z₁z₂.orderOf_mul_dvd_mul_orderOf (Nat.Coprime.mul_left hz₁o hz₂o)
  have hord : orderOf (z₁ * z₂) = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hw5)
  have hw1 : z₁ * z₂ = 1 := orderOf_eq_one_iff.1 hord
  rw [hzeq, hw1, mul_one]
  exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (mem_zpowers t₁) k₁)
    (Subgroup.pow_mem _ (mem_zpowers t₂) k₂)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123
