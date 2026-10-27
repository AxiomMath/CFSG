module

public import Certificates.Data.Kernel.Fi22Rank.Defs
public import CFSG.Certificates.Kernel.E27Lie.SoundRep

public section

namespace CFSG.KS.Fi22Rank

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Rank CFSG.KS.E27Lie
open CFSG.HardMathSupport.Foote.E27 Subgroup

variable {G : Type*} [Group G]

theorem ne_of_notB {a b : ℕ} (h : CFSG.KC.Ord.notB (Nat.beq a b) = true) : a ≠ b := by
  rw [notB_eq, Bool.not_eq_true'] at h
  exact Nat.ne_of_beq_eq_false h

theorem distinct4_spec {a b c d : ℕ} (h : distinct4 a b c d = true) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  unfold distinct4 at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h
  exact ⟨ne_of_notB h1, ne_of_notB h2, ne_of_notB h3, ne_of_notB h4, ne_of_notB h5,
    ne_of_notB h6⟩

theorem card_inf_centralizer_le {T : Subgroup G} (hT : Nat.card T = 729) {x : G} (hx : x ∈ T)
    (h : Fin 4 → G) (hh : ∀ t, h t ∈ T)
    (hd : ∀ s t, h s * x * (h s)⁻¹ = h t * x * (h t)⁻¹ → s = t) :
    Nat.card ↥(T ⊓ centralizer ({x} : Set G)) ≤ 81 := by
  set C := T ⊓ centralizer ({x} : Set G)
  have hfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  let F : Fin 4 × C → T := fun p => ⟨h p.1 * p.2, T.mul_mem (hh p.1) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨s, c⟩ ⟨t, c'⟩ e
    have e' : h s * (c : G) = h t * c' := congrArg Subtype.val e
    have hc : (c : G) * x = x * c := (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2)
    have hc' : (c' : G) * x = x * c' :=
      (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c'.2).2)
    have hconj : h s * x * (h s)⁻¹ = h t * x * (h t)⁻¹ := by
      have e1 : h s = h t * c' * (c : G)⁻¹ := by rw [← e', mul_inv_cancel_right]
      rw [e1]
      calc h t * c' * (c : G)⁻¹ * x * (h t * c' * (c : G)⁻¹)⁻¹
          = h t * (c' * ((c : G)⁻¹ * x * c) * (c' : G)⁻¹) * (h t)⁻¹ := by group
        _ = h t * x * (h t)⁻¹ := by
          have : (c : G)⁻¹ * x * c = x := by
            rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this, hc', mul_inv_cancel_right]
    have hst := hd s t hconj
    subst hst
    have : (c : G) = c' := mul_left_cancel e'
    exact Prod.ext rfl (Subtype.ext this)
  have hle := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin, hT] at hle
  have hdvd : Nat.card C ∣ 3 ^ 6 := by
    rw [show (3 : ℕ) ^ 6 = 729 by norm_num, ← hT]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hkeq] at hle ⊢
  have : k ≤ 4 := by
    by_contra hlt
    have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
    _ = 81 := by norm_num

variable {R : ℕ → G → Prop} {mm : ℕ → ℕ → ℕ} {ONE : ℕ} {g : ℕ → G}
variable {gk key pp pj : ℕ → ℕ} {m n : ℕ}

theorem card_lt_of_checks [Finite G] (hR : KeyRep R mm ONE) (hg : ∀ j < m, R (gk j) (g j))
    (ht : ∀ i < n, treeC mm key pp pj gk ONE m i = true)
    {lt : ℕ → ℕ → ℕ} (hl : ∀ i < n, ∀ j < m, leftC mm key lt gk n j i = true)
    {sg : ℕ → ℕ} (hs : ∀ q < n, sortC key sg n q = true)
    {W CI REP SM BL BP : ℕ → ℕ} {H Y : ℕ → ℕ → ℕ} {nr nb : ℕ}
    (hk : ∀ a < n, killC mm key W CI REP n nr a = true)
    (hsm : ∀ c < nr, smallC mm key REP SM H Y n c = true)
    (hb : ∀ a < n, bigC CI SM BL BP nb a = true) (hn : n = 729) (hnb : nb < 243)
    {Gs : Set G} (hGs : ∀ x ∈ Gs, ∃ i < n, R (key i) x)
    (A : Subgroup G) (hA : A ≤ Subgroup.closure Gs) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A < 243 := by
  have hT := tabData_ofR hR hg ht hl hs
  have hE := tree_specR hR hg ht
  set E := tabElt g (parOf n pp pj) with hEdef
  obtain ⟨T, hTmem, -⟩ := hT.exists_subgroup (by omega)
  have hcT : Nat.card T = 729 := (hT.card_subgroup hTmem).trans hn
  have prod : ∀ a < n, ∀ b < n, R (mm (key a) (key b)) (E a * E b) := fun a ha b hb =>
    hR.mul (hE a ha).2 (hE b hb).2
  have prodEq : ∀ a < n, ∀ b < n, ∀ c < n, ∀ e < n,
      mm (key a) (key b) = mm (key c) (key e) → E a * E b = E c * E e := by
    intro a ha b hb c hc' e he h
    have h1 := prod a ha b hb
    rw [h] at h1
    exact hR.elt h1 (prod c hc' e he)
  have hET : ∀ i < n, E i ∈ T := fun i hi => (hTmem _).2 ⟨i, hi, rfl⟩
  have hAT : A ≤ T := by
    refine le_trans hA ((Subgroup.closure_le T).2 fun x hx => ?_)
    obtain ⟨i, hi, hr⟩ := hGs x hx
    rw [← hR.elt (hE i hi).2 hr]
    exact hET i hi
  have hsmall : ∀ a < n, a ≠ 0 → SM (CI a) = 1 →
      Nat.card ↥(T ⊓ centralizer ({E a} : Set G)) ≤ 81 := by
    intro a ha ha0 hsa
    have h := hk a ha
    unfold killC at h
    have hb0 : (Nat.beq a 0 = true) = False := by simp only [Nat.beq_eq, ha0]
    rw [bRec_eq, if_neg (by rw [hb0]; exact id), sB_eq, sB_eq, bRec_eq] at h
    split_ifs at h with h1
    rw [bRec_eq] at h
    split_ifs at h with h2
    rw [sB_eq] at h
    have hw := blt_of h1
    have hci := blt_of h2
    set c := CI a with hc
    have hrc := hsm c hci
    unfold smallC at hrc
    rw [bRec_eq, if_pos (by rw [hsa]; rfl), sB_eq] at hrc
    obtain ⟨hr, hrc⟩ := (bAnd_iff _ _).1 hrc
    obtain ⟨hd4, hall⟩ := (bAnd_iff _ _).1 hrc
    obtain ⟨h01, h02, h03, h12, h13, h23⟩ := distinct4_spec hd4
    have hr' := blt_of hr
    have hconj : E (W a) * E a = E (REP c) * E (W a) := prodEq _ hw _ ha _ hr' _ hw (beq_of h)
    rw [card_inf_centralizer_conj (hET _ hw) hconj]
    have hall' : ∀ t < 3, H c t < n ∧ Y c t < n ∧
        E (H c t) * E (REP c) = E (Y c t) * E (H c t) := by
      intro t ht'
      have h5 := allN_spec hall t ht'
      rw [sB_eq, sB_eq] at h5
      obtain ⟨h6, h78⟩ := (bAnd_iff _ _).1 h5
      obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h78
      exact ⟨blt_of h6, blt_of h7, prodEq _ (blt_of h6) _ hr' _ (blt_of h7) _ (blt_of h6)
        (beq_of h8)⟩
    let hf : Fin 4 → G := fun t => if ht0 : t.val = 0 then 1 else E (H c (t.val - 1))
    let yf : Fin 4 → ℕ := fun t => if t.val = 0 then REP c else Y c (t.val - 1)
    have hyf : ∀ t, yf t < n ∧ hf t * E (REP c) * (hf t)⁻¹ = E (yf t) := by
      intro t
      by_cases ht0 : t.val = 0
      · have e1 : hf t = 1 := by simp only [hf, dif_pos ht0]
        have e2 : yf t = REP c := by simp only [yf, if_pos ht0]
        rw [e1, e2, one_mul, inv_one, mul_one]
        exact ⟨hr', rfl⟩
      · have e1 : hf t = E (H c (t.val - 1)) := by simp only [hf, dif_neg ht0]
        have e2 : yf t = Y c (t.val - 1) := by simp only [yf, if_neg ht0]
        obtain ⟨-, hy, e⟩ := hall' (t.val - 1) (by omega)
        rw [e1, e2]
        exact ⟨hy, by rw [e, mul_inv_cancel_right]⟩
    refine card_inf_centralizer_le hcT (hET _ hr') hf (fun t => ?_) (fun s t e => ?_)
    · by_cases ht0 : t.val = 0
      · simp only [hf, dif_pos ht0]
        exact T.one_mem
      · simp only [hf, dif_neg ht0]
        exact hET _ (hall' (t.val - 1) (by omega)).1
    · rw [(hyf s).2, (hyf t).2] at e
      have e' := hT.inj _ (hyf s).1 _ (hyf t).1 e
      fin_cases s <;> fin_cases t <;> simp [yf] at e' ⊢ <;>
        first
        | exact absurd e' h01 | exact absurd e'.symm h01 | exact absurd e' h02
        | exact absurd e'.symm h02 | exact absurd e' h03 | exact absurd e'.symm h03
        | exact absurd e' h12 | exact absurd e'.symm h12 | exact absurd e' h13
        | exact absurd e'.symm h13 | exact absurd e' h23 | exact absurd e'.symm h23
  by_contra hge
  push Not at hge
  have hbig : ∀ a ∈ A, ∃ i < n, E i = a ∧ BP i < nb ∧ BL (BP i) = i := by
    intro a haA
    obtain ⟨i, hi, rfl⟩ := (hTmem a).1 (hAT haA)
    refine ⟨i, hi, rfl, ?_⟩
    have hAC : A ≤ T ⊓ centralizer ({E i} : Set G) := fun b hbA =>
      Subgroup.mem_inf.2 ⟨hAT hbA, mem_centralizer_singleton_iff.2 (hcomm b hbA _ haA)⟩
    have h243 : 243 ≤ Nat.card ↥(T ⊓ centralizer ({E i} : Set G)) := by
      have hfin : Finite T := Nat.finite_of_card_ne_zero (by rw [hcT]; norm_num)
      have : Finite ↥(T ⊓ centralizer ({E i} : Set G)) :=
        Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left :
          T ⊓ centralizer ({E i} : Set G) ≤ T))
      exact hge.trans (Subgroup.card_le_of_le hAC)
    have h := hb i hi
    unfold bigC at h
    rw [bRec_eq] at h
    split_ifs at h with h1
    · obtain ⟨h1a, h1b⟩ := (bAnd_iff _ _).1 h1
      have := hsmall i hi (ne_of_notB h1a) (beq_of h1b)
      omega
    · rw [sB_eq] at h
      obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
      exact ⟨blt_of h2, beq_of h3⟩
  choose f hf hfE hfp hfl using hbig
  let F : A → Fin nb := fun a => ⟨BP (f a a.2), hfp a a.2⟩
  have hF : Function.Injective F := by
    rintro ⟨a, ha⟩ ⟨b, hb'⟩ e
    have e1 : BP (f a ha) = BP (f b hb') := congrArg Fin.val e
    have e2 : f a ha = f b hb' := by rw [← hfl a ha, ← hfl b hb', e1]
    apply Subtype.ext
    change a = b
    rw [← hfE a ha, ← hfE b hb', e2]
  have hfinA : Finite A := Finite.of_injective F hF
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card (α := Fin nb), Fintype.card_fin] at this
  omega

end CFSG.KS.Fi22Rank

end
