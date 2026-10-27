module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.AGLEmbedding.SymThreeCentralExt

open Subgroup

variable {Q : Type} [Group Q] [Finite Q] (f : Q →* Equiv.Perm (Fin 3))

theorem eq_one_of_sq_of_pow_odd {k : Q} {n : ℕ} (hn : Odd n) (hk : k ^ n = 1) (h2 : k ^ 2 = 1) :
    k = 1 := by
  have h1 : orderOf k ∣ Nat.gcd n 2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one h2)
  have hg : Nat.gcd n 2 = 1 := by
    rcases hn with ⟨m, rfl⟩
    simp [Nat.gcd_comm]
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem exists_involution_lift (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {τ : Equiv.Perm (Fin 3)} (hτ : τ ^ 2 = 1) : ∃ t : Q, t ^ 2 = 1 ∧ f t = τ := by
  obtain ⟨q, rfl⟩ := hf τ
  set n := Nat.card f.ker
  have hq2 : q ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hτ]
  refine ⟨q ^ n, ?_, ?_⟩
  · have h := pow_card_eq_one' (G := ↥f.ker) (x := ⟨q ^ 2, hq2⟩)
    have h' := congrArg Subtype.val h
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h'
    rw [← pow_mul, mul_comm, pow_mul]
    exact h'
  · obtain ⟨m, hm⟩ := hodd
    rw [map_pow, hm, pow_succ, pow_mul, hτ, one_pow, one_mul]

theorem eq_of_involution (hodd : Odd (Nat.card f.ker))
    (hc : ∀ k ∈ f.ker, ∀ q : Q, k * q = q * k) {t t' : Q} (ht : t ^ 2 = 1) (ht' : t' ^ 2 = 1)
    (he : f t = f t') : t = t' := by
  have hk : t⁻¹ * t' ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  set k := t⁻¹ * t' with hkdef
  have hkt : t' = t * k := by rw [hkdef]; group
  have hk2 : k ^ 2 = 1 := by
    have : t' ^ 2 = t ^ 2 * k ^ 2 := by
      have hkt' : k * t = t * k := hc k hk t
      calc t' ^ 2 = t * (k * t) * k := by rw [hkt, sq]; group
        _ = t * (t * k) * k := by rw [hkt']
        _ = t ^ 2 * k ^ 2 := by simp only [sq, mul_assoc]
    rw [ht', ht, one_mul] at this
    exact this.symm
  have hkn : k ^ Nat.card f.ker = 1 := by
    have h := pow_card_eq_one' (G := ↥f.ker) (x := ⟨k, hk⟩)
    have h' := congrArg Subtype.val h
    simpa using h'
  have hk1 := eq_one_of_sq_of_pow_odd hodd hkn hk2
  rw [hkt, hk1, mul_one]

abbrev τ₁ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
abbrev τ₂ : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem exists_normal_symThree (hf : Function.Surjective f)
    (hc : ∀ k ∈ f.ker, ∀ q : Q, k * q = q * k) (hodd : Odd (Nat.card f.ker)) :
    ∃ T : Subgroup Q, T.Normal ∧ Nonempty (↥T ≃* Equiv.Perm (Fin 3)) ∧ ¬ 2 ∣ T.index := by
  classical
  obtain ⟨t₁, h1, hf1⟩ := exists_involution_lift f hf hodd (τ := τ₁) (by decide)
  obtain ⟨t₂, h2, hf2⟩ := exists_involution_lift f hf hodd (τ := τ₂) (by decide)
  have h1' : t₁ * t₁ = 1 := by rw [← sq, h1]
  have h2' : t₂ * t₂ = 1 := by rw [← sq, h2]
  have hbr : t₁ * t₂ * t₁ = t₂ * t₁ * t₂ := by
    refine eq_of_involution f hodd hc ?_ ?_ ?_
    · rw [sq]
      calc t₁ * t₂ * t₁ * (t₁ * t₂ * t₁) = t₁ * t₂ * (t₁ * t₁) * t₂ * t₁ := by group
        _ = 1 := by rw [h1', mul_one, mul_assoc t₁ t₂ t₂, h2', mul_one, h1']
    · rw [sq]
      calc t₂ * t₁ * t₂ * (t₂ * t₁ * t₂) = t₂ * t₁ * (t₂ * t₂) * t₁ * t₂ := by group
        _ = 1 := by rw [h2', mul_one, mul_assoc t₂ t₁ t₁, h1', mul_one, h2']
    · rw [map_mul, map_mul, map_mul, map_mul, hf1, hf2]
      decide
  let E : Finset Q := {1, t₁, t₂, t₁ * t₂, t₂ * t₁, t₁ * t₂ * t₁}
  set T := closure ({t₁, t₂} : Set Q) with hT
  have key : ∀ y ∈ E, t₁ * y ∈ E ∧ t₂ * y ∈ E := by
    intro y hy
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simp [E], by simp [E]⟩
    · refine ⟨by rw [h1']; simp [E], by simp [E]⟩
    · refine ⟨by simp [E], by rw [h2']; simp [E]⟩
    · refine ⟨by rw [← mul_assoc, h1', one_mul]; simp [E], ?_⟩
      rw [← mul_assoc, ← hbr]; simp [E]
    · refine ⟨by rw [← mul_assoc]; simp [E], by rw [← mul_assoc, h2', one_mul]; simp [E]⟩
    · refine ⟨?_, ?_⟩
      · rw [show t₁ * (t₁ * t₂ * t₁) = t₁ * t₁ * (t₂ * t₁) by group, h1', one_mul]; simp [E]
      · rw [hbr, show t₂ * (t₂ * t₁ * t₂) = t₂ * t₂ * (t₁ * t₂) by group, h2', one_mul]
        simp [E]
  have hinv1 : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right h1'
  have hinv2 : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right h2'
  have hE : ∀ x ∈ T, x ∈ E := by
    intro x hx
    induction hx using closure_induction_left with
    | one => simp [E]
    | mul_left a ha y _ ih =>
      rcases ha with rfl | rfl
      · exact (key y ih).1
      · exact (key y ih).2
    | inv_mul_cancel a ha y _ ih =>
      rcases ha with rfl | rfl
      · rw [hinv1]; exact (key y ih).1
      · rw [hinv2]; exact (key y ih).2
  have hT6 : Nat.card T ≤ 6 := by
    have hsub : (T : Set Q) ⊆ (E : Set Q) := fun x hx => hE x hx
    calc Nat.card T = (T : Set Q).ncard := (Nat.card_coe_set_eq _)
      _ ≤ (E : Set Q).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet E)
      _ = E.card := Set.ncard_coe_finset E
      _ ≤ 6 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp
  have hmap : T.map f = ⊤ := by
    have hgen : closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
      rw [eq_top_iff]
      intro σ _
      have hmem : ∀ σ : Equiv.Perm (Fin 3), σ = 1 ∨ σ = τ₁ ∨ σ = τ₂ ∨ σ = τ₁ * τ₂ ∨
          σ = τ₂ * τ₁ ∨ σ = τ₁ * τ₂ * τ₁ := by decide
      have g1 : τ₁ ∈ closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 3))) := subset_closure (by simp)
      have g2 : τ₂ ∈ closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 3))) := subset_closure (by simp)
      rcases hmem σ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact g1
      · exact g2
      · exact mul_mem g1 g2
      · exact mul_mem g2 g1
      · exact mul_mem (mul_mem g1 g2) g1
    rw [hT, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, hf1, hf2, hgen]
  have hcardS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  set φ : ↥T →* Equiv.Perm (Fin 3) := f.comp T.subtype with hφ
  have hφs : Function.Surjective φ := by
    intro σ
    have : σ ∈ T.map f := hmap ▸ mem_top σ
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcardT : Nat.card T = 6 := by
    refine le_antisymm hT6 ?_
    rw [← hcardS]
    exact Nat.card_le_card_of_surjective φ hφs
  have hφb : Function.Bijective φ := by
    rw [Nat.bijective_iff_surjective_and_card]
    exact ⟨hφs, by rw [hcardT, hcardS]⟩
  refine ⟨T, ?_, ⟨MulEquiv.ofBijective φ hφb⟩, ?_⟩
  ·
    have hinvol : ∀ u : Q, u ^ 2 = 1 → f u ≠ 1 → u ∈ T := by
      intro u hu hu1
      have hcase : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 → σ ≠ 1 →
          σ = τ₁ ∨ σ = τ₂ ∨ σ = τ₁ * τ₂ * τ₁ := by decide
      have hfu : f u ^ 2 = 1 := by rw [← map_pow, hu, map_one]
      have g1 : t₁ ∈ T := subset_closure (by simp)
      have g2 : t₂ ∈ T := subset_closure (by simp)
      rcases hcase _ hfu hu1 with h | h | h
      · rw [eq_of_involution f hodd hc hu h1 (h.trans hf1.symm)]; exact g1
      · rw [eq_of_involution f hodd hc hu h2 (h.trans hf2.symm)]; exact g2
      · have h3 : (t₁ * t₂ * t₁) ^ 2 = 1 := by
          rw [sq]
          calc t₁ * t₂ * t₁ * (t₁ * t₂ * t₁) = t₁ * t₂ * (t₁ * t₁) * t₂ * t₁ := by group
            _ = 1 := by rw [h1', mul_one, mul_assoc t₁ t₂ t₂, h2', mul_one, h1']
        rw [eq_of_involution f hodd hc hu h3 (by rw [h, map_mul, map_mul, hf1, hf2])]
        exact mul_mem (mul_mem g1 g2) g1
    refine ⟨fun x hx q => ?_⟩
    induction hx using closure_induction with
    | mem a ha =>
      have ha2 : a ^ 2 = 1 := by rcases ha with rfl | rfl <;> assumption
      have ha1 : f a ≠ 1 := by rcases ha with rfl | rfl <;> simp [hf1, hf2]
      refine hinvol _ ?_ ?_
      · rw [conj_pow, ha2]; group
      · rw [map_mul, map_mul, map_inv]
        intro h
        apply ha1
        have := congrArg (fun σ => (f q)⁻¹ * σ * f q) h
        simpa [mul_assoc] using this
    | one => simp
    | mul a b _ _ iha ihb =>
      have : q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) := by group
      rw [this]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have : q * a⁻¹ * q⁻¹ = (q * a * q⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem iha
  ·
    have hQ : Nat.card Q = 6 * Nat.card f.ker := by
      rw [card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hcardS]
    have hTi := card_mul_index T
    rw [hcardT, hQ] at hTi
    have : T.index = Nat.card f.ker := by omega
    rw [this]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.AGLEmbedding.SymThreeCentralExt
