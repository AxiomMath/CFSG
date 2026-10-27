module

public import CFSG.Permutation.FinPackAll6
public import CFSG.Permutation.FinPackComm
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack

open Equiv Finset CFSG.Permutation.FinPack

@[expose] def ID6 : ℕ := 5517840

theorem enc_one6 : enc (1 : Perm (Fin 6)) = ID6 := by decide +kernel

theorem enc_mul6 (σ τ : Perm (Fin 6)) : enc (σ * τ) = mulK 6 (enc σ) (enc τ) :=
  enc_mul (by norm_num) σ τ

theorem eq_one_iff (σ : Perm (Fin 6)) : σ = 1 ↔ Nat.beq (enc σ) ID6 = true := by
  rw [Nat.beq_eq, ← enc_one6]
  exact ⟨fun h => h ▸ rfl, enc_inj (by norm_num)⟩

theorem commute_iff (σ τ : Perm (Fin 6)) :
    σ * τ = τ * σ ↔ Nat.beq (mulK 6 (enc σ) (enc τ)) (mulK 6 (enc τ) (enc σ)) = true := by
  rw [Nat.beq_eq, ← enc_mul6, ← enc_mul6]
  exact ⟨congrArg enc, enc_inj (by norm_num)⟩

@[expose] noncomputable def ordAux (c : ℕ) (n : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ r x => Nat.beq x ID6 || r (mulK 6 c x)) n

@[expose] noncomputable def ordB (c : ℕ) : Bool := ordAux c 4 (mulK 6 c c)

theorem check_ord : allK (fun p => ordB (lo6 p)) evenCodes6 = true := by decide +kernel

theorem orders_of_sign (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 ∨ σ ^ 5 = 1 := by
  have h := allK_iff.1 check_ord _ (memK_iff.1 (pc6_mem_even σ hs))
  rw [lo6_pc6] at h
  have h' : (Nat.beq (mulK 6 (enc σ) (enc σ)) ID6 ||
      (Nat.beq (mulK 6 (enc σ) (mulK 6 (enc σ) (enc σ))) ID6 ||
      (Nat.beq (mulK 6 (enc σ) (mulK 6 (enc σ) (mulK 6 (enc σ) (enc σ)))) ID6 ||
      (Nat.beq (mulK 6 (enc σ) (mulK 6 (enc σ) (mulK 6 (enc σ) (mulK 6 (enc σ) (enc σ)))))
        ID6 || false)))) = true := h
  simp only [← enc_mul6, ← eq_one_iff, Bool.or_false, Bool.or_eq_true] at h'
  have e2 : σ ^ 2 = σ * σ := pow_two σ
  have e3 : σ ^ 3 = σ * (σ * σ) := by rw [pow_succ', pow_two]
  have e4 : σ ^ 4 = σ * (σ * (σ * σ)) := by rw [pow_succ', pow_succ', pow_two]
  have e5 : σ ^ 5 = σ * (σ * (σ * (σ * σ))) := by rw [pow_succ', pow_succ', pow_succ', pow_two]
  rw [e2, e3, e4, e5]
  exact h'

theorem a6_orders_pack : ∀ σ : alternatingGroup (Fin 6),
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 ∨ σ ^ 5 = 1 := by
  intro σ
  have h := orders_of_sign (σ : Perm (Fin 6)) (Perm.mem_alternatingGroup.1 σ.2)
  have key : ∀ k : ℕ, (σ : Perm (Fin 6)) ^ k = 1 → σ ^ k = 1 := fun k hk =>
    Subtype.ext (by rw [Subgroup.coe_pow, hk]; rfl)
  rcases h with h | h | h | h
  · exact Or.inl (key 2 h)
  · exact Or.inr (Or.inl (key 3 h))
  · exact Or.inr (Or.inr (Or.inl (key 4 h)))
  · exact Or.inr (Or.inr (Or.inr (key 5 h)))

@[expose] def xP : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def yP : Perm (Fin 6) := swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5

theorem enc_xP : enc xP = 5517345 := by decide +kernel

theorem enc_yP : enc yP = 1393440 := by decide +kernel

theorem sign_xP : Perm.sign xP = 1 := by decide +kernel

theorem sign_yP : Perm.sign yP = 1 := by decide +kernel

@[expose] noncomputable def centB (c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 c 5517345) (mulK 6 5517345 c) && Nat.beq (mulK 6 c 1393440) (mulK 6 1393440 c))
    || Nat.beq c ID6

theorem check_cent : allK (fun p => centB (lo6 p)) allCodes6 = true := by decide +kernel

theorem s6_centralizer_a6_pack : ∀ σ : Perm (Fin 6),
    (∀ τ : alternatingGroup (Fin 6), σ * (τ : Perm (Fin 6)) = τ * σ) → σ = 1 := by
  intro σ hσ
  have hx := (commute_iff σ xP).1 (hσ ⟨xP, Perm.mem_alternatingGroup.2 sign_xP⟩)
  have hy := (commute_iff σ yP).1 (hσ ⟨yP, Perm.mem_alternatingGroup.2 sign_yP⟩)
  rw [enc_xP] at hx
  rw [enc_yP] at hy
  have h := allK_iff.1 check_cent _ (memK_iff.1 (pc6_mem_all σ))
  rw [lo6_pc6] at h
  have h' : (!(Nat.beq (mulK 6 (enc σ) 5517345) (mulK 6 5517345 (enc σ)) &&
      Nat.beq (mulK 6 (enc σ) 1393440) (mulK 6 1393440 (enc σ))) || Nat.beq (enc σ) ID6) =
      true := h
  rw [hx, hy, Bool.and_true, Bool.not_true, Bool.false_or] at h'
  exact (eq_one_iff σ).2 h'

@[expose] noncomputable def cntK (f : ℕ → Bool) (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ r => Bool.rec (motive := fun _ => ℕ) r (Nat.succ r) (f a)) L

theorem cntK_eq (f : ℕ → Bool) (L : List ℕ) : cntK f L = (L.filter f).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change Bool.rec (motive := fun _ => ℕ) (cntK f L) (Nat.succ (cntK f L)) (f a) = _
    rw [List.filter_cons]
    cases f a <;> simp [ih]

theorem evenCodes6_nodup : evenCodes6.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (fun c => lo6 c % 3106) (by decide +kernel)

theorem evenCodes6_length : evenCodes6.length = 360 := by decide +kernel

theorem card_even : (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1).card = 360 := by
  have h1 := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : Fintype.card (alternatingGroup (Fin 6)) =
      (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun g => Perm.mem_alternatingGroup)
  have h3 : Nat.factorial 6 = 720 := rfl
  omega

theorem pc6_injective : Function.Injective (pc6 : Perm (Fin 6) → ℕ) := fun σ τ h =>
  enc_inj (by norm_num) (by rw [← lo6_pc6, h, lo6_pc6])

theorem image_even :
    (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1).image pc6 = evenCodes6.toFinset := by
  refine Finset.eq_of_subset_of_card_le (fun c hc => ?_) ?_
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hc
    exact List.mem_toFinset.2 (memK_iff.1 (pc6_mem_even g (Finset.mem_filter.1 hg).2))
  · rw [Finset.card_image_of_injective _ pc6_injective, card_even,
      List.toFinset_card_of_nodup evenCodes6_nodup, evenCodes6_length]

theorem card_even_filter (f : ℕ → Bool) :
    (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1 ∧ f (enc g) = true).card =
      cntK (fun c => f (lo6 c)) evenCodes6 := by
  have hL : (evenCodes6.filter (fun c => f (lo6 c))).length =
      (evenCodes6.toFinset.filter (fun c => f (lo6 c) = true)).card := by
    rw [← List.toFinset_card_of_nodup (evenCodes6_nodup.filter _), List.toFinset_filter]
  rw [cntK_eq, hL, ← image_even, Finset.filter_image,
    Finset.card_image_of_injective _ pc6_injective, Finset.filter_filter]
  simp only [lo6_pc6]

@[expose] noncomputable def invB (c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 c c) ID6 && !(Nat.beq c ID6)) ||
    !(Nat.beq (Nat.mod (cntK (fun q => commLaneK 6 (lo6 q) c) evenCodes6) 9) 0)

theorem check_inv : allK (fun p => invB (lo6 p)) allCodes6 = true := by decide +kernel

theorem s6_involution_centralizer_pack : ∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 →
    ¬ 9 ∣ Fintype.card {τ : alternatingGroup (Fin 6) // (τ : Perm (Fin 6)) * σ = σ * τ} := by
  intro σ h2 h1 h9
  let f : ℕ → Bool := fun d => commLaneK 6 d (enc σ)
  let e : {τ : alternatingGroup (Fin 6) // (τ : Perm (Fin 6)) * σ = σ * τ} ≃
      {g : Perm (Fin 6) // Perm.sign g = 1 ∧ f (enc g) = true} :=
    { toFun := fun τ => ⟨τ.1.1, Perm.mem_alternatingGroup.1 τ.1.2,
        (commLaneK_iff (by norm_num) _ _).2 τ.2⟩
      invFun := fun g => ⟨⟨g.1, Perm.mem_alternatingGroup.2 g.2.1⟩,
        (commLaneK_iff (by norm_num) _ _).1 g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype, card_even_filter f] at h9
  have h := allK_iff.1 check_inv _ (memK_iff.1 (pc6_mem_all σ))
  rw [lo6_pc6] at h
  have h' : (!(Nat.beq (mulK 6 (enc σ) (enc σ)) ID6 && !(Nat.beq (enc σ) ID6)) ||
      !(Nat.beq (Nat.mod (cntK (fun q => commLaneK 6 (lo6 q) (enc σ)) evenCodes6) 9) 0)) =
      true := h
  have hsq : Nat.beq (mulK 6 (enc σ) (enc σ)) ID6 = true := by
    rw [← enc_mul6, ← eq_one_iff]
    exact h2
  have hne : Nat.beq (enc σ) ID6 = false := by
    cases hb : Nat.beq (enc σ) ID6
    · rfl
    · exact absurd ((eq_one_iff σ).2 hb) h1
  have hmod : Nat.beq (Nat.mod (cntK (fun q => commLaneK 6 (lo6 q) (enc σ)) evenCodes6) 9) 0 =
      true := by
    rw [Nat.beq_eq]
    exact Nat.mod_eq_zero_of_dvd h9
  rw [hsq, hne, hmod] at h'
  exact absurd h' (by decide)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack
