module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteDefs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxSix

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS.Six

@[expose] def dg (n i : ℕ) : ℕ := Nat.land (Nat.shiftRight n (3 * i)) 7

@[expose] def enc (σ : Perm (Fin 6)) : ℕ :=
  σ 0 + 8 * σ 1 + 64 * σ 2 + 512 * σ 3 + 4096 * σ 4 + 32768 * σ 5

@[expose] def mulN (a b : ℕ) : ℕ :=
  dg a (dg b 0) + 8 * dg a (dg b 1) + 64 * dg a (dg b 2) + 512 * dg a (dg b 3) +
    4096 * dg a (dg b 4) + 32768 * dg a (dg b 5)

@[expose] def oneN : ℕ := 181896

theorem dg_eq (n i : ℕ) : dg n i = n / 8 ^ i % 8 := by
  have h8 : (8 : ℕ) ^ i = 2 ^ (3 * i) := by rw [pow_mul]; norm_num
  have h7 : (7 : ℕ) = 2 ^ 3 - 1 := by norm_num
  show (n >>> (3 * i)) &&& 7 = _
  rw [h7, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, h8]

theorem dg_enc (σ : Perm (Fin 6)) (i : Fin 6) : dg (enc σ) i = σ i := by
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  rw [dg_eq]
  fin_cases i <;> simp [enc] <;> omega

theorem enc_mul (σ τ : Perm (Fin 6)) : enc (σ * τ) = mulN (enc σ) (enc τ) := by
  have key : ∀ i : Fin 6, dg (enc σ) (dg (enc τ) i) = ((σ * τ) i : ℕ) := fun i => by
    rw [dg_enc τ i, dg_enc σ (τ i)]; rfl
  have k0 : dg (enc σ) (dg (enc τ) 0) = ((σ * τ) 0 : ℕ) := key 0
  have k1 : dg (enc σ) (dg (enc τ) 1) = ((σ * τ) 1 : ℕ) := key 1
  have k2 : dg (enc σ) (dg (enc τ) 2) = ((σ * τ) 2 : ℕ) := key 2
  have k3 : dg (enc σ) (dg (enc τ) 3) = ((σ * τ) 3 : ℕ) := key 3
  have k4 : dg (enc σ) (dg (enc τ) 4) = ((σ * τ) 4 : ℕ) := key 4
  have k5 : dg (enc σ) (dg (enc τ) 5) = ((σ * τ) 5 : ℕ) := key 5
  unfold mulN
  rw [k0, k1, k2, k3, k4, k5]
  rfl

theorem enc_injective : Function.Injective enc := by
  intro σ τ h
  refine Equiv.ext fun i => Fin.ext ?_
  rw [← dg_enc σ i, ← dg_enc τ i, h]

theorem enc_one : enc 1 = oneN := by
  simp [enc, oneN]

@[expose] def powN : ℕ → ℕ → ℕ
  | 0, _ => oneN
  | k + 1, x => mulN x (powN k x)

theorem enc_pow (σ : Perm (Fin 6)) : ∀ k : ℕ, enc (σ ^ k) = powN k (enc σ)
  | 0 => by simp [powN, enc_one]
  | k + 1 => by rw [pow_succ', enc_mul, enc_pow σ k]; rfl

@[expose] def cjN (x y : ℕ) : ℕ := mulN (mulN x y) x

theorem enc_conj {σ : Perm (Fin 6)} (h : σ * σ = 1) (τ : Perm (Fin 6)) :
    enc (σ * τ * σ⁻¹) = cjN (enc σ) (enc τ) := by
  rw [inv_eq_of_mul_eq_one_right h, enc_mul, enc_mul]; rfl

theorem conj_eq_iff (σ τ ρ : Perm (Fin 6)) :
    σ * τ * σ⁻¹ = ρ ↔ mulN (enc σ) (enc τ) = mulN (enc ρ) (enc σ) := by
  rw [← enc_mul, ← enc_mul, enc_injective.eq_iff, mul_inv_eq_iff_eq_mul]

@[expose] def encT (l : List ℕ) : ℕ := l.foldr (fun d acc => d + 8 * acc) 0

theorem encT_tab (σ : Perm (Fin 6)) : encT (tab σ) = enc σ := by
  simp [encT, tab, List.ofFn_succ, enc]
  omega

@[expose] def allN : List ℕ := (allT 6).map encT

theorem mem_allN (σ : Perm (Fin 6)) : enc σ ∈ allN := by
  rw [← encT_tab]
  exact List.mem_map_of_mem (mem_allT σ)

theorem exists_of_mem_allN {n : ℕ} (h : n ∈ allN) : ∃ σ : Perm (Fin 6), enc σ = n := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
  obtain ⟨σ, rfl⟩ := exists_of_mem_allT hl
  exact ⟨σ, (encT_tab σ).symm⟩

@[expose] def invsN : List ℕ := allN.filter (fun x => mulN x x == oneN)

theorem mem_invsN {σ : Perm (Fin 6)} (h : σ * σ = 1) : enc σ ∈ invsN := by
  simp only [invsN, List.mem_filter, beq_iff_eq]
  exact ⟨mem_allN σ, by rw [← enc_mul, h, enc_one]⟩

theorem allN_pow : ∀ x ∈ allN, powN 4 x = oneN ∨ powN 5 x = oneN ∨ powN 6 x = oneN := by
  decide +kernel

theorem order_pow (x : Perm (Fin 6)) : x ^ 4 = 1 ∨ x ^ 5 = 1 ∨ x ^ 6 = 1 := by
  have h := allN_pow (enc x) (mem_allN x)
  rw [← enc_pow x 4, ← enc_pow x 5, ← enc_pow x 6, ← enc_one] at h
  rcases h with h | h | h
  · exact Or.inl (enc_injective h)
  · exact Or.inr (Or.inl (enc_injective h))
  · exact Or.inr (Or.inr (enc_injective h))

@[expose] def OrdOkN (x : ℕ) : Prop := x ≠ oneN ∧ (powN 3 x = oneN ∨ powN 5 x = oneN)

instance (x : ℕ) : Decidable (OrdOkN x) := inferInstanceAs (Decidable (_ ∧ _))

theorem ordOkN_of_orderOf {x : Perm (Fin 6)} (h : orderOf x = 3 ∨ orderOf x = 5) :
    OrdOkN (enc x) := by
  have h1 : x ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at h; omega
  refine ⟨fun h2 => h1 (enc_injective (by rw [h2, enc_one])), ?_⟩
  rcases h with h | h
  · left
    rw [← enc_pow, ← enc_one]
    congr 1
    rw [← h]; exact pow_orderOf_eq_one x
  · right
    rw [← enc_pow, ← enc_one]
    congr 1
    rw [← h]; exact pow_orderOf_eq_one x

@[expose] def insN (acc : List ℕ) (t : ℕ) : List ℕ := if t ∈ acc then acc else acc ++ [t]

@[expose] def rndN (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => l.foldl (fun acc' y => insN acc' (cjN x y)) acc) l

@[expose] def SubN (D : Set (Perm (Fin 6))) (l : List ℕ) : Prop := ∀ t ∈ l, ∃ x ∈ D, enc x = t

theorem subN_insN {D : Set (Perm (Fin 6))} {acc : List ℕ} {t : ℕ} (h : SubN D acc)
    (ht : ∃ x ∈ D, enc x = t) : SubN D (insN acc t) := by
  unfold insN
  by_cases hm : t ∈ acc
  · rw [if_pos hm]; exact h
  · rw [if_neg hm]
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact h s hs
    · rw [List.mem_singleton.1 hs]; exact ht

theorem foldl_subN {D : Set (Perm (Fin 6))} {α : Type} (f : List ℕ → α → List ℕ) :
    ∀ (m : List α) (acc : List ℕ), (∀ a ∈ m, ∀ acc, SubN D acc → SubN D (f acc a)) →
      SubN D acc → SubN D (m.foldl f acc)
  | [], _, _, h => h
  | a :: m, acc, hf, h =>
    foldl_subN f m (f acc a) (fun b hb => hf b (List.mem_cons_of_mem _ hb))
      (hf a List.mem_cons_self acc h)

theorem subN_rndN {D : Set (Perm (Fin 6))} (hconj : ∀ s ∈ D, ∀ t ∈ D, s * t * s⁻¹ ∈ D)
    (hinv : ∀ s ∈ D, s * s = 1) {l : List ℕ} (h : SubN D l) : SubN D (rndN l) := by
  unfold rndN
  refine foldl_subN _ l l (fun x hx acc hacc => ?_) h
  obtain ⟨sx, hsx, rfl⟩ := h x hx
  refine foldl_subN _ l acc (fun y hy acc' hacc' => ?_) hacc
  obtain ⟨sy, hsy, rfl⟩ := h y hy
  exact subN_insN hacc' ⟨sx * sy * sx⁻¹, hconj _ hsx _ hsy, enc_conj (hinv sx hsx) sy⟩

@[expose] def PwOk (T : List ℕ) : Prop := ∀ u ∈ T, ∀ v ∈ T, u ≠ v → OrdOkN (mulN u v)

instance (T : List ℕ) : Decidable (PwOk T) := inferInstanceAs (Decidable (∀ _ ∈ T, _))

@[expose] def NaN (a : ℕ) : List ℕ := invsN.filter (fun b => decide (b ≠ a ∧ OrdOkN (mulN a b)))

@[expose] def Cert (a : ℕ) (L : List (List ℕ)) : Prop :=
  [a] ∈ L ∧ (∀ S ∈ L, a ∈ S ∧ S.length ≤ 9) ∧
    ∀ S ∈ L, ∀ b ∈ NaN a, b ∈ S ∨ ¬ PwOk (S ++ [b]) ∨
      (∃ S' ∈ L, S.length < S'.length ∧ ∀ t ∈ S', t ∈ rndN (rndN (S ++ [b]))) ∨
      ¬ PwOk (rndN (rndN (S ++ [b])))

instance (a : ℕ) (L : List (List ℕ)) : Decidable (Cert a L) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem search_classify {a : ℕ} {L : List (List ℕ)} (hc : Cert a L)
    {D : Set (Perm (Fin 6))} (hconj : ∀ s ∈ D, ∀ t ∈ D, s * t * s⁻¹ ∈ D)
    (hinv : ∀ s ∈ D, s * s = 1)
    (hord : ∀ s ∈ D, ∀ t ∈ D, s ≠ t → OrdOkN (mulN (enc s) (enc t)))
    (haD : ∃ x ∈ D, enc x = a) :
    ∃ S ∈ L, SubN D S ∧ ∀ x ∈ D, enc x ∈ S := by
  obtain ⟨h1, h2, h3⟩ := hc
  obtain ⟨xa, hxa, hxa'⟩ := haD
  have hpw : ∀ T : List ℕ, SubN D T → PwOk T := by
    intro T hT u hu v hv huv
    obtain ⟨su, hsu, rfl⟩ := hT u hu
    obtain ⟨sv, hsv, rfl⟩ := hT v hv
    exact hord su hsu sv hsv (fun e => huv (by rw [e]))
  have key : ∀ n, ∀ S ∈ L, SubN D S → 9 - S.length = n →
      ∃ S' ∈ L, SubN D S' ∧ ∀ x ∈ D, enc x ∈ S' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hS hSub hn
      by_cases hall : ∀ x ∈ D, enc x ∈ S
      · exact ⟨S, hS, hSub, hall⟩
      · obtain ⟨x, hx⟩ := not_forall.1 hall
        obtain ⟨hxD, hxS⟩ := not_imp.1 hx
        have haS : a ∈ S := (h2 S hS).1
        have hxN : enc x ∈ NaN a := by
          simp only [NaN, List.mem_filter, decide_eq_true_eq]
          refine ⟨mem_invsN (hinv x hxD), fun h => hxS (h ▸ haS), ?_⟩
          rw [← hxa']
          exact hord xa hxa x hxD (fun h => hxS (by rw [← h, hxa']; exact haS))
        have hSub1 : SubN D (S ++ [enc x]) := by
          intro t ht
          rcases List.mem_append.1 ht with ht | ht
          · exact hSub t ht
          · rw [List.mem_singleton.1 ht]; exact ⟨x, hxD, rfl⟩
        have hSub2 : SubN D (rndN (rndN (S ++ [enc x]))) :=
          subN_rndN hconj hinv (subN_rndN hconj hinv hSub1)
        rcases h3 S hS (enc x) hxN with h | h | ⟨S', hS', hlt, hsub⟩ | h
        · exact absurd h hxS
        · exact absurd (hpw _ hSub1) h
        · refine ih (9 - S'.length) ?_ S' hS' (fun t ht => hSub2 t (hsub t ht)) rfl
          have := (h2 S' hS').2
          omega
        · exact absurd (hpw _ hSub2) h
  refine key _ [a] h1 ?_ rfl
  intro t ht
  rw [List.mem_singleton.1 ht]
  exact ⟨xa, hxa, hxa'⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxSix
