module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRoot

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

section Flip

@[expose] def pairFlip (b : Fin 4 → Bool) : Perm (Fin 4 × Fin 2) where
  toFun kc := (kc.1, if b kc.1 then swap 0 1 kc.2 else kc.2)
  invFun kc := (kc.1, if b kc.1 then swap 0 1 kc.2 else kc.2)
  left_inv kc := by
    rcases kc with ⟨k, c⟩
    by_cases h : b k <;> simp [h]
  right_inv kc := by
    rcases kc with ⟨k, c⟩
    by_cases h : b k <;> simp [h]

theorem pairFlip_apply (b : Fin 4 → Bool) (k : Fin 4) (c : Fin 2) :
    pairFlip b (k, c) = (k, if b k then swap 0 1 c else c) :=
  rfl

theorem pairFlip_mul (b b' : Fin 4 → Bool) :
    pairFlip b * pairFlip b' = pairFlip (fun k => xor (b k) (b' k)) := by
  refine Equiv.ext fun ⟨k, c⟩ => ?_
  rw [Perm.mul_apply, pairFlip_apply, pairFlip_apply, pairFlip_apply]
  by_cases h1 : b k <;> by_cases h2 : b' k <;> simp [h1, h2]

theorem pairFlip_false : pairFlip (fun _ => false) = 1 := by
  refine Equiv.ext fun ⟨k, c⟩ => ?_
  rw [pairFlip_apply]
  rfl

theorem pairFlip_mul_self (b : Fin 4 → Bool) : pairFlip b * pairFlip b = 1 := by
  rw [pairFlip_mul, ← pairFlip_false]
  congr 1
  funext k
  simp

theorem pairFlip_mul_zPair (b : Fin 4 → Bool) : pairFlip b * zPair 4 = zPair 4 * pairFlip b := by
  refine Equiv.ext fun ⟨k, c⟩ => ?_
  rw [Perm.mul_apply, Perm.mul_apply, zPair_apply, pairFlip_apply, pairFlip_apply, zPair_apply]
  by_cases h : b k <;> simp [h]

theorem diagHom_mul_pairFlip (τ : Perm (Fin 4)) (b : Fin 4 → Bool) :
    diagHom τ * pairFlip b = pairFlip (fun k => b (τ⁻¹ k)) * diagHom τ := by
  refine Equiv.ext fun ⟨k, c⟩ => ?_
  rw [Perm.mul_apply, Perm.mul_apply, pairFlip_apply, diagHom_apply, diagHom_apply,
    pairFlip_apply]
  simp

theorem pairFlip_mul_diagHom (τ : Perm (Fin 4)) (b : Fin 4 → Bool) :
    pairFlip b * diagHom τ = diagHom τ * pairFlip (fun k => b (τ k)) := by
  rw [diagHom_mul_pairFlip]
  simp

end Flip

section Tree

@[expose] def dihFour : Subgroup (Perm (Fin 4)) where
  carrier := {σ | σ * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * σ}
  one_mem' := by
    show 1 * (swap 0 1 * swap 2 3 : Perm (Fin 4)) = swap 0 1 * swap 2 3 * 1
    rw [one_mul, mul_one]
  mul_mem' := by
    intro a b ha hb
    change a * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * a at ha
    change b * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * b at hb
    change a * b * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * (a * b)
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := by
    intro a ha
    change a * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * a at ha
    change a⁻¹ * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * a⁻¹
    calc a⁻¹ * (swap 0 1 * swap 2 3) = a⁻¹ * ((swap 0 1 * swap 2 3) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (swap 0 1 * swap 2 3)) * a⁻¹ := by rw [ha]
      _ = (swap 0 1 * swap 2 3) * a⁻¹ := by group

instance : DecidablePred (· ∈ dihFour) := fun σ =>
  inferInstanceAs (Decidable (σ * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * σ))

theorem card_dihFour : Nat.card dihFour = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def treePerm : Subgroup (Perm (Fin 4 × Fin 2)) where
  carrier := {x | ∃ τ ∈ dihFour, ∃ b : Fin 4 → Bool, x = diagHom τ * pairFlip b}
  one_mem' := ⟨1, one_mem _, fun _ => false, by rw [map_one, pairFlip_false, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨τ, hτ, b, rfl⟩ ⟨τ', hτ', b', rfl⟩
    refine ⟨τ * τ', mul_mem hτ hτ', fun k => xor (b (τ' k)) (b' k), ?_⟩
    calc diagHom τ * pairFlip b * (diagHom τ' * pairFlip b') =
        diagHom τ * (pairFlip b * diagHom τ') * pairFlip b' := by group
      _ = diagHom τ * (diagHom τ' * pairFlip (fun k => b (τ' k))) * pairFlip b' := by
        rw [pairFlip_mul_diagHom]
      _ = diagHom (τ * τ') * (pairFlip (fun k => b (τ' k)) * pairFlip b') := by
        rw [map_mul]
        group
      _ = diagHom (τ * τ') * pairFlip (fun k => xor (b (τ' k)) (b' k)) := by rw [pairFlip_mul]
  inv_mem' := by
    rintro _ ⟨τ, hτ, b, rfl⟩
    refine ⟨τ⁻¹, inv_mem hτ, fun k => b (τ⁻¹ k), ?_⟩
    have hb : (pairFlip b)⁻¹ = pairFlip b := inv_eq_of_mul_eq_one_left (pairFlip_mul_self b)
    rw [mul_inv_rev, hb, ← map_inv, pairFlip_mul_diagHom]

theorem diagHom_mul_pairFlip_injective {τ τ' : Perm (Fin 4)} {b b' : Fin 4 → Bool}
    (h : diagHom τ * pairFlip b = diagHom τ' * pairFlip b') : τ = τ' ∧ b = b' := by
  have hs : (swap (0 : Fin 2) 1) 0 = 1 := by decide
  have h1 : ∀ k : Fin 4, (τ k, if b k then (1 : Fin 2) else 0) =
      (τ' k, if b' k then (1 : Fin 2) else 0) := by
    intro k
    have h2 := congrArg (fun x : Perm (Fin 4 × Fin 2) => x (k, 0)) h
    simp only [Perm.mul_apply, pairFlip_apply, diagHom_apply, hs] at h2
    exact h2
  refine ⟨Equiv.ext fun k => (Prod.mk.inj (h1 k)).1, funext fun k => ?_⟩
  have h3 := (Prod.mk.inj (h1 k)).2
  by_cases hb : b k <;> by_cases hb' : b' k <;> simp_all

theorem card_treePerm : Nat.card treePerm = 2 ^ 7 := by
  let F : dihFour × (Fin 4 → Bool) → treePerm := fun p =>
    ⟨diagHom (p.1 : Perm (Fin 4)) * pairFlip p.2, p.1, p.1.2, p.2, rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h := diagHom_mul_pairFlip_injective (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext h.1) h.2
    · obtain ⟨τ, hτ, b, hx⟩ := x.2
      exact ⟨(⟨τ, hτ⟩, b), Subtype.ext hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod, card_dihFour,
    Nat.card_eq_fintype_card (α := Fin 4 → Bool), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  norm_num

theorem treePerm_commute_zPair {x : Perm (Fin 4 × Fin 2)} (hx : x ∈ treePerm) :
    x * zPair 4 = zPair 4 * x := by
  obtain ⟨τ, -, b, rfl⟩ := hx
  rw [mul_assoc, pairFlip_mul_zPair, ← mul_assoc, diagHom_mul_zPair, mul_assoc]

end Tree

section Embed

variable {N : ℕ}

@[expose] def signSwap (h : 10 ≤ N) : ℤˣ →* Perm (Fin N) where
  toFun u := if u = 1 then 1 else swap ⟨8, by omega⟩ ⟨9, by omega⟩
  map_one' := by simp
  map_mul' u v := by
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [hne]

theorem signSwap_one (h : 10 ≤ N) : signSwap h 1 = 1 := map_one _

theorem sign_signSwap (h : 10 ≤ N) (u : ℤˣ) : sign (signSwap h u) = u := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [signSwap_one, Perm.sign_one]
  · show sign (if (-1 : ℤˣ) = 1 then 1 else swap (⟨8, by omega⟩ : Fin N) ⟨9, by omega⟩) = -1
    rw [ite_eq_right hne, sign_swap (by simp)]

theorem signSwap_apply_pairEmb (h : 10 ≤ N) (u : ℤˣ) (kc : Fin 4 × Fin 2) :
    signSwap h u (pairEmb (by omega : 2 * 4 ≤ N) kc) = pairEmb (by omega : 2 * 4 ≤ N) kc := by
  have hlt : ((pairEmb (by omega : 2 * 4 ≤ N) kc : Fin N) : ℕ) < 8 := by
    show 2 * (kc.1 : ℕ) + kc.2 < 8
    have := kc.1.2
    have := kc.2.2
    omega
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [signSwap_one, Perm.one_apply]
  · show (if (-1 : ℤˣ) = 1 then 1 else swap (⟨8, by omega⟩ : Fin N) ⟨9, by omega⟩)
      (pairEmb (by omega : 2 * 4 ≤ N) kc) = pairEmb (by omega : 2 * 4 ≤ N) kc
    rw [ite_eq_right (by decide)]
    exact swap_apply_of_ne_of_ne (fun h' => by rw [h'] at hlt; simp at hlt)
      (fun h' => by rw [h'] at hlt; simp at hlt)

theorem commute_signSwap (h : 10 ≤ N) (x : Perm (Fin 4 × Fin 2)) (u : ℤˣ) :
    viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x * signSwap h u =
      signSwap h u * viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x :=
  viaEmbeddingHom_mul_comm _ (τ := 1) (fun a => by rw [signSwap_apply_pairEmb, Perm.one_apply])
    (by rw [mul_one, one_mul])

@[expose] noncomputable def pairSignPerm (h : 10 ≤ N) : Perm (Fin 4 × Fin 2) →* Perm (Fin N) where
  toFun x := viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x * signSwap h (sign x)
  map_one' := by rw [map_one, Perm.sign_one, signSwap_one, mul_one]
  map_mul' x y := by
    rw [map_mul, Perm.sign_mul, map_mul]
    calc viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x *
          viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) y *
          (signSwap h (sign x) * signSwap h (sign y)) =
        viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x *
          (viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) y * signSwap h (sign x)) *
          signSwap h (sign y) := by group
      _ = viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x *
          (signSwap h (sign x) * viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) y) *
          signSwap h (sign y) := by rw [commute_signSwap]
      _ = _ := by group

theorem pairSignPerm_apply (h : 10 ≤ N) (x : Perm (Fin 4 × Fin 2)) :
    pairSignPerm h x =
      viaEmbeddingHom (pairEmb (by omega : 2 * 4 ≤ N)) x * signSwap h (sign x) :=
  rfl

theorem pairSignPerm_injective (h : 10 ≤ N) : Function.Injective (pairSignPerm h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [mem_bot]
  refine Equiv.ext fun kc => ?_
  have h1 := congrArg (fun π : Perm (Fin N) => π (pairEmb (by omega : 2 * 4 ≤ N) kc)) hx
  simp only [pairSignPerm_apply, Perm.mul_apply, signSwap_apply_pairEmb,
    viaEmbeddingHom_apply_image, Perm.one_apply] at h1
  exact (pairEmb (by omega : 2 * 4 ≤ N)).injective h1

@[expose] noncomputable def pairSignHom (h : 10 ≤ N) :
    Perm (Fin 4 × Fin 2) →* alternatingGroup (Fin N) :=
  (pairSignPerm h).codRestrict _ fun x => by
    rw [mem_alternatingGroup, pairSignPerm_apply, Perm.sign_mul, sign_viaEmbeddingHom,
      sign_signSwap, Int.units_mul_self]

theorem coe_pairSignHom (h : 10 ≤ N) (x : Perm (Fin 4 × Fin 2)) :
    ((pairSignHom h x : alternatingGroup (Fin N)) : Perm (Fin N)) = pairSignPerm h x :=
  rfl

theorem pairSignHom_injective (h : 10 ≤ N) : Function.Injective (pairSignHom h) := fun _ _ hxy =>
  pairSignPerm_injective h (congrArg Subtype.val hxy)

theorem pairSignHom_zPair (h : 10 ≤ N) :
    pairSignHom h (zPair 4) = pairAlt (by omega : 2 * 4 ≤ N) (zAlt (m := 4) ⟨2, rfl⟩) := by
  apply Subtype.ext
  rw [coe_pairSignHom, pairSignPerm_apply, sign_zPair ⟨2, rfl⟩, signSwap_one, mul_one]
  rfl

@[expose] noncomputable def treeTwo (h : 10 ≤ N) : Subgroup (alternatingGroup (Fin N)) :=
  treePerm.map (pairSignHom h)

theorem card_treeTwo (h : 10 ≤ N) : Nat.card (treeTwo h) = 2 ^ 7 := by
  rw [treeTwo, Subgroup.card_map_of_injective (pairSignHom_injective h), card_treePerm]

theorem treeTwo_le_centralizer (h : 10 ≤ N) :
    treeTwo h ≤ centralizer ({pairAlt (by omega : 2 * 4 ≤ N) (zAlt (m := 4) ⟨2, rfl⟩)} :
      Set (alternatingGroup (Fin N))) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff, ← pairSignHom_zPair, ← map_mul, ← map_mul,
    treePerm_commute_zPair hx]

theorem exists_card_eq_le_centralizer_of_cycleType (h : 10 ≤ N) {π : alternatingGroup (Fin N)}
    (hπ : (π : Perm (Fin N)).cycleType = {2, 2, 2, 2}) :
    ∃ P : Subgroup (alternatingGroup (Fin N)), Nat.card P = 2 ^ 7 ∧
      P ≤ centralizer ({π} : Set (alternatingGroup (Fin N))) := by
  set z := pairAlt (by omega : 2 * 4 ≤ N) (zAlt (m := 4) ⟨2, rfl⟩) with hz
  have hzc : (z : Perm (Fin N)).cycleType = (π : Perm (Fin N)).cycleType := by
    rw [hz, coe_pairAlt, cycleType_viaEmbeddingHom', hπ]
    exact cycleType_zPair
  have hzz : zAlt (m := 4) ⟨2, rfl⟩ * zAlt (m := 4) ⟨2, rfl⟩ = 1 := zAlt_mul_self _
  have hz2 : z * z = 1 := by rw [hz, ← map_mul, hzz, map_one]
  have hz1 : z ≠ 1 := fun h1 =>
    zAlt_ne_one _ (by norm_num) (pairAlt_injective _ (h1.trans (map_one _).symm))
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq hzc hz2 hz1
  refine ⟨(treeTwo h).map (MulAut.conj β).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj β).injective, card_treeTwo]
  · rintro _ ⟨y, hy, rfl⟩
    have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp (treeTwo_le_centralizer h hy)
    rw [mem_centralizer_singleton_iff, ← hβ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc β * y * β⁻¹ * (β * z * β⁻¹) = β * (y * z) * β⁻¹ := by group
      _ = β * (z * y) * β⁻¹ := by rw [hyz]
      _ = β * z * β⁻¹ * (β * y * β⁻¹) := by group

end Embed

end CFSG.ComponentClassification.RankTwoAlt
