module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six.PermTools

open Equiv Equiv.Perm

theorem alternatingGroup_le_of_orbit (H : Subgroup (Perm (Fin 7)))
    (h3 : ∃ g ∈ H, IsThreeCycle g) (ht : ∀ x : Fin 7, ∃ h ∈ H, h 6 = x) :
    alternatingGroup (Fin 7) ≤ H := by
  obtain ⟨g, hgH, hg3⟩ := h3
  have hpre : MulAction.IsPretransitive H (Fin 7) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, haH, ha⟩ := ht x
    obtain ⟨b, hbH, hb⟩ := ht y
    refine ⟨⟨b, hbH⟩ * ⟨a, haH⟩⁻¹, ?_⟩
    rw [Subgroup.smul_def, Perm.smul_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [← ha, ← Perm.mul_apply a⁻¹, inv_mul_cancel, Perm.one_apply, hb]
  have hprim : MulAction.IsPreprimitive H (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact Nat.prime_seven)
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hg3 hgH

@[expose] def encL (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℕ) : ℕ :=
  a₀ + 8 * (a₁ + 8 * (a₂ + 8 * (a₃ + 8 * (a₄ + 8 * (a₅ + 8 * a₆)))))

@[expose] def enc (σ : Perm (Fin 7)) : ℕ :=
  encL (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6)

@[expose] def dig (a j : ℕ) : ℕ := a / 8 ^ j % 8

@[expose] def mulC (a b : ℕ) : ℕ :=
  encL (dig a (dig b 0)) (dig a (dig b 1)) (dig a (dig b 2)) (dig a (dig b 3)) (dig a (dig b 4))
    (dig a (dig b 5)) (dig a (dig b 6))

@[expose] def idC : ℕ := 1754760

theorem dig_encL {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℕ} (h₀ : a₀ < 8) (h₁ : a₁ < 8) (h₂ : a₂ < 8)
    (h₃ : a₃ < 8) (h₄ : a₄ < 8) (h₅ : a₅ < 8) (h₆ : a₆ < 8) (k : ℕ) (hk : k < 7) :
    dig (encL a₀ a₁ a₂ a₃ a₄ a₅ a₆) k = ![a₀, a₁, a₂, a₃, a₄, a₅, a₆] ⟨k, hk⟩ := by
  unfold dig encL
  interval_cases k <;> simp <;> omega

theorem dig_enc (σ : Perm (Fin 7)) (k : ℕ) (hk : k < 7) : dig (enc σ) k = σ ⟨k, hk⟩ := by
  have h : ∀ i : Fin 7, ((σ i : Fin 7) : ℕ) < 8 := fun i => (σ i).isLt.trans (by norm_num)
  rw [enc, dig_encL (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) k hk]
  interval_cases k <;> rfl

theorem enc_mul (σ τ : Perm (Fin 7)) : enc (σ * τ) = mulC (enc σ) (enc τ) := by
  have e : ∀ (k : ℕ) (hk : k < 7), dig (enc σ) (dig (enc τ) k) = ((σ * τ) ⟨k, hk⟩ : ℕ) := by
    intro k hk
    rw [dig_enc τ k hk, dig_enc σ _ (τ ⟨k, hk⟩).isLt]
    rfl
  rw [mulC, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num)]
  rfl

theorem enc_one : enc 1 = idC := rfl

theorem enc_injective : Function.Injective enc := by
  intro σ τ h
  ext j
  have h1 := dig_enc σ j j.isLt
  have h2 := dig_enc τ j j.isLt
  rw [h] at h1
  exact h1.symm.trans h2

@[expose] def swD (i j k : ℕ) : ℕ := if k = i then j else if k = j then i else k

@[expose] def swapC (i j : ℕ) : ℕ :=
  encL (swD i j 0) (swD i j 1) (swD i j 2) (swD i j 3) (swD i j 4) (swD i j 5) (swD i j 6)

theorem enc_swap (i j : Fin 7) : enc (swap i j) = swapC i j := by
  have h : ∀ k : Fin 7, ((swap i j k : Fin 7) : ℕ) = swD i j k := by
    intro k
    simp only [swap_apply_def, swD, Fin.val_inj]
    split_ifs <;> rfl
  simp only [enc, swapC, h]
  rfl

@[expose] def stepC (gs L : List ℕ) : List ℕ := (L ++ L.flatMap fun a => gs.map (mulC a)).dedup

@[expose] def closeC (gs : List ℕ) : ℕ → List ℕ
  | 0 => [idC]
  | n + 1 => stepC gs (closeC gs n)

theorem mem_stepC_of_mem {gs L : List ℕ} {c : ℕ} (h : c ∈ L) : c ∈ stepC gs L :=
  List.mem_dedup.2 (List.mem_append_left _ h)

theorem idC_mem_closeC (gs : List ℕ) : ∀ n, idC ∈ closeC gs n
  | 0 => List.mem_singleton_self _
  | n + 1 => mem_stepC_of_mem (idC_mem_closeC gs n)

theorem nodup_closeC (gs : List ℕ) : ∀ n, (closeC gs n).Nodup
  | 0 => List.nodup_singleton _
  | _ + 1 => List.nodup_dedup _

theorem exists_of_mem_closeC {S : Set (Perm (Fin 7))} {gs : List ℕ}
    (hgs : ∀ g ∈ gs, ∃ s ∈ S, enc s = g) :
    ∀ n, ∀ c ∈ closeC gs n, ∃ x ∈ Subgroup.closure S, enc x = c
  | 0, c, hc => by
    rw [closeC, List.mem_singleton] at hc
    exact ⟨1, Subgroup.one_mem _, hc ▸ enc_one⟩
  | n + 1, c, hc => by
    rw [closeC, stepC, List.mem_dedup, List.mem_append] at hc
    rcases hc with hc | hc
    · exact exists_of_mem_closeC hgs n c hc
    · obtain ⟨a, ha, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_closeC hgs n a ha
      obtain ⟨s, hs, rfl⟩ := hgs g hg
      exact ⟨x * s, Subgroup.mul_mem _ hx (Subgroup.subset_closure hs), enc_mul x s⟩

theorem enc_mem_of_closed {S : Set (Perm (Fin 7))} {gs L : List ℕ}
    (hgs : ∀ s ∈ S, enc s ∈ gs) (hid : idC ∈ L) (hcl : ∀ a ∈ L, ∀ g ∈ gs, mulC a g ∈ L)
    {x : Perm (Fin 7)} (hx : x ∈ Subgroup.closure S) : enc x ∈ L := by
  have hright : ∀ x, enc x ∈ L → ∀ s ∈ S, enc (x * s) ∈ L := fun x hx s hs => by
    rw [enc_mul]; exact hcl _ hx _ (hgs s hs)
  induction hx using Subgroup.closure_induction_right with
  | one => rw [enc_one]; exact hid
  | mul_right x _ s hs ih => exact hright x ih s hs
  | mul_inv_cancel x _ s hs ih =>
    have hpow : ∀ k : ℕ, enc (x * s ^ k) ∈ L := by
      intro k
      induction k with
      | zero => rw [pow_zero, mul_one]; exact ih
      | succ k ihk => rw [pow_succ, ← mul_assoc]; exact hright _ ihk s hs
    have hinv : s⁻¹ = s ^ (orderOf s - 1) :=
      (eq_inv_of_mul_eq_one_left (by
        rw [pow_sub_one_mul (orderOf_pos s).ne', pow_orderOf_eq_one])).symm
    rw [hinv]
    exact hpow _

theorem mem_closure_iff_closeC (gens : List (Perm (Fin 7))) {S : Set (Perm (Fin 7))}
    (hS : ∀ s, s ∈ S ↔ s ∈ gens) (gs : List ℕ) (hgs : gens.map enc = gs) (n : ℕ)
    (hcl : ∀ a ∈ closeC gs n, ∀ g ∈ gs, mulC a g ∈ closeC gs n) (x : Perm (Fin 7)) :
    x ∈ Subgroup.closure S ↔ enc x ∈ closeC gs n := by
  subst hgs
  constructor
  · exact enc_mem_of_closed (fun s hs => List.mem_map_of_mem ((hS s).1 hs)) (idC_mem_closeC _ n) hcl
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_of_mem_closeC (S := S) (fun g hg => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      exact ⟨s, (hS s).2 hs, rfl⟩) n _ hx
    rwa [← enc_injective hyx]

theorem card_closure_closeC (gens : List (Perm (Fin 7))) {S : Set (Perm (Fin 7))}
    (hS : ∀ s, s ∈ S ↔ s ∈ gens) (gs : List ℕ) (hgs : gens.map enc = gs) (n : ℕ)
    (hcl : ∀ a ∈ closeC gs n, ∀ g ∈ gs, mulC a g ∈ closeC gs n) :
    Nat.card (Subgroup.closure S) = (closeC gs n).length := by
  classical
  have hmem := mem_closure_iff_closeC gens hS gs hgs n hcl
  subst hgs
  have hgs' : ∀ g ∈ gens.map enc, ∃ s ∈ S, enc s = g := fun g hg => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
    exact ⟨s, (hS s).2 hs, rfl⟩
  have hreal := exists_of_mem_closeC hgs' n
  let f : Subgroup.closure S → {c // c ∈ (closeC (gens.map enc) n).toFinset} :=
    fun x => ⟨enc x, List.mem_toFinset.2 ((hmem x).1 x.2)⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      have h0 : enc (x : Perm (Fin 7)) = enc (y : Perm (Fin 7)) := congrArg Subtype.val h
      exact Subtype.ext (enc_injective h0)
    · intro c
      obtain ⟨x, hx, hxc⟩ := hreal c (List.mem_toFinset.1 c.2)
      exact ⟨⟨x, hx⟩, Subtype.ext hxc⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (nodup_closeC _ n)]

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six.PermTools
