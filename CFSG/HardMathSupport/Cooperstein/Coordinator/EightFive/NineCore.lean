module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NineFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section Perm

variable {α : Type*} [DecidableEq α]

theorem conj_swap_mul_swap (σ : Perm α) (a b c : α) :
    σ * (swap a b * swap a c) * σ⁻¹ = swap (σ a) (σ b) * swap (σ a) (σ c) := by
  rw [swap_apply_apply, swap_apply_apply]
  group

theorem swap_mul_swap_eq_inv {a b c : α} (hac : a ≠ c) (hbc : b ≠ c) :
    swap b a * swap b c = (swap a b * swap a c)⁻¹ := by
  rw [mul_inv_rev, swap_inv, swap_inv, swap_comm b a]
  have h := swap_apply_apply (swap a b) b c
  rw [swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_inv] at h
  rw [h, mul_assoc (swap a b * swap b c), swap_mul_self, mul_one]

theorem conj_swap_mul_swap_eq_inv {σ : Perm α} {a b c : α} (hac : a ≠ c) (hbc : b ≠ c)
    (ha : σ a = b) (hb : σ b = a) (hc : σ c = c) :
    σ * (swap a b * swap a c) * σ⁻¹ = (swap a b * swap a c)⁻¹ := by
  rw [conj_swap_mul_swap, ha, hb, hc]
  exact swap_mul_swap_eq_inv hac hbc

theorem commute_swap_mul_swap {τ : Perm α} {a b c : α} (ha : τ a = a) (hb : τ b = b)
    (hc : τ c = c) : τ * (swap a b * swap a c) = swap a b * swap a c * τ := by
  have h := conj_swap_mul_swap τ a b c
  rw [ha, hb, hc] at h
  calc τ * (swap a b * swap a c) = τ * (swap a b * swap a c) * τ⁻¹ * τ := by group
    _ = swap a b * swap a c * τ := by rw [h]

theorem viaEmbedding_swap {β : Type*} [DecidableEq β] (ι : α ↪ β) (a b : α) :
    viaEmbedding (swap a b) ι = swap (ι a) (ι b) := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨y, rfl⟩ := hx
    rw [viaEmbedding_apply, ι.injective.swap_apply]
  · rw [viaEmbedding_apply_of_notMem _ _ _ hx, swap_apply_of_ne_of_ne] <;>
      · rintro rfl
        exact hx ⟨_, rfl⟩

theorem isThreeCycle_viaEmbedding {β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ι : α ↪ β) {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (viaEmbedding (swap a b * swap a c) ι).IsThreeCycle := by
  rw [← viaEmbeddingHom_apply, map_mul, viaEmbeddingHom_apply, viaEmbeddingHom_apply,
    viaEmbedding_swap, viaEmbedding_swap]
  exact isThreeCycle_swap_mul_swap_same (ι.injective.ne hab) (ι.injective.ne hac)
    (ι.injective.ne hbc)

end Perm

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

@[expose] noncomputable def altPreInv (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) : alternatingGroup (Fin n) →* ↥H :=
  (Subgroup.inclusion altPre_le).comp (altPreEquiv hψ hA).symm.toMonoidHom

theorem apply_altPreInv (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (σ : alternatingGroup (Fin n)) : ψ (altPreInv hψ hA σ) = σ := by
  change ψ (Subgroup.inclusion altPre_le ((altPreEquiv hψ hA).symm σ)) = σ
  rw [← coe_altPreEquiv hψ hA, MulEquiv.apply_symm_apply]

theorem exists_inverted (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {s : ↥H} (hs : ψ s * ψ s = 1) {u w : Fin n} (hu : ψ s u ≠ u) (hw : ψ s w = w) :
    ∃ x : ↥H, (x : MulAut V) ^ 3 = 1 ∧ fixV (Subgroup.zpowers (x : MulAut V)) = ⊥ ∧
      (s : MulAut V) * x * (s : MulAut V)⁻¹ = (x : MulAut V)⁻¹ ∧
      ∀ b : ↥H, ψ b u = u → ψ b (ψ s u) = ψ s u → ψ b w = w →
        (b : MulAut V) * x = x * b := by
  have hss : ψ s (ψ s u) = u := by
    have := congrArg (fun τ : Perm (Fin n) => τ u) hs
    simpa [Perm.mul_apply] using this
  have h1 : u ≠ ψ s u := fun h => hu h.symm
  have h2 : u ≠ w := by
    rintro rfl
    exact hu hw
  have h3' : ψ s u ≠ w := by
    intro h
    apply h2
    rw [← hss, h, hw]
  have hc3 : (swap u (ψ s u) * swap u w).IsThreeCycle := isThreeCycle_swap_mul_swap_same h1 h2 h3'
  set x := altPreInv hψ hA ⟨swap u (ψ s u) * swap u w, hc3.mem_alternatingGroup⟩
  have hψx : ψ x = swap u (ψ s u) * swap u w := apply_altPreInv hψ hA _
  refine ⟨x, ?_, h3 x (hψx ▸ hc3), ?_, fun b hbu hbs hbw => ?_⟩
  · have hx3 : x ^ 3 = 1 :=
      hψ (by rw [map_pow, hψx, map_one, ← hc3.orderOf, pow_orderOf_eq_one])
    rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  · have hinv : s * x * s⁻¹ = x⁻¹ := hψ (by
      rw [map_mul, map_mul, map_inv, map_inv, hψx]
      exact conj_swap_mul_swap_eq_inv h2 h3' rfl hss hw)
    exact congrArg Subtype.val hinv
  · have hbx : b * x = x * b := hψ (by
      rw [map_mul, map_mul, hψx]
      exact commute_swap_mul_swap hbu hbs hbw)
    exact congrArg Subtype.val hbx

theorem apply_mul_apply_eq_one {s : ↥H} (hs : (s : MulAut V) ^ 2 = 1) : ψ s * ψ s = 1 := by
  have h : s ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hs)
  rw [← map_mul, ← pow_two, h, map_one]

theorem card_fixV_sq_of_apply_ne [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {s : ↥H} (hs : (s : MulAut V) ^ 2 = 1) {u w : Fin n} (hu : ψ s u ≠ u) (hw : ψ s w = w) :
    Nat.card (fixV (Subgroup.zpowers (s : MulAut V))) ^ 2 = Nat.card V := by
  obtain ⟨x, hx3, hxf, hinv, -⟩ := exists_inverted hψ hA h3 (apply_mul_apply_eq_one hs) hu hw
  exact card_fixV_zpowers_sq_eq hV hs hx3 hinv hxf

theorem two_pow_eight_le_card [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hn : 9 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥) :
    2 ^ 8 ≤ Nat.card V := by
  let ι : Fin 9 ↪ Fin n := Fin.castLEEmb hn
  let ρ : alternatingGroup (Fin 9) →* ↥H := (altPreInv hψ hA).comp (altLift ι)
  have hρ : ∀ σ, ψ (ρ σ) = viaEmbedding (σ : Perm (Fin 9)) ι := fun σ =>
    (apply_altPreInv hψ hA _).trans (coe_altLift ι σ)
  let ρ' : alternatingGroup (Fin 9) →* MulAut V := H.subtype.comp ρ
  let c₁ : alternatingGroup (Fin 9) := ⟨swap 0 1 * swap 0 2, by rw [mem_alternatingGroup]; decide⟩
  let c₂ : alternatingGroup (Fin 9) := ⟨swap 3 4 * swap 3 5, by rw [mem_alternatingGroup]; decide⟩
  let c₃ : alternatingGroup (Fin 9) := ⟨swap 6 7 * swap 6 8, by rw [mem_alternatingGroup]; decide⟩
  let d : alternatingGroup (Fin 9) := ⟨swap 4 5 * swap 7 8, by rw [mem_alternatingGroup]; decide⟩
  let d' : alternatingGroup (Fin 9) :=
    ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 7 8, by rw [mem_alternatingGroup]; decide⟩
  have e₁ : c₁ ^ 3 = 1 := by decide
  have e₂ : c₂ ^ 3 = 1 := by decide
  have e₃ : c₃ ^ 3 = 1 := by decide
  have r₁₂ : c₁ * c₂ = c₂ * c₁ := by decide
  have r₁₃ : c₁ * c₃ = c₃ * c₁ := by decide
  have r₂₃ : c₂ * c₃ = c₃ * c₂ := by decide
  have s₁ : d * c₁ * d⁻¹ = c₁ := by decide
  have s₂ : d * c₂ * d⁻¹ = c₂⁻¹ := by decide
  have s'₁ : d' * c₁ * d'⁻¹ = c₂ := by decide
  have s'₂ : d' * c₂ * d'⁻¹ = c₁ := by decide
  have s'₃ : d' * c₃ * d'⁻¹ = c₃⁻¹ := by decide
  have hf : ∀ {a b c : Fin 9}, a ≠ b → a ≠ c → b ≠ c →
      ∀ hm : swap a b * swap a c ∈ alternatingGroup (Fin 9),
        fixV (Subgroup.zpowers (ρ' ⟨_, hm⟩)) = ⊥ := by
    intro a b c hab hac hbc hm
    exact h3 (ρ ⟨_, hm⟩) (by rw [hρ]; exact isThreeCycle_viaEmbedding ι hab hac hbc)
  have f₁ : fixV (Subgroup.zpowers (ρ' c₁)) = ⊥ := hf (by decide) (by decide) (by decide) _
  have f₂ : fixV (Subgroup.zpowers (ρ' c₂)) = ⊥ := hf (by decide) (by decide) (by decide) _
  have f₃ : fixV (Subgroup.zpowers (ρ' c₃)) = ⊥ := hf (by decide) (by decide) (by decide) _
  have hx₁ : ρ' c₁ ≠ 1 := by
    intro h
    have h1 : ρ c₁ = 1 := Subtype.ext h
    have h2 := hρ c₁
    rw [h1, map_one] at h2
    have h3c := isThreeCycle_viaEmbedding ι (a := (0 : Fin 9)) (b := 1) (c := 2) (by decide)
      (by decide) (by decide)
    exact h3c.ne_one h2.symm
  refine two_pow_eight_le_card_of_three hV (x₁ := ρ' c₁) (x₂ := ρ' c₂) (x₃ := ρ' c₃)
    (g := ρ' d) (g' := ρ' d') ?_ ?_ ?_ ?_ ?_ ?_ f₁ f₂ f₃ hx₁ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, e₁, map_one]
  · rw [← map_pow, e₂, map_one]
  · rw [← map_pow, e₃, map_one]
  · rw [← map_mul, ← map_mul, r₁₂]
  · rw [← map_mul, ← map_mul, r₁₃]
  · rw [← map_mul, ← map_mul, r₂₃]
  · rw [← map_inv, ← map_mul, ← map_mul, s₁]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, s₂]
  · rw [← map_inv, ← map_mul, ← map_mul, s'₁]
  · rw [← map_inv, ← map_mul, ← map_mul, s'₂]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, s'₃]

theorem false_of_core3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hn : 9 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {B : Subgroup (MulAut V)} (hel : IsElemAbelian2 B) (hB16 : Nat.card B ≤ 16)
    (hoff : Nat.card V ≤ Nat.card B * Nat.card (fixV B))
    {t b : ↥H} (htB : (t : MulAut V) ∈ B) (hbB : (b : MulAut V) ∈ B) (hb1 : b ≠ 1)
    {p r : Fin n} (htr : ψ t r = r) (htp : ψ t p ≠ p) (hbp : ψ b p = p) (hbr : ψ b r = r) :
    False := by
  have hV8 := two_pow_eight_le_card hV hn hψ hA h3
  obtain ⟨u, hu⟩ : ∃ u, ψ b u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hb1 (hψ (by rw [map_one]; exact Equiv.ext hcon))
  have hb := card_fixV_sq_of_apply_ne hV hψ hA h3 (hel.2 _ hbB) hu hbp
  obtain ⟨x, hx3, hxf, hinv, hcomm⟩ :=
    exists_inverted hψ hA h3 (apply_mul_apply_eq_one (hel.2 _ htB)) htp htr
  have hbt : ψ b (ψ t p) = ψ t p := by
    have hc : b * t = t * b := Subtype.ext (hel.1 _ hbB _ htB)
    have h1 := congrArg (fun τ : Perm (Fin n) => τ p) (congrArg ψ hc)
    simp only [map_mul, Perm.mul_apply, hbp] at h1
    exact h1
  exact false_of_fixV_eq hB16 hV8 hoff htB hbB hb hx3 hxf hinv (hcomm b hbp hbt hbr).symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
