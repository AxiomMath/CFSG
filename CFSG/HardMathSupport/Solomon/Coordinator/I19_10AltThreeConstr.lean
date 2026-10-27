module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Construct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Equiv

section Four

@[expose] def i1910a3_e4 (n : ℕ) (hn : 4 ≤ n) : Fin 4 ↪ Fin n :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

@[expose] def i1910a3_u4 : Perm (Fin 4) := swap 0 1 * swap 2 3
@[expose] def i1910a3_v4 : Perm (Fin 4) := swap 0 2 * swap 1 3
@[expose] def i1910a3_c4 : Perm (Fin 4) := swap 0 1 * swap 1 2

@[expose] def i1910a3_V4 : Subgroup (Perm (Fin 4)) where
  carrier := {x | x = 1 ∨ x = i1910a3_u4 ∨ x = i1910a3_v4 ∨ x = i1910a3_u4 * i1910a3_v4}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      decide +kernel
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel

theorem i1910a3_V4_sq (x : Perm (Fin 4)) (hx : x ∈ i1910a3_V4) : x ^ 2 = 1 := by
  change x = 1 ∨ x = i1910a3_u4 ∨ x = i1910a3_v4 ∨ x = i1910a3_u4 * i1910a3_v4 at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem i1910a3_V4_sign (x : Perm (Fin 4)) (hx : x ∈ i1910a3_V4) : Perm.sign x = 1 := by
  change x = 1 ∨ x = i1910a3_u4 ∨ x = i1910a3_v4 ∨ x = i1910a3_u4 * i1910a3_v4 at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem i1910a3_c4_cube : i1910a3_c4 ^ 3 = 1 := by decide +kernel

theorem i1910a3_c4_sign : Perm.sign i1910a3_c4 = 1 := by decide +kernel

theorem i1910a3_c4_normalizes : i1910a3_c4 ∈ Subgroup.normalizer (i1910a3_V4 : Set (Perm (Fin 4))) := by
  have h : ∀ x : Perm (Fin 4), x ∈ i1910a3_V4 → i1910a3_c4 * x * i1910a3_c4⁻¹ ∈ i1910a3_V4 := by
    intro x hx
    change x = 1 ∨ x = i1910a3_u4 ∨ x = i1910a3_v4 ∨ x = i1910a3_u4 * i1910a3_v4 at hx
    show _ = 1 ∨ _ = i1910a3_u4 ∨ _ = i1910a3_v4 ∨ _ = i1910a3_u4 * i1910a3_v4
    rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h2 : ∀ y : Perm (Fin 4), y ∈ i1910a3_V4 → i1910a3_c4⁻¹ * y * i1910a3_c4 ∈ i1910a3_V4 := by
    intro y hy
    change y = 1 ∨ y = i1910a3_u4 ∨ y = i1910a3_v4 ∨ y = i1910a3_u4 * i1910a3_v4 at hy
    show _ = 1 ∨ _ = i1910a3_u4 ∨ _ = i1910a3_v4 ∨ _ = i1910a3_u4 * i1910a3_v4
    rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel
  have := h2 _ hx
  simpa [mul_assoc] using this

end Four

section Build

variable {n : ℕ}

private theorem i1910a3_commute_block_via (hn : 4 ≤ n) (q : ℕ) (h : q * 3 + 4 ≤ n)
    (g : Multiplicative (Fin q → ZMod 3)) (x : Perm (Fin 4)) :
    Commute (blockHom 3 q n h g) (Perm.viaEmbeddingHom (i1910a3_e4 n hn) x) := by
  apply Perm.Disjoint.commute
  intro a
  by_cases ha : a.val < 4
  · left; exact blockHom_fix 3 q n h g a ha
  · right
    rw [Perm.viaEmbeddingHom_apply]
    apply Perm.viaEmbedding_apply_of_notMem
    rintro ⟨i, hi⟩
    apply ha
    have h1 : a.val = i.val := by rw [← hi]; rfl
    have := i.isLt
    omega

private theorem i1910a3_c4_pow_zero_of_fix (k : ℕ) (hk : k < 3) (h : (i1910a3_c4 ^ k) 0 = 0) : k = 0 := by
  interval_cases k
  · rfl
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)

theorem i1910a3_exists_elemAbelian_normalizing_two (hn : 4 ≤ n) :
    ∃ E T : Subgroup (alternatingGroup (Fin n)),
      IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 3 ^ ((n - 4) / 3 + 1) ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set (alternatingGroup (Fin n))) := by
  obtain ⟨q, hq⟩ : ∃ q, q = (n - 4) / 3 := ⟨_, rfl⟩
  rw [← hq]
  have h : q * 3 + 4 ≤ n := by
    have := Nat.div_mul_le_self (n - 4) 3
    rw [← hq] at this
    omega
  set Φ : Perm (Fin 4) →* Perm (Fin n) := Perm.viaEmbeddingHom (i1910a3_e4 n hn) with hΦ
  have hΦinj : Function.Injective Φ := Perm.viaEmbeddingHom_injective _
  have hcomm : ∀ (g : Multiplicative (Fin q → ZMod 3)) (x : Perm (Fin 4)),
      Commute (blockHom 3 q n h g) (Φ x) := i1910a3_commute_block_via hn q h
  have hΦsign : ∀ z : Perm (Fin 4), Perm.sign (Φ z) = Perm.sign z := by
    intro z
    classical
    show Perm.sign (Perm.viaEmbedding z (i1910a3_e4 n hn)) = _
    unfold Perm.viaEmbedding
    convert Perm.sign_extendDomain z (ofInjective (i1910a3_e4 n hn).1 (i1910a3_e4 n hn).2)
  have hcsign : ∀ k : ℕ, Perm.sign (Φ (i1910a3_c4 ^ k)) = 1 := by
    intro k
    rw [hΦsign, map_pow, i1910a3_c4_sign, one_pow]
  let rr : Multiplicative (Fin (q + 1) → ZMod 3) →* Perm (Fin n) :=
    (blockHom 3 q n h).comp
      { toFun := fun g => Multiplicative.ofAdd (fun j : Fin q => g.toAdd j.succ)
        map_one' := rfl
        map_mul' := fun a b => rfl }
  let G : Multiplicative (Fin (q + 1) → ZMod 3) →* Perm (Fin n) :=
    { toFun := fun g => rr g * Φ (i1910a3_c4 ^ (g.toAdd 0).val)
      map_one' := by
        show rr 1 * Φ (i1910a3_c4 ^ ((1 : Multiplicative (Fin (q + 1) → ZMod 3)).toAdd 0).val) = 1
        rw [map_one, show ((1 : Multiplicative (Fin (q + 1) → ZMod 3)).toAdd 0) = 0 from rfl,
          ZMod.val_zero, pow_zero, map_one, mul_one]
      map_mul' := by
        intro a b
        have e1 : Φ (i1910a3_c4 ^ ((a * b).toAdd 0).val) =
            Φ (i1910a3_c4 ^ (a.toAdd 0).val) * Φ (i1910a3_c4 ^ (b.toAdd 0).val) := by
          rw [← map_mul, ← pow_add]
          congr 1
          rw [pow_eq_pow_mod _ i1910a3_c4_cube, pow_eq_pow_mod (_ + _) i1910a3_c4_cube]
          congr 1
          rw [show ((a * b).toAdd 0) = a.toAdd 0 + b.toAdd 0 from rfl, ZMod.val_add, Nat.mod_mod]
        have hrb : Commute (rr b) (Φ (i1910a3_c4 ^ (a.toAdd 0).val)) := hcomm _ _
        calc rr (a * b) * Φ (i1910a3_c4 ^ ((a * b).toAdd 0).val)
            = (rr a * rr b) * (Φ (i1910a3_c4 ^ (a.toAdd 0).val) *
                Φ (i1910a3_c4 ^ (b.toAdd 0).val)) := by rw [map_mul, e1]
          _ = (rr a * Φ (i1910a3_c4 ^ (a.toAdd 0).val)) *
                (rr b * Φ (i1910a3_c4 ^ (b.toAdd 0).val)) := hrb.mul_mul_mul_comm _ _ }
  have hGdef : ∀ g, G g = rr g * Φ (i1910a3_c4 ^ (g.toAdd 0).val) := fun g => rfl
  have hGinj : Function.Injective G := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hGdef] at hg
    have hpt : (⟨0, by omega⟩ : Fin n) = i1910a3_e4 n hn 0 := rfl
    have h0 := congrArg (fun σ : Perm (Fin n) => σ ⟨0, by omega⟩) hg
    simp only [Perm.mul_apply, Perm.one_apply] at h0
    have h1 : Φ (i1910a3_c4 ^ (g.toAdd 0).val) (i1910a3_e4 n hn 0) =
        i1910a3_e4 n hn ((i1910a3_c4 ^ (g.toAdd 0).val) 0) := by
      rw [hΦ, Perm.viaEmbeddingHom_apply]
      exact Perm.viaEmbedding_apply _ _ _
    rw [hpt, h1] at h0
    have h2 : rr g (i1910a3_e4 n hn ((i1910a3_c4 ^ (g.toAdd 0).val) 0)) =
        i1910a3_e4 n hn ((i1910a3_c4 ^ (g.toAdd 0).val) 0) := by
      refine blockHom_fix 3 q n h _ _ ?_
      have := ((i1910a3_c4 ^ (g.toAdd 0).val) 0).isLt
      show ((i1910a3_c4 ^ (g.toAdd 0).val) 0).val < 4
      exact this
    rw [h2] at h0
    have h3 : (i1910a3_c4 ^ (g.toAdd 0).val) 0 = 0 := (i1910a3_e4 n hn).injective h0
    have h4 : (g.toAdd 0).val = 0 :=
      i1910a3_c4_pow_zero_of_fix _ (ZMod.val_lt _) h3
    have h5 : g.toAdd 0 = 0 := (ZMod.val_eq_zero _).1 h4
    rw [h4, pow_zero, map_one, mul_one] at hg
    have h6 : (Multiplicative.ofAdd (fun j : Fin q => g.toAdd j.succ)) = 1 :=
      blockHom_injective 3 q n h (by rw [map_one]; exact hg)
    apply Multiplicative.toAdd.injective
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using h5
    · have := congrArg (fun m : Multiplicative (Fin q → ZMod 3) => m.toAdd i) h6
      simpa using this
  set E₀ : Subgroup (Perm (Fin n)) := G.range with hE₀
  set T₀ : Subgroup (Perm (Fin n)) := i1910a3_V4.map Φ with hT₀
  set A := alternatingGroup (Fin n) with hA
  have hE₀A : E₀ ≤ A := by
    rintro _ ⟨g, rfl⟩
    have hrr : rr g ∈ alternatingGroup (Fin n) :=
      blockHom_mem_alt Nat.prime_three (by norm_num) q n h _
    rw [hA, Equiv.Perm.mem_alternatingGroup, hGdef, map_mul, hcsign,
      Equiv.Perm.mem_alternatingGroup.1 hrr, mul_one]
  have hT₀A : T₀ ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hA, Equiv.Perm.mem_alternatingGroup, hΦsign]
    exact i1910a3_V4_sign x hx
  have hnorm : E₀ ≤ Subgroup.normalizer (T₀ : Set (Perm (Fin n))) := by
    rintro _ ⟨g, rfl⟩
    rw [hGdef]
    refine Subgroup.mul_mem _ ?_ ?_
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (hcomm _ x).symm.eq
    · have h1 : i1910a3_c4 ^ (g.toAdd 0).val ∈
          Subgroup.normalizer (i1910a3_V4 : Set (Perm (Fin 4))) :=
        Subgroup.pow_mem _ i1910a3_c4_normalizes _
      exact Subgroup.le_normalizer_map Φ ⟨_, h1, rfl⟩
  refine ⟨E₀.subgroupOf A, T₀.subgroupOf A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · intro x hx
    obtain ⟨g, hg⟩ := (Subgroup.mem_subgroupOf.mp hx)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hg, ← map_pow]
    have : g ^ 3 = 1 := by
      have h30 : (3 : ZMod 3) = 0 := rfl
      apply Multiplicative.toAdd.injective
      funext j
      simp [h30]
    rw [this, map_one]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀A).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hGinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
    simp
  · intro hT
    have hmem : (⟨Φ i1910a3_u4, hT₀A ⟨_, (by
        change i1910a3_u4 = 1 ∨ i1910a3_u4 = i1910a3_u4 ∨ _ ∨ _
        exact Or.inr (Or.inl rfl) : i1910a3_u4 ∈ i1910a3_V4), rfl⟩⟩ : A) ∈ T₀.subgroupOf A :=
      Subgroup.mem_subgroupOf.mpr ⟨_, (by
        change i1910a3_u4 = 1 ∨ i1910a3_u4 = i1910a3_u4 ∨ _ ∨ _
        exact Or.inr (Or.inl rfl) : i1910a3_u4 ∈ i1910a3_V4), rfl⟩
    rw [hT, Subgroup.mem_bot] at hmem
    have := hΦinj ((congrArg Subtype.val hmem).trans (map_one Φ).symm)
    exact absurd this (by decide +kernel)
  · intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨x, hx, hgx⟩ := Subgroup.mem_subgroupOf.mp g.2
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← hgx]
    have : Φ x ^ 2 = 1 := by rw [← map_pow, i1910a3_V4_sq x hx, map_one]
    simpa using this
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hxN := hnorm (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_normalizer_iff] at hxN
    have := hxN (t : Perm (Fin n))
    simp only [Subgroup.mem_subgroupOf]
    exact this

end Build

end CFSG.HardMathSupport.Solomon.Coordinator
