module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

section Coset

variable {N : Type} [Group N]

def cosetUnion (V : Subgroup N) (t : N) (htt : t * t = 1)
    (hVt : ∀ v ∈ V, t * v * t⁻¹ ∈ V) : Subgroup N where
  carrier := {p | p ∈ V ∨ p * t ∈ V}
  one_mem' := Or.inl V.one_mem
  mul_mem' := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rintro p q (hp | hp) (hq | hq)
    · exact Or.inl (V.mul_mem hp hq)
    · refine Or.inr ?_
      have : p * q * t = p * (q * t) := by group
      show p * q * t ∈ V
      rw [this]
      exact V.mul_mem hp hq
    · refine Or.inr ?_
      have h1 := hVt q hq
      have : p * q * t = (p * t) * (t * q * t⁻¹) := by
        calc p * q * t = p * (t * t) * q * t⁻¹ := by rw [htt, hti]; group
          _ = (p * t) * (t * q * t⁻¹) := by group
      show p * q * t ∈ V
      rw [this]
      exact V.mul_mem hp h1
    · refine Or.inl ?_
      have h1 := hVt _ hq
      have : p * q = (p * t) * (t * (q * t) * t⁻¹) := by
        calc p * q = p * (t * t) * q * (t * t⁻¹) := by rw [htt]; group
          _ = (p * t) * (t * (q * t) * t⁻¹) := by group
      show p * q ∈ V
      rw [this]
      exact V.mul_mem hp h1
  inv_mem' := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rintro p (hp | hp)
    · exact Or.inl (V.inv_mem hp)
    · refine Or.inr ?_
      have h1 := hVt _ (V.inv_mem hp)
      have : p⁻¹ * t = t * (p * t)⁻¹ * t⁻¹ := by rw [hti]; group
      show p⁻¹ * t ∈ V
      rw [this]
      exact h1

theorem mem_cosetUnion {V : Subgroup N} {t : N} {htt : t * t = 1}
    {hVt : ∀ v ∈ V, t * v * t⁻¹ ∈ V} {p : N} :
    p ∈ cosetUnion V t htt hVt ↔ p ∈ V ∨ p * t ∈ V := Iff.rfl

theorem relIndex_cosetUnion {V : Subgroup N} {t : N} (htt : t * t = 1)
    (hVt : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (htV : t ∉ V) :
    V.relIndex (cosetUnion V t htt hVt) = 2 := by
  have htP : t ∈ cosetUnion V t htt hVt :=
    mem_cosetUnion.2 (Or.inr (by rw [htt]; exact V.one_mem))
  show (V.subgroupOf (cosetUnion V t htt hVt)).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htP⟩, fun b => ?_⟩
  have hb : (b : N) ∈ V ∨ (b : N) * t ∈ V := mem_cosetUnion.1 b.2
  have hbt : ¬ ((b : N) ∈ V ∧ (b : N) * t ∈ V) := by
    rintro ⟨h1, h2⟩
    apply htV
    have := V.mul_mem (V.inv_mem h1) h2
    simpa using this
  show Xor (((b * ⟨t, htP⟩ : ↥(cosetUnion V t htt hVt)) : N) ∈ V) ((b : N) ∈ V)
  rcases hb with h | h
  · exact Or.inr ⟨h, fun h' => hbt ⟨h, h'⟩⟩
  · exact Or.inl ⟨h, fun h' => hbt ⟨h', h⟩⟩

theorem exists_phi {V Zf K : Subgroup N} {t z₀ : N} (htt : t * t = 1)
    (hVt : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hKt : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hKV : K ≤ V)
    (hZV : Zf ≤ V) (hdec : ∀ v ∈ V, ∃ k ∈ K, ∃ z ∈ Zf, v = k * z)
    (hKZ : ∀ x ∈ K, x ∈ Zf → x = 1) (hz₀ : z₀ ∈ Zf) (hz₀1 : z₀ ≠ 1)
    (hZf : ∀ z ∈ Zf, z = 1 ∨ z = z₀) (hz₀c : ∀ n : N, n * z₀ = z₀ * n) (hz₀2 : z₀ * z₀ = 1)
    (htV : t ∉ V) :
    ∃ ϕ : ↥(cosetUnion V t htt hVt) →* Multiplicative (ZMod 2),
      ϕ ⟨z₀, mem_cosetUnion.2 (Or.inl (hZV hz₀))⟩ ≠ 1 := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let P := cosetUnion V t htt hVt
  let H₀ := cosetUnion K t htt hKt
  have hz₀V : z₀ ∈ V := hZV hz₀
  have hz₀P : z₀ ∈ P := mem_cosetUnion.2 (Or.inl hz₀V)
  have hz₀H : z₀ ∉ H₀ := by
    rintro (h | h)
    · exact hz₀1 (hKZ z₀ h hz₀)
    · apply htV
      have h2 := hKV h
      have : t = z₀⁻¹ * (z₀ * t) := by group
      rw [this]
      exact V.mul_mem (V.inv_mem hz₀V) h2
  have hcover : ∀ p ∈ P, p ∈ H₀ ∨ z₀ * p ∈ H₀ := by
    rintro p (hp | hp)
    · obtain ⟨k, hk, z, hz, hpkz⟩ := hdec p hp
      rcases hZf z hz with h1 | h1
      · rw [h1, mul_one] at hpkz
        exact Or.inl (Or.inl (by rw [hpkz]; exact hk))
      · rw [h1] at hpkz
        refine Or.inr (Or.inl ?_)
        have : z₀ * p = k := by
          rw [hpkz]
          calc z₀ * (k * z₀) = (z₀ * k) * z₀ := by group
            _ = (k * z₀) * z₀ := by rw [← hz₀c k]
            _ = k := by rw [mul_assoc, hz₀2, mul_one]
        rw [this]
        exact hk
    · obtain ⟨k, hk, z, hz, hpkz⟩ := hdec _ hp
      rcases hZf z hz with h1 | h1
      · rw [h1, mul_one] at hpkz
        exact Or.inl (Or.inr (by rw [hpkz]; exact hk))
      · rw [h1] at hpkz
        refine Or.inr (Or.inr ?_)
        have : z₀ * p * t = k := by
          calc z₀ * p * t = z₀ * (p * t) := by group
            _ = z₀ * (k * z₀) := by rw [hpkz]
            _ = (z₀ * k) * z₀ := by group
            _ = (k * z₀) * z₀ := by rw [← hz₀c k]
            _ = k := by rw [mul_assoc, hz₀2, mul_one]
        rw [this]
        exact hk
  let g : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have hgg : g * g = 1 := by
    show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
    rw [← ofAdd_add]
    rfl
  have hg1 : g ≠ 1 := by
    intro h
    have := congrArg Multiplicative.toAdd h
    simp [g] at this
  let f : ↥P → Multiplicative (ZMod 2) := fun p => if (p : N) ∈ H₀ then 1 else g
  have hmul : ∀ p q : ↥P, f (p * q) = f p * f q := by
    intro p q
    by_cases hp : (p : N) ∈ H₀ <;> by_cases hq : (q : N) ∈ H₀
    · have : (p : N) * q ∈ H₀ := H₀.mul_mem hp hq
      simp [f, hp, hq, this]
    · have : (p : N) * q ∉ H₀ := fun h => hq (by
        have := H₀.mul_mem (H₀.inv_mem hp) h
        simpa using this)
      simp [f, hp, hq, this]
    · have : (p : N) * q ∉ H₀ := fun h => hp (by
        have := H₀.mul_mem h (H₀.inv_mem hq)
        simpa using this)
      simp [f, hp, hq, this]
    · have h1 : z₀ * (p : N) ∈ H₀ := (hcover p p.2).resolve_left hp
      have h2 : z₀ * (q : N) ∈ H₀ := (hcover q q.2).resolve_left hq
      have : (p : N) * q ∈ H₀ := by
        have h3 := H₀.mul_mem h1 h2
        have e : z₀ * (p : N) * (z₀ * (q : N)) = p * q := by
          calc z₀ * (p : N) * (z₀ * (q : N)) = z₀ * (z₀ * (p : N)) * (q : N) := by
                rw [mul_assoc, ← mul_assoc (p : N) z₀ q, ← hz₀c p]
                group
            _ = (p : N) * q := by rw [← mul_assoc, hz₀2, one_mul]
        rw [e] at h3
        exact h3
      simp [f, hp, hq, this, hgg]
  refine ⟨⟨⟨f, ?_⟩, hmul⟩, ?_⟩
  · simp [f, H₀.one_mem]
  · show f ⟨z₀, hz₀P⟩ ≠ 1
    simp [f, hz₀H, hg1]

open scoped IsMulCommutative in
theorem exists_retraction_of_transfer [Finite N] {z : N}
    (hzc : ∀ n : N, n * z = z * n) (hz2 : z * z = 1) {P : Subgroup N}
    (hzP : z ∈ P) (hodd : ¬ 2 ∣ P.index)
    (ϕ : P →* Multiplicative (ZMod 2)) (hϕ : ϕ ⟨z, hzP⟩ ≠ 1) :
    ∃ κ : N →* Multiplicative (ZMod 2), κ z ≠ 1 := by
  classical
  have : P.FiniteIndex := inferInstance
  refine ⟨MonoidHom.transfer ϕ, ?_⟩
  have key : ∀ (k : ℕ) (g₀ : N), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : g₀ * z ^ k = z ^ k * g₀ := (Commute.pow_right (hzc g₀) k).eq
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hc]
      _ = z ^ k := by group
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have hz_odd : z ^ P.index = z := by
    obtain ⟨k, hk⟩ : ∃ k, P.index = 2 * k + 1 := by
      rcases Nat.even_or_odd P.index with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact absurd ⟨k, by omega⟩ hodd
      · exact ⟨k, hk⟩
    rw [hk, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  intro h
  apply hϕ
  have h2 : ϕ ⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z key⟩ = ϕ ⟨z, hzP⟩ :=
    congrArg ϕ (Subtype.ext hz_odd)
  exact h2.symm.trans (h1.symm.trans h)

end Coset

section FK

variable {N : Type} [Group N] {F : Type} [Field F] [Fintype F]

theorem exists_K {V Zf : Subgroup N} (hcardF : Fintype.card F = 2) (hF2 : (2 : F) = 0)
    (hVel : ∀ v ∈ V, v * v = 1) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hVn : ∀ c : N, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (α : N →* SL(2, F)) (hαk : ∀ n, α n = 1 ↔ n ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : ∀ v : ↥V, β v = 1 ↔ (v : N) ∈ Zf)
    (hβe : ∀ (c : N) (u v : ↥V), (v : N) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {t : N} (htt : t * t = 1) (htV : t ∉ V) :
    ∃ K : Subgroup N, K ≤ V ∧ (∀ k ∈ K, t * k * t⁻¹ ∈ K) ∧
      (∀ v ∈ V, ∃ k ∈ K, ∃ z ∈ Zf, v = k * z) ∧ ∀ x ∈ K, x ∈ Zf → x = 1 := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨w₀, hw₀⟩ : ∃ w : Fin 2 → F, (α t : Matrix (Fin 2) (Fin 2) F).mulVec w ≠ w := by
    by_contra hcon
    have hall : ∀ w : Fin 2 → F, (α t : Matrix (Fin 2) (Fin 2) F).mulVec w = w := fun w => by
      by_contra h
      exact hcon ⟨w, h⟩
    exact htV ((hαk t).1 (sl2_eq_one_of_fix hall))
  obtain ⟨v₁, hv₁⟩ := hβ (Multiplicative.ofAdd w₀)
  have hv₁V : (v₁ : N) ∈ V := v₁.2
  have hv₂V : t * (v₁ : N) * t⁻¹ ∈ V := hVn t _ hv₁V
  set v₂ : ↥V := ⟨t * (v₁ : N) * t⁻¹, hv₂V⟩ with hv₂
  have hβv₂ : Multiplicative.toAdd (β v₂) = (α t : Matrix (Fin 2) (Fin 2) F).mulVec w₀ := by
    have := hβe t v₁ v₂ rfl
    rw [this, hv₁]
    rfl
  set w₁ := (α t : Matrix (Fin 2) (Fin 2) F).mulVec w₀ with hw₁
  have hw₀0 : w₀ ≠ 0 := by
    intro h
    apply hw₀
    rw [hw₁, h, Matrix.mulVec_zero]
  have hw₁0 : w₁ ≠ 0 := by
    intro h
    apply hw₀0
    have h2 := congrArg (fun w => ((α t)⁻¹ : SL(2, F)).1.mulVec w) h
    simp only [hw₁, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  have hw01 : w₁ ≠ w₀ := hw₀
  have hdbl : ∀ w : Fin 2 → F, w + w = 0 := fun w => by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination (w i) * hF2
  have hw01' : w₀ + w₁ ≠ 0 := by
    intro h
    apply hw01
    have h2 : w₀ + w₁ + w₀ = w₀ := by rw [h, zero_add]
    have h3 : w₀ + w₁ + w₀ = w₁ + (w₀ + w₀) := by abel
    rw [h3, hdbl, add_zero] at h2
    exact h2
  have hv₁sq : (v₁ : N) * v₁ = 1 := hVel _ hv₁V
  have hv₂sq : (v₂ : N) * v₂ = 1 := hVel _ v₂.2
  have hv₁₂ : (v₁ : N) * v₂ = v₂ * v₁ := hVab _ hv₁V _ v₂.2
  have h1inv : (v₁ : N)⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁sq
  have h2inv : (v₂ : N)⁻¹ = v₂ := inv_eq_of_mul_eq_one_right hv₂sq
  have h16 : ∀ a b : N, (a = 1 ∨ a = v₁ ∨ a = v₂ ∨ a = (v₁ : N) * v₂) →
      (b = 1 ∨ b = v₁ ∨ b = v₂ ∨ b = (v₁ : N) * v₂) →
      (a * b = 1 ∨ a * b = v₁ ∨ a * b = v₂ ∨ a * b = (v₁ : N) * v₂) := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp
    · right; left; simp
    · left; exact hv₁sq
    · right; right; right; rfl
    · right; right; left
      calc (v₁ : N) * (v₁ * v₂) = (v₁ * v₁) * v₂ := by group
        _ = v₂ := by rw [hv₁sq, one_mul]
    · right; right; left; simp
    · right; right; right; exact hv₁₂.symm
    · left; exact hv₂sq
    · right; left
      calc (v₂ : N) * (v₁ * v₂) = (v₂ * v₁) * v₂ := by group
        _ = (v₁ * v₂) * v₂ := by rw [← hv₁₂]
        _ = v₁ := by rw [mul_assoc, hv₂sq, mul_one]
    · right; right; right; simp
    · right; right; left
      calc (v₁ : N) * v₂ * v₁ = v₂ * v₁ * v₁ := by rw [hv₁₂]
        _ = v₂ := by rw [mul_assoc, hv₁sq, mul_one]
    · right; left
      calc (v₁ : N) * v₂ * v₂ = v₁ * (v₂ * v₂) := by group
        _ = v₁ := by rw [hv₂sq, mul_one]
    · left
      calc (v₁ : N) * v₂ * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ := by group
        _ = v₁ * (v₁ * v₂) * v₂ := by rw [← hv₁₂]
        _ = (v₁ * v₁) * (v₂ * v₂) := by group
        _ = 1 := by rw [hv₁sq, hv₂sq, one_mul]
  let K : Subgroup N :=
    { carrier := {x | x = 1 ∨ x = v₁ ∨ x = v₂ ∨ x = (v₁ : N) * v₂}
      one_mem' := Or.inl rfl
      mul_mem' := fun {a b} ha hb => h16 a b ha hb
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        · left; simp
        · right; left; exact h1inv
        · right; right; left; exact h2inv
        · right; right; right
          rw [mul_inv_rev, h1inv, h2inv]
          exact hv₁₂.symm }
  have hKV : K ≤ V := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact V.one_mem
    · exact hv₁V
    · exact v₂.2
    · exact V.mul_mem hv₁V v₂.2
  have ht₁ : t * (v₁ : N) * t⁻¹ = v₂ := rfl
  have ht₂ : t * (v₂ : N) * t⁻¹ = v₁ := by
    show t * (t * (v₁ : N) * t⁻¹) * t⁻¹ = v₁
    calc t * (t * (v₁ : N) * t⁻¹) * t⁻¹ = (t * t) * v₁ * (t⁻¹ * t⁻¹) := by group
      _ = v₁ := by rw [htt, hti, htt]; group
  have hβ₁ : Multiplicative.toAdd (β v₁) = w₀ := by rw [hv₁]; rfl
  have hall : ∀ u : Fin 2 → F, u = 0 ∨ u = w₀ ∨ u = w₁ ∨ u = w₀ + w₁ := by
    have h0 : (0 : Fin 2 → F) ∉ ({w₀, w₁, w₀ + w₁} : Finset (Fin 2 → F)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hw₀0.symm, hw₁0.symm, hw01'.symm⟩
    have h1 : w₀ ∉ ({w₁, w₀ + w₁} : Finset (Fin 2 → F)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hw01.symm, fun h => hw₁0 ?_⟩
      have h' : w₀ + 0 = w₀ + w₁ := by rw [add_zero]; exact h
      exact (add_left_cancel h').symm
    have h2 : w₁ ∉ ({w₀ + w₁} : Finset (Fin 2 → F)) := by
      simp only [Finset.mem_singleton]
      intro h
      apply hw₀0
      have h' : 0 + w₁ = w₀ + w₁ := by rw [zero_add]; exact h
      exact (add_right_cancel h').symm
    have hcard : ({0, w₀, w₁, w₀ + w₁} : Finset (Fin 2 → F)).card =
        Fintype.card (Fin 2 → F) := by
      rw [Fintype.card_fun, Fintype.card_fin, hcardF, Finset.card_insert_of_notMem h0,
        Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
      norm_num
    have huniv := Finset.eq_univ_of_card _ hcard
    intro u
    have : u ∈ ({0, w₀, w₁, w₀ + w₁} : Finset (Fin 2 → F)) := by
      rw [huniv]
      exact Finset.mem_univ u
    simpa using this
  refine ⟨K, hKV, ?_, ?_, ?_⟩
  · rintro k (rfl | rfl | rfl | rfl)
    · left; simp
    · right; right; left; exact ht₁
    · right; left; exact ht₂
    · right; right; right
      calc t * ((v₁ : N) * v₂) * t⁻¹ = (t * v₁ * t⁻¹) * (t * v₂ * t⁻¹) := by group
        _ = (v₂ : N) * v₁ := by rw [ht₁, ht₂]
        _ = v₁ * v₂ := hv₁₂.symm
  · intro v hv
    have hfin : ∀ (κ : ↥V), β κ = β ⟨v, hv⟩ → ∃ z ∈ Zf, v = (κ : N) * z := by
      intro κ hκ
      refine ⟨(κ : N)⁻¹ * v, ?_, by group⟩
      have : β (κ⁻¹ * ⟨v, hv⟩) = 1 := by rw [map_mul, map_inv, hκ, inv_mul_cancel]
      exact (hβk _).1 this
    rcases hall (Multiplicative.toAdd (β ⟨v, hv⟩)) with h | h | h | h
    · obtain ⟨z, hz, hvz⟩ := hfin 1 (by
        apply Multiplicative.toAdd.injective
        rw [h]; simp)
      exact ⟨1, K.one_mem, z, hz, by simpa using hvz⟩
    · obtain ⟨z, hz, hvz⟩ := hfin v₁ (by
        apply Multiplicative.toAdd.injective
        rw [h, hβ₁])
      exact ⟨v₁, Or.inr (Or.inl rfl), z, hz, hvz⟩
    · obtain ⟨z, hz, hvz⟩ := hfin v₂ (by
        apply Multiplicative.toAdd.injective
        rw [h, hβv₂])
      exact ⟨v₂, Or.inr (Or.inr (Or.inl rfl)), z, hz, hvz⟩
    · obtain ⟨z, hz, hvz⟩ := hfin (v₁ * v₂) (by
        apply Multiplicative.toAdd.injective
        rw [h, map_mul, toAdd_mul, hβ₁, hβv₂])
      exact ⟨(v₁ : N) * v₂, Or.inr (Or.inr (Or.inr rfl)), z, hz, hvz⟩
  · rintro x (rfl | rfl | rfl | rfl) hxZ
    · rfl
    · exfalso
      have h1 : β v₁ = 1 := (hβk v₁).2 hxZ
      apply hw₀0
      have := congrArg Multiplicative.toAdd h1
      rw [hβ₁] at this
      exact this
    · exfalso
      have h1 : β v₂ = 1 := (hβk v₂).2 hxZ
      apply hw₁0
      have := congrArg Multiplicative.toAdd h1
      rw [hβv₂] at this
      exact this
    · exfalso
      have h1 : β (v₁ * v₂) = 1 := (hβk (v₁ * v₂)).2 hxZ
      apply hw01'
      have := congrArg Multiplicative.toAdd h1
      rw [map_mul, toAdd_mul, hβ₁, hβv₂] at this
      exact this

theorem card_sl2_two (hcardF : Fintype.card F = 2) : Nat.card SL(2, F) = 6 := by
  rw [Matrix.card_SL_field (𝔽 := F) 2, hcardF]
  simp [Fin.prod_univ_two]

theorem exists_kappa [Finite N] {V Zf : Subgroup N}
    (hcardF : Fintype.card F = 2) (hF2 : (2 : F) = 0)
    (hVel : ∀ v ∈ V, v * v = 1) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hZV : Zf ≤ V) (hZc : ∀ n : N, ∀ z ∈ Zf, n * z = z * n) (hZcard : Nat.card Zf = 2)
    (α : N →* SL(2, F)) (hα : Function.Surjective α) (hαk : ∀ n, α n = 1 ↔ n ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : ∀ v : ↥V, β v = 1 ↔ (v : N) ∈ Zf)
    (hβe : ∀ (c : N) (u v : ↥V), (v : N) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {t : N} (htt : t * t = 1) (htV : t ∉ V) :
    ∃ κ : N →* Multiplicative (ZMod 2), ∀ z ∈ Zf, z ≠ 1 → κ z ≠ 1 := by
  classical
  have hVn : ∀ c : N, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    intro c v hv
    rw [← hαk] at hv ⊢
    rw [map_mul, map_mul, hv, mul_one, map_inv, mul_inv_cancel]
  have hVt : ∀ v ∈ V, t * v * t⁻¹ ∈ V := hVn t
  obtain ⟨K, hKV, hKt, hdec, hKZ⟩ :=
    exists_K hcardF hF2 hVel hVab hVn α hαk β hβ hβk hβe htt htV
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hZcard
  have hall : ∀ w : ↥Zf, w = x ∨ w = y := fun w => by
    have : w ∈ ({x, y} : Set ↥Zf) := by rw [hset]; exact Set.mem_univ w
    simpa using this
  obtain ⟨z₀, hz₀, hz₀1, hZf⟩ : ∃ z₀ ∈ Zf, z₀ ≠ 1 ∧ ∀ z ∈ Zf, z = 1 ∨ z = z₀ := by
    by_cases hx1 : (x : N) = 1
    · have hy1 : (y : N) ≠ 1 := fun h => hxy (Subtype.ext (hx1.trans h.symm))
      refine ⟨y, y.2, hy1, fun z hz => ?_⟩
      rcases hall ⟨z, hz⟩ with h | h
      · left
        rw [← hx1]
        exact congrArg Subtype.val h
      · right
        exact congrArg Subtype.val h
    · have hy1 : (y : N) = 1 := by
        rcases hall ⟨1, Zf.one_mem⟩ with h | h
        · exact absurd (congrArg Subtype.val h).symm hx1
        · exact (congrArg Subtype.val h).symm
      refine ⟨x, x.2, hx1, fun z hz => ?_⟩
      rcases hall ⟨z, hz⟩ with h | h
      · right
        exact congrArg Subtype.val h
      · left
        rw [← hy1]
        exact congrArg Subtype.val h
  have hz₀c : ∀ n : N, n * z₀ = z₀ * n := fun n => hZc n z₀ hz₀
  have hz₀2 : z₀ * z₀ = 1 := hVel z₀ (hZV hz₀)
  obtain ⟨ϕ, hϕ⟩ := exists_phi htt hVt hKt hKV hZV hdec hKZ hz₀ hz₀1 hZf hz₀c hz₀2 htV
  have hVker : α.ker = V := by
    ext n
    rw [MonoidHom.mem_ker, hαk]
  have hVidx : V.index = 6 := by
    rw [← hVker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hα, Subgroup.card_top,
      card_sl2_two hcardF]
  have hrel := Subgroup.relIndex_mul_index
    (show V ≤ cosetUnion V t htt hVt from fun v hv => mem_cosetUnion.2 (Or.inl hv))
  rw [relIndex_cosetUnion htt hVt htV, hVidx] at hrel
  have hodd : ¬ 2 ∣ (cosetUnion V t htt hVt).index := by
    have h3 : (cosetUnion V t htt hVt).index = 3 := by omega
    rw [h3]
    decide
  obtain ⟨κ, hκ⟩ := exists_retraction_of_transfer hz₀c hz₀2
    (mem_cosetUnion.2 (Or.inl (hZV hz₀))) hodd ϕ hϕ
  refine ⟨κ, fun z hz hz1 => ?_⟩
  rcases hZf z hz with h | h
  · exact absurd h hz1
  · rw [h]
    exact hκ

theorem zmod2_mul_eq_one : ∀ x y : Multiplicative (ZMod 2), x ≠ 1 → y ≠ 1 → x * y = 1 := by
  decide

theorem z2_s4_of_kappa [Finite N] {V Zf : Subgroup N}
    (hcardF : Fintype.card F = 2) (hF2 : (2 : F) = 0) (hVel : IsElemAbelian 2 V)
    (hZV : Zf ≤ V) (hZc : ∀ n : N, ∀ z ∈ Zf, n * z = z * n) (hZcard : Nat.card Zf = 2)
    (α : N →* SL(2, F)) (hα : Function.Surjective α) (hαk : ∀ n, α n = 1 ↔ n ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : ∀ v : ↥V, β v = 1 ↔ (v : N) ∈ Zf)
    (hβe : ∀ (c : N) (u v : ↥V), (v : N) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (κ : N →* Multiplicative (ZMod 2)) (hκ : ∀ z ∈ Zf, z ≠ 1 → κ z ≠ 1) :
    Nonempty (N ≃* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) := by
  classical
  have hVn : ∀ c : N, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    intro c v hv
    rw [← hαk] at hv ⊢
    rw [map_mul, map_mul, hv, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ Zf, z₀ ≠ 1 := by
    obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.1 hZcard
    by_cases hx1 : (x : N) = 1
    · exact ⟨y, y.2, fun h => hxy (Subtype.ext (hx1.trans h.symm))⟩
    · exact ⟨x, x.2, hx1⟩
  have hκz₀ : κ z₀ ≠ 1 := hκ z₀ hz₀ hz₀1
  have hfix : ∀ n : N, ∃ z ∈ Zf, κ (n * z) = 1 := by
    intro n
    by_cases hn : κ n = 1
    · exact ⟨1, Zf.one_mem, by simpa using hn⟩
    · exact ⟨z₀, hz₀, by rw [map_mul]; exact zmod2_mul_eq_one _ _ hn hκz₀⟩
  let C₀ : Subgroup N := κ.ker
  have hC₀ : ∀ n, n ∈ C₀ ↔ κ n = 1 := fun n => MonoidHom.mem_ker
  have hz₀C₀ : ∀ z ∈ Zf, z ∈ C₀ → z = 1 := by
    intro z hz hzC
    by_contra h
    exact hκ z hz h ((hC₀ z).1 hzC)
  have hperm : Nonempty (↥C₀ ≃* Equiv.Perm (Fin 4)) := by
    have hVel₀ : IsElemAbelian 2 (V ⊓ C₀) := IsElemAbelian.mono inf_le_left hVel
    refine perm_four_of_data (C := C₀) (V := V ⊓ C₀) hcardF hF2 inf_le_right hVel₀ ?_
      (α.comp C₀.subtype) ?_ ?_ (β.comp (Subgroup.inclusion (inf_le_left : V ⊓ C₀ ≤ V))) ?_ ?_ ?_
    · intro c hc v hv
      refine ⟨hVn c v hv.1, (hC₀ _).2 ?_⟩
      have h1 : κ c = 1 := (hC₀ c).1 hc
      have h2 : κ v = 1 := (hC₀ v).1 hv.2
      have h3 : κ c⁻¹ = 1 := by
        have := (map_mul κ c c⁻¹).symm
        rw [mul_inv_cancel, map_one, h1, one_mul] at this
        exact this
      rw [map_mul, map_mul, h1, h2, h3, one_mul, one_mul]
    · intro Y
      obtain ⟨n, hn⟩ := hα Y
      obtain ⟨z, hz, hnz⟩ := hfix n
      refine ⟨⟨n * z, (hC₀ _).2 hnz⟩, ?_⟩
      show α (n * z) = Y
      have : α z = 1 := (hαk z).2 (hZV hz)
      rw [map_mul, this, mul_one, hn]
    · intro c
      show α c = 1 ↔ (c : N) ∈ V ⊓ C₀
      rw [hαk]
      exact ⟨fun h => ⟨h, c.2⟩, fun h => h.1⟩
    · intro y
      obtain ⟨v, hv⟩ := hβ y
      obtain ⟨z, hz, hvz⟩ := hfix (v : N)
      have hzV : z ∈ V := hZV hz
      refine ⟨⟨(v : N) * z, V.mul_mem v.2 hzV, (hC₀ _).2 hvz⟩, ?_⟩
      show β ⟨(v : N) * z, V.mul_mem v.2 hzV⟩ = y
      have e : (⟨(v : N) * z, V.mul_mem v.2 hzV⟩ : ↥V) = v * ⟨z, hzV⟩ := rfl
      rw [e, map_mul, (hβk ⟨z, hzV⟩).2 hz, mul_one, hv]
    · intro v hv
      have h1 : (v : N) ∈ Zf := (hβk ⟨v, v.2.1⟩).1 hv
      exact Subtype.ext (hz₀C₀ _ h1 v.2.2)
    · intro c u v hv
      exact hβe (c : N) ⟨u, u.2.1⟩ ⟨v, v.2.1⟩ hv
  obtain ⟨e₀⟩ := hperm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥Zf := isCyclic_of_prime_card (p := 2) hZcard
  have hcyc' : IsCyclic (Multiplicative (ZMod 2)) :=
    isCyclic_of_prime_card (p := 2) (by simp [Nat.card_eq_fintype_card])
  have hcard : Nat.card ↥Zf = Nat.card (Multiplicative (ZMod 2)) := by
    rw [hZcard]
    simp [Nat.card_eq_fintype_card]
  let eZ : ↥Zf ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq hcard
  let φ : ↥C₀ × ↥Zf →* N := C₀.subtype.noncommCoprod Zf.subtype
    (fun c z => hZc (c : N) (z : N) z.2)
  have hφ : ∀ c z, φ (c, z) = (c : N) * z := fun c z => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨c, z⟩ h
    rw [hφ] at h
    have hκc : κ (c : N) = 1 := (hC₀ _).1 c.2
    have hκz : κ (z : N) = 1 := by
      have h1 : κ ((c : N) * z) = 1 := by rw [h, map_one]
      rwa [map_mul, hκc, one_mul] at h1
    have hz1 : (z : N) = 1 := hz₀C₀ _ z.2 ((hC₀ _).2 hκz)
    have hc1 : (c : N) = 1 := by
      rw [hz1, mul_one] at h
      exact h
    exact Prod.ext (Subtype.ext hc1) (Subtype.ext hz1)
  have hsurj : Function.Surjective φ := by
    intro n
    obtain ⟨z, hz, hnz⟩ := hfix n
    refine ⟨(⟨n * z, (hC₀ _).2 hnz⟩, ⟨z⁻¹, Zf.inv_mem hz⟩), ?_⟩
    rw [hφ]
    show n * z * z⁻¹ = n
    group
  let eN : ↥C₀ × ↥Zf ≃* N := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact ⟨eN.symm.trans (MulEquiv.prodCongr e₀ eZ)⟩

end FK

section Transport

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem z2_s4_of_data {C V Zf : Subgroup G}
    (hcardF : Fintype.card F = 2) (hF2 : (2 : F) = 0) (hVC : V ≤ C) (hVel : IsElemAbelian 2 V)
    (hZV : Zf ≤ V) (hZc : ∀ c ∈ C, ∀ z ∈ Zf, c * z = z * c) (hZcard : Nat.card Zf = 2)
    (α : ↥C →* SL(2, F)) (hα : Function.Surjective α)
    (hαk : ∀ c : ↥C, α c = 1 ↔ (c : G) ∈ V)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβk : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Zf)
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {t : G} (htC : t ∈ C) (htt : t * t = 1) (htV : t ∉ V) :
    Nonempty (↥C ≃* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) := by
  classical
  let VN : Subgroup ↥C := V.subgroupOf C
  let ZN : Subgroup ↥C := Zf.subgroupOf C
  let eV : ↥VN ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVC
  let βN : ↥VN →* Multiplicative (Fin 2 → F) := β.comp eV.toMonoidHom
  have hVN : ∀ x : ↥C, x ∈ VN ↔ (x : G) ∈ V := fun x => Subgroup.mem_subgroupOf
  have hZN : ∀ x : ↥C, x ∈ ZN ↔ (x : G) ∈ Zf := fun x => Subgroup.mem_subgroupOf
  have hVelN : IsElemAbelian 2 VN := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact IsElemAbelian.comm hVel ((hVN a).1 a.2) ((hVN b).1 b.2)
    · apply Subtype.ext
      exact hVel.2 _ ((hVN x).1 hx)
  have hZcardN : Nat.card ZN = 2 := by
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZV.trans hVC)).toEquiv
  have hβN : Function.Surjective βN := by
    intro y
    obtain ⟨v, hv⟩ := hβ y
    exact ⟨eV.symm v, by simp [βN, hv]⟩
  have hβkN : ∀ v : ↥VN, βN v = 1 ↔ ((v : ↥C) : ↥C) ∈ ZN := by
    intro v
    show β (eV v) = 1 ↔ _
    rw [hβk, hZN]
    rfl
  have hβeN : ∀ (c : ↥C) (u v : ↥VN), (v : ↥C) = c * u * c⁻¹ →
      Multiplicative.toAdd (βN v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (βN u)) := by
    intro c u v hv
    apply hβe c (eV u) (eV v)
    exact congrArg Subtype.val hv
  have hZcN : ∀ n : ↥C, ∀ z ∈ ZN, n * z = z * n := by
    intro n z hz
    apply Subtype.ext
    exact hZc n n.2 z ((hZN z).1 hz)
  have hZVN : ZN ≤ VN := fun z hz => (hVN z).2 (hZV ((hZN z).1 hz))
  have hVabN : ∀ a ∈ VN, ∀ b ∈ VN, a * b = b * a := fun a ha b hb =>
    Subtype.ext (IsElemAbelian.comm hVel ((hVN a).1 ha) ((hVN b).1 hb))
  have hVelN' : ∀ v ∈ VN, v * v = 1 := fun v hv => Subtype.ext (by
    have := hVel.2 _ ((hVN v).1 hv)
    simpa [sq] using this)
  let tN : ↥C := ⟨t, htC⟩
  have httN : tN * tN = 1 := Subtype.ext htt
  have htVN : tN ∉ VN := fun h => htV ((hVN tN).1 h)
  have hαkN : ∀ n : ↥C, α n = 1 ↔ n ∈ VN := fun n => by rw [hαk, hVN]
  obtain ⟨κ, hκ⟩ := exists_kappa (V := VN) (Zf := ZN) hcardF hF2 hVelN' hVabN hZVN hZcN hZcardN α
    hα hαkN βN hβN hβkN hβeN httN htVN
  exact z2_s4_of_kappa hcardF hF2 hVelN hZVN hZcN hZcardN α hα hαkN βN hβN hβkN hβeN κ hκ

end Transport

end CFSG.QuasithinUnique.Lin2
