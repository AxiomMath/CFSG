module

public import CFSG.Fischer.Classification.Orthogonal3.Local

public section

namespace CFSG.Fischer.Classification.Recognition.R3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification F3

variable {n : ℕ}

@[expose] noncomputable def normCount (f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3))
    (c : ZMod 3) : ℕ :=
  Nat.card {x : Fin n → ZMod 3 // f x x = c}

theorem normCount_def (f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)) (c : ZMod 3) :
    normCount f c = Nat.card {x : Fin n → ZMod 3 // f x x = c} :=
  rfl

section Split

variable {f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3)} {v : Fin (n + 1) → ZMod 3}

theorem pair_splitEquiv (hv : f v v = 1) (a : ZMod 3) (w : F3.perpOne f v) :
    f (a • v + w) v = a := by
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hv, F3.mem_perpOne.1 w.2,
    mul_one, add_zero]

noncomputable def splitEquiv (hv : f v v = 1) :
    ZMod 3 × F3.perpOne f v ≃ (Fin (n + 1) → ZMod 3) where
  toFun p := p.1 • v + p.2
  invFun x := (f x v, ⟨x - f x v • v, F3.mem_perpOne.2 (by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self])⟩)
  left_inv p := by
    obtain ⟨a, w⟩ := p
    refine Prod.ext (pair_splitEquiv hv a w) (Subtype.ext ?_)
    simp only [pair_splitEquiv hv a w]
    abel
  right_inv x := by
    simp only
    abel

theorem norm_splitEquiv (hf : IsF3Form f) (hv : f v v = 1) (p : ZMod 3 × F3.perpOne f v) :
    f (splitEquiv hv p) (splitEquiv hv p) = p.1 * p.1 + f p.2 p.2 := by
  obtain ⟨a, w⟩ := p
  have hw : f v w = 0 := by rw [hf.symm]; exact F3.mem_perpOne.1 w.2
  change f (a • v + w) (a • v + w) = a * a + f w w
  rw [F3.norm_add hf, F3.norm_smul, hv, LinearMap.BilinForm.smul_left, hw]
  ring

theorem normCount_eq (hf : IsF3Form f) (hv : f v v = 1)
    (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) (c : ZMod 3) :
    normCount f c = normCount (restrictForm f e) c + 2 * normCount (restrictForm f e) (c - 1) := by
  have h1 : normCount f c =
      Nat.card {p : ZMod 3 × F3.perpOne f v // p.1 * p.1 + f p.2 p.2 = c} :=
    Nat.card_congr ((splitEquiv hv).subtypeEquiv fun p => by
      rw [norm_splitEquiv hf hv]).symm
  have h2 : ∀ a : ZMod 3, Nat.card {w : F3.perpOne f v // a * a + f w w = c} =
      normCount (restrictForm f e) (c - a * a) := fun a =>
    Nat.card_congr (e.toEquiv.subtypeEquiv fun w => by
      change _ ↔ restrictForm f e (e w) (e w) = c - a * a
      rw [restrictForm_apply]
      constructor <;> intro h <;> linear_combination h)
  rw [h1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      fun (a : ZMod 3) (w : F3.perpOne f v) => a * a + f w w = c),
    Nat.card_sigma]
  simp only [h2]
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    show (2 : ZMod 3) * 2 = 1 from rfl, mul_zero, sub_zero, mul_one]
  ring

end Split

@[expose] def T (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.1 + 2 * t.2.2, t.2.1 + 2 * t.1, t.2.2 + 2 * t.2.1)

theorem normTriple_one {f : LinearMap.BilinForm (ZMod 3) (Fin 1 → ZMod 3)} (hf : IsF3Form f) :
    (normCount f 0, normCount f 1, normCount f 2) = (1, 2, 0) ∨
      (normCount f 0, normCount f 1, normCount f 2) = (1, 0, 2) := by
  set o : Fin 1 → ZMod 3 := fun _ => 1
  have hx : ∀ x : Fin 1 → ZMod 3, x = x 0 • o := fun x => by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [o]
  have hnorm : ∀ x : Fin 1 → ZMod 3, f x x = x 0 * x 0 * f o o := fun x => by
    conv_lhs => rw [hx x]
    rw [F3.norm_smul]
  have hl : f o o ≠ 0 := by
    intro h0
    have : o = 0 := hf.nondeg o fun y => by
      rw [hx y, LinearMap.BilinForm.smul_right, h0, mul_zero]
    exact one_ne_zero (congrFun this 0)
  have hc : ∀ c, normCount f c = Fintype.card {a : ZMod 3 // a * a * f o o = c} := fun c => by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((Equiv.funUnique (Fin 1) (ZMod 3)).subtypeEquiv fun x => by
      rw [hnorm]
      rfl)
  rw [hc, hc, hc]
  generalize f o o = l at hl
  revert l
  decide

theorem normTriple_eq : ∀ (n : ℕ) (f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3)),
    IsF3Form f → (normCount f 0, normCount f 1, normCount f 2) = T^[n] (1, 2, 0) ∨
      (normCount f 0, normCount f 1, normCount f 2) = T^[n] (1, 0, 2)
  | 0, _, hf => normTriple_one hf
  | n + 1, f, hf => by
    obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
    let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin (n + 1) → ZMod 3) :=
      LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun]; omega)
    have h : (normCount f 0, normCount f 1, normCount f 2) =
        T (normCount (restrictForm f e) 0, normCount (restrictForm f e) 1,
          normCount (restrictForm f e) 2) := by
      rw [normCount_eq hf hv e 0, normCount_eq hf hv e 1, normCount_eq hf hv e 2, T]
      rfl
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h]
    rcases normTriple_eq n (restrictForm f e) (isF3Form_restrictForm hf hv e) with h' | h'
    · exact Or.inl (by rw [h'])
    · exact Or.inr (by rw [h'])

theorem normCount_one_mem {f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3)}
    (hf : IsF3Form f) :
    normCount f 1 = (T^[n] (1, 2, 0)).2.1 ∨ normCount f 1 = (T^[n] (1, 0, 2)).2.1 := by
  rcases normTriple_eq n f hf with h | h
  · exact Or.inl (by rw [← h])
  · exact Or.inr (by rw [← h])

theorem not_eleven_dvd_normCount {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    (hf : IsF3Form f) (hn : 5 ≤ n) (hn' : n ≤ 9) : ¬ 11 ∣ normCount f 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have key : ∀ k < 9, 4 ≤ k → ¬ 11 ∣ (T^[k] (1, 2, 0)).2.1 ∧ ¬ 11 ∣ (T^[k] (1, 0, 2)).2.1 := by
    decide
  obtain ⟨h₁, h₂⟩ := key k (by omega) (by omega)
  rcases normCount_one_mem hf with h | h <;> rw [h]
  · exact h₁
  · exact h₂

theorem pow_dvd_normCount {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    (hf : IsF3Form f) :
    ((n = 7 ∨ n = 8) → 3 ^ 3 ∣ normCount f 1) ∧ ((n = 9 ∨ n = 10) → 3 ^ 4 ∣ normCount f 1) := by
  have key : ∀ k < 10, ((k = 6 ∨ k = 7) → 3 ^ 3 ∣ (T^[k] (1, 2, 0)).2.1 ∧
      3 ^ 3 ∣ (T^[k] (1, 0, 2)).2.1) ∧ ((k = 8 ∨ k = 9) → 3 ^ 4 ∣ (T^[k] (1, 2, 0)).2.1 ∧
      3 ^ 4 ∣ (T^[k] (1, 0, 2)).2.1) := by
    decide
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h₁, h₂⟩ := (key k (by omega)).1 (by omega)
    rcases normCount_one_mem hf with h | h <;> rw [h]
    · exact h₁
    · exact h₂
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h₁, h₂⟩ := (key k (by omega)).2 (by omega)
    rcases normCount_one_mem hf with h | h <;> rw [h]
    · exact h₁
    · exact h₂

end CFSG.Fischer.Classification.Recognition.R3
