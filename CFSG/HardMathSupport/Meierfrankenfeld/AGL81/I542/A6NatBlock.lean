module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EMod
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.S6Aut

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3

@[expose] def blkDim (i : ℕ) : ℕ := eNs.getD (i + 1) 0 - eNs.getD i 0

@[expose] def wordC33 : List Bool := [true, true, false, true, false, true, true, false]

theorem evalG_wordC33 : evalG wordC33 = c33A6 := by
  apply Subtype.ext
  decide +kernel

theorem gen_false_eq : gen false = c3A6 := rfl

@[expose] noncomputable def blkWord (i : ℕ) : List Bool → (Vec (blkDim i) →ₗ[ZMod 2] Vec (blkDim i))
  | [] => LinearMap.id
  | b :: w => (lin (blkDim i) (blkOf i b)).comp (blkWord i w)

@[expose] def fixCount {d : ℕ} (f : Vec d →ₗ[ZMod 2] Vec d) : ℕ :=
  (Finset.univ.filter fun v : Vec d => f v = v).card

theorem block_counts : ∀ i < 12, blkDim i = 4 →
    (fixCount (blkWord i [false]) = 4 ∧ fixCount (blkWord i wordC33) = 1) ∨
    (fixCount (blkWord i [false]) = 1 ∧ fixCount (blkWord i wordC33) = 4) := by
  decide +kernel

theorem blkDim_cases : ∀ i < 12, blkDim i = 1 ∨ blkDim i = 4 ∨ blkDim i = 16 := by
  decide +kernel

theorem blkDim_one_blkOf : ∀ i < 12, blkDim i = 1 → ∀ b, blkOf i b = [1] := by
  decide +kernel

theorem lin_one_one : ∀ s : Vec 1, lin 1 [1] s = s := by decide +kernel

theorem lin_one_of_dim {d : ℕ} (hd : d = 1) (s : Vec d) : lin d [1] s = s := by
  subst hd
  exact lin_one_one s

section Dims

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

section

variable [Finite W]

omit [Finite W] in
theorem intertwine_word {i : ℕ} (σ0 : S6 →* (W ≃ₗ[ZMod 2] W)) (Ψ : Vec (blkDim i) ≃ₗ[ZMod 2] W)
    (hΨ : ∀ (b : Bool) (s : Vec (blkDim i)), Ψ (lin (blkDim i) (blkOf i b) s) = σ0 (gen b) (Ψ s))
    (w : List Bool) (s : Vec (blkDim i)) : Ψ (blkWord i w s) = σ0 (evalG w) (Ψ s) := by
  induction w generalizing s with
  | nil => simp [blkWord, evalG]
  | cons b w ih =>
    simp only [blkWord, LinearMap.comp_apply, evalG, map_mul, LinearEquiv.mul_apply]
    rw [hΨ, ih]

theorem two_pow_finrank_ker {d : ℕ} (Ψ : Vec d ≃ₗ[ZMod 2] W) (M : Vec d →ₗ[ZMod 2] Vec d)
    (g : W ≃ₗ[ZMod 2] W) (h : ∀ s, Ψ (M s) = g (Ψ s)) :
    2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ((g : W →ₗ[ZMod 2] W) - 1)) = fixCount M := by
  have h1 : Nat.card ↥(LinearMap.ker ((g : W →ₗ[ZMod 2] W) - 1)) =
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ((g : W →ₗ[ZMod 2] W) - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [← h1]
  have h2 : Nat.card ↥(LinearMap.ker ((g : W →ₗ[ZMod 2] W) - 1)) =
      Nat.card {s : Vec d // M s = s} := by
    refine Nat.card_congr (Ψ.symm.toEquiv.subtypeEquiv fun w => ?_)
    have e1 : w ∈ LinearMap.ker ((g : W →ₗ[ZMod 2] W) - 1) ↔ g w = w := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      rfl
    rw [e1]
    show g w = w ↔ M (Ψ.symm w) = Ψ.symm w
    constructor
    · intro hw
      apply Ψ.injective
      rw [h, LinearEquiv.apply_symm_apply, hw]
    · intro hw
      have := congrArg Ψ hw
      rw [h, LinearEquiv.apply_symm_apply] at this
      exact this
  rw [h2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem a6_block_dims (σ0 : S6 →* (W ≃ₗ[ZMod 2] W)) (hS : IsLSimple σ0 ⊤ ⊤)
    (hdim : Module.finrank (ZMod 2) W ≤ 6) (hnt : σ0 c3A6 ≠ 1) :
    Module.finrank (ZMod 2) W = 4 ∧
      ((Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c3A6 : W →ₗ[ZMod 2] W) - 1)) = 2 ∧
          Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c33A6 : W →ₗ[ZMod 2] W) - 1)) = 0) ∨
        (Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c3A6 : W →ₗ[ZMod 2] W) - 1)) = 0 ∧
          Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c33A6 : W →ₗ[ZMod 2] W) - 1)) = 2)) := by
  obtain ⟨i, hi, Ψ, hΨ⟩ := exists_block_iso σ0 hS
  have hΨ' : ∀ (b : Bool) (s : Vec (blkDim i)),
      Ψ (lin (blkDim i) (blkOf i b) s) = σ0 (gen b) (Ψ s) := hΨ
  have hd : Module.finrank (ZMod 2) W = blkDim i := by
    rw [← LinearEquiv.finrank_eq Ψ]
    exact Module.finrank_fin_fun (ZMod 2)
  rcases blkDim_cases i hi with h1 | h4 | h16
  · exfalso
    apply hnt
    have : σ0 (gen false) = 1 := by
      apply LinearEquiv.ext
      intro w
      obtain ⟨s, rfl⟩ := Ψ.surjective w
      have key : lin (blkDim i) (blkOf i false) s = s := by
        rw [blkDim_one_blkOf i hi h1 false]
        exact lin_one_of_dim h1 s
      have := hΨ' false s
      rw [key] at this
      exact this.symm
    exact this
  · refine ⟨hd.trans h4, ?_⟩
    have hw : ∀ w : List Bool, ∀ s, Ψ (blkWord i w s) = σ0 (evalG w) (Ψ s) :=
      fun w s => intertwine_word σ0 Ψ hΨ' w s
    have hc3 : ∀ s, Ψ (blkWord i [false] s) = σ0 c3A6 (Ψ s) := by
      intro s; rw [hw]; simp [evalG, gen_false_eq]
    have hc33 : ∀ s, Ψ (blkWord i wordC33 s) = σ0 c33A6 (Ψ s) := by
      intro s; rw [hw, evalG_wordC33]
    have e3 := two_pow_finrank_ker Ψ _ (σ0 c3A6) hc3
    have e33 := two_pow_finrank_ker Ψ _ (σ0 c33A6) hc33
    rcases block_counts i hi h4 with ⟨a, b⟩ | ⟨a, b⟩
    · left
      have e3' : 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c3A6 : W →ₗ[ZMod 2] W) - 1)) =
          2 ^ 2 := e3.trans a
      have e33' : 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c33A6 : W →ₗ[ZMod 2] W) - 1)) =
          2 ^ 0 := e33.trans b
      exact ⟨Nat.pow_right_injective (le_refl 2) e3', Nat.pow_right_injective (le_refl 2) e33'⟩
    · right
      have e3' : 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c3A6 : W →ₗ[ZMod 2] W) - 1)) =
          2 ^ 0 := e3.trans a
      have e33' : 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker ((σ0 c33A6 : W →ₗ[ZMod 2] W) - 1)) =
          2 ^ 2 := e33.trans b
      exact ⟨Nat.pow_right_injective (le_refl 2) e3', Nat.pow_right_injective (le_refl 2) e33'⟩
  · omega

end

end Dims

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
