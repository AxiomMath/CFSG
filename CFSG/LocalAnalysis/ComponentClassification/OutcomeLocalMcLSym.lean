module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import CFSG.Fischer.Classification.Symplectic.Stars

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module Submodule CFSG.Fischer.Classification.Symplectic
open CFSG.Fischer.Classification.Symplectic.SympConfig

@[expose] def dotB (m : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin m → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum])

theorem dotB_apply {m : ℕ} (x y : Fin m → ZMod 2) : dotB m x y = ∑ i, x i * y i :=
  rfl

theorem dotB_pairVec {m : ℕ} (x : Fin m → ZMod 2) (i j : Fin m) :
    dotB m x (pairVec i j) = x i + x j := by
  classical
  rw [dotB_apply, coe_pairVec]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (C : SympConfig V)

theorem exists_sumZero_hom [Finite V] (hTN : C.TN) (hD : C.D.Nonempty) :
    ∃ (m : ℕ) (γ : sumZero m →ₗ[ZMod 2] V),
      (∀ x y : sumZero m, C.b (γ x) (γ y) = dotB m x y) ∧
      (∀ i j : Fin m, i ≠ j → γ (pairVec i j) ∈ C.D) ∧
      ∀ d ∈ C.D, ∃ i j : Fin m, i ≠ j ∧ γ (pairVec i j) = d := by
  classical
  let m := Nat.card C.Stars
  let e : C.Stars ≃ Fin m := Finite.equivFin C.Stars
  let T : Fin m → Set V := fun j => (e.symm j : Set V)
  have hT : ∀ j, C.IsStar (T j) := fun j => (e.symm j).2
  have hTinj : ∀ j k, T j = T k → j = k := fun j k h => e.symm.injective (Subtype.ext h)
  have hTD : ∀ j, T j ⊆ C.D := fun j f hf => by
    obtain ⟨d, hd, c, hc, hdc, hS⟩ := hT j
    rw [hS] at hf
    exact hf.1
  have hTe : ∀ S : C.Stars, T (e S) = S := fun S => by simp [T]
  obtain ⟨d₀, hd₀⟩ := hD
  obtain ⟨e₀, he₀, he₀d₀⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hd₀)
  have hd₀e₀ : C.b d₀ e₀ = 1 := by rw [C.comm]; exact he₀d₀
  let i₀ : Fin m := e ⟨C.star d₀ e₀, isStar_star hd₀ he₀ hd₀e₀⟩
  have hmeet : ∀ j, j ≠ i₀ → ∃ f, f ∈ T i₀ ∧ f ∈ T j := fun j hj =>
    exists_mem_inter hTN (hT i₀) (hT j) fun h => hj (hTinj _ _ h).symm
  choose! q hq using hmeet
  let p : Fin m → V := fun j => if j = i₀ then 0 else q j
  have hp0 : p i₀ = 0 := by simp [p]
  have hpT : ∀ j, j ≠ i₀ → p j ∈ T i₀ ∧ p j ∈ T j := fun j hj => by
    have h : p j = q j := by simp [p, hj]
    rw [h]
    exact hq j hj
  have hpD : ∀ j, j ≠ i₀ → p j ∈ C.D := fun j hj => hTD j (hpT j hj).2
  have hpne : ∀ j k, j ≠ i₀ → k ≠ i₀ → j ≠ k → p j ≠ p k := by
    intro j k hj hk hjk h
    have h1 := hpT j hj
    have h2 := hpT k hk
    rw [h] at h1
    rcases eq_or_eq_of_mem_of_mem hTN (hpD k hk) (hT i₀) (hT j) (hT k)
      (fun h' => hj (hTinj _ _ h').symm) h2.1 h1.2 h2.2 with h' | h'
    · exact hk (hTinj _ _ h')
    · exact hjk (hTinj _ _ h').symm
  have hclique : ∀ f ∈ T i₀, ∀ g ∈ T i₀, f ≠ g → C.b f g = 1 := by
    obtain ⟨a, ha, c, hc, hac, hS⟩ := hT i₀
    intro f hf g hg hfg
    rw [hS] at hf hg
    exact b_eq_one_of_mem_star hTN ha hc hac hf hg hfg
  have hgram : ∀ j k, C.b (p j) (p k) =
      dotB m (Pi.single i₀ 1 + Pi.single j 1) (Pi.single i₀ 1 + Pi.single k 1) := by
    intro j k
    rw [show (Pi.single i₀ 1 + Pi.single k 1 : Fin m → ZMod 2) = pairVec i₀ k from rfl,
      dotB_pairVec]
    by_cases hj : j = i₀
    · rw [hj, hp0, map_zero, LinearMap.zero_apply]
      have h0 : (Pi.single i₀ 1 + Pi.single i₀ 1 : Fin m → ZMod 2) = 0 :=
        funext fun l => add_self_zmod2 _
      rw [h0, Pi.zero_apply, Pi.zero_apply, add_zero]
    by_cases hk : k = i₀
    · rw [hk, hp0, map_zero, add_self_zmod2]
    by_cases hjk : j = k
    · subst hjk
      rw [C.self_eq_zero, Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same,
        Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (Ne.symm hj), add_zero, zero_add,
        add_self_zmod2]
    · rw [hclique _ (hpT j hj).1 _ (hpT k hk).1 (hpne j k hj hk hjk), Pi.add_apply, Pi.add_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj), Pi.single_eq_of_ne hk,
        Pi.single_eq_of_ne (Ne.symm hjk), add_zero, add_zero, add_zero]
  let γ₀ : (Fin m → ZMod 2) →ₗ[ZMod 2] V := Fintype.linearCombination (ZMod 2) p
  let L : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    Fintype.linearCombination (ZMod 2) fun j => Pi.single i₀ 1 + Pi.single j 1
  have hbil : C.b.compl₁₂ γ₀ γ₀ = (dotB m).compl₁₂ L L :=
    LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin m)) fun j k => by
      simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, γ₀, L,
        Fintype.linearCombination_apply_single, one_smul]
      exact hgram j k
  have hL : ∀ x ∈ sumZero m, L x = x := by
    intro x hx
    rw [mem_sumZero] at hx
    simp only [L, Fintype.linearCombination_apply, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul, hx, zero_smul, zero_add]
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  let γ : sumZero m →ₗ[ZMod 2] V := γ₀ ∘ₗ (sumZero m).subtype
  have hγpair : ∀ i j, γ (pairVec i j) = p i + p j := by
    intro i j
    simp only [γ, γ₀, LinearMap.comp_apply, Submodule.coe_subtype, coe_pairVec, map_add,
      Fintype.linearCombination_apply_single, one_smul]
  have hpairT : ∀ i j, i ≠ j → p i + p j ∈ T i ∧ p i + p j ∈ T j := by
    intro i j hij
    by_cases hi : i = i₀
    · subst hi
      rw [hp0, zero_add]
      exact hpT j (Ne.symm hij)
    by_cases hj : j = i₀
    · subst hj
      rw [hp0, add_zero]
      exact ⟨(hpT i hi).2, (hpT i hi).1⟩
    have hdi := hpD i hi
    have hdj := hpD j hj
    have hb : C.b (p i) (p j) = 1 := hclique _ (hpT i hi).1 _ (hpT j hj).1 (hpne i j hi hj hij)
    have hsum : p i + p j ∈ C.D := C.add_mem _ hdi _ hdj hb
    have hT0 : T i₀ = C.star (p i) (p j) := by
      obtain ⟨a, ha, c, hc, hac, hS⟩ := hT i₀
      have h1 := (hpT i hi).1
      have h2 := (hpT j hj).1
      rw [hS] at h1 h2 ⊢
      exact (star_eq_star hTN ha hc hac h1 h2 (hpne i j hi hj hij)).symm
    constructor
    · rcases eq_or_eq_of_mem hTN hdi hdj hb (hT i) (hpT i hi).2 with h | h
      · exact absurd (hTinj _ _ (h.trans hT0.symm)) hi
      · rw [h]
        exact mem_star_right hsum
    · have hb' : C.b (p j) (p i) = 1 := by rw [C.comm]; exact hb
      rcases eq_or_eq_of_mem hTN hdj hdi hb' (hT j) (hpT j hj).2 with h | h
      · exact absurd (hTinj _ _ (h.trans (by rw [hT0, star_comm]))) hj
      · rw [h]
        convert mem_star_right (C.add_mem _ hdj _ hdi hb') using 1
        exact add_comm _ _
  refine ⟨m, γ, fun x y => ?_, fun i j hij => ?_, fun d hd => ?_⟩
  · have h := LinearMap.congr_fun₂ hbil (x : Fin m → ZMod 2) (y : Fin m → ZMod 2)
    simp only [LinearMap.compl₁₂_apply] at h
    rw [hL x x.2, hL y y.2] at h
    exact h
  · rw [hγpair]
    exact hTD i (hpairT i j hij).1
  · obtain ⟨u, hu, hud⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hd)
    have hdu : C.b d u = 1 := by rw [C.comm]; exact hud
    have hdu' : d + u ∈ C.D := C.add_mem d hd u hu hdu
    let S₁ : C.Stars := ⟨C.star d u, isStar_star hd hu hdu⟩
    let S₂ : C.Stars := ⟨C.star d (d + u), isStar_star hd hdu' (b_add_right_eq_one hdu)⟩
    have hij : e S₁ ≠ e S₂ := fun h => star_ne_star hd hu hdu (by
      have := congrArg T h
      rwa [hTe, hTe] at this)
    refine ⟨e S₁, e S₂, hij, ?_⟩
    rw [hγpair]
    obtain ⟨h1, h2⟩ := hpairT _ _ hij
    refine eq_of_mem_of_mem hTN (hT (e S₁)) (hT (e S₂)) (fun h => hij (hTinj _ _ h)) h1 h2 ?_ ?_
    · rw [hTe]
      exact mem_star_left hd
    · rw [hTe]
      exact mem_star_left hd

section Hom

variable {C} {m : ℕ} {γ : sumZero m →ₗ[ZMod 2] V}

theorem surjective_of_forall_mem (hall : ∀ d ∈ C.D, ∃ i j : Fin m, i ≠ j ∧ γ (pairVec i j) = d) :
    Function.Surjective γ := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← C.span_eq, span_le]
  intro d hd
  obtain ⟨i, j, -, h⟩ := hall d hd
  exact ⟨_, h⟩

theorem ker_eq_onesLine (hiso : ∀ x y : sumZero m, C.b (γ x) (γ y) = dotB m x y)
    (hall : ∀ d ∈ C.D, ∃ i j : Fin m, i ≠ j ∧ γ (pairVec i j) = d) :
    LinearMap.ker γ = onesLine m := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hconst : ∀ i j, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j := by
      intro i j
      have h := hiso x (pairVec i j)
      rw [hx, map_zero, LinearMap.zero_apply, dotB_pairVec] at h
      calc (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) i + ((x : Fin m → ZMod 2) i +
            (x : Fin m → ZMod 2) j) := by rw [← h, add_zero]
        _ = (x : Fin m → ZMod 2) j := by rw [← add_assoc, add_self_zmod2, zero_add]
    rw [mem_onesLine]
    by_cases hm : m = 0
    · subst hm
      exact ⟨0, funext fun i => i.elim0⟩
    · exact ⟨(x : Fin m → ZMod 2) ⟨0, by omega⟩, funext fun i => hconst i _⟩
  · intro x hx
    rw [LinearMap.mem_ker]
    obtain ⟨c, hc⟩ := mem_onesLine.mp hx
    refine C.nondeg _ fun v => ?_
    obtain ⟨y, rfl⟩ := surjective_of_forall_mem hall v
    rw [hiso, dotB_apply, hc, ← Finset.mul_sum, mem_sumZero.mp y.2, mul_zero]

theorem map_sumZeroEquiv_swap (hiso : ∀ x y : sumZero m, C.b (γ x) (γ y) = dotB m x y)
    (i j : Fin m) (x : sumZero m) :
    γ (sumZeroEquiv (Equiv.swap i j) x) =
      γ x + C.b (γ x) (γ (pairVec i j)) • γ (pairVec i j) := by
  have h : sumZeroEquiv (Equiv.swap i j) x =
      x + ((x : Fin m → ZMod 2) i + (x : Fin m → ZMod 2) j) • pairVec i j :=
    Subtype.ext (by rw [coe_sumZeroEquiv, permCoord_swap]; rfl)
  rw [h, map_add, map_smul, hiso, dotB_pairVec]

end Hom

end CFSG.ComponentClassification.OutcomeLocal
