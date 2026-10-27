module

import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421RProof

open Matrix

section Monomial

variable {F : Type} [Field F] {S T : Type} [Group S] [Group T] [Fintype T] [DecidableEq T]

def monoMat (c : S →* Fˣ) (w : S ≀ᵣ T) : Matrix T T F :=
  Matrix.of fun x y => if x = w.right * y then ((c (w.left x) : Fˣ) : F) else 0

theorem monoMat_mul (c : S →* Fˣ) (w₁ w₂ : S ≀ᵣ T) :
    monoMat c (w₁ * w₂) = monoMat c w₁ * monoMat c w₂ := by
  ext x z
  simp only [monoMat, Matrix.mul_apply, Matrix.of_apply, RegularWreathProduct.mul_right,
    mul_assoc]
  rw [Finset.sum_eq_single (w₂.right * z)]
  · by_cases hx : x = w₁.right * (w₂.right * z)
    · have h1 : w₁.right⁻¹ * x = w₂.right * z := by rw [hx]; group
      simp [hx, RegularWreathProduct.mul_left, h1]
    · simp [hx]
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem monoMat_one (c : S →* Fˣ) : monoMat c (1 : S ≀ᵣ T) = (1 : Matrix T T F) := by
  ext x y
  simp [monoMat, Matrix.one_apply]

theorem monoMat_transpose_mul (c : S →* Fˣ) (w : S ≀ᵣ T) :
    (monoMat c w)ᵀ * monoMat c⁻¹ w = 1 := by
  ext x z
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monoMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (w.right * x)]
  · by_cases hxz : x = z
    · subst hxz
      simp [Matrix.one_apply]
    · have h : ¬ w.right * x = w.right * z := fun h => hxz (mul_left_cancel h)
      simp [h, hxz, Matrix.one_apply]
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eq_one_of_monoMat_eq_one [Nontrivial F] (c : S →* Fˣ) (hc : Function.Injective c)
    {w : S ≀ᵣ T} (h : monoMat c w = (1 : Matrix T T F)) : w = 1 := by
  have h1 : w.right = 1 := by
    by_contra hne
    have := congrFun (congrFun h 1) 1
    simp only [monoMat, Matrix.of_apply, Matrix.one_apply_eq] at this
    rw [if_neg (by simpa using Ne.symm hne)] at this
    exact zero_ne_one this
  refine RegularWreathProduct.ext ?_ h1
  funext x
  have := congrFun (congrFun h x) x
  simp only [monoMat, Matrix.of_apply, Matrix.one_apply_eq, h1, one_mul, if_true] at this
  have h2 : c (w.left x) = 1 := Units.ext this
  exact hc (h2.trans (map_one c).symm)

end Monomial

section Symplectic

variable {F : Type} [Field F] {S T : Type} [Group S] [Group T] [Fintype T] [DecidableEq T]

def spMat (c : S →* Fˣ) (w : S ≀ᵣ T) : Matrix (T ⊕ T) (T ⊕ T) F :=
  Matrix.fromBlocks (monoMat c w) 0 0 (monoMat c⁻¹ w)

theorem spMat_mul (c : S →* Fˣ) (w₁ w₂ : S ≀ᵣ T) :
    spMat c (w₁ * w₂) = spMat c w₁ * spMat c w₂ := by
  simp only [spMat, monoMat_mul, Matrix.fromBlocks_multiply]
  simp

theorem spMat_one (c : S →* Fˣ) : spMat c (1 : S ≀ᵣ T) = (1 : Matrix (T ⊕ T) (T ⊕ T) F) := by
  simp only [spMat, monoMat_one, Matrix.fromBlocks_one]

theorem spMat_symplectic (c : S →* Fˣ) (w : S ≀ᵣ T) :
    (spMat c w)ᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (T ⊕ T) (T ⊕ T) F) * spMat c w =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  have h1 := monoMat_transpose_mul c w
  have h2 : (monoMat c⁻¹ w)ᵀ * monoMat c w = 1 := by
    have hcc : c⁻¹⁻¹ = c := by
      ext s
      simp
    have := monoMat_transpose_mul c⁻¹ w
    rwa [hcc] at this
  simp only [spMat, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp [h1, h2]

theorem submatrix_symplectic {n : ℕ} (e : T ≃ Fin n) {M : Matrix (T ⊕ T) (T ⊕ T) F}
    (hM : Mᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (T ⊕ T) (T ⊕ T) F) * M =
      Matrix.fromBlocks 0 1 (-1) 0) :
    (M.submatrix (Equiv.sumCongr e e).symm (Equiv.sumCongr e e).symm)ᵀ *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      M.submatrix (Equiv.sumCongr e e).symm (Equiv.sumCongr e e).symm =
        Matrix.fromBlocks 0 1 (-1) 0 := by
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (T ⊕ T) (T ⊕ T) F).submatrix
        (Equiv.sumCongr e e).symm (Equiv.sumCongr e e).symm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.one_apply, Matrix.submatrix_apply]
  rw [hJ, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hM]

end Symplectic

section StatedHom

variable {F : Type} [Field F] {S T : Type} [Group S] [Group T] [Fintype T] [DecidableEq T]

def spMat3 (e : T ≃ Fin 3) (c : S →* Fˣ) (w : S ≀ᵣ T) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  (spMat c w).submatrix (Equiv.sumCongr e e).symm (Equiv.sumCongr e e).symm

def spHom3 (e : T ≃ Fin 3) (c : S →* Fˣ) :
    S ≀ᵣ T →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F where
  toFun := spMat3 e c
  map_one' := by
    simp only [spMat3, spMat_one]
    exact Matrix.submatrix_one_equiv (Equiv.sumCongr e e).symm
  map_mul' w₁ w₂ := by
    simp only [spMat3, spMat_mul]
    exact (Matrix.submatrix_mul_equiv _ _ _ (Equiv.sumCongr e e).symm _).symm

def wreathToSp (e : T ≃ Fin 3) (c : S →* Fˣ) : S ≀ᵣ T →* CFSG.Open.StatedSp 3 F :=
  ((spHom3 e c).toHomUnits).codRestrict (CFSG.Open.StatedSp 3 F) (fun w => by
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
    exact submatrix_symplectic e (spMat_symplectic c w))

theorem wreathToSp_injective (e : T ≃ Fin 3) (c : S →* Fˣ) (hc : Function.Injective c) :
    Function.Injective (wreathToSp (F := F) e c) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h1 : spMat3 e c w = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    have := congrArg (fun g : CFSG.Open.StatedSp 3 F =>
      ((g : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) hw
    simpa [wreathToSp, spHom3] using this
  have h2 : spMat c w = (1 : Matrix (T ⊕ T) (T ⊕ T) F) := by
    simp only [spMat3] at h1
    have h1' := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F =>
      M.submatrix (Equiv.sumCongr e e) (Equiv.sumCongr e e)) h1
    simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
      Matrix.submatrix_one_equiv] at h1'
    exact h1'
  simp only [spMat, ← Matrix.fromBlocks_one] at h2
  have h3 := (Matrix.fromBlocks_inj.mp h2).1
  exact eq_one_of_monoMat_eq_one c hc h3

end StatedHom

section Arith

theorem padicValNat_three_pow_sub_one {N : ℕ} (hN : N % 3 = 1) (hN1 : 1 < N) {m : ℕ}
    (hm : m ≠ 0) :
    padicValNat 3 (N ^ m - 1) = padicValNat 3 (N - 1) + padicValNat 3 m := by
  have h := padicValNat.pow_sub_pow (p := 3) (by decide) (x := N) (y := 1) hN1
    (by omega) (by omega) hm
  simpa using h

theorem padicValNat_three_small : padicValNat 3 2 = 0 ∧ padicValNat 3 4 = 0 ∧
    padicValNat 3 6 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact padicValNat.eq_zero_of_not_dvd (by norm_num)
  · exact padicValNat.eq_zero_of_not_dvd (by norm_num)
  · have : (6 : ℕ) = 3 * 2 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem padicValNat_sp6 {N : ℕ} (hN : N % 3 = 1) (hN1 : 1 < N) :
    padicValNat 3 (N ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (N ^ (2 * j) - 1)) =
      3 * padicValNat 3 (N - 1) + 1 := by
  have hI : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)]
  have hne : ∀ m : ℕ, m ≠ 0 → N ^ m - 1 ≠ 0 := fun m hm => by
    have : 1 < N ^ m := Nat.one_lt_pow hm hN1
    omega
  have h2 := hne 2 (by norm_num)
  have h4 := hne 4 (by norm_num)
  have h6 := hne 6 (by norm_num)
  have hN0 : N ≠ 0 := by omega
  have hNp : padicValNat 3 (N ^ (3 ^ 2)) = 0 := by
    rw [padicValNat.pow N (3 ^ 2), padicValNat.eq_zero_of_not_dvd (by omega), mul_zero]
  obtain ⟨s2, s4, s6⟩ := padicValNat_three_small
  have v2 := padicValNat_three_pow_sub_one hN hN1 (m := 2) (by norm_num)
  have v4 := padicValNat_three_pow_sub_one hN hN1 (m := 4) (by norm_num)
  have v6 := padicValNat_three_pow_sub_one hN hN1 (m := 6) (by norm_num)
  simp only [show 2 * 1 = 2 by norm_num, show 2 * 2 = 4 by norm_num, show 2 * 3 = 6 by norm_num]
  rw [padicValNat.mul (pow_ne_zero _ hN0) (mul_ne_zero h2 (mul_ne_zero h4 h6)),
    padicValNat.mul h2 (mul_ne_zero h4 h6), padicValNat.mul h4 h6, hNp, v2, v4, v6, s2, s4, s6]
  ring

end Arith

section MatrixSylow

variable {F : Type} [Field F] [Finite F]

theorem factorization_statedSp_three (hN : Nat.card F % 3 = 1) :
    (Nat.card (CFSG.Open.StatedSp 3 F)).factorization 3 =
      3 * padicValNat 3 (Nat.card F - 1) + 1 := by
  have hN1 : 1 < Nat.card F := Finite.one_lt_card
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 3,
    Nat.factorization_def _ Nat.prime_three]
  exact padicValNat_sp6 hN hN1

theorem exists_unit_orderOf_three_pow :
    ∃ ζ : Fˣ, orderOf ζ = 3 ^ padicValNat 3 (Nat.card F - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hdvd : 3 ^ padicValNat 3 (Nat.card F - 1) ∣ orderOf g := by
    rw [hg, hcard]
    exact pow_padicValNat_dvd
  refine ⟨g ^ (orderOf g / 3 ^ padicValNat 3 (Nat.card F - 1)), ?_⟩
  exact orderOf_pow_orderOf_div (by rw [hg]; exact Nat.card_pos.ne') hdvd

theorem sylow_statedSp (hN : Nat.card F % 3 = 1) (P : Sylow 3 (CFSG.Open.StatedSp 3 F)) :
    Nonempty (↥P ≃* (Multiplicative (ZMod (3 ^ padicValNat 3 (Nat.card F - 1))) ≀ᵣ
      Multiplicative (ZMod 3))) := by
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_three_pow (F := F)
  set k := padicValNat 3 (Nat.card F - 1) with hk
  let S : Subgroup Fˣ := Subgroup.zpowers ζ
  let c : S →* Fˣ := S.subtype
  have hTcard : Fintype.card (Multiplicative (ZMod 3)) = 3 := by simp
  let e : Multiplicative (ZMod 3) ≃ Fin 3 := Fintype.equivFinOfCardEq hTcard
  have hinj : Function.Injective (wreathToSp (F := F) e c) :=
    wreathToSp_injective e c Subtype.val_injective
  have hScard : Nat.card S = 3 ^ k := by rw [Nat.card_zpowers, hζ]
  have hTc : Nat.card (Multiplicative (ZMod 3)) = 3 := by rw [Nat.card_eq_fintype_card, hTcard]
  have hrange : Nat.card (wreathToSp (F := F) e c).range =
      3 ^ (Nat.card (CFSG.Open.StatedSp 3 F)).factorization 3 := by
    rw [factorization_statedSp_three hN, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      RegularWreathProduct.card, hScard, hTc]
    ring
  let P₀ : Sylow 3 (CFSG.Open.StatedSp 3 F) := Sylow.ofCard (wreathToSp (F := F) e c).range hrange
  have e1 : ↥P ≃* ↥P₀ := Sylow.equiv P P₀
  have e2 : ↥P₀ ≃* (S ≀ᵣ Multiplicative (ZMod 3)) := (MonoidHom.ofInjective hinj).symm
  have hS : Nat.card S = Nat.card (Multiplicative (ZMod (3 ^ k))) := by
    rw [hScard, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (3 ^ k)) ≃ ZMod (3 ^ k)),
      Nat.card_zmod]
  let e3 : S ≃* Multiplicative (ZMod (3 ^ k)) := mulEquivOfCyclicCardEq hS
  exact ⟨(e1.trans e2).trans (RegularWreathProduct.congr e3 (MulEquiv.refl _))⟩

end MatrixSylow

section Bridge

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {F : Type} [Field F] [Finite F]

noncomputable def statedSpEquivProj (hev : 2 ∣ Nat.card F) :
    CFSG.Open.StatedSp 3 F ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp 3 F) := by
  refine MulEquiv.ofBijective (proj 3 F) ⟨?_, proj_surjective⟩
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, ← Subgroup.card_eq_one,
    CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd F (by norm_num : 1 ≤ 3)]
  have hpos : 0 < Nat.card F := Nat.card_pos
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)

end Bridge

end K421RProof

end CFSG.LocalAnalysis.RankThreeUC.S15
