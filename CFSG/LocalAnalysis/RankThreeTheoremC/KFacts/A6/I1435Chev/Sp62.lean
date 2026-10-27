module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Setup
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpAdj
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Sp62

open Subgroup Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LieType.SteinbergBR.EvenSp (planeMat planeHom planeHom_val planeHom_mem_statedSp
  planeHom_injective planeMat_mul tGL tGL_pow_three orderOf_tGL det_of_mem_zpowers)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spIncl inclMat spEmbed spEmbed_injective
  spIncl_transpose_mul gram_mul_spIncl ofSymplecticMat mat_ofSymplecticMat IsSupp
  isSupp_spEmbed coords mem_coords)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435 (isPSolvable_of_equiv)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

section Supp

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem commute_of_supp {S T : Set ι} (hST : Disjoint S T) {A B : Matrix ι ι K}
    (hA : ∀ r t, ¬ (r ∈ S ∧ t ∈ S) → A r t = (1 : Matrix ι ι K) r t)
    (hB : ∀ r t, ¬ (r ∈ T ∧ t ∈ T) → B r t = (1 : Matrix ι ι K) r t) : A * B = B * A := by
  have h0 : ∀ {A B : Matrix ι ι K} {S T : Set ι}, Disjoint S T →
      (∀ r t, ¬ (r ∈ S ∧ t ∈ S) → A r t = (1 : Matrix ι ι K) r t) →
      (∀ r t, ¬ (r ∈ T ∧ t ∈ T) → B r t = (1 : Matrix ι ι K) r t) → (A - 1) * (B - 1) = 0 := by
    intro A B S T hST hA hB
    ext r t
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hu : u ∈ S
    · have hu' : u ∉ T := Set.disjoint_left.1 hST hu
      rw [Matrix.sub_apply (B), hB u t (fun h => hu' h.1), sub_self, mul_zero]
    · rw [Matrix.sub_apply A, hA r u (fun h => hu h.2), sub_self, zero_mul]
  have h1 := h0 hST hA hB
  have h2 := h0 hST.symm hB hA
  calc A * B = 1 + (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
    _ = 1 + (B - 1) + (A - 1) + (B - 1) * (A - 1) := by rw [h1, h2]; abel
    _ = B * A := by noncomm_ring

end Supp

section Torus

variable {K : Type} [Field K] [CharP K 2]

@[expose] def tPow (c : ZMod 3) : GL (Fin 2) K := tGL ^ c.val

theorem tPow_add (x y : ZMod 3) : tPow (K := K) (x + y) = tPow x * tPow y := by
  rw [tPow, tPow, tPow, ← pow_add, ZMod.val_add]
  have h := pow_mod_orderOf (tGL (K := K)) (x.val + y.val)
  rwa [orderOf_tGL] at h

theorem tPow_injective : Function.Injective (tPow (K := K)) := by
  intro x y h
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have := pow_injOn_Iio_orderOf (x := (tGL : GL (Fin 2) K)) (by rw [orderOf_tGL]; exact hx)
    (by rw [orderOf_tGL]; exact hy) h
  exact ZMod.val_injective 3 this

theorem det_tPow (c : ZMod 3) : ((tPow c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
  det_of_mem_zpowers (Subgroup.npow_mem_zpowers _ _)

@[expose] noncomputable def eps : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 3 K where
  toFun a := ⟨planeHom fun j => tPow (Multiplicative.toAdd a j),
    planeHom_mem_statedSp _ fun j => det_tPow _⟩
  map_one' := Subtype.ext (by
    show planeHom (fun j => tPow (K := K) 0) = 1
    simp only [tPow, ZMod.val_zero, pow_zero]
    exact map_one planeHom)
  map_mul' a b := Subtype.ext (by
    show planeHom (fun j => tPow (K := K) (Multiplicative.toAdd a j + Multiplicative.toAdd b j)) =
      planeHom (fun j => tPow (Multiplicative.toAdd a j)) *
        planeHom (fun j => tPow (Multiplicative.toAdd b j))
    rw [← map_mul]
    congr 1
    funext j
    exact tPow_add _ _)

theorem coe_eps (a : Multiplicative (Fin 3 → ZMod 3)) :
    ((eps (K := K) a : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) =
      planeHom fun j => tPow (Multiplicative.toAdd a j) := rfl

theorem eps_injective : Function.Injective (eps (K := K)) := by
  intro a b h
  have h1 := planeHom_injective (congrArg Subtype.val h)
  apply Multiplicative.toAdd.injective
  funext j
  exact tPow_injective (congrFun h1 j)

theorem eq_of_zpowers_eps {a b : Fin 3 → ZMod 3}
    (h : zpowers (eps (K := K) (Multiplicative.ofAdd a)) =
      zpowers (eps (Multiplicative.ofAdd b))) : b = a ∨ b = -a ∨ b = 0 := by
  have hm : eps (K := K) (Multiplicative.ofAdd b) ∈ zpowers (eps (Multiplicative.ofAdd a)) := by
    rw [h]
    exact mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
  rw [← map_zpow] at hk
  have hk' := congrArg Multiplicative.toAdd (eps_injective hk)
  simp only [toAdd_zpow, toAdd_ofAdd] at hk'
  rw [← hk', ← Int.cast_smul_eq_zsmul (ZMod 3)]
  have hc : ((k : ℤ) : ZMod 3) = 0 ∨ ((k : ℤ) : ZMod 3) = 1 ∨ ((k : ℤ) : ZMod 3) = 2 := by
    generalize ((k : ℤ) : ZMod 3) = c
    revert c
    decide
  rcases hc with h0 | h1 | h2
  · right; right; rw [h0, zero_smul]
  · left; rw [h1, one_smul]
  · right; left
    rw [h2, show (2 : ZMod 3) = -1 by decide, neg_smul, one_smul]

end Torus

section Normalizer

variable {K : Type} [Field K] [CharP K 2]

@[expose] def pGL : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    rw [mul_fin_two, one_fin_two]
    simp, by
    rw [mul_fin_two, one_fin_two]
    simp⟩

theorem det_pGL : ((pGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]

theorem pGL_conj_tGL : pGL (K := K) * tGL * pGL⁻¹ = tGL ^ 2 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
  change !![0, 1; 1, 0] * !![0, 1; 1, 1] * !![0, 1; 1, 0] =
    (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ^ 2
  rw [sq, mul_fin_two, mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem pGL_conj_tPow (c : ZMod 3) : pGL (K := K) * tPow c * pGL⁻¹ = tPow (-c) := by
  have hconj : ∀ k : ℕ, pGL (K := K) * tGL ^ k * pGL⁻¹ = (tGL ^ 2) ^ k := by
    intro k
    rw [← pGL_conj_tGL, conj_pow]
  rw [tPow, tPow, hconj, ← pow_mul, ← pow_mod_orderOf, orderOf_tGL]
  conv_rhs => rw [← pow_mod_orderOf, orderOf_tGL]
  congr 1
  revert c
  decide

@[expose] noncomputable def swapEl (j : Fin 3) : StatedSp 3 K :=
  ⟨planeHom (Pi.mulSingle j pGL), planeHom_mem_statedSp _ fun i => by
    by_cases h : i = j
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact det_pGL
    · rw [Pi.mulSingle_eq_of_ne h]
      simp⟩

@[expose] def flip (j : Fin 3) (a : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun i => if i = j then -a i else a i

theorem swapEl_conj (j : Fin 3) (a : Fin 3 → ZMod 3) :
    swapEl (K := K) j * eps (Multiplicative.ofAdd a) * (swapEl j)⁻¹ =
      eps (Multiplicative.ofAdd (flip j a)) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  show planeHom (Pi.mulSingle j pGL) * planeHom (fun i => tPow (a i)) *
      (planeHom (Pi.mulSingle j pGL))⁻¹ = planeHom fun i => tPow (flip j a i)
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply, flip]
  by_cases h : i = j
  · subst h
    rw [Pi.mulSingle_eq_same, if_pos rfl, pGL_conj_tPow]
  · rw [Pi.mulSingle_eq_of_ne h, if_neg h, one_mul, inv_one, mul_one]

theorem inclMat_mul_diagonal (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → K) :
    inclMat (K := K) σ * diagonal d = diagonal (d ∘ σ.symm) * inclMat σ := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [inclMat, of_apply, Function.comp]
  split_ifs with h
  · subst h
    simp
  · simp

theorem spIncl_mul_planeMat (σ : Equiv.Perm (Fin 3)) (h : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    spIncl (K := K) σ * planeMat h = planeMat (h ∘ σ.symm) * spIncl σ := by
  simp only [spIncl, planeMat, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, inclMat_mul_diagonal]
  rfl

theorem spIncl_symplectic (σ : Equiv.Perm (Fin 3)) :
    (spIncl (K := K) σ)ᵀ * CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K 3 * spIncl σ =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K 3 := by
  rw [Matrix.mul_assoc, gram_mul_spIncl, ← Matrix.mul_assoc, spIncl_transpose_mul σ.injective,
    Matrix.one_mul]

@[expose] noncomputable def permEl (σ : Equiv.Perm (Fin 3)) : StatedSp 3 K :=
  ofSymplecticMat (spIncl σ) (spIncl_symplectic σ)

theorem permEl_conj (σ : Equiv.Perm (Fin 3)) (a : Fin 3 → ZMod 3) :
    permEl (K := K) σ * eps (Multiplicative.ofAdd a) * (permEl σ)⁻¹ =
      eps (Multiplicative.ofAdd (a ∘ σ.symm)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul]
  show spIncl σ * planeMat (fun j => ((tPow (a j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
    planeMat (fun j => ((tPow ((a ∘ σ.symm) j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      spIncl σ
  rw [spIncl_mul_planeMat]
  rfl

end Normalizer

section Centralizer

variable {K : Type} [Field K] [CharP K 2]

@[expose] def others (i : Fin 3) : Fin 2 → Fin 3 := Fin.succAbove i

theorem others_injective (i : Fin 3) : Function.Injective (others i) :=
  Fin.succAbove_right_injective

theorem commute_spEmbed_eps (i : Fin 3) {a : Fin 3 → ZMod 3} (ha : ∀ j, j ≠ i → a j = 0)
    (g : StatedSp 2 K) :
    spEmbed (others i) (others_injective i) g * eps (Multiplicative.ofAdd a) =
      eps (Multiplicative.ofAdd a) * spEmbed (others i) (others_injective i) g := by
  apply mat_injective
  rw [map_mul, map_mul]
  have hsupp := isSupp_spEmbed (K := K) (others_injective i) g
  refine commute_of_supp (S := Set.range (Sum.map (others i) (others i))) (T := coords i)
    ?_ hsupp ?_
  · rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ hx
    rcases mem_coords.1 hx with h | h <;> rcases x with x | x <;>
      simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
    · exact Fin.succAbove_ne i x h
    · exact Fin.succAbove_ne i x h
  · intro r t hrt
    rw [mat_apply, coe_eps]
    show planeMat (fun j => ((tPow (a j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) r t =
      (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) r t
    have hone : ∀ j, j ≠ i → ((tPow (K := K) (a j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        1 := by
      intro j hj
      rw [ha j hj]
      simp [tPow]
    rcases r with x | x <;> rcases t with y | y <;>
      simp only [planeMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, diagonal_apply, one_apply, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, if_false] <;>
      by_cases hxy : x = y <;> simp only [hxy, if_true, if_false]
    all_goals
      subst hxy
      have hx : x ≠ i := fun h => hrt ⟨by rw [h]; simp [coords], by rw [h]; simp [coords]⟩
      rw [hone x hx]
      simp

end Centralizer

@[expose] def cyc : Equiv.Perm (Fin 3) := finRotate 3

@[expose] def cact : Fin 6 → (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) :=
  ![fun a => a, flip 0, flip 1, flip 2, fun a => a ∘ cyc.symm, fun a => a ∘ (cyc * cyc).symm]

@[expose] def lineD (a b : Fin 3 → ZMod 3) : Prop := b ≠ a ∧ b ≠ -a ∧ b ≠ 0

instance (a b : Fin 3 → ZMod 3) : Decidable (lineD a b) := inferInstanceAs (Decidable (_ ∧ _))

@[expose] def pick (a : Fin 3 → ZMod 3) : Fin 4 → Fin 6 :=
  if a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ a 2 ≠ 0 then ![0, 1, 2, 3]
  else if a 0 ≠ 0 then ![0, 1, 4, 5] else ![0, 2, 4, 5]

theorem sp_check : ∀ a : Fin 3 → ZMod 3, a ≠ 0 →
    (∃ i, ∀ j, j ≠ i → a j = 0) ∨
      ∀ i j : Fin 4, i ≠ j → lineD (cact (pick a i) a) (cact (pick a j) a) := by
  decide +kernel

section Witness

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def cel : Fin 6 → StatedSp 3 K :=
  ![1, swapEl 0, swapEl 1, swapEl 2, permEl cyc, permEl (cyc * cyc)]

theorem cel_conj (c : Fin 6) (a : Fin 3 → ZMod 3) :
    cel (K := K) c * eps (Multiplicative.ofAdd a) * (cel c)⁻¹ =
      eps (Multiplicative.ofAdd (cact c a)) := by
  fin_cases c
  · simp [cel, cact]
  · exact swapEl_conj 0 a
  · exact swapEl_conj 1 a
  · exact swapEl_conj 2 a
  · exact permEl_conj cyc a
  · exact permEl_conj (cyc * cyc) a

end Witness

theorem witness_sp6two : Witness (StatedSp 3 (ZMod 2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨(eps (K := ZMod 2)).range, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [← Nat.card_congr (MonoidHom.ofInjective (eps_injective (K := ZMod 2))).toEquiv,
      Nat.card_eq_fintype_card]
    rfl
  · rintro _ ⟨a, rfl⟩ ha1
    obtain ⟨a, rfl⟩ : ∃ b : Fin 3 → ZMod 3, Multiplicative.ofAdd b = a := ⟨a.toAdd, rfl⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha1 (map_one _)
    rcases sp_check a ha0 with ⟨i, hi⟩ | hlines
    ·
      left
      have hle : (spEmbed (K := ZMod 2) (others i) (others_injective i)).range ≤
          centralizer ({eps (Multiplicative.ofAdd a)} : Set (StatedSp 3 (ZMod 2))) := by
        rintro _ ⟨g, rfl⟩
        rw [mem_centralizer_singleton_iff]
        exact commute_spEmbed_eps i hi g
      intro hs
      have h1 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        hs hle
      exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.not_isPSolvable_statedSp_two
        (F := ZMod 2) (Nat.card_zmod 2)
        (isPSolvable_of_equiv (MonoidHom.ofInjective (spEmbed_injective (K := ZMod 2)
          (others_injective i))).symm h1)
    ·
      right
      refine ⟨fun k => cel (pick a k), fun k => ?_, fun k l hkl => ?_⟩
      · rw [cel_conj]
        exact ⟨_, rfl⟩
      · rw [cel_conj, cel_conj] at hkl
        by_contra hne
        obtain ⟨d1, d2, d3⟩ := hlines k l hne
        rcases eq_of_zpowers_eps hkl with h | h | h
        · exact d1 h
        · exact d2 h
        · exact d3 h

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Sp62
