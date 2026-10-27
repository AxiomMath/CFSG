module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinPlus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusNode

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinPlus

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.SquareSpinPlus QuadraticMap

section Model

variable {n : ℕ} {F : Type} [Field F]

@[expose] def trv (c : F) (x y : Fin n ⊕ Fin n) (v : Fin n ⊕ Fin n → F) : Fin n ⊕ Fin n → F :=
  v + (c * v y.swap) • Pi.single x 1 - (c * v x.swap) • Pi.single y 1

theorem spinAction_rootD_eq_trv (hn : 3 ≤ n) (k : Fin n) (c : F) (v : Fin n ⊕ Fin n → F) :
    spinAction (quadPlus n F) (rootD F hn k (.ofAdd c)) v = trv c (nodeX k) (nodeY k) v :=
  spinAction_rootD hn k c v

theorem spinAction_negRootD_eq_trv (hn : 3 ≤ n) (k : Fin n) (c : F) (v : Fin n ⊕ Fin n → F) :
    spinAction (quadPlus n F) (negRootD F hn k (.ofAdd c)) v =
      trv c (nodeY k).swap (nodeX k).swap v := by
  rw [spinAction_negRootD, trv, Sum.swap_swap, Sum.swap_swap]

variable {m : ℕ}

@[expose] noncomputable def modelExt (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :
    (Fin m ⊕ Fin m → F) →ₗ[F] (Fin n ⊕ Fin n → F) :=
  Fintype.linearCombination F (fun a => (Pi.single (ι a) 1 : Fin n ⊕ Fin n → F))

theorem modelExt_apply (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) (u : Fin m ⊕ Fin m → F) :
    modelExt ι u = ∑ a, u a • (Pi.single (ι a) 1 : Fin n ⊕ Fin n → F) :=
  Fintype.linearCombination_apply F _ u

theorem modelExt_single (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) (p : Fin m ⊕ Fin m) :
    modelExt ι (Pi.single p 1 : Fin m ⊕ Fin m → F) = Pi.single (ι p) 1 := by
  rw [modelExt_apply, Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem modelExt_apply_ι (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) (hι : Function.Injective ι)
    (u : Fin m ⊕ Fin m → F) (b : Fin m ⊕ Fin m) : modelExt ι u (ι b) = u b := by
  rw [modelExt_apply, Finset.sum_apply, Finset.sum_eq_single b]
  · simp
  · intro a _ ha
    simp [hι.ne ha]
  · simp

theorem modelExt_injective (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) (hι : Function.Injective ι) :
    Function.Injective (modelExt (F := F) ι) := fun u w h =>
  funext fun b => by rw [← modelExt_apply_ι ι hι u b, h, modelExt_apply_ι ι hι]

@[expose] def modelTrv {R : Type*} [Ring R] (c : R) (p q : Fin m ⊕ Fin m) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
  1 + c • (Matrix.single p q.swap 1 - Matrix.single q p.swap 1)

theorem modelTrv_mulVec (c : F) (p q : Fin m ⊕ Fin m) (u : Fin m ⊕ Fin m → F) :
    modelTrv c p q *ᵥ u = u + (c * u q.swap) • Pi.single p 1 - (c * u p.swap) • Pi.single q 1 := by
  simp only [modelTrv, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Function.update_apply, Pi.zero_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem trv_modelExt (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) (hι : Function.Injective ι)
    (hsw : ∀ a, ι a.swap = (ι a).swap) (c : F) (p q : Fin m ⊕ Fin m) (u : Fin m ⊕ Fin m → F) :
    trv c (ι p) (ι q) (modelExt ι u) = modelExt ι (modelTrv c p q *ᵥ u) := by
  rw [modelTrv_mulVec, trv, ← hsw, ← hsw, modelExt_apply_ι ι hι, modelExt_apply_ι ι hι, map_sub,
    map_add, map_smul, map_smul, modelExt_single, modelExt_single]

theorem spinAction_rootD_model (hn : 3 ≤ n) (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n)
    (hι : Function.Injective ι) (hsw : ∀ a, ι a.swap = (ι a).swap) {k : Fin n}
    {p q : Fin m ⊕ Fin m} (hp : nodeX k = ι p) (hq : nodeY k = ι q) (c : F)
    (u : Fin m ⊕ Fin m → F) :
    spinAction (quadPlus n F) (rootD F hn k (.ofAdd c)) (modelExt ι u) =
      modelExt ι (modelTrv c p q *ᵥ u) := by
  rw [spinAction_rootD_eq_trv, hp, hq, trv_modelExt ι hι hsw]

theorem spinAction_negRootD_model (hn : 3 ≤ n) (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n)
    (hι : Function.Injective ι) (hsw : ∀ a, ι a.swap = (ι a).swap) {k : Fin n}
    {p q : Fin m ⊕ Fin m} (hp : nodeX k = ι p) (hq : nodeY k = ι q) (c : F)
    (u : Fin m ⊕ Fin m → F) :
    spinAction (quadPlus n F) (negRootD F hn k (.ofAdd c)) (modelExt ι u) =
      modelExt ι (modelTrv c q.swap p.swap *ᵥ u) := by
  rw [spinAction_negRootD_eq_trv, hp, hq, ← hsw, ← hsw, trv_modelExt ι hι hsw]

theorem modelTrv_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (c : R)
    (p q : Fin m ⊕ Fin m) : (modelTrv c p q).map f = modelTrv (f c) p q := by
  ext a b
  simp only [modelTrv, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem trv_single_of_ne {x y z : Fin n ⊕ Fin n} (hz : z ≠ y.swap) (hz' : z ≠ x.swap) (c : F) :
    trv c x y (Pi.single z 1) = Pi.single z 1 := by
  have h1 : (Pi.single z 1 : Fin n ⊕ Fin n → F) y.swap = 0 := Pi.single_eq_of_ne hz.symm _
  have h2 : (Pi.single z 1 : Fin n ⊕ Fin n → F) x.swap = 0 := Pi.single_eq_of_ne hz'.symm _
  simp [trv, h1, h2]

theorem rootD_fix_of_not_mem_range (hn : 3 ≤ n) (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n)
    (hsw : ∀ a, ι a.swap = (ι a).swap) {k : Fin n} {p q : Fin m ⊕ Fin m} (hp : nodeX k = ι p)
    (hq : nodeY k = ι q) (c : F) {z : Fin n ⊕ Fin n} (hz : z ∉ Set.range ι) :
    spinAction (quadPlus n F) (rootD F hn k (.ofAdd c)) (Pi.single z 1) = Pi.single z 1 := by
  rw [spinAction_rootD_eq_trv, hp, hq]
  refine trv_single_of_ne (fun h => hz ⟨q.swap, by rw [hsw, h]⟩) (fun h => hz ⟨p.swap, by
    rw [hsw, h]⟩) c

theorem negRootD_fix_of_not_mem_range (hn : 3 ≤ n) (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n)
    {k : Fin n} {p q : Fin m ⊕ Fin m} (hp : nodeX k = ι p)
    (hq : nodeY k = ι q) (c : F) {z : Fin n ⊕ Fin n} (hz : z ∉ Set.range ι) :
    spinAction (quadPlus n F) (negRootD F hn k (.ofAdd c)) (Pi.single z 1) = Pi.single z 1 := by
  rw [spinAction_negRootD_eq_trv, hp, hq]
  refine trv_single_of_ne (fun h => hz ⟨p, by rw [h, Sum.swap_swap]⟩)
    (fun h => hz ⟨q, by rw [h, Sum.swap_swap]⟩) c

theorem eq_one_of_model [CharP F 2] {W : spinGroup (quadPlus n F)}
    (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n)
    (hfix : ∀ z, z ∉ Set.range ι →
      spinAction (quadPlus n F) W (Pi.single z 1) = Pi.single z 1)
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hW : ∀ u, spinAction (quadPlus n F) W (modelExt ι u) = modelExt ι (A *ᵥ u)) (hA : A = 1) :
    W = 1 := by
  refine spinAction_injective (spinAction_eq_one_of_forall_single (fun z => ?_) |>.trans
    (map_one _).symm)
  by_cases hz : z ∈ Set.range ι
  · obtain ⟨b, rfl⟩ := hz
    rw [← modelExt_single ι b, hW, hA, Matrix.one_mulVec]
  · exact hfix z hz

theorem ne_one_of_model (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) (hι : Function.Injective ι)
    {W : spinGroup (quadPlus n F)} {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hW : ∀ u, spinAction (quadPlus n F) W (modelExt ι u) = modelExt ι (A *ᵥ u)) (hA : A ≠ 1) :
    W ≠ 1 := by
  rintro rfl
  apply hA
  ext a b
  have h := modelExt_injective ι hι (by rw [← hW, map_one]; rfl : modelExt ι (A *ᵥ Pi.single b 1) =
    modelExt (F := F) ι (Pi.single b 1))
  have := congrFun h a
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

@[expose] def wordX {R : Type*} [Ring R] (p₁ q₁ p₂ q₂ p₃ q₃ : Fin m ⊕ Fin m) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
  modelTrv 1 p₁ q₁ * modelTrv 1 p₃ q₃ * modelTrv 1 q₂.swap p₂.swap

@[expose] def wordY {R : Type*} [Ring R] (p₁ q₁ p₂ q₂ p₃ q₃ : Fin m ⊕ Fin m) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
  modelTrv 1 p₂ q₂ * modelTrv 1 q₁.swap p₁.swap * modelTrv 1 q₃.swap p₃.swap

theorem wordX_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (p₁ q₁ p₂ q₂ p₃ q₃ : Fin m ⊕ Fin m) :
    (wordX (R := R) p₁ q₁ p₂ q₂ p₃ q₃).map f = wordX (R := S) p₁ q₁ p₂ q₂ p₃ q₃ := by
  simp only [wordX, Matrix.map_mul, modelTrv_map, map_one]

theorem wordY_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (p₁ q₁ p₂ q₂ p₃ q₃ : Fin m ⊕ Fin m) :
    (wordY (R := R) p₁ q₁ p₂ q₂ p₃ q₃).map f = wordY (R := S) p₁ q₁ p₂ q₂ p₃ q₃ := by
  simp only [wordY, Matrix.map_mul, modelTrv_map, map_one]

theorem spinAction_pow_model (ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n) {g : spinGroup (quadPlus n F)}
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hg : ∀ u, spinAction (quadPlus n F) g (modelExt ι u) = modelExt ι (A *ᵥ u)) (k : ℕ)
    (u : Fin m ⊕ Fin m → F) :
    spinAction (quadPlus n F) (g ^ k) (modelExt ι u) = modelExt ι ((A ^ k) *ᵥ u) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, map_mul, LinearEquiv.mul_apply, hg, ih, pow_succ, ← Matrix.mulVec_mulVec]

@[expose] noncomputable def pieceX (hn : 3 ≤ n) (F : Type) [Field F] (k₁ k₂ k₃ : Fin n) :
    spinGroup (quadPlus n F) :=
  rootD F hn k₁ (.ofAdd 1) * rootD F hn k₃ (.ofAdd 1) * negRootD F hn k₂ (.ofAdd 1)

@[expose] noncomputable def pieceY (hn : 3 ≤ n) (F : Type) [Field F] (k₁ k₂ k₃ : Fin n) :
    spinGroup (quadPlus n F) :=
  rootD F hn k₂ (.ofAdd 1) * negRootD F hn k₁ (.ofAdd 1) * negRootD F hn k₃ (.ofAdd 1)

theorem piece_real [CharP F 2] (hn : 3 ≤ n) (j : Fin m → Fin n) (hj : Function.Injective j)
    {k₁ k₂ k₃ : Fin n} {p₁ q₁ p₂ q₂ p₃ q₃ : Fin m ⊕ Fin m}
    (hp₁ : nodeX k₁ = Sum.map j j p₁) (hq₁ : nodeY k₁ = Sum.map j j q₁)
    (hp₂ : nodeX k₂ = Sum.map j j p₂) (hq₂ : nodeY k₂ = Sum.map j j q₂)
    (hp₃ : nodeX k₃ = Sum.map j j p₃) (hq₃ : nodeY k₃ = Sum.map j j q₃)
    (h1 : wordX (R := ZMod 2) p₁ q₁ p₂ q₂ p₃ q₃ * wordX p₁ q₁ p₂ q₂ p₃ q₃ = 1)
    (h2 : wordY (R := ZMod 2) p₁ q₁ p₂ q₂ p₃ q₃ * wordY p₁ q₁ p₂ q₂ p₃ q₃ = 1)
    (h3 : (wordX (R := ZMod 2) p₁ q₁ p₂ q₂ p₃ q₃ * wordY p₁ q₁ p₂ q₂ p₃ q₃) ^ 5 = 1)
    (h4 : wordX (R := ZMod 2) p₁ q₁ p₂ q₂ p₃ q₃ * wordY p₁ q₁ p₂ q₂ p₃ q₃ ≠ 1) :
    pieceX hn F k₁ k₂ k₃ * pieceX hn F k₁ k₂ k₃ = 1 ∧
      pieceY hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃ = 1 ∧
      (pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃) ^ 5 = 1 ∧
      pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃ ≠ 1 := by
  set ι : Fin m ⊕ Fin m → Fin n ⊕ Fin n := Sum.map j j with hιdef
  have hι : Function.Injective ι := Sum.map_injective.2 ⟨hj, hj⟩
  have hsw : ∀ a, ι a.swap = (ι a).swap := fun a => by cases a <;> rfl
  have hX : ∀ u, spinAction (quadPlus n F) (pieceX hn F k₁ k₂ k₃) (modelExt ι u) =
      modelExt ι (wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ *ᵥ u) := fun u => by
    rw [pieceX, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      spinAction_negRootD_model hn ι hι hsw hp₂ hq₂, spinAction_rootD_model hn ι hι hsw hp₃ hq₃,
      spinAction_rootD_model hn ι hι hsw hp₁ hq₁, wordX, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hY : ∀ u, spinAction (quadPlus n F) (pieceY hn F k₁ k₂ k₃) (modelExt ι u) =
      modelExt ι (wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃ *ᵥ u) := fun u => by
    rw [pieceY, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      spinAction_negRootD_model hn ι hι hsw hp₃ hq₃, spinAction_negRootD_model hn ι hι hsw hp₁ hq₁,
      spinAction_rootD_model hn ι hι hsw hp₂ hq₂, wordY, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hfX : ∀ z, z ∉ Set.range ι →
      spinAction (quadPlus n F) (pieceX hn F k₁ k₂ k₃) (Pi.single z 1) = Pi.single z 1 :=
    fun z hz => by
    rw [pieceX, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      negRootD_fix_of_not_mem_range hn ι hp₂ hq₂ _ hz,
      rootD_fix_of_not_mem_range hn ι hsw hp₃ hq₃ _ hz,
      rootD_fix_of_not_mem_range hn ι hsw hp₁ hq₁ _ hz]
  have hfY : ∀ z, z ∉ Set.range ι →
      spinAction (quadPlus n F) (pieceY hn F k₁ k₂ k₃) (Pi.single z 1) = Pi.single z 1 :=
    fun z hz => by
    rw [pieceY, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      negRootD_fix_of_not_mem_range hn ι hp₃ hq₃ _ hz,
      negRootD_fix_of_not_mem_range hn ι hp₁ hq₁ _ hz,
      rootD_fix_of_not_mem_range hn ι hsw hp₂ hq₂ _ hz]
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have hmX : (wordX (R := ZMod 2) p₁ q₁ p₂ q₂ p₃ q₃).map f =
      wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ := wordX_map f _ _ _ _ _ _
  have hmY : (wordY (R := ZMod 2) p₁ q₁ p₂ q₂ p₃ q₃).map f =
      wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃ := wordY_map f _ _ _ _ _ _
  have e1 : wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ * wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ = 1 := by
    rw [← hmX, ← Matrix.map_mul, h1]
    exact Matrix.map_one f (map_zero f) (map_one f)
  have e2 : wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃ * wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃ = 1 := by
    rw [← hmY, ← Matrix.map_mul, h2]
    exact Matrix.map_one f (map_zero f) (map_one f)
  have e3 : (wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ * wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃) ^ 5 = 1 := by
    have := congrArg f.mapMatrix h3
    rw [map_pow, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hmX,
      hmY] at this
    exact this
  have e4 : wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ * wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃ ≠ 1 := by
    intro h
    apply h4
    rw [← hmX, ← hmY, ← Matrix.map_mul] at h
    exact Matrix.map_injective f.injective
      (h.trans (Matrix.map_one f (map_zero f) (map_one f)).symm)
  have hXY : ∀ u, spinAction (quadPlus n F) (pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃)
      (modelExt ι u) = modelExt ι ((wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ *
        wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃) *ᵥ u) := fun u => by
    rw [map_mul, LinearEquiv.mul_apply, hY, hX, Matrix.mulVec_mulVec]
  have hfXY : ∀ z, z ∉ Set.range ι →
      spinAction (quadPlus n F) (pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃) (Pi.single z 1) =
        Pi.single z 1 := fun z hz => by
    rw [map_mul, LinearEquiv.mul_apply, hfY z hz, hfX z hz]
  refine ⟨eq_one_of_model ι (fun z hz => by rw [map_mul, LinearEquiv.mul_apply, hfX z hz, hfX z hz])
    (fun u => by rw [map_mul, LinearEquiv.mul_apply, hX, hX, Matrix.mulVec_mulVec]) e1,
    eq_one_of_model ι (fun z hz => by rw [map_mul, LinearEquiv.mul_apply, hfY z hz, hfY z hz])
    (fun u => by rw [map_mul, LinearEquiv.mul_apply, hY, hY, Matrix.mulVec_mulVec]) e2,
    eq_one_of_model ι (A := (wordX (R := F) p₁ q₁ p₂ q₂ p₃ q₃ *
        wordY (R := F) p₁ q₁ p₂ q₂ p₃ q₃) ^ 5) ?_ (spinAction_pow_model ι hXY 5) e3,
    ne_one_of_model ι hι hXY e4⟩
  intro z hz
  have : ∀ k : ℕ, spinAction (quadPlus n F) ((pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃) ^ k)
      (Pi.single z 1) = Pi.single z 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, map_mul, LinearEquiv.mul_apply, hfXY z hz, ih]
  exact this 5

end Model

section Real

variable {n : ℕ} {F : Type} [Field F]

theorem rankOneD_injective (hn : 3 ≤ n) (k : Fin n) : Function.Injective (rankOneD F hn k) :=
  CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ _ _ _

theorem rootD_mem_rankOne (hn : 3 ≤ n) (k : Fin n) (c : Multiplicative F) :
    rootD F hn k c ∈ rankOne (plusDatum n F hn).rootGroup k := by
  have h : (plusDatum n F hn).rootGroup (Pi.single k 1) = (rootD F hn k).range :=
    plusRootGroup_single hn k
  exact (le_sup_left : (plusDatum n F hn).rootGroup (Pi.single k 1) ≤ _)
    (by rw [h]; exact ⟨c, rfl⟩)

theorem negRootD_mem_rankOne (hn : 3 ≤ n) (k : Fin n) (c : Multiplicative F) :
    negRootD F hn k c ∈ rankOne (plusDatum n F hn).rootGroup k := by
  have h : (plusDatum n F hn).rootGroup (-Pi.single k 1) = (negRootD F hn k).range :=
    plusRootGroup_neg_single hn k
  exact (le_sup_right : (plusDatum n F hn).rootGroup (-Pi.single k 1) ≤ _)
    (by rw [h]; exact ⟨c, rfl⟩)

theorem rankOneD_mem_rankOne (hn : 3 ≤ n) (k : Fin n) (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    rankOneD F hn k M ∈ rankOne (plusDatum n F hn).rootGroup k := by
  refine (Subgroup.closure_le _).2 ?_ (rankOneD_mem_closure F hn k M)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact rootD_mem_rankOne hn k c
  · exact negRootD_mem_rankOne hn k c

theorem weylSL2_mul_self (t : Fˣ) : weylSL2 t * weylSL2 t = diagSL2 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagSL2_neg_one [CharP F 2] : diagSL2 (-1 : Fˣ) = 1 := by
  have : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [this, map_one]

theorem weylSL2_mul_weylSL2_one [CharP F 2] (t : Fˣ) : weylSL2 t * weylSL2 1 = diagSL2 t := by
  rw [diagSL2_eq]
  have : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [this]

theorem matrix_pow_five_aux {F : Type} [Field F] [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (!![1 + ω, 1; ω, 1] : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set A : Matrix (Fin 2) (Fin 2) F := !![1 + ω, 1; ω, 1] with hA
  have A2 : A * A = !![0, ω; ω + 1, ω + 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hω + ω * h2
    · linear_combination h2
    · linear_combination hω - h2
  have A4 : (A * A) * (A * A) = !![1, 1; ω, ω + 1] := by
    rw [A2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hω - h2
    · linear_combination hω - h2
    · linear_combination hω
    · linear_combination (ω ^ 2 + ω) * h2
  have A5 : (!![1, 1; ω, ω + 1] : Matrix (Fin 2) (Fin 2) F) * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ω * h2
    · linear_combination h2
    · linear_combination (ω + ω ^ 2) * h2
    · linear_combination ω * h2
  calc A ^ 5 = (A * A) * (A * A) * A := by noncomm_ring
    _ = 1 := by rw [A4, A5]

theorem upperSL2_mul_lowerSL2_pow_five [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (upperSL2 (1 : F) * lowerSL2 ω) ^ 5 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2,
    coe_lowerSL2, Matrix.SpecialLinearGroup.coe_one]
  have h : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; ω, 1] = !![1 + ω, 1; ω, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]
  exact matrix_pow_five_aux hω

theorem upperSL2_mul_lowerSL2_ne_one (ω : F) : upperSL2 (1 : F) * lowerSL2 ω ≠ 1 := by
  intro h
  have := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

end Real

section RealOver

variable {n : ℕ} {F : Type} [Field F] {Y : Type*} [Group Y]

theorem realOver_torus [CharP F 2] (hn : 3 ≤ n) {π : spinGroup (quadPlus n F) →* Y}
    {J : Subgroup Y}
    (hBJ : borel (plusDatum n F hn) (fun k => (torusD F hn k).range) ≤ J.comap π) {t : Fˣ}
    (ht5 : t ^ 5 = 1) (ht1 : t ≠ 1) (k : Fin n) :
    HeisEngine.RealOver 5 π (rankOne (plusDatum n F hn).rootGroup k) J := by
  have hT : torusD F hn k t ∈ J.comap π :=
    ((le_iSup (fun k => (torusD F hn k).range) k).trans (le_sup_left.trans hBJ)) ⟨t, rfl⟩
  have hxy : rankOneD F hn k (weylSL2 t) * rankOneD F hn k (weylSL2 1) = torusD F hn k t := by
    rw [← map_mul, weylSL2_mul_weylSL2_one, torusD_apply]
  refine HeisEngine.RealOver.of_involutions' (by decide)
    (x := rankOneD F hn k (weylSL2 t)) (y := rankOneD F hn k (weylSL2 1))
    (rankOneD_mem_rankOne hn k (weylSL2 t)) (rankOneD_mem_rankOne hn k (weylSL2 1)) ?_ ?_ ?_ ?_ ?_
  · rw [_root_.sq, ← map_mul, weylSL2_mul_self, diagSL2_neg_one, map_one]
  · rw [_root_.sq, ← map_mul, weylSL2_mul_self, diagSL2_neg_one, map_one]
  · rw [hxy, ← map_pow, ht5, map_one]
  · rw [hxy]
    exact torusD_ne_one hn k ht1
  · rw [hxy]
    exact hT

theorem realOver_omega [CharP F 2] (hn : 3 ≤ n) {π : spinGroup (quadPlus n F) →* Y}
    {J : Subgroup Y} {ω : F} (hω : ω ^ 2 + ω + 1 = 0) {k : Fin n}
    (hk : rankOne (plusDatum n F hn).rootGroup k ≤ J.comap π) :
    HeisEngine.RealOver 5 π (rankOne (plusDatum n F hn).rootGroup k) J := by
  have hxy : rootD F hn k (.ofAdd 1) * negRootD F hn k (.ofAdd ω) =
      rankOneD F hn k (upperSL2 1 * lowerSL2 ω) := by
    rw [map_mul, rankOneD_upperSL2, rankOneD_lowerSL2]
  have hx := rootD_mem_rankOne hn k (.ofAdd (1 : F))
  have hy := negRootD_mem_rankOne hn k (.ofAdd ω)
  refine HeisEngine.RealOver.of_involutions' (by decide) hx hy ?_ ?_ ?_ ?_ (hk (mul_mem hx hy))
  · rw [_root_.sq, ← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
  · rw [_root_.sq, ← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
  · rw [hxy, ← map_pow, upperSL2_mul_lowerSL2_pow_five hω, map_one]
  · rw [hxy]
    intro h
    exact upperSL2_mul_lowerSL2_ne_one ω (rankOneD_injective hn k (h.trans (map_one _).symm))

@[expose] def Piece5 (hn : 3 ≤ n) (F : Type) [Field F] (k₁ k₂ k₃ : Fin n) : Prop :=
  pieceX hn F k₁ k₂ k₃ * pieceX hn F k₁ k₂ k₃ = 1 ∧
    pieceY hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃ = 1 ∧
    (pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃) ^ 5 = 1 ∧
      pieceX hn F k₁ k₂ k₃ * pieceY hn F k₁ k₂ k₃ ≠ 1

theorem piece_A3 [CharP F 2] (hn : 3 ≤ n) {u : ℕ} (hu : u + 3 < n) :
    Piece5 hn F ⟨u, by omega⟩ ⟨u + 1, by omega⟩ ⟨u + 2, by omega⟩ := by
  refine piece_real hn (fun a : Fin 4 => (⟨u + a.val, by omega⟩ : Fin n))
    (fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
    (p₁ := .inl 0) (q₁ := .inr 1) (p₂ := .inl 1) (q₂ := .inr 2) (p₃ := .inl 2) (q₃ := .inr 3)
    ?_ ?_ ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide)
  · rw [nodeX_of_lt (by show u + 1 < n; omega)]
    rfl
  · rw [nodeY_of_lt (by show u + 1 < n; omega)]
    rfl
  · rw [nodeX_of_lt (by show u + 1 + 1 < n; omega)]
    rfl
  · rw [nodeY_of_lt (by show u + 1 + 1 < n; omega)]
    rfl
  · rw [nodeX_of_lt (by show u + 2 + 1 < n; omega)]
    rfl
  · rw [nodeY_of_lt (by show u + 2 + 1 < n; omega)]
    rfl

theorem piece_D3 [CharP F 2] (hn : 3 ≤ n) :
    Piece5 hn F ⟨n - 2, by omega⟩ ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ := by
  refine piece_real hn (fun a : Fin 3 => (⟨n - 3 + a.val, by omega⟩ : Fin n))
    (fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
    (p₁ := .inl 1) (q₁ := .inr 2) (p₂ := .inl 0) (q₂ := .inr 1) (p₃ := .inl 1) (q₃ := .inl 2)
    ?_ ?_ ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide)
  · rw [nodeX_of_lt (by show n - 2 + 1 < n; omega)]
    exact congrArg Sum.inl (Fin.ext (by simp; omega))
  · rw [nodeY_of_lt (by show n - 2 + 1 < n; omega)]
    exact congrArg Sum.inr (Fin.ext (by simp; omega))
  · rw [nodeX_of_lt (by show n - 3 + 1 < n; omega)]
    exact congrArg Sum.inl (Fin.ext (by simp))
  · rw [nodeY_of_lt (by show n - 3 + 1 < n; omega)]
    exact congrArg Sum.inr (Fin.ext (by simp))
  · rw [nodeX_of_last (by show n - 1 + 1 = n; omega) (by omega)]
    exact congrArg Sum.inl (Fin.ext (by simp; omega))
  · rw [nodeY_of_last (by show n - 1 + 1 = n; omega) (by omega)]
    exact congrArg Sum.inl (Fin.ext (by simp; omega))

theorem realOver_piece (hn : 3 ≤ n) {π : spinGroup (quadPlus n F) →* Y} {J : Subgroup Y}
    {k₁ k₂ k₃ : Fin n} (hP : Piece5 hn F k₁ k₂ k₃)
    (h₁ : rankOne (plusDatum n F hn).rootGroup k₁ ≤ J.comap π)
    (h₂ : rankOne (plusDatum n F hn).rootGroup k₂ ≤ J.comap π)
    (h₃ : rankOne (plusDatum n F hn).rootGroup k₃ ≤ J.comap π) :
    HeisEngine.RealOver 5 π (rankOne (plusDatum n F hn).rootGroup k₁ ⊔
      rankOne (plusDatum n F hn).rootGroup k₂ ⊔ rankOne (plusDatum n F hn).rootGroup k₃) J := by
  obtain ⟨hx2, hy2, h5, hne⟩ := hP
  set L₁ := rankOne (plusDatum n F hn).rootGroup k₁
  set L₂ := rankOne (plusDatum n F hn).rootGroup k₂
  set L₃ := rankOne (plusDatum n F hn).rootGroup k₃
  have m₁ : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have m₂ : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have m₃ : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have hx : pieceX hn F k₁ k₂ k₃ ∈ L₁ ⊔ L₂ ⊔ L₃ :=
    mul_mem (mul_mem (m₁ (rootD_mem_rankOne hn k₁ _)) (m₃ (rootD_mem_rankOne hn k₃ _)))
      (m₂ (negRootD_mem_rankOne hn k₂ _))
  have hy : pieceY hn F k₁ k₂ k₃ ∈ L₁ ⊔ L₂ ⊔ L₃ :=
    mul_mem (mul_mem (m₂ (rootD_mem_rankOne hn k₂ _)) (m₁ (negRootD_mem_rankOne hn k₁ _)))
      (m₃ (negRootD_mem_rankOne hn k₃ _))
  refine HeisEngine.RealOver.of_involutions' (by decide) hx hy ?_ ?_ h5 hne ?_
  · rw [_root_.sq]; exact hx2
  · rw [_root_.sq]; exact hy2
  · exact (sup_le (sup_le h₁ h₂) h₃) (mul_mem hx hy)

end RealOver

end CFSG.AGLEmbeddingD2.HeisSpinPlus
