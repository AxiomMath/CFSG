module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Cast

variable (K : Type) [Field K] [CharP K 2]

abbrev omCast : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

variable {K}

theorem omCast_injective : Function.Injective (omCast K) := (omCast K).injective

theorem omCast_surjective [Finite K] (hK : Nat.card K = 2) : Function.Surjective (omCast K) :=
  (omCast_injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])).2

theorem exists_omCast_comp [Finite K] (hK : Nat.card K = 2) {ι : Type} (w : ι → K) :
    ∃ v : ι → ZMod 2, w = omCast K ∘ v :=
  ⟨fun i => (omCast_surjective hK (w i)).choose,
    funext fun i => (omCast_surjective hK (w i)).choose_spec.symm⟩

variable {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ]

variable (K) in
abbrev omMat (A : Matrix ι κ (ZMod 2)) : Matrix ι κ K := A.map (omCast K)

theorem omMat_mul (A : Matrix ι κ (ZMod 2)) (B : Matrix κ μ (ZMod 2)) :
    omMat K (A * B) = omMat K A * omMat K B :=
  Matrix.map_mul

theorem omMat_one : omMat K (1 : Matrix ι ι (ZMod 2)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem omMat_mulVec (A : Matrix ι κ (ZMod 2)) (v : κ → ZMod 2) :
    omMat K A *ᵥ (omCast K ∘ v) = omCast K ∘ (A *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (omCast K) A v i).symm

theorem omMat_injective : Function.Injective (omMat (ι := ι) (κ := κ) K) := fun A B h => by
  ext i j
  exact omCast_injective (congrFun (congrFun h i) j)

theorem omMat_fromBlocks {ι' κ' : Type} (A : Matrix ι κ (ZMod 2)) (B : Matrix ι κ' (ZMod 2))
    (C : Matrix ι' κ (ZMod 2)) (D : Matrix ι' κ' (ZMod 2)) :
    omMat K (fromBlocks A B C D) = fromBlocks (omMat K A) (omMat K B) (omMat K C) (omMat K D) :=
  fromBlocks_map _ _ _ _ _

variable (K) in
@[expose] def omGL (A B : Matrix ι ι (ZMod 2)) (h : A * B = 1) : GL ι K :=
  ⟨omMat K A, omMat K B, by rw [← omMat_mul, h, omMat_one],
    by rw [← omMat_mul, mul_eq_one_comm.1 h, omMat_one]⟩

@[simp] theorem coe_omGL (A B : Matrix ι ι (ZMod 2)) (h : A * B = 1) :
    ((omGL K A B h : GL ι K) : Matrix ι ι K) = omMat K A :=
  rfl

theorem coe_omGL_inv (A B : Matrix ι ι (ZMod 2)) (h : A * B = 1) :
    (((omGL K A B h)⁻¹ : GL ι K) : Matrix ι ι K) = omMat K B :=
  rfl

theorem omGL_commutator (A B C D E F : Matrix ι ι (ZMod 2)) (hA : A * B = 1) (hC : C * D = 1)
    (hE : E * F = 1) (h : A * C * B * D = E) :
    ⁅omGL K A B hA, omGL K C D hC⁆ = omGL K E F hE := by
  apply Units.ext
  simp only [commutatorElement_def, Units.val_mul, coe_omGL, coe_omGL_inv]
  rw [← omMat_mul, ← omMat_mul, ← omMat_mul, h]

theorem omIsom [Finite K] (hK : Nat.card K = 2) {Qz : (ι → ZMod 2) → ZMod 2} {Qk : (ι → K) → K}
    (hQ : ∀ v, Qk (omCast K ∘ v) = omCast K (Qz v)) {A : Matrix ι ι (ZMod 2)}
    (hA : ∀ v, Qz (A *ᵥ v) = Qz v) (w : ι → K) : Qk (omMat K A *ᵥ w) = Qk w := by
  obtain ⟨v, rfl⟩ := exists_omCast_comp hK w
  rw [omMat_mulVec, hQ, hQ, hA]

theorem statedQuadPlus_omCast (n : ℕ) (v : Fin n ⊕ Fin n → ZMod 2) :
    StatedQuadPlus n K (omCast K ∘ v) = omCast K (StatedQuadPlus n (ZMod 2) v) := by
  simp [StatedQuadPlus, map_sum, map_mul]

theorem statedQuadMinus_omCast (n : ℕ) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus n K 1 1 (omCast K ∘ v) = omCast K (StatedQuadMinus n (ZMod 2) 1 1 v) := by
  simp only [StatedQuadMinus, map_add, map_sum, map_mul, map_pow, map_one, Function.comp_apply]

end Cast

section Isom

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev omIsoSet (Q : (ι → K) → K) : Set (GL ι K) :=
  {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}

theorem statedOmega_eq_omIsoSet (Q : (ι → K) → K) :
    StatedOmega Q = ⁅closure (omIsoSet Q), closure (omIsoSet Q)⁆ :=
  rfl

theorem isom_of_mem_closure {Q : (ι → K) → K} {X : GL ι K} (hX : X ∈ closure (omIsoSet Q))
    (v : ι → K) : Q ((X : Matrix ι ι K) *ᵥ v) = Q v := by
  induction hX using Subgroup.closure_induction generalizing v with
  | mem x hx => exact hx v
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, ← mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    rw [← hx (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v), mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mulVec]

theorem closure_omIsoSet_le (Q : (ι → K) → K) :
    StatedOmega Q ≤ closure (omIsoSet Q) := by
  rw [statedOmega_eq_omIsoSet, Subgroup.commutator_le]
  intro a ha b hb
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem isom_of_mem_statedOmega {Q : (ι → K) → K} {X : GL ι K} (hX : X ∈ StatedOmega Q)
    (v : ι → K) : Q ((X : Matrix ι ι K) *ᵥ v) = Q v :=
  isom_of_mem_closure (closure_omIsoSet_le Q hX) v

theorem commutator_mem_statedOmega {Q : (ι → K) → K} {X Y : GL ι K} (hX : X ∈ omIsoSet Q)
    (hY : Y ∈ omIsoSet Q) : ⁅X, Y⁆ ∈ StatedOmega Q :=
  Subgroup.commutator_mem_commutator (subset_closure hX) (subset_closure hY)

end Isom

section Xi

variable {K : Type} [Field K]

@[expose] def omXi : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 1]

theorem omXi_mul_sub_one : omXi * (omXi - 1) = (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omXi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem sub_one_mul_omXi : (omXi - 1) * omXi = (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omXi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem eq_of_mul_omXi_comm {A : Matrix (Fin 2) (Fin 2) K} (hA : A * omXi = omXi * A) :
    A = !![A 0 0, A 0 1; A 0 1, A 0 0 + A 0 1] := by
  have a1 := congrFun (congrFun hA 0) 0
  have a2 := congrFun (congrFun hA 0) 1
  simp [omXi, Matrix.mul_apply, Fin.sum_univ_two] at a1 a2
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination a1 | linear_combination -a1 | linear_combination a2 |
      linear_combination -a2

theorem omXi_comm {A B : Matrix (Fin 2) (Fin 2) K} (hA : A * omXi = omXi * A)
    (hB : B * omXi = omXi * B) : A * B = B * A := by
  rw [eq_of_mul_omXi_comm hA, eq_of_mul_omXi_comm hB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Xi

section Conj

variable {K : Type} [Field K] {ι₈ ι₆ : Type} [Fintype ι₈] [DecidableEq ι₈] [Fintype ι₆]
  [DecidableEq ι₆] (T : Matrix ι₈ (Fin 2 ⊕ ι₆) K) (Ti : Matrix (Fin 2 ⊕ ι₆) ι₈ K)
  (h1 : T * Ti = 1) (h2 : Ti * T = 1)

include h2 in
theorem omConj_mul (A B : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) :
    T * A * Ti * (T * B * Ti) = T * (A * B) * Ti := by
  have key : ∀ X : Matrix (Fin 2 ⊕ ι₆) ι₈ K, Ti * (T * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [Matrix.mul_assoc, key]

@[expose] def omConj : GL (Fin 2 ⊕ ι₆) K →* GL ι₈ K where
  toFun G := ⟨T * (G : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) * Ti,
    T * ((G⁻¹ : GL (Fin 2 ⊕ ι₆) K) : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) * Ti,
    by rw [omConj_mul T Ti h2, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, h1],
    by rw [omConj_mul T Ti h2, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, h1]⟩
  map_one' := Units.ext (by simp [h1])
  map_mul' G H := Units.ext (by
    change T * ((G * H : GL (Fin 2 ⊕ ι₆) K) : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) * Ti =
      T * (G : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) * Ti *
        (T * (H : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) * Ti)
    rw [omConj_mul T Ti h2, Units.val_mul])

theorem coe_omConj (G : GL (Fin 2 ⊕ ι₆) K) :
    ((omConj T Ti h1 h2 G : GL ι₈ K) : Matrix ι₈ ι₈ K) =
      T * (G : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) * Ti :=
  rfl

@[expose] def omBlock : GL (Fin 2) K × GL ι₆ K →* GL (Fin 2 ⊕ ι₆) K where
  toFun p := ⟨fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) K) 0 0 (p.2 : Matrix ι₆ ι₆ K),
    fromBlocks ((p.1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
      ((p.2⁻¹ : GL ι₆ K) : Matrix ι₆ ι₆ K),
    by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' p q := Units.ext (by simp [fromBlocks_multiply])

theorem coe_omBlock (p : GL (Fin 2) K × GL ι₆ K) :
    ((omBlock p : GL (Fin 2 ⊕ ι₆) K) : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K) =
      fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) K) 0 0 (p.2 : Matrix ι₆ ι₆ K) :=
  rfl

@[expose] def omEps : GL ι₆ K →* GL ι₈ K :=
  (omConj T Ti h1 h2).comp (omBlock.comp (MonoidHom.inr _ _))

theorem coe_omEps (D : GL ι₆ K) :
    ((omEps T Ti h1 h2 D : GL ι₈ K) : Matrix ι₈ ι₈ K) =
      T * fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 (D : Matrix ι₆ ι₆ K) * Ti :=
  rfl

theorem omEps_injective : Function.Injective (omEps T Ti h1 h2) := by
  intro D D' h
  have h' := congrArg (fun G : GL ι₈ K => Ti * (G : Matrix ι₈ ι₈ K) * T) h
  simp only [coe_omEps] at h'
  have key : ∀ X : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K, Ti * (T * X * Ti) * T = X := fun X => by
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [key, key] at h'
  exact Units.ext (fromBlocks_inj.1 h').2.2.2

include h1 in
theorem omConj_eq (G : Matrix ι₈ ι₈ K) : T * (Ti * G * T) * Ti = G := by
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]

include h1 h2 in
theorem commute_of_conj {G H : Matrix ι₈ ι₈ K}
    (h : Ti * G * T * (Ti * H * T) = Ti * H * T * (Ti * G * T)) : G * H = H * G := by
  rw [← omConj_eq T Ti h1 G, ← omConj_eq T Ti h1 H, omConj_mul T Ti h2, omConj_mul T Ti h2, h]

include h1 in
theorem omConjInv_mul (A B : Matrix ι₈ ι₈ K) : Ti * A * T * (Ti * B * T) = Ti * (A * B) * T := by
  have key : ∀ X : Matrix ι₈ (Fin 2 ⊕ ι₆) K, T * (Ti * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [Matrix.mul_assoc, key]

end Conj

section LeviFact

variable {K : Type} [Field K] {ι₈ ι₆ : Type} [Fintype ι₈] [DecidableEq ι₈] [Fintype ι₆]
  [DecidableEq ι₆] {T : Matrix ι₈ (Fin 2 ⊕ ι₆) K} {Ti : Matrix (Fin 2 ⊕ ι₆) ι₈ K}
  (h1 : T * Ti = 1) (h2 : Ti * T = 1) {Q₈ : (ι₈ → K) → K} {QP : (Fin 2 → K) → K}
  {Q₆ : (ι₆ → K) → K} (hQ : ∀ w, Q₈ (T *ᵥ w) = QP (w ∘ Sum.inl) + Q₆ (w ∘ Sum.inr))

include hQ in
theorem omEps_mem_omIsoSet {D : GL ι₆ K} (hD : D ∈ omIsoSet Q₆) :
    omEps T Ti h1 h2 D ∈ omIsoSet Q₈ := by
  intro v
  have hv : T *ᵥ (Ti *ᵥ v) = v := by rw [mulVec_mulVec, h1, one_mulVec]
  rw [coe_omEps, ← mulVec_mulVec, ← mulVec_mulVec, hQ, fromBlocks_mulVec]
  conv_rhs => rw [← hv, hQ]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec, add_zero, zero_add]
  rw [hD]

include hQ in
theorem map_omEps_statedOmega_le :
    (StatedOmega Q₆).map (omEps T Ti h1 h2) ≤ StatedOmega Q₈ := by
  rw [statedOmega_eq_omIsoSet, statedOmega_eq_omIsoSet, Subgroup.map_commutator]
  have h : (closure (omIsoSet Q₆)).map (omEps T Ti h1 h2) ≤ closure (omIsoSet Q₈) := by
    rw [MonoidHom.map_closure]
    exact closure_mono (by rintro _ ⟨D, hD, rfl⟩; exact omEps_mem_omIsoSet h1 h2 hQ hD)
  exact Subgroup.commutator_mono h h

@[expose] def omEps0 : StatedOmega Q₆ →* StatedOmega Q₈ :=
  ((omEps T Ti h1 h2).comp (StatedOmega Q₆).subtype).codRestrict _
    fun D => map_omEps_statedOmega_le h1 h2 hQ ⟨D, D.2, rfl⟩

theorem coe_omEps0 (D : StatedOmega Q₆) :
    ((omEps0 h1 h2 hQ D : StatedOmega Q₈) : GL ι₈ K) = omEps T Ti h1 h2 D :=
  rfl

theorem omEps0_injective : Function.Injective (omEps0 h1 h2 hQ) := fun _ _ h =>
  Subtype.ext (omEps_injective T Ti h1 h2 (congrArg Subtype.val h))

theorem omShape (G : Matrix (Fin 2 ⊕ ι₆) (Fin 2 ⊕ ι₆) K)
    (hG : G * fromBlocks omXi 0 0 1 = fromBlocks omXi 0 0 1 * G) :
    G = fromBlocks G.toBlocks₁₁ 0 0 G.toBlocks₂₂ ∧
      G.toBlocks₁₁ * omXi = omXi * G.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks G, fromBlocks_multiply, fromBlocks_multiply] at hG
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at hG
  obtain ⟨e11, e12, e21, -⟩ := fromBlocks_inj.1 hG
  have z12 : G.toBlocks₁₂ = 0 := by
    have h0 : ((omXi : Matrix (Fin 2) (Fin 2) K) - 1) * G.toBlocks₁₂ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, ← e12, sub_self]
    rw [← Matrix.one_mul G.toBlocks₁₂, ← omXi_mul_sub_one, Matrix.mul_assoc, h0, Matrix.mul_zero]
  have z21 : G.toBlocks₂₁ = 0 := by
    have h0 : G.toBlocks₂₁ * ((omXi : Matrix (Fin 2) (Fin 2) K) - 1) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, e21, sub_self]
    rw [← Matrix.mul_one G.toBlocks₂₁, ← sub_one_mul_omXi, ← Matrix.mul_assoc, h0,
      Matrix.zero_mul]
  refine ⟨?_, e11⟩
  conv_lhs => rw [← fromBlocks_toBlocks G]
  rw [z12, z21]

include h1 h2 hQ in
theorem omBlock_decomp {x g : GL ι₈ K}
    (hx : Ti * (x : Matrix ι₈ ι₈ K) * T = fromBlocks omXi 0 0 1) (hg : g * x = x * g)
    (hgQ : g ∈ omIsoSet Q₈) :
    ∃ (A : GL (Fin 2) K) (D : GL ι₆ K),
      (A : Matrix (Fin 2) (Fin 2) K) * omXi = omXi * (A : Matrix (Fin 2) (Fin 2) K) ∧
      D ∈ omIsoSet Q₆ ∧ g = omConj T Ti h1 h2 (omBlock (A, D)) := by
  have hcomm : ∀ y : GL ι₈ K, y * x = x * y →
      Ti * (y : Matrix ι₈ ι₈ K) * T * fromBlocks omXi 0 0 1 =
        fromBlocks omXi 0 0 1 * (Ti * (y : Matrix ι₈ ι₈ K) * T) := by
    intro y hy
    rw [← hx, omConjInv_mul T Ti h1, omConjInv_mul T Ti h1, ← Units.val_mul, ← Units.val_mul, hy]
  have hginv : g⁻¹ * x = x * g⁻¹ := ((Commute.inv_left hg)).eq
  obtain ⟨hG, hA⟩ := omShape (Ti * (g : Matrix ι₈ ι₈ K) * T) (hcomm g hg)
  obtain ⟨hH, -⟩ := omShape (Ti * ((g⁻¹ : GL ι₈ K) : Matrix ι₈ ι₈ K) * T) (hcomm g⁻¹ hginv)
  set G := Ti * (g : Matrix ι₈ ι₈ K) * T with hGdef
  set H := Ti * ((g⁻¹ : GL ι₈ K) : Matrix ι₈ ι₈ K) * T with hHdef
  have hGH : G * H = 1 := by
    rw [hGdef, hHdef, omConjInv_mul T Ti h1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, h2]
  have hHG : H * G = 1 := by
    rw [hGdef, hHdef, omConjInv_mul T Ti h1, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, h2]
  rw [hG, hH, fromBlocks_multiply, ← fromBlocks_one] at hGH hHG
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hGH hHG
  obtain ⟨a1, -, -, a4⟩ := fromBlocks_inj.1 hGH
  obtain ⟨b1, -, -, b4⟩ := fromBlocks_inj.1 hHG
  refine ⟨⟨G.toBlocks₁₁, H.toBlocks₁₁, a1, b1⟩, ⟨G.toBlocks₂₂, H.toBlocks₂₂, a4, b4⟩, hA, ?_, ?_⟩
  · intro f
    change Q₆ (G.toBlocks₂₂ *ᵥ f) = Q₆ f
    have hgm : (g : Matrix ι₈ ι₈ K) = T * G * Ti := (omConj_eq T Ti h1 _).symm
    have key : (g : Matrix ι₈ ι₈ K) *ᵥ (T *ᵥ Sum.elim 0 f) =
        T *ᵥ Sum.elim 0 (G.toBlocks₂₂ *ᵥ f) := by
      rw [hgm, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec (M := Ti) (N := T), h2,
        one_mulVec, hG, fromBlocks_mulVec]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_mulVec, add_zero,
        zero_add]
      rw [Matrix.toBlocks_fromBlocks₂₂]
    have := hgQ (T *ᵥ Sum.elim 0 f)
    rw [key, hQ, hQ] at this
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at this
    exact add_left_cancel this
  · apply Units.ext
    rw [coe_omConj, coe_omBlock]
    change (g : Matrix ι₈ ι₈ K) = T * fromBlocks G.toBlocks₁₁ 0 0 G.toBlocks₂₂ * Ti
    rw [← hG, hGdef, omConj_eq T Ti h1]

include h1 h2 hQ in
theorem commutator_centralizer_le_range_omEps0 {x : StatedOmega Q₈}
    (hx : Ti * ((x : GL ι₈ K) : Matrix ι₈ ι₈ K) * T = fromBlocks omXi 0 0 1) :
    ⁅centralizer ({x} : Set (StatedOmega Q₈)), centralizer ({x} : Set (StatedOmega Q₈))⁆ ≤
      (omEps0 h1 h2 hQ).range := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hcx : ∀ y : StatedOmega Q₈, y ∈ centralizer ({x} : Set (StatedOmega Q₈)) →
      (y : GL ι₈ K) * x = x * y := fun y hy => by
    have := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact congrArg Subtype.val this
  obtain ⟨A, D, hA, hD, hgA⟩ :=
    omBlock_decomp h1 h2 hQ hx (hcx a ha) (fun v => isom_of_mem_statedOmega a.2 v)
  obtain ⟨A', D', hA', hD', hgB⟩ :=
    omBlock_decomp h1 h2 hQ hx (hcx b hb) (fun v => isom_of_mem_statedOmega b.2 v)
  refine ⟨⟨⁅D, D'⁆, commutator_mem_statedOmega hD hD'⟩, Subtype.ext ?_⟩
  have hAA : ⁅A, A'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact omXi_comm hA hA')
  have hprod : ⁅((A, D) : GL (Fin 2) K × GL ι₆ K), (A', D')⁆ = (1, ⁅D, D'⁆) := by
    refine Prod.ext ?_ rfl
    simpa only [commutatorElement_def, Prod.fst_mul, Prod.fst_inv] using hAA
  rw [coe_omEps0]
  change omEps T Ti h1 h2 ⁅D, D'⁆ = ⁅(a : GL ι₈ K), (b : GL ι₈ K)⁆
  rw [hgA, hgB, ← map_commutatorElement, ← map_commutatorElement, hprod]
  rfl

include h1 h2 hQ in
theorem range_omEps0_le_centralizer {x : StatedOmega Q₈}
    (hx : Ti * ((x : GL ι₈ K) : Matrix ι₈ ι₈ K) * T = fromBlocks omXi 0 0 1) :
    (omEps0 h1 h2 hQ).range ≤ centralizer ({x} : Set (StatedOmega Q₈)) := by
  rintro _ ⟨D, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  change (omEps T Ti h1 h2 D : Matrix ι₈ ι₈ K) * ((x : GL ι₈ K) : Matrix ι₈ ι₈ K) =
    ((x : GL ι₈ K) : Matrix ι₈ ι₈ K) * (omEps T Ti h1 h2 D : Matrix ι₈ ι₈ K)
  apply commute_of_conj T Ti h1 h2
  have key : Ti * ((omEps T Ti h1 h2 D : GL ι₈ K) : Matrix ι₈ ι₈ K) * T =
      fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 ((D : GL ι₆ K) : Matrix ι₆ ι₆ K) := by
    rw [coe_omEps]
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [hx, key, fromBlocks_multiply, fromBlocks_multiply]
  simp

include h1 h2 hQ in
theorem commutator_range_omEps0 (hperf : ⁅StatedOmega Q₆, StatedOmega Q₆⁆ = StatedOmega Q₆) :
    ⁅(omEps0 h1 h2 hQ).range, (omEps0 h1 h2 hQ).range⁆ = (omEps0 h1 h2 hQ).range := by
  have htop : ⁅(⊤ : Subgroup (StatedOmega Q₆)), (⊤ : Subgroup (StatedOmega Q₆))⁆ = ⊤ := by
    apply Subgroup.map_injective (StatedOmega Q₆).subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]

include h1 h2 hQ in
theorem perfectCore_centralizer_omOrth {x : StatedOmega Q₈}
    (hx : Ti * ((x : GL ι₈ K) : Matrix ι₈ ι₈ K) * T = fromBlocks omXi 0 0 1)
    (hperf : ⁅StatedOmega Q₆, StatedOmega Q₆⁆ = StatedOmega Q₆) :
    perfectCore (centralizer ({x} : Set (StatedOmega Q₈))) = (omEps0 h1 h2 hQ).range := by
  refine le_antisymm ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans ?_)
    (CFSG.Quasithin.le_perfectCore_of_perfect (range_omEps0_le_centralizer h1 h2 hQ hx)
      (commutator_range_omEps0 h1 h2 hQ hperf))
  have e : CFSG.Quasithin.derivedSeriesOf (centralizer ({x} : Set (StatedOmega Q₈))) 1 =
      ⁅centralizer ({x} : Set (StatedOmega Q₈)), centralizer ({x} : Set (StatedOmega Q₈))⁆ := rfl
  rw [e]
  exact commutator_centralizer_le_range_omEps0 h1 h2 hQ hx

end LeviFact

section Image

variable {A B : Type*} [Group A] [Group B]

theorem centralizer_singleton_inf_range {φ : A →* B} (hφ : Function.Injective φ) (a : A) :
    centralizer ({φ a} : Set B) ⊓ φ.range = (centralizer ({a} : Set A)).map φ := by
  ext y
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hy, ⟨z, rfl⟩⟩
    refine ⟨z, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact hφ (by rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.1 hy)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ⟨z, rfl⟩⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hz
    rw [mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hz]

theorem card_centralizer_singleton_inf_range {φ : A →* B} (hφ : Function.Injective φ) (a : A) :
    Nat.card (centralizer ({φ a} : Set B) ⊓ φ.range : Subgroup B) =
      Nat.card (centralizer ({a} : Set A)) := by
  rw [centralizer_singleton_inf_range hφ, Subgroup.card_map_of_injective hφ]

end Image

end CFSG.SeitzReduction.F4Pilot
