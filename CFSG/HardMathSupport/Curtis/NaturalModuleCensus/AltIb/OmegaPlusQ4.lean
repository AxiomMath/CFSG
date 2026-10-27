module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusBase
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OrthEscape

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {n : ℕ} {F : Type} [Field F]

theorem finrank_isoFlag {i : ℕ} (hi : i ≤ n) : Module.finrank F (SymplecticFlag.isoFlag n F i) = i := by
  let f : Fin i → Fin n ⊕ Fin n := fun j => .inl ⟨j.val, lt_of_lt_of_le j.isLt hi⟩
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f, Sum.inl.injEq, Fin.mk.injEq] at hab
    exact Fin.ext hab
  have hli : LinearIndependent F (fun j : Fin i => (Pi.basisFun F (Fin n ⊕ Fin n)) (f j)) :=
    (Pi.basisFun F (Fin n ⊕ Fin n)).linearIndependent.comp f hf
  have hspan : SymplecticFlag.isoFlag n F i = Submodule.span F (Set.range
      (fun j : Fin i => (Pi.basisFun F (Fin n ⊕ Fin n)) (f j))) := by
    unfold SymplecticFlag.isoFlag
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Pi.basisFun_apply, f]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.val, lt_of_lt_of_le j.isLt hi⟩, j.isLt, rfl⟩
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

theorem false_of_q4 [Finite F] [CharP F 2] (hn : 4 ≤ n) (hF4 : Nat.card F = 4) {S : Finset ℕ}
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) {i : ℕ} (hiS : i ∈ S) (hi2 : 2 ≤ i)
    {x : ↥(Om n F)} (hxp : x ^ 5 = 1)
    (hfix : ∀ g : ↥(Om n F), g * x = x * g → g ∈ JO n F S) : False := by
  have hxJ : x ∈ JO n F S := hfix x rfl
  have hxsJ : omSp x ∈ Jfl n F S := hxJ
  set M : GL (Fin n ⊕ Fin n) F := (x : GL (Fin n ⊕ Fin n) F) with hM
  set W : Submodule F (Fin n ⊕ Fin n → F) := SymplecticFlag.isoFlag n F i with hW
  have hin := (hS i hiS).2
  have hgi : ∀ g : ↥(Om n F), g ∈ JO n F S → ∀ w ∈ W,
      ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w ∈ W := by
    intro g hg w hw
    have hgst := SymplecticHigher.mem_flagStabilizer.mp hg i hiS
    rw [flag_eq_isoFlag hin] at hgst
    exact spMat_mulVec_mem_of_mem_stabilizer (g := omSp g) hgst hw
  have hC : ∀ g ∈ StatedOmega (quadPlusForm n F).Q, g * M = M * g →
      ∀ w ∈ W, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w ∈ W := by
    intro g hg hgM w hw
    have hgx : (⟨g, hg⟩ : ↥(Om n F)) * x = x * ⟨g, hg⟩ := Subtype.ext hgM
    exact hgi _ (hfix _ hgx) w hw
  have hι : 5 ≤ Fintype.card (Fin n ⊕ Fin n) := by simp; omega
  have hWQ : ∀ w ∈ W, (quadPlusForm n F).Q w = 0 := by
    intro w hw
    rw [hW, SymplecticFlag.mem_isoFlag] at hw
    show ∑ j, w (.inl j) * w (.inr j) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [hw.1 j, mul_zero]
  have hM5 : M ^ 5 = 1 := by rw [hM, ← Subgroup.coe_pow, hxp]; rfl
  have hMQ : ∀ v, (quadPlusForm n F).Q ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      (quadPlusForm n F).Q v := fun v => om_preserves x.2 v
  set T : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F) :=
    Matrix.toLin' (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hT
  have hT5 : T ^ 5 = 1 := toLin'_pow_eq_one M hM5
  have hTQ : ∀ v, (quadPlusForm n F).Q (T v) = (quadPlusForm n F).Q v := fun v => by
    rw [hT, Matrix.toLin'_apply]; exact hMQ v
  have hWT : ∀ w ∈ W, T w ∈ W := fun w hw => by
    rw [hT, Matrix.toLin'_apply]; exact hgi x hxJ w hw
  have hE := eichler_stable_of_centralizer (quadPlusForm n F) M hι W hC
  have hfixW : ∀ w ∈ W, T w = w := by
    intro f hfW
    by_contra hf
    obtain ⟨a, f', ha, hf'W, hf'0, hf'T⟩ := NM_exists_quadratic_vec T hF4 hT5 W hWT hfW hf
    exact NM_false_of_quadratic (quadPlusForm n F) T hF4 hT5 hTQ W hWQ hWT hE ha hf'W hf'0 hf'T
  set W₁ : Submodule F (Fin n ⊕ Fin n → F) :=
    LinearMap.ker ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVecLin - LinearMap.id)
    with hW₁
  have hW₁mem : ∀ v, v ∈ W₁ ↔ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v = v :=
    fun v => by
    rw [hW₁, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hWW₁ : W ⊓ W₁ = W := by
    refine inf_eq_left.2 fun w hw => (hW₁mem w).2 ?_
    have := hfixW w hw
    rwa [hT, Matrix.toLin'_apply] at this
  have hdim : 2 ≤ Module.finrank F ↥(W ⊓ W₁) := by
    rw [hWW₁, hW, finrank_isoFlag hin]
    exact hi2
  exact false_of_fixed_escape_omega (quadPlusForm n F) M hι (by decide : Odd 5) hM5 hMQ hW₁mem
    hWQ hdim hC

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
