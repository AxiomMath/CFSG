module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.LieType.SemisimpleCentralizers.HeldLangSU

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement
open CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uFieldAut_mul_uConjAut (hn1 : 1 ≤ n) (φ : K ≃+* K) (B : uU h n)
    (hB : glAut φ (B : GL (Fin n) K) ∈ uU h n) :
    uFieldAut h hn1 φ * uConjAut h hn1 B = uConjAut h hn1 ⟨glAut φ B, hB⟩ * uFieldAut h hn1 φ := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.mul_apply, MulAut.mul_apply]
  let y : StatedSU n (p ^ f) K :=
    ⟨(B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹, uConjSU_mem h B g⟩
  let x' : StatedSU n (p ^ f) K := ⟨glAut φ (g : GL (Fin n) K), uFieldSU_mem h φ g⟩
  let B' : uU h n := ⟨glAut φ B, hB⟩
  have e1 : uConjAut h hn1 B (QuotientGroup.mk g) = QuotientGroup.mk y := uConjAut_proj h hn1 B g
  have e2 : uFieldAut h hn1 φ (QuotientGroup.mk g) = QuotientGroup.mk x' := uFieldAut_proj h hn1 φ g
  have e3 : uFieldAut h hn1 φ (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨glAut φ (y : GL (Fin n) K), uFieldSU_mem h φ y⟩ : StatedSU n (p ^ f) K) :=
    uFieldAut_proj h hn1 φ y
  have e4 : uConjAut h hn1 B' (QuotientGroup.mk x') =
      QuotientGroup.mk (⟨(B' : GL (Fin n) K) * (x' : GL (Fin n) K) * (B' : GL (Fin n) K)⁻¹,
        uConjSU_mem h B' x'⟩ : StatedSU n (p ^ f) K) := uConjAut_proj h hn1 B' x'
  rw [e1, e2, e3, e4]
  congr 1
  apply Subtype.ext
  change glAut φ ((B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹) =
    glAut φ (B : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (glAut φ (B : GL (Fin n) K))⁻¹
  rw [map_mul, map_mul, map_inv]

variable [Finite K] [Fact p.Prime] [CharP K p]

theorem bar_eq (c : K) : h.bar c = unitaryInvolution K p f c := by
  rw [h.bar_apply, unitaryInvolution_apply]

theorem isIso_of_mem_uU (hbb : ∀ x, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    {A : GL (Fin n) K} (hA : A ∈ uU h n) : IsIso (unitaryInvolution K p f) A := by
  have := (mem_uU h).1 hA
  unfold IsIso conjTr
  have e : (A : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K p f) = (A : Matrix (Fin n) (Fin n) K).map h.bar := by
    ext i j
    simp [bar_eq h]
  rw [e]
  exact this

theorem mem_uU_of_isIso {A : GL (Fin n) K} (hA : IsIso (unitaryInvolution K p f) A) : A ∈ uU h n := by
  rw [mem_uU]
  have e : (A : Matrix (Fin n) (Fin n) K).map h.bar = (A : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K p f) := by
    ext i j
    simp [bar_eq h]
  rw [e]
  exact hA

theorem uConjAut_mem_innAutDerived (hn : 3 ≤ n) (A : uU h n)
    (hA3 : (uConjAut h (by omega) A) ^ 3 = 1) :
    uConjAut h (by omega) A ∈ innAutDerived (StatedProj (StatedSU n (p ^ f) K)) := by
  have hn1 : 1 ≤ n := by omega
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, Nat.mul_comm]
  set bar : K ≃+* K := unitaryInvolution K p f with hbardef
  have hbb : ∀ x, bar (bar x) = x := fun x => by
    rw [← bar_eq h, ← bar_eq h, h.bar_bar]
  have hIso : IsIso bar (A : GL (Fin n) K) := isIso_of_mem_uU h hbb A.2
  have hIsoA' : IsIso bar (glAut bar (A : GL (Fin n) K)) := hIso.glMap (fun x => rfl)
  have hmem : glAut bar (A : GL (Fin n) K) ∈ uU h n := mem_uU_of_isIso h hIsoA'
  let A' : uU h n := ⟨glAut bar A, hmem⟩
  let X := uConjAut h hn1 A
  let τ := uFieldAut h hn1 bar
  let X' := uConjAut h hn1 A'
  have hτX : τ * X = X' * τ := uFieldAut_mul_uConjAut h hn1 bar A hmem
  have hC : ⁅X, τ⁆ = uConjAut h hn1 (A * A'⁻¹) := by
    rw [commutatorElement_def, map_mul, map_inv]
    have h1 : τ * X * τ⁻¹ = X' := by rw [hτX, mul_assoc, mul_inv_cancel, mul_one]
    calc X * τ * X⁻¹ * τ⁻¹ = X * (τ * X * τ⁻¹)⁻¹ := by group
      _ = X * X'⁻¹ := by rw [h1]
  set s : uU h n := A * A'⁻¹ * A⁻¹ * A⁻¹ with hsdef
  have hsIso : IsIso bar (s : GL (Fin n) K) := isIso_of_mem_uU h hbb s.2
  have hdetA := hIso.det_mul_det
  have hdA : Matrix.GeneralLinearGroup.det (glAut bar (A : GL (Fin n) K)) =
      (Matrix.GeneralLinearGroup.det (A : GL (Fin n) K))⁻¹ := by
    have h1 : ((glAut bar (A : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
        bar ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := det_glMap bar (A : GL (Fin n) K)
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply, h1]
    exact eq_inv_of_mul_eq_one_left hdetA
  have hdetU : Matrix.GeneralLinearGroup.det (s : GL (Fin n) K) = 1 := by
    show Matrix.GeneralLinearGroup.det ((A : GL (Fin n) K) * (glAut bar (A : GL (Fin n) K))⁻¹ *
      (A : GL (Fin n) K)⁻¹ * (A : GL (Fin n) K)⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hdA]
    group
  have hs : (s : GL (Fin n) K) ∈ StatedSU n (p ^ f) K := by
    rw [← SUid_eq_statedSU hK n]
    refine mem_SUid.2 ⟨?_, hsIso⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdetU, Units.val_one]
  have hS : uConjAut h hn1 s ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSU n (p ^ f) K)) := by
    refine ⟨QuotientGroup.mk ⟨(s : GL (Fin n) K), hs⟩, ?_⟩
    refine MulEquiv.ext fun z => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    have e : uConjAut h hn1 s (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, uConjSU_mem h s g⟩ :=
      uConjAut_proj h hn1 s g
    rw [e, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  have hB : (A * A'⁻¹ : uU h n) = s * A * A := by rw [hsdef]; group
  have hC' : ⁅X, τ⁆ = uConjAut h hn1 s * X * X := by
    rw [hC, hB, map_mul, map_mul]
  have hX3 : X * X * X = 1 := by
    rw [← pow_three']
    exact hA3
  have hXeq : X = ⁅X, τ⁆⁻¹ * uConjAut h hn1 s := by
    calc X = (X * X)⁻¹ := (inv_eq_of_mul_eq_one_right hX3).symm
      _ = (uConjAut h hn1 s * X * X)⁻¹ * uConjAut h hn1 s := by group
      _ = ⁅X, τ⁆⁻¹ * uConjAut h hn1 s := by rw [hC']
  have hcomm : ⁅X, τ⁆ ∈ innAutDerived (StatedProj (StatedSU n (p ^ f) K)) :=
    commutator_le_innAutDerived _ (by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  show X ∈ innAutDerived (StatedProj (StatedSU n (p ^ f) K))
  rw [hXeq]
  exact mul_mem (inv_mem hcomm) (inner_le_innAutDerived _ hS)

end CFSG.LieType.SemisimpleCentralizers.HeldLang
