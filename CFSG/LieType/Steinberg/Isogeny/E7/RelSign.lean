module

public import CFSG.LieType.Steinberg.Adjoint.CertE7
public import CFSG.LieType.Steinberg.Adjoint.Unipotent
public import CFSG.LieType.Chevalley.RootOps.All
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag}

namespace RootOperatorFamily'

variable (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid)
include hD

theorem D_one_eq_of_signs (δ : Root τ → ℤ) (hδs : ∀ j, δ (simpleRoot τ j) = 1)
    (hδr : ∀ i α, δ (simple τ i • α) = F.sign i α * D.rootSign α i * δ α) (α : Root τ)
    (R : Type) [CommRing R] : F.D R α 1 = (δ α : R) • D.rootOp R α := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    rw [show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) = simpleRoot τ j from rfl, hδs,
      Int.cast_one, one_smul, F.D_simple, xCoeff_one]
    exact (AdjData.rootOp_simple hD j).symm
  | @reflect i v hv ih =>
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot i ⟨v, hv⟩).symm
    rw [hs, hδr, F.D_simple_smul, pow_one, ih, mul_smul_comm, smul_mul_assoc, ← weylElt_inv,
      AdjData.rootOp_weyl hD, smul_smul, smul_smul, simple_smul_eq_sRoot]
    push_cast
    ring_nf

theorem relSign_eq_of_signs (δ : Root τ → ℤ) (hδs : ∀ j, δ (simpleRoot τ j) = 1)
    (hδr : ∀ i α, δ (simple τ i • α) = F.sign i α * D.rootSign α i * δ α) (α : Root τ) :
    relSign F hD α = δ α := by
  obtain ⟨a, b, hab⟩ := exists_D_one_apply_ne_zero F (R := ℤ) α
  have h1 := congrArg (fun f : Module.End ℤ (RootModule τ ℤ) => f (Finsupp.single b 1) a)
    (D_one_eq F hD α ℤ)
  have h2 := congrArg (fun f : Module.End ℤ (RootModule τ ℤ) => f (Finsupp.single b 1) a)
    (D_one_eq_of_signs F hD δ hδs hδr α ℤ)
  simp only [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul, Int.cast_id] at h1 h2
  have hne : D.rootOp ℤ α (Finsupp.single b 1) a ≠ 0 := fun h => hab (by rw [h1, h, mul_zero])
  exact mul_right_cancel₀ hne (h1.symm.trans h2)

end RootOperatorFamily'

@[expose] def e7RelSignBits : ℕ := 0x2ab338f1d1d8e63ce3a33a99aa500000

@[expose] def e7RelSign (a : ℕ) : ℤ := if e7RelSignBits / 2 ^ a % 2 = 1 then -1 else 1

@[expose] def e7RelSignCheck : Bool :=
  ((List.finRange (Tag.rank .E7)).all fun j => e7RelSign j == 1) &&
    (List.range 126).all fun a => (List.finRange (Tag.rank .E7)).all fun i =>
      e7RelSign ((Tag.E7).rootCertificate.image a i) ==
        signOf .E7 a i * e7AdjData.weylSign a i * e7RelSign a

theorem e7RelSignCheck_eq : e7RelSignCheck = true := by decide +kernel

theorem pos_eq_rootPos (α : Root τ) : pos α = rootPos α :=
  (pos_eq_iff (rootPos_lt α)).2 (root_rootPos α)

theorem relSign_e7 (α : Root .E7) :
    RootOperatorFamily'.relSign (rootOperatorFamily .E7) e7AdjData_valid α =
      e7RelSign (rootPos α) := by
  have h := e7RelSignCheck_eq
  simp only [e7RelSignCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    List.mem_range, beq_iff_eq, true_implies] at h
  refine RootOperatorFamily'.relSign_eq_of_signs _ e7AdjData_valid
    (fun α => e7RelSign (rootPos α)) (fun j => ?_) (fun i β => ?_) α
  · rw [rootPos_simpleRoot]
    exact h.1 j
  · have hβ : rootPos β < 126 := by
      have := rootPos_lt β
      rwa [Tag.rootCertificate_length] at this
    rw [rootPos_smul, h.2 _ hβ i, AdjData.rootSign, pos_eq_rootPos]
    rfl

end CFSG.LieType.Steinberg.Adjoint
