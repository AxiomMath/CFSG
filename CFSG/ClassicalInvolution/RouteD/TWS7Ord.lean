module

public import CFSG.ClassicalInvolution.RouteD.TWS6D4MF
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.Asc77.AscT8ZA1
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Central

variable {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
  {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}

theorem exists_central_involution (c : TWS6.SpinCtx8 t Q D) {R : Subgroup (spinGroup Q)}
    (hR : R ∈ fundamentalSubgroups t D) :
    ∃ x ∈ R, x ≠ 1 ∧ (∀ r ∈ R, x * r = r * x) ∧
      ∃ i : (ι → F) ≃ₗ[F] (ι → F), IsFundamental Q (R.map (spinAction Q)) i ∧
        spinAction Q x = i := by
  obtain ⟨i, hi⟩ := c.hcorr R hR
  obtain ⟨x, hx, hxi⟩ := hi.mem
  refine ⟨x, hx, ?_, ?_, i, hi, hxi⟩
  · intro h
    rw [h, map_one] at hxi
    exact hi.ne_one c.hodd hxi.symm
  · intro r hr
    have hcomm : i * spinAction Q r = spinAction Q r * i :=
      Subgroup.mem_centralizer_singleton_iff.mp (hi.le_centralizer ⟨r, hr, rfl⟩) |>.symm
    have h1 : x * r * (r * x)⁻¹ = 1 := by
      refine c.hinj hR _ (R.mul_mem (R.mul_mem hx hr) (R.inv_mem (R.mul_mem hr hx))) ?_
      rw [map_mul, map_mul, map_inv, map_mul, hxi, hcomm, mul_inv_cancel]
    exact mul_inv_eq_one.mp h1

end Central

section Ord

variable {p f : ℕ} [Fact p.Prime]


theorem exists_ordinary_pair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {A B : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (hA : A ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hB : B ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)))
    (hne : A ≠ B) (hc : Commutes A B) :
    ∃ (σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)))
      (fr : OFrame (quadPlus 4 (GaloisField p f))),
      PreservesFund p f σ ∧ PreservesFund p f σ.symm ∧
      (A.map σ.toMonoidHom).map (spinAction (quadPlus 4 (GaloisField p f))) = fr.La.range ∧
      (B.map σ.toMonoidHom).map (spinAction (quadPlus 4 (GaloisField p f))) =
        fr.swap.La.range := by
  classical
  have hf1 : 1 ≤ f := one_le_of_five_le_pow hq
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf1, le_refl 4⟩
  have c := TWS6.spinCtx8_plus hp2 hq hadm
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) := c.perfect
  obtain ⟨x, hxA, hx1, hcx, i, hi, hθx⟩ := exists_central_involution c hA
  obtain ⟨x', hxB, hx'1, hcx', j, hj, hθx'⟩ := exists_central_involution c hB
  have hk : Commutes (A.map (spinAction (quadPlus 4 (GaloisField p f))))
      (B.map (spinAction (quadPlus 4 (GaloisField p f)))) :=
    commutes_map_of_commutes _ hc
  have hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    obtain ⟨μ, hμ⟩ := Asc77.T8ZZ.fund_prod_scalar c.hodd c.hV hi hj hk
    have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj.mul_self
    refine mem_center_of_commutators_central fun s => ker_spinAction_le_center _ ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    have hscal : spinAction (quadPlus 4 (GaloisField p f)) (x * x'⁻¹) ∈
        scalars (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) :=
      mem_scalars.mpr ⟨μ, fun v => by rw [map_mul, map_inv, hθx, hθx', hjinv]; exact hμ v⟩
    exact commute_of_mem_scalars hscal _
  have hd : TwinDatumOn .POmegaPlus ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ A B x x' :=
    { mem := hA, mem' := hB, ne := hne, comm := hc, hx := hxA, hx' := hxB, cx := hcx,
      cx' := hcx', nx := hx1, nx' := hx'1, same := hsame }
  obtain ⟨σ, hσ, hσ', hord⟩ := TWS6.exists_ordinary_datum hp2 hq hadm hd
  have hd₁ := TWS6.map_datum_equiv hd σ hσ
  obtain ⟨F₁, h1, h2, -, -⟩ := swap_of_twin_pair_ord c.hodd (c.hperf _ hd₁.mem)
    (c.hperf _ hd₁.mem') (c.hcorr _ hd₁.mem) (c.hcorr _ hd₁.mem') (c.hinj hd₁.mem)
    (c.hinj hd₁.mem') hd₁.ne hd₁.hx (c.sq_eq_one hd₁.mem hd₁.hx hd₁.cx) hd₁.nx hd₁.hx'
    (c.sq_eq_one hd₁.mem' hd₁.hx' hd₁.cx') hd₁.nx' hord
  exact ⟨σ, F₁, hσ, hσ', h1, h2⟩

end Ord

end CFSG.ClassicalInvolution.RouteD.TWS7
