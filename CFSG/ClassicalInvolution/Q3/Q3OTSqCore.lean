module

public import CFSG.ClassicalInvolution.Q3.Q3OTBase
public import CFSG.ClassicalInvolution.Q3.Q3OTInn
public import CFSG.ClassicalInvolution.Q3.Q3OTDict
public import CFSG.ClassicalInvolution.Q3.Q3OTCplx
public import CFSG.ClassicalInvolution.Asc77.AscT7OJ
public import CFSG.ClassicalInvolution.Asc77.AscT7OD
public import CFSG.ClassicalInvolution.Asc77.AscT7OF
public import CFSG.ClassicalInvolution.Asc77.AscT7OI

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.ModelFacts.Orth15.T7O
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.G2D4Models.Twin (LiftSimFr)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Core

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem alphaOf_sq_core (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q)
    (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1) (hV : 7 ≤ Module.finrank F (ι → F))
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q)
    {H : Type} [Group H] [Finite H] (L : Subgroup H) {θ : spinGroup Q →* ↥L}
    (hθs : Function.Surjective θ) (hθk : θ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSimFr Q θ) (fr : OFrame Q) {kk x₀ : spinGroup Q}
    (hkk : spinAction Q kk ∈ fr.La.range) (hx₀ : spinAction Q x₀ = fr.La (-1))
    (hx₀2 : x₀ * x₀ = 1) (hkx : θ kk * θ kk = θ x₀) (vv : ↥(inducedAutOn L))
    (hv : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      vv * innL L (θ s) = innL L (θ s) * vv)
    (hvv : vv * vv = innL L (θ x₀)) (hb1 : innL L (θ x₀) ≠ 1)
    (hb0 : CFSG.Assembly.Dichotomy.involutionOddCore (innL L (θ x₀)) = ⊥) :
    alphaOf (Subgroup.closure ({innL L (θ kk) * vv, innL L (θ x₀)} :
      Set ↥(inducedAutOn L))) = ⊥ := by
  classical
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hZ3 := center_no_three hF3 hrange hZ hker2
  have hdim6 : 6 ≤ Module.finrank F (ι → F) := by omega
  have hN1 : ∀ {g : (ι → F) ≃ₗ[F] (ι → F)}
      (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q), (∀ u, g (g u) = -u) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hg))) = ⊥ :=
    fun hg hg2 => oddCoreIn_fixed_eq_bot_of_cplx hF3 hQ hdim6 hOE hg hg2
  have hα : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ g : ↥L, (vv : MulAut ↥L) (θ s * g * (θ s)⁻¹) = θ s * (vv : MulAut ↥L) g * (θ s)⁻¹ := by
    intro s hs
    refine pointwise_of_comm_conj (vv : MulAut ↥L) (θ s) ?_
    have h := congrArg Subtype.val (hv s hs)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, innL_coe] at h
  obtain ⟨αK, w, hθα, hwO, hwspan, hθw⟩ :=
    exists_isometry_abs hodd hF3 hrange hZ3 fr hθs hθk (vv : MulAut ↥L) hlift hα
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwO
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange αK hy_mem hθw
  have hvvM : (vv : MulAut ↥L) * (vv : MulAut ↥L) = MulAut.conj (θ x₀) := by
    have h := congrArg Subtype.val hvv
    rwa [Subgroup.coe_mul, innL_coe] at h
  have hconj : MulAut.conj (θ ŷ) = MulAut.conj (θ x₀) := by
    rw [← hvvM]
    refine MulEquiv.ext fun g => ?_
    obtain ⟨s, rfl⟩ := hθs g
    rw [MulAut.conj_apply, MulAut.mul_apply, ← hθα, ← hθα, hαα, map_mul, map_mul, map_inv]
  have hmk := (conj_eq_conj_iff_mk _ _).mp hconj
  have hker1 : ŷ⁻¹ * x₀ ∈ Subgroup.center (spinGroup Q) := by
    refine ker_quot_le_center θ hθs hθk ?_
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_inv]
    exact (QuotientGroup.eq_one_iff _).mpr (QuotientGroup.eq.mp hmk)
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hker1
  have hww : ∀ u, w (w u) = -(fr.La (-1) u) := by
    obtain ⟨z₀, hz₀, hz₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (span_ne_bot fr)
    have hLz₀ : fr.La (-1) z₀ = -z₀ := La_neg_one_of_mem_span fr hz₀
    have hwz : w z₀ = z₀ := hwspan z₀ hz₀
    have hyz : (w * w) z₀ = z₀ := by rw [LinearEquiv.mul_apply, hwz, hwz]
    have hsa : spinAction Q (ŷ⁻¹ * x₀) = (w * w)⁻¹ * fr.La (-1) := by
      rw [map_mul, map_inv, hŷ, hx₀]
    have hμ1 : μ = -1 := by
      have h1 := hμ z₀
      rw [hsa, LinearEquiv.mul_apply, hLz₀, map_neg] at h1
      have h2 : (w * w)⁻¹ z₀ = z₀ := by
        apply (w * w).injective
        rw [LinearEquiv.apply_inv_apply', hyz]
      rw [h2] at h1
      have h3 : (μ + 1) • z₀ = 0 := by rw [add_smul, one_smul, ← h1, neg_add_cancel]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h3).resolve_right hz₀0)
    intro u
    have h1 := hμ u
    rw [hsa, LinearEquiv.mul_apply, hμ1, neg_one_smul] at h1
    have h2 : (w * w) ((w * w)⁻¹ (fr.La (-1) u)) = fr.La (-1) u :=
      LinearEquiv.apply_inv_apply' _ _
    rw [h1, map_neg] at h2
    exact (neg_eq_iff_eq_neg.mp h2).symm ▸ rfl
  have hkk' := hkk
  obtain ⟨a, ha⟩ := hkk
  have haa : a * a = -1 := by
    have hc : (kk * kk)⁻¹ * x₀ ∈ Subgroup.center (spinGroup Q) :=
      hθk (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hkx, inv_mul_cancel])
    obtain ⟨μ', hμ'⟩ := exists_smul_of_central hrange hZ hc
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (perp_ne_bot fr (by omega))
    have hsa' : spinAction Q ((kk * kk)⁻¹ * x₀) = (fr.La a * fr.La a)⁻¹ * fr.La (-1) := by
      rw [map_mul, map_inv, map_mul, ← ha, hx₀]
    have hLu : fr.La (-1) u = u := La_fix_perp fr (-1) hu
    have hLau : fr.La a u = u := La_fix_perp fr a hu
    have hμ'1 : μ' = 1 := by
      have h1 := hμ' u
      rw [hsa', LinearEquiv.mul_apply, hLu] at h1
      have h2 : (fr.La a * fr.La a)⁻¹ u = u := by
        apply (fr.La a * fr.La a).injective
        rw [LinearEquiv.apply_inv_apply', LinearEquiv.mul_apply, hLau, hLau]
      rw [h2] at h1
      have h3 : (μ' - 1) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu0)
    have hLaLa : fr.La a * fr.La a = fr.La (-1) := by
      refine LinearEquiv.ext fun u' => ?_
      have h1 := hμ' u'
      rw [hsa', LinearEquiv.mul_apply, hμ'1, one_smul] at h1
      calc (fr.La a * fr.La a) u'
          = (fr.La a * fr.La a) ((fr.La a * fr.La a)⁻¹ (fr.La (-1) u')) := by rw [h1]
        _ = fr.La (-1) u' := LinearEquiv.apply_inv_apply' _ _
    apply fr.La_injective
    rw [map_mul]
    exact hLaLa
  have hwLa := w_comm_La fr hwO hwspan
  set A : (ι → F) ≃ₗ[F] (ι → F) := fr.La a * w with hAdef
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (Frame.La_mem_orthogonalGroup fr a) hwO
  have hLL : ∀ u, fr.La (-1) (fr.La (-1) u) = u := fun u =>
    congrArg (fun m : (ι → F) ≃ₗ[F] (ι → F) => m u) fr.La_neg_one_mul_self
  have hLaa : ∀ u, fr.La a (fr.La a u) = fr.La (-1) u := fun u => by
    rw [← LinearEquiv.mul_apply, ← map_mul, haa]
  have hA2 : ∀ u, A (A u) = -u := by
    intro u
    have h1 : ∀ t, w (fr.La a t) = fr.La a (w t) := fun t =>
      (congrArg (fun m : (ι → F) ≃ₗ[F] (ι → F) => m t) (hwLa a)).symm
    simp only [hAdef, LinearEquiv.mul_apply]
    rw [h1, hLaa, hww, map_neg, hLL]
  have hAz : A * fr.La (-1) = fr.La (-1) * A := by
    calc A * fr.La (-1) = fr.La a * (w * fr.La (-1)) := by rw [hAdef, mul_assoc]
      _ = fr.La a * (fr.La (-1) * w) := by rw [← hwLa (-1)]
      _ = (fr.La a * fr.La (-1)) * w := by rw [mul_assoc]
      _ = (fr.La (-1) * fr.La a) * w := by rw [fr.La_neg_one_comm a]
      _ = fr.La (-1) * A := by rw [hAdef, mul_assoc]
  set A' : (ι → F) ≃ₗ[F] (ι → F) := fr.La (-1) * A with hA'def
  have hA'O : A' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (Frame.La_mem_orthogonalGroup fr (-1)) hAO
  have hA'2 : ∀ u, A' (A' u) = -u := by
    intro u
    have hc : ∀ t, fr.La (-1) (A t) = A (fr.La (-1) t) := fun t =>
      congrArg (fun m : (ι → F) ≃ₗ[F] (ι → F) => m t) hAz.symm
    simp only [hA'def, LinearEquiv.mul_apply]
    rw [hc, hLL, hA2]
  set y : ↥(inducedAutOn L) := innL L (θ kk) * vv with hydef
  set b : ↥(inducedAutOn L) := innL L (θ x₀) with hbdef
  have hyM : (y : MulAut ↥L) = MulAut.conj (θ kk) * (vv : MulAut ↥L) := by
    rw [hydef, Subgroup.coe_mul, innL_coe]
  have hbM : (b : MulAut ↥L) = MulAut.conj (θ x₀) := innL_coe L _
  have hsupLa : fr.La.range ≤ fr.La.range ⊔ fr.swap.La.range := le_sup_left
  have hvk : vv * innL L (θ kk) = innL L (θ kk) * vv := hv kk (hsupLa hkk')
  have hvx : vv * b = b * vv := hv x₀ (by rw [hx₀]; exact hsupLa ⟨-1, rfl⟩)
  have hcomm_kx : θ kk * θ x₀ = θ x₀ * θ kk := by rw [← hkx]; group
  have hbb : b * b = 1 := by
    rw [hbdef, ← map_mul (innL L), ← map_mul θ, hx₀2, map_one, map_one]
  have hyb : y * b = b * y := by
    have hik : innL L (θ kk) * b = b * innL L (θ kk) := by
      rw [hbdef, ← map_mul (innL L), ← map_mul (innL L), hcomm_kx]
    rw [hydef, mul_assoc, hvx, ← mul_assoc, hik, mul_assoc]
  have hy2 : y * y = 1 := by
    have h1 : innL L (θ kk) * innL L (θ kk) = b := by
      rw [hbdef, ← map_mul (innL L), hkx]
    calc y * y = innL L (θ kk) * (vv * innL L (θ kk)) * vv := by rw [hydef]; group
      _ = innL L (θ kk) * (innL L (θ kk) * vv) * vv := by rw [hvk]
      _ = (innL L (θ kk) * innL L (θ kk)) * (vv * vv) := by group
      _ = b * b := by rw [h1, hvv]
      _ = 1 := hbb
  set αy : MulAut (spinGroup Q) := MulAut.conj kk * αK with hαy
  have hαyapp : ∀ s, αy s = kk * αK s * kk⁻¹ := fun s => by
    rw [hαy, MulAut.mul_apply, MulAut.conj_apply]
  have hθαy : ∀ s, θ (αy s) = (y : MulAut ↥L) (θ s) := by
    intro s
    rw [hαyapp, map_mul, map_mul, map_inv, hθα, hyM, MulAut.mul_apply, MulAut.conj_apply]
  have hgαy : ∀ s, spinAction Q (αy s) = A * spinAction Q s * A⁻¹ := by
    intro s
    rw [hαyapp, map_mul, map_mul, map_inv, hθw, ← ha, hAdef, mul_inv_rev]
    group
  set αyb : MulAut (spinGroup Q) := MulAut.conj x₀ * αy with hαyb
  have hαybapp : ∀ s, αyb s = x₀ * αy s * x₀⁻¹ := fun s => by
    rw [hαyb, MulAut.mul_apply, MulAut.conj_apply]
  have hθαyb : ∀ s, θ (αyb s) = ((y * b : ↥(inducedAutOn L)) : MulAut ↥L) (θ s) := by
    intro s
    have h2 : ((y * b : ↥(inducedAutOn L)) : MulAut ↥L) = (b : MulAut ↥L) * (y : MulAut ↥L) := by
      rw [hyb]
      rfl
    rw [hαybapp, map_mul, map_mul, map_inv, hθαy, h2, hbM, MulAut.mul_apply, MulAut.conj_apply]
  have hgαyb : ∀ s, spinAction Q (αyb s) = A' * spinAction Q s * A'⁻¹ := by
    intro s
    rw [hαybapp, map_mul, map_mul, map_inv, hgαy, hx₀, hA'def]
    group
  have hfy : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥L (y : MulAut ↥L))) = ⊥ :=
    oddCoreIn_fixed_of_lift hrange hθs hθk (y : MulAut ↥L) αy hθαy hAO hgαy (hN1 hAO hA2)
  have hfyb : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥L
      ((y * b : ↥(inducedAutOn L)) : MulAut ↥L))) = ⊥ :=
    oddCoreIn_fixed_of_lift hrange hθs hθk _ αyb hθαyb hA'O hgαyb (hN1 hA'O hA'2)
  exact alphaOf_klein_outer_good3 L hy2 hbb hyb hb1 ⟨θ x₀, (innL_coe L _).symm⟩ hfy hfyb hb0

end Core

end CFSG.ClassicalInvolution.Q3.Q3OT
