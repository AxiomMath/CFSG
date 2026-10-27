module

public import CFSG.LargeExtraspecial.S14C13B1Defs
public import CFSG.LargeExtraspecial.S14C13Cent
public import CFSG.LargeExtraspecial.S14C13YHalf
public import CFSG.LargeExtraspecial.S14C13YConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem ybar_half8 (hCE : CentralExtInput.{0}) {t : S.O} (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) [NQHyp S g t] :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate)
      (hX : RmodN S g t = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
      (p p₁ : Vt S g t), LmodN S g t = pointRadical Q p ∧ Half8 (nqRep S g t hX) p p₁ := by
  have haQ := hSt.hyp4.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  obtain ⟨Q, hQ, hX, p, p₁, hdimV, hp0, hp, hp₁, hpp, hE, hcomp⟩ :=
    omega_data hCE hSt hocc hocc.1.1
  exact ⟨Q, hQ, hX, p, p₁, hE, hdimV,
    finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 16) hocc.2.2, hp0, hp, hp₁, hpp, hcomp⟩

theorem exists_ne_cLin_mul {t : S.O} [NQHyp S g t] (h7 : Concl14_7 S g t) {a b : S.O}
    (ha : a ∈ Ct S t) (hb : b ∈ Ct S t) (hab : a * b ∉ Nbar S g t)
    (hne : ∃ n ∈ Nbar S g t, n ∉ zpowers t) :
    ∃ v, cLin (g := g) ha (cLin (g := g) hb v) ≠ v := by
  by_contra hcon
  have hcon' : ∀ v, cLin (g := g) ha (cLin (g := g) hb v) = v := fun v => by
    by_contra hv
    exact hcon ⟨v, hv⟩
  refine hab (mem_Nbar_of_cLin_eq_smul h7 (mul_mem ha hb) hne (c := 1)
    (LinearMap.ext fun v => ?_))
  rw [cLin_mul_apply (g := g) ha hb, hcon', one_smul, LinearMap.id_apply]

theorem ybar_mem_Nbar (hCE : CentralExtInput.{0}) {t : S.O} (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (h7 : Concl14_7 S g t) {α β : S.O} (hα : α ∈ Ct S t) (hβ : β ∈ Ct S t)
    (hα2 : α * α ∈ Nbar S g t) (hβ2 : β * β ∈ Nbar S g t) (hαβ : α * β ∉ Nbar S g t)
    (hαβ3 : (α * β) ^ 3 ∈ Nbar S g t)
    (hαR : ∀ r ∈ Rbar S g t, α * r * α⁻¹ * r⁻¹ ∈ Nbar S g t ∧ β * r * β⁻¹ * r⁻¹ ∈ Nbar S g t)
    {z : S.O} (hz : z ∈ Ct S t) (hzR : ∀ r ∈ Rbar S g t, z * r * z⁻¹ * r⁻¹ ∈ Nbar S g t)
    (hzα : z * α * z⁻¹ * α⁻¹ ∈ Nbar S g t) (hzβ : z * β * z⁻¹ * β⁻¹ ∈ Nbar S g t) :
    z ∈ Nbar S g t := by
  have : NQHyp S g t := nqHyp_of_occurs hCE hSt hocc
  have haQ := hSt.hyp4.conj_mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hne := exists_mem_Nbar_not_mem_zpowers hext htN hSt.ne_one fun n hn =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)).symm
  obtain ⟨Q, hQ, hX, p, p₁, -, hH⟩ := ybar_half8 hCE hSt hocc
  have hid := hH.eq_id (A := cLin (g := g) hα) (B := cLin (g := g) hβ) (φ := cLin (g := g) hz)
    (cLin_comm_nqRep hα (fun r hr => (hαR r hr).1) hX)
    (cLin_comm_nqRep hβ (fun r hr => (hαR r hr).2) hX)
    (cLin_sq (g := g) hα hα2) (cLin_sq (g := g) hβ hβ2) (cLin_cube (g := g) hα hβ hαβ3)
    (exists_ne_cLin_mul h7 hα hβ hαβ hne) (cLin_comm_nqRep hz hzR hX)
    (cLin_comm_of_mem (g := g) hz hα hzα) (cLin_comm_of_mem (g := g) hz hβ hzβ)
    (fun a b hab => (cEquiv (g := g) hz).injective hab)
  refine mem_Nbar_of_cLin_eq_smul h7 hz hne (c := 1) (LinearMap.ext fun v => ?_)
  rw [hid v, one_smul, LinearMap.id_apply]

theorem ybar_inner (hCE : CentralExtInput.{0}) {t : S.O} (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (h7 : Concl14_7 S g t) {α β : S.O} (hα : α ∈ Ct S t) (hβ : β ∈ Ct S t)
    (hα2 : α * α ∈ Nbar S g t) (hβ2 : β * β ∈ Nbar S g t) (hαβ : α * β ∉ Nbar S g t)
    (hαβ3 : (α * β) ^ 3 ∈ Nbar S g t)
    (hαR : ∀ r ∈ Rbar S g t, α * r * α⁻¹ * r⁻¹ ∈ Nbar S g t ∧ β * r * β⁻¹ * r⁻¹ ∈ Nbar S g t)
    {y : Ct S t} (hyL : (y : S.O) ∈ normalizer (S.Lbar g : Set S.O))
    (hyα : (y : S.O) * α * (y : S.O)⁻¹ * α⁻¹ ∈ Nbar S g t) :
    ∃ r₀ : Rbar S g t, ∀ e : RmodN S g t,
      (autC hSt.hyp4.conj_mem y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
        resV hSt.hyp4.conj_mem t r₀ * e * (resV hSt.hyp4.conj_mem t r₀)⁻¹ := by
  have : NQHyp S g t := nqHyp_of_occurs hCE hSt hocc
  have haQ := hSt.hyp4.conj_mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hne := exists_mem_Nbar_not_mem_zpowers hext htN hSt.ne_one fun n hn =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)).symm
  obtain ⟨Q, hQ, hX, p, p₁, hE, hH⟩ := ybar_half8 hCE hSt hocc
  have hA1 := (Half8.exists_ne_of_sym3 (cLin_sq (g := g) hα hα2) (cLin_sq (g := g) hβ hβ2)
    (cLin_cube (g := g) hα hβ hαβ3) (exists_ne_cLin_mul h7 hα hβ hαβ hne)).1
  let θ : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ ≃*
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    ((MulEquiv.subgroupCongr hX).symm.trans (autC haQ y)).trans (MulEquiv.subgroupCongr hX)
  have hθL : ∀ w : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ,
      (w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical Q p ↔
        (θ w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical Q p := by
    intro w
    rw [← hE]
    exact (autC_mem_LmodN_iff haQ hyL ((MulEquiv.subgroupCongr hX).symm w)).symm
  have hτ : ∀ (w : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) (v : NQ S g t),
      cEquiv y.2 (nqRep S g t hX w v) = nqRep S g t hX (θ w) (cEquiv y.2 v) :=
    fun w v => cLin_nqRep_autC y hX w v
  obtain ⟨x, hx⟩ := hH.inner (cLin_comm_nqRep hα (fun r hr => (hαR r hr).1) hX)
    (cLin_sq (g := g) hα hα2) hA1 θ hθL (cEquiv (g := g) y.2) hτ
    (cLin_comm_of_mem (g := g) y.2 hα hyα)
  have he₀R : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hX]
    exact x.2
  obtain ⟨r₀, hr₀⟩ := exists_resV_eq haQ he₀R
  refine ⟨r₀, fun e => ?_⟩
  have h1 := congrArg Subtype.val (hx (MulEquiv.subgroupCongr hX e))
  rw [hr₀]
  simpa only [θ, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.subgroupCongr_apply] using h1

theorem ybar13Stmt_of (hCE : CentralExtInput.{0}) : Ybar13Stmt := by
  intro G _ _ _ S g t hSt hocc hext h7 _ α hα β hβ hα2 hβ2 hαβ hαβ3 hαR y hy hyα hyβ
  have haQ := hSt.hyp4.conj_mem
  obtain ⟨-, -, -, -, -, -, h6⟩ := case_of_occurs hocc
  obtain ⟨r, hr, hra⟩ := exists_mem_Rbar_apply_eq hCE hSt h6 hy
  have hrC : r ∈ Ct S t := Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar hr, Rbar_le_centralizer haQ hr⟩
  let y' : Ct S t := ⟨r⁻¹ * y, mul_mem (inv_mem hrC) hy⟩
  have hya : ((y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    show ((r⁻¹ * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = _
    rw [coe_mul_apply, hra, inv_apply_apply_O]
  have hyL : (y' : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) haQ hSt.hyp4.conj_ne
      (Subgroup.mem_inf.mp y'.2).1 (by simpa using hya)
    simpa using this
  have hy'α : (r⁻¹ * y) * α * (r⁻¹ * y)⁻¹ * α⁻¹ ∈ Nbar S g t :=
    comm_inv_mul_mem haQ hrC (hαR r hr).1 hyα
  have hy'β : (r⁻¹ * y) * β * (r⁻¹ * y)⁻¹ * β⁻¹ ∈ Nbar S g t :=
    comm_inv_mul_mem haQ hrC (hαR r hr).2 hyβ
  obtain ⟨r₀, hr₀⟩ := ybar_inner hCE hSt hocc hext h7 hα hβ hα2 hβ2 hαβ hαβ3 hαR hyL hy'α
  have hr₀C : (r₀ : S.O) ∈ Ct S t :=
    Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar r₀.2, Rbar_le_centralizer haQ r₀.2⟩
  have hz : (r₀ : S.O)⁻¹ * (r⁻¹ * y) ∈ Ct S t := mul_mem (inv_mem hr₀C) y'.2
  have hzN := ybar_mem_Nbar hCE hSt hocc hext h7 hα hβ hα2 hβ2 hαβ hαβ3 hαR hz
    (comm_mem_Nbar_of_autC_eq haQ y' r₀ hr₀) (comm_inv_mul_mem haQ hr₀C (hαR _ r₀.2).1 hy'α)
    (comm_inv_mul_mem haQ hr₀C (hαR _ r₀.2).2 hy'β)
  have e : y = r * ((r₀ : S.O) * ((r₀ : S.O)⁻¹ * (r⁻¹ * y))) := by group
  rw [e]
  exact mul_mem hr (mul_mem r₀.2 (Nbar_le_Rbar hzN))

end CFSG.LargeExtraspecial.S14
