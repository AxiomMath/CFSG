module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthTrans
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.K159 CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

theorem i167COrth_innerImage_fixed {S T : Type} [Group S] [Group T] (e : S ≃* T) {p : ℕ}
    (hZ : Subgroup.center S = ⊥) {Bb : Subgroup (MulAut S)} (hBb : IsElemAbelian p Bb)
    {β : MulAut S} (hβ : β ∈ Bb) : ∀ a ∈ COrthInnerImage e Bb, (MulAut.congr e β) a = a := by
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  haveI : IsMulCommutative Bb := hBb.1
  intro a ha
  obtain ⟨s, hs, hes⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_comap] at hs
  have hval : β * MulAut.conj s = MulAut.conj s * β :=
    congrArg Subtype.val (mul_comm' (⟨β, hβ⟩ : Bb) ⟨MulAut.conj s, hs⟩)
  have hconj : (MulAut.conj (β s) : MulAut S) = MulAut.conj s := by
    ext x
    have hx := congrFun (congrArg DFunLike.coe hval) (β⁻¹ x)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply] at hx ⊢
    exact hx
  have hkey : β s = s := hinj hconj
  rw [← hes]
  change (MulAut.congr e β) (e s) = e s
  rw [show (MulAut.congr e β) (e s) = e (β s) by
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply]]
  rw [hkey]

theorem i167COrth_descent_max_outer {S T : Type} [Group S] [Group T] (e : S ≃* T) {p : ℕ}
    {Bb : Subgroup (MulAut S)} {β : MulAut S} (hβ : β ∈ Bb)
    (hcyc : ∀ β' ∈ Bb, ∃ (j : ℤ) (s : S), (MulAut.conj s : MulAut S) ∈ Bb ∧
      β' = MulAut.conj s * β ^ j)
    (hScp : ∀ s : S, (∀ β ∈ Bb, β s = s) → s ^ p = 1 → (MulAut.conj s : MulAut S) ∈ Bb) :
    ∀ y : T, (MulAut.congr e β) y = y → y ^ p = 1 →
      (∀ a ∈ COrthInnerImage e Bb, a * y = y * a) → y ∈ COrthInnerImage e Bb := by
  intro y hy hy_pow hcomm
  let s : S := e.symm y
  have hys : e s = y := e.apply_symm_apply y
  have hβs : β s = s := by
    apply e.injective
    have h1 : (MulAut.congr e β) (e s) = e (β s) := by
      simp [MulAut.congr_apply]
    have h3 : (MulAut.congr e β) (e s) = e s := by
      rw [hys]; exact hy
    rwa [h1] at h3
  have hs_pow : s ^ p = 1 := by
    apply e.injective
    rw [map_pow, map_one, hys]
    exact hy_pow
  have hcomm' : ∀ β' ∈ Bb, β' s = s := by
    intro β' hβ'
    obtain ⟨j, t, ht, hβ'eq⟩ := hcyc β' hβ'
    have het : e t ∈ COrthInnerImage e Bb := ⟨t, ht, rfl⟩
    have hts : t * s = s * t := by
      apply e.injective
      have h := hcomm (e t) het
      rw [← hys] at h
      simpa only [map_mul] using h
    have hbjs : (β ^ j) s = s := by
      have hstab : β ∈ MulAction.stabilizer (MulAut S) s := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hβs
      have h := zpow_mem hstab j
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
    rw [hβ'eq, MulAut.mul_apply, hbjs, MulAut.conj_apply, hts, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨s, hScp s hcomm' hs_pow, hys⟩

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem i167COrth_descent_cent_triv_aux1 {x t j : V ≃ₗ[F] V}
    (hx : OddOrderIsometry Q p x) (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htW : ∀ w ∈ fixedSpace x, t w = w) (hj : j ∈ supportedFixedDerived Q x) :
    t * j = j * t := by
  have hj' : j ∈ supportedOrthDerived Q (fixedSpace x) :=
    (CFSG.RankThree.PartOne.KCOrthogonalD4.supportedOrthDerived_fixedSpace hx).symm ▸ hj
  obtain ⟨j', -, hjW, hjP⟩ := mem_supportedOrthDerived.1 hj'
  exact commute_of_apply_eq hx.polarBilin_fixed_nondegenerate ht htW
    (fun y hy => by rw [hjW ⟨y, hy⟩]; exact (j' ⟨y, hy⟩).2) hjP

theorem i167COrth_descent_cent_triv (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Type} [Group S] (e : S ≃* ↥(orthDerived Q)) (hZ : Subgroup.center S = ⊥)
    {Bb : Subgroup (MulAut S)} {a₀ : S} {J : Subgroup S}
    (hCent : ∀ β ∈ Bb, (∀ j ∈ J, β j = j) →
      β ∈ Subgroup.zpowers (MulAut.conj a₀ : MulAut S))
    (hg : orderOf (e a₀) = p)
    (hJle : J.map e.toMonoidHom ≤
      (supportedFixedDerived Q ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    ∀ a ∈ COrthInnerImage e Bb,
      (∀ w ∈ fixedSpace ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V), (a : V ≃ₗ[F] V) w = w) →
        a ∈ Subgroup.zpowers (e a₀) := by
  intro a ha haW
  refine i167COrth_descent_cent e hZ hCent a ha ?_
  intro j hj
  have hx : OddOrderIsometry Q p ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ (e a₀) hg
  have hj' : (j : V ≃ₗ[F] V) ∈
      supportedFixedDerived Q ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
    Subgroup.mem_subgroupOf.1 (hJle hj)
  exact Subtype.ext (i167COrth_descent_cent_triv_aux1 hx (orthDerived_le_orthogonalGroup a.2) haW hj')

end Model

end CFSG.LocalAnalysis.GLTheoremA.I167

end
