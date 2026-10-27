module

public import CFSG.LargeExtraspecial.S14NQSixPre
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S14C13B2Weak
public import CFSG.LargeExtraspecial.S14C13Conj
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

section Comm

variable {O : Type*} [Group O] {X : Subgroup O} {t : O} {N : Subgroup O}

theorem WeakSetting.comm_of_fix (W : WeakSetting X t N) {α a' n : O} (hαt : α * t = t * α)
    (ha'N : a' ∈ N) (hnN : n ∈ N) (hαnN : α * n * α⁻¹ ∈ N)
    (hfix : (α * a' * α⁻¹)⁻¹ * a' ∈ zpowers t) :
    a' * (α * n * α⁻¹ * n⁻¹) = (α * n * α⁻¹ * n⁻¹) * a' := by
  set s := (α * a' * α⁻¹)⁻¹ * a' with hs
  have hsN : s ∈ N := (zpowers_le.mpr W.t_mem_N) hfix
  have hαs : α⁻¹ * s * α = s := by
    rcases eq_one_or_eq_of_mem_zpowers W.tt hfix with h | h
    · rw [h]; group
    · rw [h]
      calc α⁻¹ * t * α = α⁻¹ * (t * α) := by group
        _ = α⁻¹ * (α * t) := by rw [hαt]
        _ = t := by group
  have h1 : α⁻¹ * a' * α = a' * s := by
    calc α⁻¹ * a' * α = α⁻¹ * ((α * a' * α⁻¹) * s) * α := by rw [hs]; group
      _ = a' * (α⁻¹ * s * α) := by group
      _ = a' * s := by rw [hαs]
  have hsn : s * n * s⁻¹ * n⁻¹ = 1 :=
    (comm_eq_one_iff s n).mpr (W.zpowers_comm hfix hnN)
  have h2 : a' * (α * n * α⁻¹) * a'⁻¹ * (α * n * α⁻¹)⁻¹ = a' * n * a'⁻¹ * n⁻¹ := by
    have e : a' * (α * n * α⁻¹) * a'⁻¹ * (α * n * α⁻¹)⁻¹ =
        α * ((α⁻¹ * a' * α) * n * (α⁻¹ * a' * α)⁻¹ * n⁻¹) * α⁻¹ := by group
    rw [e, h1, W.comm_mul_left ha'N hsN hnN, hsn, mul_one]
    rcases W.comm_eq ha'N hnN with h | h <;> rw [h]
    · group
    · calc α * t * α⁻¹ = t * α * α⁻¹ := by rw [hαt]
        _ = t := by group
  have h3 := W.comm_mul_right ha'N hnN (inv_mem hnN)
  simp only [mul_inv_cancel, mul_one, inv_one] at h3
  rw [← comm_eq_one_iff, W.comm_mul_right ha'N hαnN (inv_mem hnN), h2]
  exact h3.symm

end Comm

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section A

variable {t : S.O} [NQHyp S g t]

theorem cLin_sub_one_mk {α : S.O} (hα : α ∈ Ct S t) (n : Nbar S g t) :
    (cLin (g := g) hα - 1) (nqMk n) = nqMk (cConj hα n) - nqMk n :=
  rfl

theorem conj_inv_mul_mem_of_ker {α : S.O} (hα : α ∈ Ct S t) {n : Nbar S g t}
    (h : (cLin (g := g) hα - 1) (nqMk n) = 0) :
    (α * n * α⁻¹)⁻¹ * n ∈ zpowers t :=
  (nqMk_eq_iff _ _).mp (sub_eq_zero.mp ((cLin_sub_one_mk hα n).symm.trans h))

theorem conj_inv_mul_mem_of_eq {α : S.O} (hα : α ∈ Ct S t) {n m : Nbar S g t}
    (h : (cLin (g := g) hα - 1) (nqMk n) = nqMk m) :
    (α * n * α⁻¹)⁻¹ * (m * n) ∈ zpowers t :=
  (nqMk_eq_iff _ _).mp ((sub_eq_iff_eq_add.mp ((cLin_sub_one_mk hα n).symm.trans h)).trans
    (nqMk_mul m n).symm)

theorem comm_of_mem_nqPre_range (W : WeakSetting S.Mbar t (Nbar S g t)) {α : S.O}
    (hα : α ∈ Ct S t)
    (hrk : LinearMap.range (cLin (g := g) hα - 1) = LinearMap.ker (cLin (g := g) hα - 1))
    {a a' : S.O} (ha : a ∈ nqPre S g t (LinearMap.range (cLin (g := g) hα - 1)))
    (ha' : a' ∈ nqPre S g t (LinearMap.range (cLin (g := g) hα - 1))) : a * a' = a' * a := by
  have haQ : g * S.z * g⁻¹ ∈ S.QG := NQHyp.conj_mem (S := S) (g := g) (t := t)
  have hαt : α * t = t * α := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hα).2
  obtain ⟨haN, w, hw⟩ := ha
  obtain ⟨ha'N, ha'R⟩ := ha'
  have hker' : nqMk (⟨a', ha'N⟩ : Nbar S g t) ∈ LinearMap.ker (cLin (g := g) hα - 1) :=
    hrk ▸ ha'R
  have hker := conj_inv_mul_mem_of_ker hα (LinearMap.mem_ker.mp hker')
  have hsw := nqMk_surjective w
  obtain ⟨n, rfl⟩ := hsw
  have hw' := conj_inv_mul_mem_of_eq hα hw
  have hαnN : α * n * α⁻¹ ∈ Nbar S g t := conj_mem_Nbar_of_mem_Ct haQ hα n.2
  have hc := W.comm_of_fix hαt ha'N n.2 hαnN hker
  have hnt : (n : S.O) * t = t * n := W.N_comm _ n.2
  have hs : (α * n * α⁻¹ * (n : S.O)⁻¹)⁻¹ * a ∈ zpowers t := by
    have e : (α * n * α⁻¹ * (n : S.O)⁻¹)⁻¹ * a =
        (n : S.O) * ((α * n * α⁻¹)⁻¹ * (a * n)) * (n : S.O)⁻¹ := by group
    rw [e]
    exact (conj_mem_zpowers_iff hnt).mpr hw'
  have hsc := W.zpowers_comm hs ha'N
  calc a * a' = (α * n * α⁻¹ * (n : S.O)⁻¹) *
        (((α * n * α⁻¹ * (n : S.O)⁻¹)⁻¹ * a) * a') := by group
    _ = (α * n * α⁻¹ * (n : S.O)⁻¹) * (a' * ((α * n * α⁻¹ * (n : S.O)⁻¹)⁻¹ * a)) := by
        rw [hsc]
    _ = ((α * n * α⁻¹ * (n : S.O)⁻¹) * a') * (α * n * α⁻¹ * (n : S.O)⁻¹)⁻¹ * a := by group
    _ = (a' * (α * n * α⁻¹ * (n : S.O)⁻¹)) * (α * n * α⁻¹ * (n : S.O)⁻¹)⁻¹ * a := by
        rw [← hc]
    _ = a' * a := by group

theorem conj_mem_nqPre_range {ψ : Module.End (ZMod 2) (NQ S g t)}
    (hψc : ∀ (c : S.O) (hc : c ∈ Ct S t), cLin (g := g) hc * ψ = ψ * cLin (g := g) hc)
    {c a : S.O} (hc : c ∈ Ct S t) (ha : a ∈ nqPre S g t (LinearMap.range ψ)) :
    c * a * c⁻¹ ∈ nqPre S g t (LinearMap.range ψ) := by
  have haQ : g * S.z * g⁻¹ ∈ S.QG := NQHyp.conj_mem (S := S) (g := g) (t := t)
  obtain ⟨haN, w, hw⟩ := ha
  have h1 : cLin (g := g) hc (ψ w) = ψ (cLin (g := g) hc w) := LinearMap.congr_fun (hψc c hc) w
  refine ⟨conj_mem_Nbar_of_mem_Ct haQ hc haN, cLin (g := g) hc w, ?_⟩
  exact h1.symm.trans (congrArg (cLin (g := g) hc) hw)

end A

end CFSG.LargeExtraspecial.S14
