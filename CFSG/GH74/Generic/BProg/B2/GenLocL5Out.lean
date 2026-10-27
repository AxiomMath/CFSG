module

public import CFSG.GH74.Generic.BProg.B2.GenLocL5Gen
public import CFSG.GH74.Generic.BProg.B2.PumpupTable
import CFSG.GH74.Generic.BProg.B2.GenLocL5Lin
import CFSG.GH74.Generic.BProg.B2.GenLocL5Uni
import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc
import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL5Out

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem stated_PSL {J : Type} [Group J] {n p f : ℕ} (h : LieModel J .PSL n p f) :
    StatedClassicalModel J .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem stated_PSU {J : Type} [Group J] {n p f : ℕ} (h : LieModel J .PSU n p f) :
    StatedClassicalModel J .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem out16_of_puL5 {J : Type} [Group J] (hJ : PuL5 J) : GenLocL5Gen.Out16 J := by
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hJ
  · exact GenLocL5Lin.out16_of_stated hp2 (stated_PSL hm)
  · exact GenLocL5Uni.out16_of_stated hp2 (stated_PSU hm)

theorem isSimpleGroup_of_puL5 {J : Type} [Group J] (hJ : PuL5 J) : IsSimpleGroup J := by
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hJ
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity J 5 p f (stated_PSL hm)).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity J 5 p f (stated_PSU hm)).2

theorem conj_injective_of_simple_perfect {J : Type} [Group J] (hs : IsSimpleGroup J)
    (hp : Group.IsPerfect J) : Function.Injective (MulAut.conj : J →* MulAut J) := by
  have hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
    intro z hz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hb | ht
    · have : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
      rw [hb] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      have hcomm : IsMulCommutative J :=
        ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top a) b).symm⟩⟩
      exact Group.IsPerfect.not_isMulCommutative J hcomm
  exact GenLocBasic.conj_injective_of_center_trivial hZ

@[expose] def GenInner (J : Type) [Group J] : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A →
    α.range ≤ (MulAut.conj : J →* MulAut J).range → gammaAct α = ⊤

theorem GenInner.of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (h : GenInner J) :
    GenInner J' := by
  intro A _ _ α' hA hin
  let α : A →* MulAut J := (MulAut.congr e.symm).toMonoidHom.comp α'
  have hc : ∀ a x, α' a (e x) = e (α a x) := by
    intro a x
    simp [α, MulAut.congr_apply]
  have hin' : α.range ≤ (MulAut.conj : J →* MulAut J).range := by
    rintro _ ⟨a, rfl⟩
    have h1 : α' a ∈ (MulAut.conj : J' →* MulAut J').range := hin ⟨a, rfl⟩
    have h2 := Subgroup.mem_map_of_mem (MulAut.congr e.symm).toMonoidHom h1
    rwa [GenLocBasic.map_congr_inn e.symm] at h2
  rw [GenLocBasic.gammaAct_map_equiv e α α' hc, h A α hA hin',
    Subgroup.map_top_of_surjective _ e.surjective]

theorem genInner_projectiveSL {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : GenInner (LinearFlag.projectiveSL 5 F) := by
  have hK2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  let e := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F
  have hs0 := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 5) (by norm_num)
    (Or.inl (by norm_num))).2.1
  have hs : IsSimpleGroup (LinearFlag.projectiveSL 5 F) := e.symm.isSimpleGroup
  have hp0 := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 5) (by norm_num)
    (Or.inl (by norm_num))
  have hperf : Group.IsPerfect (LinearFlag.projectiveSL 5 F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hinj := conj_injective_of_simple_perfect hs hperf
  intro A _ _ α hA hin
  exact gammaAct_projectiveSL_of_inner_odd' (by decide) hK2 hinj hA.1 α fun a => hin ⟨a, rfl⟩

theorem genInner_statedSU {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) : GenInner (StatedProj (StatedSU 5 (p ^ f) K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hnq : ((5 : ℕ), p ^ f) ≠ (3, 2) := fun h => by simp at h
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 5 (by norm_num) hnq
  have hP : Group.IsPerfect (StatedSU 5 (p ^ f) K) := by
    have h := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (n := 5)
      (by norm_num) fun h3 => by omega
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 5] at h
    exact h
  have hperf : Group.IsPerfect (StatedProj (StatedSU 5 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hinj := conj_injective_of_simple_perfect hs hperf
  intro A _ _ α hA hin
  exact gammaAct_projectiveSU_of_inner_odd' hp hp2 hK (by decide) hinj hA.1 α fun a => hin ⟨a, rfl⟩

theorem genInner_of_puL5 {J : Type} [Group J] (hJ : PuL5 J) : GenInner J := by
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hJ
  · obtain ⟨⟨hprime, hf', -⟩, F, _, _, hF, ⟨e⟩⟩ := stated_PSL hm
    let ψ : J ≃* LinearFlag.projectiveSL 5 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
    exact GenInner.of_mulEquiv ψ.symm (genInner_projectiveSL hprime hp2 hF)
  · obtain ⟨⟨hprime, hf', -⟩, K, _, _, hK, ⟨e⟩⟩ := stated_PSU hm
    exact GenInner.of_mulEquiv e.symm (genInner_statedSU hprime hp2 hK)

end CFSG.GH74.Generic.BProg.B2.GenLocL5Out


