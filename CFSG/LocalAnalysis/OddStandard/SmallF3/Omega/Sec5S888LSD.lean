module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Ord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem l515S_ctrQ_dvd {E K : Subgroup G} {u d : G} (hE : IsQuasisimple E)
    (hK : IsComponentIn K (centralizer ({d} : Set G))) (hu : u ∈ centralizer ({d} : Set G))
    (hle : E ≤ K ⊔ CFSG.conjugate K u) : ctrQ E ∣ ctrQ K := by
  by_cases hKu : CFSG.conjugate K u = K
  · rw [hKu, sup_idem] at hle
    exact ctrQ_dvd_of_le hle
  · have hKc : IsComponentIn (CFSG.conjugate K u) (centralizer ({d} : Set G)) :=
      hK.conjugate hu
    have hcomm : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K u, a * b = b * a :=
      hK.commute_of_ne hKc (Ne.symm hKu)
    rcases ctrQ_dvd_of_le_sup_of_commute hE hcomm hle with hEK' | ⟨hdvd, -⟩
    · rw [← ctrQ_conjugate K u]
      exact ctrQ_dvd_of_le hEK'
    · exact hdvd

theorem l515S_m3 (h36 : Asc82Lemma36) {t₀ : G} {L₀ : Subgroup G} (S : Sec3SettingLB G t₀ L₀)
    {u d : G} (hu : orderOf u = 2) (hd : orderOf d = 2) (hud : u * d = d * u)
    {E : Subgroup G} (hE : IsComponentIn E (centralizer ({u, d} : Set G)))
    (hEm : LieModel ↥E .PSU 3 3 1) :
    ∃ I : Subgroup G, IsComponentIn I (centralizer ({d} : Set G)) ∧ InFStar I ∧
      (InF I ∨ IsL3Eps3 I) ∧ E ≤ I ∧
      ∀ J : Subgroup G, IsComponentIn J (centralizer ({d} : Set G)) → InFStar J → J = I := by
  obtain ⟨K, hK, hle⟩ := S.lBalance u d hu hd hud E hE
  have hEF : InFStar E := l515S_inFStar_of_u33 hE hEm
  have hKF : InFStar K := S.a2 u d hu hd hud E K hE hK hle hEF
  have hudC : u ∈ centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hud
  have hdvd : 6048 ∣ ctrQ K := by
    have := l515S_ctrQ_dvd hE.isQuasisimple hK hudC hle
    rwa [l515S_ctrQ_of_u33 hEm] at this
  have hpk : InF K ∨ IsL3Eps3 K := by
    by_contra hnot
    push Not at hnot
    have := ctrQ_mem_of_not_pocketed hKF hnot.1 hnot.2
    omega
  have huniq := (h36 G t₀ L₀ S d K hd hK hpk).2
  have hKu : CFSG.conjugate K u = K := huniq _ (hK.conjugate hudC) (hKF.conjugate u)
  refine ⟨K, hK, hKF, hpk, ?_, huniq⟩
  rw [hKu, sup_idem] at hle
  exact hle

end CFSG.OddStandard.SmallF3.Omega
