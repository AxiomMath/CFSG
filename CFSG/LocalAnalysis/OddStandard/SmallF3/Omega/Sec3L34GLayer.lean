module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L311Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIII

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] noncomputable def fstarLayer (y : G) : Subgroup G :=
  ⨆ (J : Subgroup G) (_ : IsComponentIn J (centralizer ({y} : Set G)) ∧ InFStar J), J

theorem le_fstarLayer {y : G} {J : Subgroup G} (hJ : IsComponentIn J (centralizer ({y} : Set G)))
    (hJF : InFStar J) : J ≤ fstarLayer y :=
  le_iSup₂_of_le J ⟨hJ, hJF⟩ le_rfl

theorem fstarLayer_conj {y h : G} (hh : h ∈ centralizer ({y} : Set G)) {e : G}
    (he : e ∈ fstarLayer y) : h * e * h⁻¹ ∈ fstarLayer y := by
  have hle : fstarLayer y ≤ (fstarLayer y).comap (MulAut.conj h).toMonoidHom := by
    refine iSup₂_le fun J hJ => ?_
    intro j hj
    have hJ' : IsComponentIn (CFSG.conjugate J h⁻¹) (centralizer ({y} : Set G)) :=
      hJ.1.conjugate (Subgroup.inv_mem _ hh)
    have hmem : h * j * h⁻¹ ∈ CFSG.conjugate J h⁻¹ := by
      rw [conjugate_inv_eq_map_conj]
      exact ⟨j, hj, by simp [MulAut.conj_apply]⟩
    exact le_fstarLayer hJ' (hJ.2.conjugate h⁻¹) hmem
  simpa [MulAut.conj_apply] using hle he

theorem sec3_pocket_comm_fstarLayer (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hS : Asc82SchurU43) [Finite G] {t : G} {L : Subgroup G} (hSet : Sec3SettingLB G t L)
    {x y : G} {X K : Subgroup G} (hD : Sec3PocketData x X y K) :
    ⁅K, fstarLayer y⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun J hJ => ?_
  have hData : Sec3L34Data x X y K y J := ⟨hD, hD.involution_y,
    ⟨1, Subgroup.one_mem _, (one_mul y).symm⟩, hJ.1, hJ.2⟩
  rcases asc82Lemma34a_of_inputs hT2 hC1 G t L hSet x X y K y J hD hD.involution_y
      ⟨1, Subgroup.one_mem _, (one_mul y).symm⟩ hJ.1 hJ.2 with hKJ | hQJ
  · rw [Subgroup.commutator_comm] at hKJ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKJ
  · exact (l34g_false_of_pCore_le_component asc82NoQ8InL2_holds
      asc82OddCoreCentralizerQ8_holds hS hD hJ.1 hJ.2 hQJ).elim

theorem sec3_pocket_not_mem_fstarLayer (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hS : Asc82SchurU43) (hCor : Asc82CorIII) [Finite G] {t : G} {L : Subgroup G}
    (hSet : Sec3SettingLB G t L) {v y : G} {D K' : Subgroup G}
    (hD : Sec3PocketData v D y K') : v ∉ fstarLayer y ⊔ zpowers y := by
  intro hv
  obtain ⟨hyK, hKle, hKsub, hKSL⟩ := hD.pocket
  have hcomm := sec3_pocket_comm_fstarLayer hT2 hC1 hS hSet hD
  have hKC : K' ≤ centralizer ({y} : Set G) ⊓ centralizer (fstarLayer y : Set G) :=
    le_inf (hKle.trans inf_le_right) (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hCv : centralizer ({y} : Set G) ⊓ centralizer (fstarLayer y : Set G) ≤
      centralizer ({v} : Set G) ⊓ centralizer ({y} : Set G) := by
    refine le_inf (fun c hc => ?_) inf_le_left
    have hZ : fstarLayer y ⊔ zpowers y ≤ centralizer ({c} : Set G) := by
      refine sup_le (fun e he => ?_) ?_
      · exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
          rw [Set.mem_singleton_iff.mp hg]
          exact (Subgroup.mem_centralizer_iff.mp hc.2 e he).symm
      · refine (Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
        rw [Set.mem_singleton_iff.mp hg]
        exact (Subgroup.mem_centralizer_iff.mp hc.1 y rfl).symm
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff.mp hg]
      exact (Subgroup.mem_centralizer_iff.mp (hZ hv) c rfl).symm
  have hsubC := isSubnormal_subgroupOf_of_le hCv hKsub
  have hCnorm : ((centralizer ({y} : Set G) ⊓ centralizer (fstarLayer y : Set G)).subgroupOf
      (centralizer ({y} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left, Subgroup.le_normalizer_iff]
    intro h hh c hc
    refine ⟨(centralizer ({y} : Set G)).mul_mem
      ((centralizer ({y} : Set G)).mul_mem hh hc.1) ((centralizer ({y} : Set G)).inv_mem hh),
      Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    have he' : h⁻¹ * e * h⁻¹⁻¹ ∈ fstarLayer y :=
      fstarLayer_conj ((centralizer ({y} : Set G)).inv_mem hh) he
    have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ he'
    simp only [inv_inv] at hc'
    calc e * (h * c * h⁻¹) = h * ((h⁻¹ * e * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * e * h)) * h⁻¹ := by rw [hc']
      _ = h * c * h⁻¹ * e := by group
  have hKH := isSubnormal_subgroupOf_of_normal hKC inf_le_left hsubC hCnorm
  have hpocket : Sl23PocketIn (⊤ : Subgroup G) y K' := by
    refine ⟨hyK, ?_, ?_, hKSL⟩
    · rw [top_inf_eq]
      exact hKle.trans inf_le_right
    · rw [top_inf_eq]
      exact hKH
  exact hCor G t L hSet y ⟨hD.involution_y, K', hpocket⟩

end CFSG.OddStandard.SmallF3.Omega
