module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentBK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentOP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentOPM
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_iotaP_injective (S : FGSplit Q) (hW : 0 < Module.finrank (ZMod 3) S.W) :
    Function.Injective (fgIotaP S) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have h1 : toProj Q (S.extP b) = 1 :=
    projOrthToProjSim_injective (by rw [map_one]; exact hb)
  have hmem : S.extP b ∈ piGroup Q := (QuotientGroup.eq_one_iff _).mp h1
  rcases mem_piGroup_iff.mp hmem with h | h
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    have h2 := S.extP_P b p
    rw [h] at h2
    exact Subtype.ext (by simpa using h2.symm)
  · exfalso
    haveI : Nontrivial S.W := Module.finrank_pos_iff.mp hW
    obtain ⟨w, hw0⟩ := exists_ne (0 : S.W)
    have h2 := S.extP_W b w
    rw [h, coe_piOrth_apply] at h2
    have h3 : (2 : ZMod 3) • (w : V) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h2]
      exact neg_add_cancel _
    exact hw0 (Subtype.ext ((smul_eq_zero.mp h3).resolve_left (by decide)))

theorem fg_cent_range (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W)
    (hperf : Group.IsPerfect (omegaGroup S.nondegW)) {A : Subgroup (ProjSim Q)}
    (hA : ∀ γ ∈ A, ∀ a ∈ omegaGroup S.nondegW,
      projSimAct Q γ (toProj Q (S.extW a)) = toProj Q (S.extW a)) :
    A ≤ (fgIotaP S).range := by
  intro γ hγ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨b, hb⟩ := fg_bk S h3 hperf g (fun a ha => hA _ hγ a ha)
  exact ⟨b, hb.symm⟩

theorem fg_cent_equiv (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W)
    (hperf : Group.IsPerfect (omegaGroup S.nondegW)) {A : Subgroup (ProjSim Q)}
    (hA : ∀ γ ∈ A, ∀ a ∈ omegaGroup S.nondegW,
      projSimAct Q γ (toProj Q (S.extW a)) = toProj Q (S.extW a)) :
    Nonempty (↥(A.comap (fgIotaP S)) ≃* ↥A) := by
  have hinj := fg_iotaP_injective S (by omega)
  have hmap : (A.comap (fgIotaP S)).map (fgIotaP S) = A :=
    Subgroup.map_comap_eq_self (fg_cent_range S h3 hperf hA)
  exact ⟨(Subgroup.equivMapOfInjective _ (fgIotaP S) hinj).trans (MulEquiv.subgroupCongr hmap)⟩

theorem fg_det_of_simInOmegaStar (hQ : Q.Nondegenerate) (S : FGSplit Q)
    (hev : Even (Module.finrank (ZMod 3) V)) (b : OGroup (Q.restrict S.P))
    (hb : SimInOmegaStar hQ (fgIotaP S b)) :
    QuadraticMap.orthogonalDet (Q.restrict S.P) b = 1 := by
  obtain ⟨y, hy, hyb⟩ := hb
  have hy' : y = toProj Q (S.extP b) := projOrthToProjSim_injective hyb
  rw [hy', mem_omegaProj_iff hQ] at hy
  obtain ⟨g, hg, hgb⟩ := hy
  have hdetg : QuadraticMap.orthogonalDet Q g = 1 :=
    congrArg Prod.fst ((mem_omegaGroup_iff hQ).mp hg)
  rw [← S.det_extP b]
  rcases toProj_eq_or_eq_piOrth hgb with h | h
  · rw [← h]
    exact hdetg
  · rw [h, map_mul, orthogonalDet_piOrth, hev.neg_one_pow, one_mul] at hdetg
    exact hdetg

theorem fg_cent_dim_one (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W)
    (hperf : Group.IsPerfect (omegaGroup S.nondegW)) {A : Subgroup (ProjSim Q)}
    (hA : ∀ γ ∈ A, ∀ a ∈ omegaGroup S.nondegW,
      projSimAct Q γ (toProj Q (S.extW a)) = toProj Q (S.extW a))
    (hP : Module.finrank (ZMod 3) S.P = 1) : Nat.card A ≤ 2 := by
  obtain ⟨e⟩ := fg_cent_equiv S h3 hperf hA
  rw [← Nat.card_congr e.toEquiv]
  exact fg_card_le_two_of_dim_one S.nondegP hP _

theorem fg_cent_two_plus (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W)
    (hperf : Group.IsPerfect (omegaGroup S.nondegW)) {A : Subgroup (ProjSim Q)}
    (hA : ∀ γ ∈ A, ∀ a ∈ omegaGroup S.nondegW,
      projSimAct Q γ (toProj Q (S.extW a)) = toProj Q (S.extW a))
    (hP : Module.finrank (ZMod 3) S.P = 2) (hs : quadSign (Q.restrict S.P) = 1) :
    Nat.card A ≤ 2 ∨
      Nonempty (↥A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := fg_cent_equiv S h3 hperf hA
  rcases fg_subgroup_two_plus S.nondegP hP hs (A.comap (fgIotaP S)) with h | hf
  · left
    rw [← Nat.card_congr e.toEquiv]
    exact h
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨e.symm.trans f⟩

theorem fg_cent_two_minus (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W)
    (hperf : Group.IsPerfect (omegaGroup S.nondegW)) {A : Subgroup (ProjSim Q)}
    (hA : ∀ γ ∈ A, ∀ a ∈ omegaGroup S.nondegW,
      projSimAct Q γ (toProj Q (S.extW a)) = toProj Q (S.extW a))
    (hP : Module.finrank (ZMod 3) S.P = 2) (hs : quadSign (Q.restrict S.P) = -1)
    (hdet : ∀ b : OGroup (Q.restrict S.P), fgIotaP S b ∈ A →
      QuadraticMap.orthogonalDet (Q.restrict S.P) b = 1) :
    Nat.card A ≤ 2 ∨ Nonempty (↥A ≃* Multiplicative (ZMod 4)) := by
  obtain ⟨e⟩ := fg_cent_equiv S h3 hperf hA
  rcases fg_subgroup_two_minus S.nondegP hP hs (A.comap (fgIotaP S))
      (fun b hb => hdet b hb) with h | hf
  · left
    rw [← Nat.card_congr e.toEquiv]
    exact h
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨e.symm.trans f⟩

end CFSG.OddStandard.SmallF3.Omega
