module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

structure PspFrame {G : Type} [Group G] (L : Subgroup G) where
  φ : ↥(normalizer (L : Set G)) →* P45
  mem_A : ∀ y : ↥(normalizer (L : Set G)), φ y ∈ QA45.originalSubgroup
  ker_iff : ∀ y : ↥(normalizer (L : Set G)), φ y = 1 ↔ (y : G) ∈ centralizer (L : Set G)
  mem_P : ∀ y : ↥(normalizer (L : Set G)), (y : G) ∈ L → φ y ∈ QP45.originalSubgroup
  inj_L : ∀ y y' : ↥(normalizer (L : Set G)), (y : G) ∈ L → (y' : G) ∈ L → φ y = φ y' → y = y'
  surj_P : ∀ p ∈ QP45.originalSubgroup, ∃ y : ↥(normalizer (L : Set G)), (y : G) ∈ L ∧ φ y = p

theorem QP45_le_QA45 : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure]
  exact Subgroup.closure_mono
    (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))

theorem card_QP45 : Nat.card QP45.originalSubgroup = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem card_QA45 : Nat.card QA45.originalSubgroup = 51840 := by
  rw [card_group QA45 QA45_ok, QA45_valid.2]

theorem autModel_phi_conj {K H : Type} [Group K] [Group H] (M : AutModel K H) (hPA : M.P ≤ M.A)
    (k : K) : (M.Φ (MulAut.conj k) : H) = (M.e k : H) := by
  set a : M.A := ⟨(M.e k : H), hPA (M.e k).2⟩ with ha
  have hΦψ : M.Φ (M.Φ.symm a) = a := M.Φ.apply_symm_apply a
  have hψ : M.Φ.symm a = MulAut.conj k := by
    ext x
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec _ x, hΦψ]
    simp [ha, MulAut.conj_apply]
  rw [← hψ, hΦψ]

theorem exists_pspFrame {G : Type} [Group G] {L : Subgroup G}
    (hL : IsPSp43 L) : Nonempty (PspFrame L) := by
  obtain ⟨e⟩ := PSp43.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := PSp43.exists_model e
  have hPA : M.P ≤ M.A := by rw [hMP, hMA]; exact QP45_le_QA45
  have hconj : ∀ (y : ↥(normalizer (L : Set G))) (hy : (y : G) ∈ L),
      L.normalizerMonoidHom y = MulAut.conj (⟨y, hy⟩ : ↥L) := by
    intro y hy
    ext x
    simp [MulAut.conj_apply]
  have hval : ∀ (y : ↥(normalizer (L : Set G))) (hy : (y : G) ∈ L),
      M.ι (L.normalizerMonoidHom y) = (M.e ⟨y, hy⟩ : P45) := by
    intro y hy
    show (M.Φ (L.normalizerMonoidHom y) : P45) = _
    rw [hconj y hy, autModel_phi_conj M hPA]
  refine ⟨⟨M.ι.comp L.normalizerMonoidHom, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y
    rw [← hMA]
    exact M.ι_mem _
  · intro y
    rw [MonoidHom.comp_apply, ← map_one M.ι, M.ι_injective.eq_iff]
    have h := congrArg (fun S : Subgroup _ => y ∈ S) (Subgroup.normalizerMonoidHom_ker L)
    simpa [Subgroup.mem_subgroupOf] using h
  · intro y hy
    rw [MonoidHom.comp_apply, hval y hy, ← hMP]
    exact (M.e _).2
  · intro y y' hy hy' h
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hval y hy, hval y' hy'] at h
    have h1 := M.e.injective (Subtype.ext h)
    exact Subtype.ext (Subtype.mk.inj h1)
  · intro p hp
    rw [← hMP] at hp
    refine ⟨⟨(M.e.symm ⟨p, hp⟩ : G), Subgroup.le_normalizer (M.e.symm ⟨p, hp⟩).2⟩,
      (M.e.symm ⟨p, hp⟩).2, ?_⟩
    rw [MonoidHom.comp_apply, hval _ (M.e.symm ⟨p, hp⟩).2]
    simp

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

@[expose] def incl (L : Subgroup G) : ↥L →* ↥(normalizer (L : Set G)) :=
  Subgroup.inclusion Subgroup.le_normalizer

@[expose] def ψ : ↥L →* P45 := F.φ.comp (incl L)

theorem ψ_apply (l : ↥L) : F.ψ l = F.φ ⟨(l : G), Subgroup.le_normalizer l.2⟩ := rfl

theorem ψ_injective : Function.Injective F.ψ := by
  intro l l' h
  have h1 := F.inj_L ⟨(l : G), Subgroup.le_normalizer l.2⟩ ⟨(l' : G), Subgroup.le_normalizer l'.2⟩
    l.2 l'.2 h
  exact Subtype.ext (Subtype.mk.inj h1)

theorem ψ_mem (l : ↥L) : F.ψ l ∈ QP45.originalSubgroup := F.mem_P _ l.2

theorem ψ_surj {p : P45} (hp : p ∈ QP45.originalSubgroup) : ∃ l : ↥L, F.ψ l = p := by
  obtain ⟨y, hy, h⟩ := F.surj_P p hp
  exact ⟨⟨(y : G), hy⟩, h⟩

theorem le_range : QP45.originalSubgroup ≤ F.φ.range := by
  intro p hp
  obtain ⟨y, -, h⟩ := F.surj_P p hp
  exact ⟨y, h⟩

theorem range_le : F.φ.range ≤ QA45.originalSubgroup := by
  rintro _ ⟨y, rfl⟩
  exact F.mem_A y

theorem sup_subgroupOf_eq : (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) =
    QP45.originalSubgroup.comap F.φ := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · intro hy
    have hle : L ⊔ centralizer (L : Set G) ≤
        (QP45.originalSubgroup.comap F.φ).map (normalizer (L : Set G)).subtype := by
      refine sup_le (fun l hl => ?_) (fun c hc => ?_)
      · exact ⟨⟨l, Subgroup.le_normalizer hl⟩, F.mem_P _ hl, rfl⟩
      · have hcn : c ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hc
        refine ⟨⟨c, hcn⟩, ?_, rfl⟩
        show F.φ ⟨c, hcn⟩ ∈ QP45.originalSubgroup
        rw [(F.ker_iff _).2 hc]
        exact Subgroup.one_mem _
    obtain ⟨y', hy', hyy⟩ := hle hy
    have : y' = y := Subtype.ext hyy
    rw [← this]
    exact hy'
  · intro hy
    obtain ⟨y', hy'L, h⟩ := F.surj_P _ hy
    have hc : ((y'⁻¹ * y : ↥(normalizer (L : Set G))) : G) ∈ centralizer (L : Set G) := by
      rw [← F.ker_iff, map_mul, map_inv, h, inv_mul_cancel]
    have : (y : G) = (y' : G) * ((y'⁻¹ * y : ↥(normalizer (L : Set G))) : G) := by
      simp
    rw [this]
    exact Subgroup.mul_mem_sup hy'L hc

end PspFrame

theorem relIndex_QP45_QA45 :
    QP45.originalSubgroup.relIndex QA45.originalSubgroup = 2 := by
  have h := Subgroup.relIndex_mul_card (H := QP45.originalSubgroup) (K := QA45.originalSubgroup)
  rw [inf_eq_left.2 QP45_le_QA45, card_QP45, card_QA45] at h
  generalize QP45.originalSubgroup.relIndex QA45.originalSubgroup = r at h ⊢
  omega

theorem asc82FactOut5_of_cert : Asc82FactOut5 := by
  intro G _ _ L hL
  obtain ⟨F⟩ := exists_pspFrame hL
  rw [Subgroup.relIndex, F.sup_subgroupOf_eq, Subgroup.index_comap]
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ F.le_range F.range_le
  rw [relIndex_QP45_QA45] at h1
  have h2 : (QP45.originalSubgroup.relIndex F.φ.range) ∣ 2 := ⟨_, h1.symm⟩
  exact Nat.le_of_dvd (by norm_num) h2

end CFSG.OddStandard.SmallF3.Omega
