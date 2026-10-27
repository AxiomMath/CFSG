module

public import CFSG.Quasithin.Background.B6Defs
import CFSG.Quasithin.Background.SimsD1TransGrp
import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddSylow
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddBasic
import CFSG.LocalAnalysis.RankThreeUC.GN15Sym
import CFSG.CGT.PushingUpLit.BHSSym.PermSylow
import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127.AltBig
open CFSG.Quasithin.SimsD1.TransGrp
open scoped Pointwise

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem isSylowTwoOf_subgroupOf_top {G : Type*} [Group G] {T L : Subgroup G}
    (hT : IsSylowTwoOf T L) : IsSylowTwoOf (T.subgroupOf L) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  · rw [show ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index from
      Subgroup.relIndex_top_right (T.subgroupOf L)]
    exact hT.2.2

private theorem isSylowTwoOf_map_subgroupOf {Ω X : Type*} [Group Ω] [Group X] {L T : Subgroup Ω}
    (e : ↥L ≃* X) (hT : IsSylowTwoOf T L) :
    IsSylowTwoOf ((T.subgroupOf L).map e.toMonoidHom) ⊤ := by
  have hS := isSylowTwoOf_subgroupOf_top hT
  refine ⟨le_top, hS.2.1.map e.toMonoidHom, ?_⟩
  rw [show (((T.subgroupOf L).map e.toMonoidHom).subgroupOf ⊤).index =
    ((T.subgroupOf L).map e.toMonoidHom).index from
      Subgroup.relIndex_top_right ((T.subgroupOf L).map e.toMonoidHom)]
  have hindex : (Subgroup.map e.toMonoidHom (T.subgroupOf L)).index =
      (T.subgroupOf L).index := by
    simp
  rw [hindex]
  simpa [show ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index from
    Subgroup.relIndex_top_right (T.subgroupOf L)] using hS.2.2

private theorem map_normalizer_subgroupOf {Ω : Type*} [Group Ω] {L T : Subgroup Ω} (hT : T ≤ L) :
    (Subgroup.normalizer (T.subgroupOf L : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.normalizer (T : Set Ω) := by
  have h := Subgroup.subgroupOf_normalizer_eq (H := T) (N := L) hT
  have h' := congrArg (fun U : Subgroup ↥L => U.map L.subtype) h.symm
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT, inf_comm] using h'

private theorem isUniqueMaxOver_inf_normalizer_of_mulEquiv
    {Ω X : Type*} [Group Ω] [Group X] {L T : Subgroup Ω} (e : ↥L ≃* X)
    (hT : IsSylowTwoOf T L)
    (h : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → IsUniqueMaxOver ⊤ P (Subgroup.normalizer P)) :
    IsUniqueMaxOver L T (L ⊓ Subgroup.normalizer (T : Set Ω)) := by
  have hmodel' : IsUniqueMaxOver ⊤ (T.subgroupOf L)
      (Subgroup.normalizer (T.subgroupOf L)) := by
    have hmap : IsUniqueMaxOver ((⊤ : Subgroup ↥L).map e.toMonoidHom)
        ((T.subgroupOf L).map e.toMonoidHom)
        ((Subgroup.normalizer (T.subgroupOf L)).map e.toMonoidHom) := by
      rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
        Subgroup.map_equiv_normalizer_eq]
      exact h _ (isSylowTwoOf_map_subgroupOf e hT)
    exact (isUniqueMaxOver_map_iff e.toMonoidHom e.injective ⊤ (T.subgroupOf L)
      (Subgroup.normalizer (T.subgroupOf L))).1 hmap
  have hmain : IsUniqueMaxOver L T
      ((Subgroup.normalizer (T.subgroupOf L)).map L.subtype) := by
    have hmap := (isUniqueMaxOver_map_iff L.subtype L.subtype_injective ⊤ (T.subgroupOf L)
      (Subgroup.normalizer (T.subgroupOf L))).2 hmodel'
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT.1,
      show (⊤ : Subgroup ↥L).map L.subtype = L by
        rw [Subgroup.map_top, Subgroup.range_subtype]] at hmap
  rwa [map_normalizer_subgroupOf hT.1] at hmain

private theorem exists_isUniqueMaxOver_map_of_mulEquiv
    {Ω X : Type*} [Group Ω] [Group X] {L T : Subgroup Ω} (e : ↥L ≃* X)
    (hT : IsSylowTwoOf T L) (B₀ : Subgroup X)
    (hB₀ : IsUniqueMaxOver ⊤ ((T.subgroupOf L).map e.toMonoidHom) B₀) :
    ∃ B : Subgroup Ω, IsUniqueMaxOver L T B := by
  have hmodel : IsUniqueMaxOver ⊤ (T.subgroupOf L) (B₀.comap e.toMonoidHom) := by
    have hmap : IsUniqueMaxOver ((⊤ : Subgroup ↥L).map e.toMonoidHom)
        ((T.subgroupOf L).map e.toMonoidHom)
        ((B₀.comap e.toMonoidHom).map e.toMonoidHom) := by
      rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
        Subgroup.map_comap_eq_self_of_surjective e.surjective]
      exact hB₀
    exact (isUniqueMaxOver_map_iff e.toMonoidHom e.injective ⊤ (T.subgroupOf L)
      (B₀.comap e.toMonoidHom)).1 hmap
  refine ⟨(B₀.comap e.toMonoidHom).map L.subtype, ?_⟩
  have hmain := (isUniqueMaxOver_map_iff L.subtype L.subtype_injective ⊤ (T.subgroupOf L)
    (B₀.comap e.toMonoidHom)).2 hmodel
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT.1,
    show (⊤ : Subgroup ↥L).map L.subtype = L by
      rw [Subgroup.map_top, Subgroup.range_subtype]] at hmain

private theorem eq_of_le_normalizer_of_mulEquiv
    {Ω X : Type*} [Group Ω] [Group X] {L T : Subgroup Ω} (e : ↥L ≃* X)
    (hT : IsSylowTwoOf T L)
    (h : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → ∀ K : Subgroup X, P ≤ K → K.Normal → K = ⊤)
    {K : Subgroup Ω} (hTK : T ≤ K) (hKL : K ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set Ω)) : K = L := by
  have hKnormal : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLK
  have hmapnormal : ((K.subgroupOf L).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hKnormal e.toMonoidHom e.surjective
  have hle : (T.subgroupOf L).map e.toMonoidHom ≤ (K.subgroupOf L).map e.toMonoidHom :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono L hTK)
  have htop : (K.subgroupOf L).map e.toMonoidHom = ⊤ :=
    h _ (isSylowTwoOf_map_subgroupOf e hT) _ hle hmapnormal
  have hK' : K.subgroupOf L = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop]
    exact (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have h2 : K = L := by
    have h := congrArg (fun U : Subgroup ↥L => U.map L.subtype) hK'
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL,
      show (⊤ : Subgroup ↥L).map L.subtype = L by
        rw [Subgroup.map_top, Subgroup.range_subtype]] at h
  exact h2

section SL2

private noncomputable def sylowOfIsSylowTwoOfTop {G : Type*} [Group G] {P : Subgroup G}
    (hP : IsSylowTwoOf P ⊤) : Sylow 2 G := by
  exact hP.2.1.toSylow (by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this)

private theorem coe_sylowOfIsSylowTwoOfTop {G : Type*} [Group G] {P : Subgroup G}
    (hP : IsSylowTwoOf P ⊤) :
    (sylowOfIsSylowTwoOfTop hP : Subgroup G) = P := by
  exact IsPGroup.toSylow_coe hP.2.1 _

private theorem isUniqueMaxOver_sl2 {k : Type} [Field k] [Finite k] [CharP k 2]
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)} (hP : IsSylowTwoOf P ⊤) :
    IsUniqueMaxOver ⊤ P (Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) k))) := by
  let P' := sylowOfIsSylowTwoOfTop hP
  have hP'coe : (P' : Subgroup _) = P := coe_sylowOfIsSylowTwoOfTop hP
  have hNtop : Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) k)) ≠ ⊤ := by
    intro hN
    have hPnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    have hbot : P = ⊥ :=
      @CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_eq_bot_of_normal_le_normalizer
        k _ _ _ (Matrix.SpecialLinearGroup (Fin 2) k) _
        (MulEquiv.refl _) P' P hPnormal (by rw [hP'coe]; exact Subgroup.le_normalizer)
    have hne := CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_sylow_ne_bot
      (MulEquiv.refl _) P'
    rw [hP'coe] at hne
    exact hne hbot
  have hmax : IsMaxSubgroupIn ⊤
      (Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) k))) := by
    refine ⟨lt_top_iff_ne_top.mpr hNtop, ?_⟩
    intro K hNK hKle
    by_contra hKtop
    have hPK : P ≤ K := Subgroup.le_normalizer.trans hNK.le
    have hPK' : (P' : Subgroup _) ≤ K := by rwa [hP'coe]
    have hKN : K ≤ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) k)) := by
      have h := CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_le_normalizer_of_sylow_le
        (MulEquiv.refl _) P' hPK' hKtop
      rwa [hP'coe] at h
    exact (not_le_of_gt hNK) hKN
  refine (isUniqueMaxOver_iff).2 ⟨hmax, Subgroup.le_normalizer, ?_⟩
  intro N hNmax hPN
  have hNle : N ≤ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) k)) := by
    have hPN' : (P' : Subgroup _) ≤ N := by rwa [hP'coe]
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_le_normalizer_of_sylow_le
      (MulEquiv.refl _) P' hPN' (ne_of_lt hNmax.1)
    rwa [hP'coe] at h
  by_contra hNe
  exact hNtop (hNmax.2 _ (lt_of_le_of_ne hNle hNe) le_top)

private theorem sl2_normal_eq_top_of_sylow_le {k : Type} [Field k] [Finite k] [CharP k 2]
    {P K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)}
    (hP : IsSylowTwoOf P ⊤) (hPK : P ≤ K) [K.Normal] : K = ⊤ := by
  let P' := sylowOfIsSylowTwoOfTop hP
  have hP'coe : (P' : Subgroup _) = P := coe_sylowOfIsSylowTwoOfTop hP
  by_contra hKtop
  have hPK' : (P' : Subgroup _) ≤ K := by rwa [hP'coe]
  have hKN : K ≤ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) k)) := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_le_normalizer_of_sylow_le
      (MulEquiv.refl _) P' hPK' hKtop
    rwa [hP'coe] at h
  have hbot : K = ⊥ :=
    @CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_eq_bot_of_normal_le_normalizer
      k _ _ _ (Matrix.SpecialLinearGroup (Fin 2) k) _
      (MulEquiv.refl _) P' K inferInstance (by rwa [hP'coe])
  have hPbot : P = ⊥ := le_bot_iff.mp (hPK.trans (le_of_eq hbot))
  have hne := CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_sylow_ne_bot (MulEquiv.refl _) P'
  rw [hP'coe] at hne
  exact hne hPbot

end SL2

theorem isUniqueMaxOver_inf_normalizer_of_mulEquiv_sl2
    {Ω : Type*} [Group Ω] [Finite Ω] {L T : Subgroup Ω}
    {k : Type} [Field k] [Finite k] [CharP k 2]
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) k) (hT : IsSylowTwoOf T L) :
    IsUniqueMaxOver L T (L ⊓ Subgroup.normalizer (T : Set Ω)) :=
  isUniqueMaxOver_inf_normalizer_of_mulEquiv e hT fun _ hP => isUniqueMaxOver_sl2 hP

theorem eq_of_le_normalizer_of_mulEquiv_sl2
    {Ω : Type*} [Group Ω] [Finite Ω] {L T : Subgroup Ω}
    {k : Type} [Field k] [Finite k] [CharP k 2]
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) k) (hT : IsSylowTwoOf T L) {K : Subgroup Ω}
    (hTK : T ≤ K) (hKL : K ≤ L) (hLK : L ≤ Subgroup.normalizer (K : Set Ω)) : K = L :=
  eq_of_le_normalizer_of_mulEquiv e hT (fun _ hP _ hPK _hKn => sl2_normal_eq_top_of_sylow_le hP hPK)
    hTK hKL hLK

section Alt

private theorem eq_of_isSylowTwoOf_le_of_isPGroup {G : Type*} [Group G]
    {S C : Subgroup G} (hS : IsSylowTwoOf S ⊤) (hSC : S ≤ C) (hC : IsPGroup 2 C) :
    C = S := by
  have hSidx : ¬ 2 ∣ S.index := by
    simpa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] using hS.2.2
  let S' : Sylow 2 G := hS.2.1.toSylow hSidx
  have hcoe : (S' : Subgroup G) = S := IsPGroup.toSylow_coe hS.2.1 hSidx
  have h := Sylow.is_maximal' S' hC (by rwa [hcoe])
  rwa [hcoe] at h

private theorem stabilizer_index_alt (m : ℕ) (c : Fin (2 ^ m + 1)) :
    (MulAction.stabilizer (Equiv.Perm (Fin (2 ^ m + 1))) c).index = 2 ^ m + 1 := by
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
  simp [Nat.card_eq_fintype_card]

private theorem exists_sylow_sym_fixing {m : ℕ} (hm : 2 ≤ m)
    {T : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))} (hT : IsSylowTwoOf T ⊤)
    {c : Fin (2 ^ m + 1)} (hc : ∀ t ∈ T, (t : Equiv.Perm (Fin (2 ^ m + 1))) c = c) :
    ∃ T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1))),
      IsPGroup 2 T₁ ∧ ¬ 2 ∣ T₁.index ∧ (∀ t ∈ T₁, t c = c) ∧
        T.map (alternatingGroup (Fin (2 ^ m + 1))).subtype ≤ T₁ := by
  classical
  let α := Fin (2 ^ m + 1)
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  let T₀ : Subgroup (Equiv.Perm α) := T.map A.subtype
  let H : Subgroup (Equiv.Perm α) := MulAction.stabilizer (Equiv.Perm α) c
  have hT₀p : IsPGroup 2 T₀ := hT.2.1.map A.subtype
  have hT₀H : T₀ ≤ H := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
    rw [MulAction.mem_stabilizer_iff]
    simpa [Subgroup.smul_def] using hc u hu
  have hHindex : H.index = 2 ^ m + 1 := stabilizer_index_alt m c
  have hoddn : ¬ 2 ∣ 2 ^ m + 1 := by
    have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨S, hT₀S⟩ := (hT₀p.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(S : Subgroup ↥H).map H.subtype, S.isPGroup'.map H.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.index_map_subtype, hHindex]
    exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index hoddn
  · rintro t ⟨u, -, rfl⟩
    have := MulAction.mem_stabilizer_iff.mp u.2
    simpa [Subgroup.smul_def] using this
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
    have htH : (u : Equiv.Perm α) ∈ H := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hc u hu
    have htS : (⟨(u : Equiv.Perm α), htH⟩ : ↥H) ∈ (S : Subgroup ↥H) :=
      hT₀S (Subgroup.mem_subgroupOf.mpr ht)
    exact Subgroup.mem_map_of_mem H.subtype htS

private theorem map_subtype_eq_inf_of_le {m : ℕ}
    {T : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))} (hT : IsSylowTwoOf T ⊤)
    {T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    (hT₀T₁ : T.map (alternatingGroup (Fin (2 ^ m + 1))).subtype ≤ T₁)
    (hT₁p : IsPGroup 2 T₁) :
    T.map (alternatingGroup (Fin (2 ^ m + 1))).subtype =
      T₁ ⊓ alternatingGroup (Fin (2 ^ m + 1)) := by
  let A : Subgroup (Equiv.Perm (Fin (2 ^ m + 1))) := alternatingGroup (Fin (2 ^ m + 1))
  refine le_antisymm (fun t ht => ⟨hT₀T₁ ht, Subgroup.map_subtype_le T ht⟩) ?_
  intro t ht
  have hC2 : IsPGroup 2 (T₁.subgroupOf A) := hT₁p.comap_subtype
  have hTC : T ≤ T₁.subgroupOf A := by
    intro a ha
    exact hT₀T₁ (Subgroup.mem_map_of_mem A.subtype ha)
  have hCeq : T₁.subgroupOf A = T := eq_of_isSylowTwoOf_le_of_isPGroup hT hTC hC2
  have htA : (⟨t, ht.2⟩ : ↥A) ∈ T₁.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact ht.1
  exact Subgroup.mem_map_of_mem A.subtype (hCeq ▸ htA)

private theorem relIndex_inf_eq_two {m : ℕ}
    {T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))} (hT₁idx : ¬ 2 ∣ T₁.index) :
    (T₁ ⊓ alternatingGroup (Fin (2 ^ m + 1))).relIndex T₁ = 2 := by
  classical
  let α := Fin (2 ^ m + 1)
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hNontriv : Nontrivial α := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hAidx : A.index = 2 := @alternatingGroup.index_eq_two α _ _ hNontriv
  have hnotSub : ¬ T₁ ≤ A := by
    intro hTA
    have hdvd : A.index ∣ T₁.index := Subgroup.index_dvd_of_le hTA
    rw [hAidx] at hdvd
    exact hT₁idx hdvd
  have hjoin : A ⊔ T₁ = ⊤ := by
    have hdvd : A.relIndex (A ⊔ T₁) ∣ A.index := by
      rw [← Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ T₁)]
      exact dvd_mul_right _ _
    have hne : A.relIndex (A ⊔ T₁) ≠ 1 := by
      intro h1
      exact hnotSub (le_trans le_sup_right (Subgroup.relIndex_eq_one.mp h1))
    have hrel2 : A.relIndex (A ⊔ T₁) = 2 := by
      rw [hAidx] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact absurd h1 hne
      · exact h2
    have hprod := Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ T₁)
    rw [hrel2, hAidx] at hprod
    exact Subgroup.index_eq_one.mp (by omega)
  calc (T₁ ⊓ A).relIndex T₁ = A.relIndex T₁ := Subgroup.inf_relIndex_left T₁ A
    _ = A.relIndex (A ⊔ T₁) := (Subgroup.relIndex_sup_left (H := T₁) (K := A)).symm
    _ = A.relIndex ⊤ := by rw [hjoin]
    _ = A.index := Subgroup.relIndex_top_right A
    _ = 2 := hAidx

private theorem exists_swap_outside {m : ℕ} (hm : 2 ≤ m)
    {T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    (hT₁p : IsPGroup 2 T₁) (hT₁idx : ¬ 2 ∣ T₁.index)
    {c : Fin (2 ^ m + 1)} (hfix : ∀ t ∈ T₁, t c = c) {x : Fin (2 ^ m + 1)} (hx : x ≠ c) :
    ∃ x' z z' : Fin (2 ^ m + 1),
      x ≠ x' ∧ Equiv.swap x x' ∈ T₁ ∧ z ≠ c ∧ z ≠ x ∧ z ≠ x' ∧
      z ≠ z' ∧ Equiv.swap z z' ∈ T₁ ∧ z' ≠ x ∧ z' ≠ x' := by
  obtain ⟨x', hxx', hsx⟩ :=
    CFSG.CGT.PushingUpLit.BHSSym.exists_edge hT₁p hT₁idx hfix hx
  obtain ⟨z, hz⟩ : ∃ z : Fin (2 ^ m + 1), z ≠ c ∧ z ≠ x ∧ z ≠ x' := by
    have hcard : ({c, x, x'} : Finset (Fin (2 ^ m + 1))).card <
        (Finset.univ : Finset (Fin (2 ^ m + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 : ({c, x, x'} : Finset (Fin (2 ^ m + 1))).card ≤ 3 := Finset.card_le_three
      refine lt_of_le_of_lt h3 ?_
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨z, ?_⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hz
  obtain ⟨hzc, hzx, hzx'⟩ := hz
  obtain ⟨z', hzz', hsz⟩ :=
    CFSG.CGT.PushingUpLit.BHSSym.exists_edge hT₁p hT₁idx hfix hzc
  have hz'x : z' ≠ x := by
    intro h
    apply hzx'
    have h2 : Equiv.swap x z ∈ T₁ := by rw [Equiv.swap_comm]; simpa [h] using hsz
    exact CFSG.CGT.PushingUpLit.BHSSym.eq_of_swap_mem hT₁p hzx.symm hxx' h2 hsx
  have hz'x' : z' ≠ x' := by
    intro h
    apply hzx
    have h2 : Equiv.swap x' z ∈ T₁ := by rw [Equiv.swap_comm]; simpa [h] using hsz
    exact CFSG.CGT.PushingUpLit.BHSSym.eq_of_swap_mem hT₁p hzx'.symm hxx'.symm h2
      (by rw [Equiv.swap_comm]; exact hsx)
  exact ⟨x', z, z', hxx', hsx, hzc, hzx, hzx', hzz', hsz, hz'x, hz'x'⟩

private theorem swap_orbit_step {m : ℕ}
    {T₀ T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    (hT₀eq : T₀ = T₁ ⊓ alternatingGroup (Fin (2 ^ m + 1)))
    {x x' z z' : Fin (2 ^ m + 1)}
    (hxx' : x ≠ x') (hsx : Equiv.swap x x' ∈ T₁)
    (hzx : z ≠ x) (hzz' : z ≠ z') (hsz : Equiv.swap z z' ∈ T₁)
    (hz'x : z' ≠ x) :
    Equiv.swap x x' ∉ T₀ ∧ Equiv.swap x x' * Equiv.swap x x' = 1 ∧
      x' ∈ MulAction.orbit (↥T₀) x := by
  have hs0 : Equiv.swap x x' ∉ T₀ := by
    intro h
    rw [hT₀eq] at h
    have hA : Equiv.swap x x' ∈ alternatingGroup (Fin (2 ^ m + 1)) := h.2
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hxx'] at hA
    norm_num at hA
  refine ⟨hs0, Equiv.swap_mul_self x x', ?_⟩
  refine ⟨⟨Equiv.swap x x' * Equiv.swap z z', ?_⟩, ?_⟩
  · rw [hT₀eq]
    refine ⟨T₁.mul_mem hsx hsz, ?_⟩
    change Equiv.swap x x' * Equiv.swap z z' ∈
      alternatingGroup (Fin (2 ^ m + 1))
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hxx', Equiv.Perm.sign_swap hzz']
    norm_num
  · show (Equiv.swap x x' * Equiv.swap z z') x = x'
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzx.symm hz'x.symm,
      Equiv.swap_apply_left]

private theorem orbit_subset_of_fixes {m : ℕ}
    {T : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    {c x : Fin (2 ^ m + 1)} (hfix : ∀ t ∈ T, t c = c) (hx : x ≠ c) :
    MulAction.orbit (↥T) x ⊆ {a | a ≠ c} := by
  rintro a ⟨⟨u, hu⟩, rfl⟩
  intro hac
  have hu_fix : (u : Equiv.Perm (Fin (2 ^ m + 1))) c = c := hfix u hu
  have hux : (u : Equiv.Perm (Fin (2 ^ m + 1))) x = c := hac
  exact hx ((u : Equiv.Perm (Fin (2 ^ m + 1))).injective (hux.trans hu_fix.symm))

private theorem orbit_eq_of_transitive_fixes {m : ℕ}
    {T : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    {c x : Fin (2 ^ m + 1)} (hfix : ∀ t ∈ T, t c = c)
    (htr : ∀ a b, a ≠ c → b ≠ c → ∃ t ∈ T, t a = b) (hx : x ≠ c) :
    MulAction.orbit (↥T) x = {a | a ≠ c} := by
  apply Set.eq_of_subset_of_subset (orbit_subset_of_fixes hfix hx)
  intro a ha
  obtain ⟨t, ht, hta⟩ := htr x a hx ha
  exact ⟨⟨t, ht⟩, hta⟩

private theorem swap_orbit_invariant {m : ℕ}
    {T₀ T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    (hT₀T₁ : T₀ ≤ T₁) (hT₀idx2 : (T₀.subgroupOf T₁).index = 2)
    {x x' : Fin (2 ^ m + 1)} {s : Equiv.Perm (Fin (2 ^ m + 1))}
    (hs : s ∈ T₁) (hsx : s x = x') (hsq : s * s = 1)
    (hx'O : x' ∈ MulAction.orbit (↥T₀) x) :
    ∀ a, a ∈ MulAction.orbit (↥T₀) x → s a ∈ MulAction.orbit (↥T₀) x := by
  rintro a ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨⟨h, hh⟩, hhx⟩ := hx'O
  have hhx' : (h : Equiv.Perm (Fin (2 ^ m + 1))) x = x' := by
    simpa [Subgroup.smul_def] using hhx
  have hN : (T₀.subgroupOf T₁).Normal := Subgroup.normal_of_index_eq_two hT₀idx2
  have hconj_sub : (⟨s, hs⟩ : ↥T₁) * ⟨(u : Equiv.Perm _), hT₀T₁ hu⟩ *
      (⟨s, hs⟩ : ↥T₁)⁻¹ ∈ T₀.subgroupOf T₁ :=
    Subgroup.Normal.conj_mem hN _ (Subgroup.mem_subgroupOf.mpr hu) _
  have hconj : s * (u : Equiv.Perm (Fin (2 ^ m + 1))) * s⁻¹ ∈ T₀ :=
    Subgroup.mem_subgroupOf.mp hconj_sub
  refine ⟨⟨s * (u : Equiv.Perm _) * s⁻¹ * h, ?_⟩, ?_⟩
  · exact T₀.mul_mem hconj hh
  · show (s * (u : Equiv.Perm (Fin (2 ^ m + 1))) * s⁻¹ * h) x =
      s ((u : Equiv.Perm (Fin (2 ^ m + 1))) x)
    have hsx' : s x' = x := by
      rw [← hsx, ← Equiv.Perm.mul_apply, hsq, Equiv.Perm.one_apply]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hhx',
      inv_eq_of_mul_eq_one_right hsq, hsx']

private theorem mem_or_mul_mem_of_index_two {m : ℕ}
    {T₀ T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    (hT₀idx2 : (T₀.subgroupOf T₁).index = 2)
    {s : Equiv.Perm (Fin (2 ^ m + 1))} (hs : s ∈ T₁) (hs0 : s ∉ T₀) :
    ∀ t ∈ T₁, t ∈ T₀ ∨ s * t ∈ T₀ := by
  intro t ht
  by_cases ht0 : t ∈ T₀
  · exact Or.inl ht0
  · right
    have h := Subgroup.mul_mem_iff_of_index_two hT₀idx2
      (a := (⟨s, hs⟩ : ↥T₁)) (b := (⟨t, ht⟩ : ↥T₁))
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h
    exact h.mpr (iff_of_false hs0 ht0)

private theorem orbit_eq_of_index_two {m : ℕ}
    {T₀ T₁ : Subgroup (Equiv.Perm (Fin (2 ^ m + 1)))}
    (hT₀T₁ : T₀ ≤ T₁) (hT₀idx2 : (T₀.subgroupOf T₁).index = 2)
    {c x x' : Fin (2 ^ m + 1)} {s : Equiv.Perm (Fin (2 ^ m + 1))}
    (hs : s ∈ T₁) (hs0 : s ∉ T₀) (hsq : s * s = 1) (hsx : s x = x')
    (hx'O : x' ∈ MulAction.orbit (↥T₀) x)
    (hOsub : MulAction.orbit (↥T₀) x ⊆ {a | a ≠ c})
    (hT₁orbit : MulAction.orbit (↥T₁) x = {a | a ≠ c}) :
    MulAction.orbit (↥T₀) x = {a | a ≠ c} := by
  have hsO := swap_orbit_invariant hT₀T₁ hT₀idx2 hs hsx hsq hx'O
  apply Set.eq_of_subset_of_subset hOsub
  intro a ha
  have ha' : a ∈ MulAction.orbit (↥T₁) x := by rw [hT₁orbit]; exact ha
  obtain ⟨⟨t, ht⟩, rfl⟩ := ha'
  rcases mem_or_mul_mem_of_index_two hT₀idx2 hs hs0 t ht with ht0 | hst
  · exact ⟨⟨t, ht0⟩, rfl⟩
  · have hzO : (s * t : Equiv.Perm (Fin (2 ^ m + 1))) x ∈
        MulAction.orbit (↥T₀) x := ⟨⟨s * t, hst⟩, rfl⟩
    have hs' := hsO _ hzO
    have hcalc : s ((s * t : Equiv.Perm (Fin (2 ^ m + 1))) x) = t x := by
      rw [← Equiv.Perm.mul_apply, ← mul_assoc, hsq, one_mul]
    rwa [hcalc] at hs'

theorem exists_apply_eq_of_isSylowTwoOf_alt {m : ℕ} (hm : 2 ≤ m)
    {T : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))} (hT : IsSylowTwoOf T ⊤)
    {c x y : Fin (2 ^ m + 1)} (hc : ∀ t ∈ T, (t : Equiv.Perm (Fin (2 ^ m + 1))) c = c)
    (hx : x ≠ c) (hy : y ≠ c) : ∃ t ∈ T, (t : Equiv.Perm (Fin (2 ^ m + 1))) x = y := by
  classical
  let α := Fin (2 ^ m + 1)
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  let T₀ : Subgroup (Equiv.Perm α) := T.map A.subtype
  obtain ⟨T₁, hT₁p, hT₁idx, hfixT₁, hT₀T₁⟩ := exists_sylow_sym_fixing hm hT hc
  have hT₀eq : T₀ = T₁ ⊓ A := map_subtype_eq_inf_of_le hT hT₀T₁ hT₁p
  have hrel : T₀.relIndex T₁ = 2 := by
    rw [hT₀eq]
    exact relIndex_inf_eq_two hT₁idx
  have hT₀idx2 : (T₀.subgroupOf T₁).index = 2 := by
    rw [show (T₀.subgroupOf T₁).index = T₀.relIndex T₁ from rfl, hrel]
  have htrans₁ : ∀ a b, a ≠ c → b ≠ c → ∃ t ∈ T₁, t a = b := fun a b ha hb =>
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.exists_apply_eq_of_sylowTwo_two_pow_succ
      (m := m) (by omega) hT₁p hT₁idx hfixT₁ ha hb
  have hT₀fix : ∀ t ∈ T₀, t c = c := by
    rintro _ ⟨t, ht, rfl⟩
    exact hc t ht
  obtain ⟨x', z, z', hxx', hsx, hzc, hzx, hzx', hzz', hsz, hz'x, hz'x'⟩ :=
    exists_swap_outside hm hT₁p hT₁idx hfixT₁ hx
  obtain ⟨hs0, hsq, hx'O⟩ :=
    swap_orbit_step hT₀eq hxx' hsx hzx hzz' hsz hz'x
  have hOsub := orbit_subset_of_fixes hT₀fix hx
  have hT₁orbit : MulAction.orbit (↥T₁) x = {a | a ≠ c} :=
    orbit_eq_of_transitive_fixes hfixT₁ htrans₁ hx
  have hOeq : MulAction.orbit (↥T₀) x = {a | a ≠ c} :=
    orbit_eq_of_index_two hT₀T₁ hT₀idx2 hsx hs0 hsq (Equiv.swap_apply_left x x')
      hx'O hOsub hT₁orbit
  have haO : y ∈ MulAction.orbit (↥T₀) x := by rw [hOeq]; exact hy
  obtain ⟨⟨u, hu⟩, hux⟩ := haO
  obtain ⟨t, ht, htu⟩ := Subgroup.mem_map.mp hu
  refine ⟨t, ht, ?_⟩
  have hux' : (u : Equiv.Perm α) x = y := by simpa [Subgroup.smul_def] using hux
  rw [← htu] at hux'
  simpa using hux'

private theorem orbit_eq_univ_of_not_le_stabilizer {m : ℕ}
    {T K : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))}
    (hTK : T ≤ K) {p : OddInv (Fin (2 ^ m + 1))}
    (htr : ∀ x y, x ≠ p.ω → y ≠ p.ω → ∃ t ∈ T,
      (t : Equiv.Perm (Fin (2 ^ m + 1))) x = y)
    (hK : ¬ K ≤ (MulAction.stabilizer (Equiv.Perm (Fin (2 ^ m + 1))) p.ω).comap
      (alternatingGroup (Fin (2 ^ m + 1))).subtype) :
    MulAction.orbit (↥K) p.ω = Set.univ := by
  classical
  obtain ⟨k, hkK, hkB⟩ := Set.not_subset.mp hK
  have hkc : (k : Equiv.Perm (Fin (2 ^ m + 1))) p.ω ≠ p.ω := by
    intro h
    exact hkB (Subgroup.mem_comap.mpr (MulAction.mem_stabilizer_iff.mpr (by simpa using h)))
  rw [Set.eq_univ_iff_forall]
  intro z
  by_cases hzc : z = p.ω
  · rw [hzc]
    exact MulAction.mem_orbit_self p.ω
  · obtain ⟨t, ht, htd⟩ := htr ((k : Equiv.Perm _) p.ω) z hkc hzc
    refine ⟨⟨t * k, K.mul_mem (hTK ht) hkK⟩, ?_⟩
    show (⟨t * k, K.mul_mem (hTK ht) hkK⟩ : ↥K) • p.ω = z
    rw [Subgroup.smul_def]
    change (((t * k : ↥(alternatingGroup (Fin (2 ^ m + 1)))) : Equiv.Perm _)) p.ω = z
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply]
    exact htd

private theorem isPretransitive_of_orbit_eq_univ {G α : Type*} [Group G] [MulAction G α]
    {c : α} (h : MulAction.orbit G c = Set.univ) : MulAction.IsPretransitive G α := by
  rw [MulAction.isPretransitive_iff]
  intro a b
  have ha : a ∈ MulAction.orbit G c := by rw [h]; exact Set.mem_univ a
  have hb : b ∈ MulAction.orbit G c := by rw [h]; exact Set.mem_univ b
  obtain ⟨g, hga⟩ := ha
  obtain ⟨g', hgb⟩ := hb
  refine ⟨g' * g⁻¹, ?_⟩
  have h1 : g⁻¹ • a = c := by
    rw [← hga]
    simp
  calc (g' * g⁻¹) • a = g' • (g⁻¹ • a) := by rw [mul_smul]
    _ = g' • c := by rw [h1]
    _ = b := hgb

private theorem eq_top_of_pretransitive_of_three_le {m : ℕ} (hm3 : 3 ≤ m)
    {T K : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))}
    (hTK : T ≤ K) {p : OddInv (Fin (2 ^ m + 1))}
    (hpCont : p.Contained (T.map (alternatingGroup (Fin (2 ^ m + 1))).subtype))
    (hKpretrans : MulAction.IsPretransitive ↥K (Fin (2 ^ m + 1))) :
    K = ⊤ := by
  classical
  let α := Fin (2 ^ m + 1)
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  have h9 : 9 ≤ Fintype.card α := by
    rw [show Fintype.card α = 2 ^ m + 1 from Fintype.card_fin _]
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega
  have hodd : Odd (Fintype.card α) := by
    rw [show Fintype.card α = 2 ^ m + 1 from Fintype.card_fin _]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hContK : p.Contained (K.map A.subtype) := fun x y hx hy hxy hyμ =>
    Subgroup.map_mono hTK (hpCont x y hx hy hxy hyμ)
  have hKmaptrans : MulAction.IsPretransitive ↥(K.map A.subtype) α := by
    rw [MulAction.isPretransitive_iff] at hKpretrans ⊢
    intro a b
    obtain ⟨g, hg⟩ := hKpretrans a b
    refine ⟨⟨A.subtype (g : ↥A), Subgroup.mem_map_of_mem A.subtype g.2⟩, ?_⟩
    simpa [Subgroup.smul_def] using hg
  have hle : A ≤ K.map A.subtype :=
    CFSG.QuasithinUnique.L246C127.AltBig.alt_le_odd p h9 hodd hContK hKmaptrans
  have hKm : K.map A.subtype = A := le_antisymm (Subgroup.map_subtype_le K) hle
  have htop : K.map A.subtype = (⊤ : Subgroup ↥A).map A.subtype := by
    rw [hKm, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective (f := A.subtype) A.subtype_injective htop

private theorem eq_top_of_four_five_dvd_card {K : Subgroup ↥(alternatingGroup (Fin 5))}
    (h4 : 4 ∣ Nat.card K) (h5 : 5 ∣ Nat.card K) : K = ⊤ := by
  by_contra hKne
  have h20 : 20 ∣ Nat.card K := by
    have hcop : Nat.Coprime 4 5 := by norm_num
    simpa using hcop.mul_dvd_of_dvd_of_dvd h4 h5
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hdvd60 : Nat.card K ∣ 60 := by
    have h := Subgroup.card_mul_index K
    rw [hA5] at h
    exact ⟨K.index, h.symm⟩
  have hlt60 : Nat.card K < 60 := by
    have hle : Nat.card K ≤ 60 := by
      have h := Subgroup.card_le_card_group K
      rwa [hA5] at h
    have hne : Nat.card K ≠ 60 := by
      intro hcard
      exact hKne (Subgroup.eq_top_of_card_eq K (by rw [hcard, hA5]))
    exact lt_of_le_of_ne hle hne
  have hcard20 : Nat.card K = 20 := by
    obtain ⟨c, hc⟩ := h20
    obtain ⟨d, hd⟩ := hdvd60
    have hcd : c * d = 3 := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 20)
      calc 20 * (c * d) = (20 * c) * d := by ring
        _ = Nat.card K * d := by rw [← hc]
        _ = 60 := hd.symm
        _ = 20 * 3 := by norm_num
    have hc1 : c = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 ⟨d, hcd.symm⟩ with h1 | h3
      · exact h1
      · omega
    rw [hc, hc1, mul_one]
  exact CFSG.GroupTheory.AlternatingFive.card_ne_twenty K hcard20

private theorem eq_top_of_pretransitive_alt_five
    {T K : Subgroup ↥(alternatingGroup (Fin 5))}
    (hT : IsSylowTwoOf T ⊤) (hTK : T ≤ K)
    (hKpretrans : MulAction.IsPretransitive ↥K (Fin 5)) : K = ⊤ := by
  have hcardT : Nat.card T = 4 := by
    have hidx : ¬ 2 ∣ T.index := by
      simpa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] using
        hT.2.2
    let T' : Sylow 2 ↥(alternatingGroup (Fin 5)) := hT.2.1.toSylow hidx
    have hcoe : (T' : Subgroup ↥(alternatingGroup (Fin 5))) = T :=
      IsPGroup.toSylow_coe hT.2.1 hidx
    have := CFSG.GroupTheory.AlternatingFive.card_sylow_two_eq T'
    rwa [hcoe] at this
  have h4 : 4 ∣ Nat.card K := by
    have hdvd : Nat.card T ∣ Nat.card K := by
      refine ⟨(T.subgroupOf K).index, ?_⟩
      have h := Subgroup.card_mul_index (T.subgroupOf K)
      have hcard : Nat.card ↥(T.subgroupOf K) = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
      rw [hcard] at h
      exact h.symm
    rwa [hcardT] at hdvd
  have h5 : 5 ∣ Nat.card K := by
    have horbit : MulAction.orbit (↥K) (0 : Fin 5) = Set.univ :=
      MulAction.orbit_eq_univ ↥K 0
    have hidx5 : (MulAction.stabilizer (↥K) (0 : Fin 5)).index = 5 := by
      rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_eq_fintype_card]
      simp
    have h := Subgroup.card_mul_index (MulAction.stabilizer (↥K) (0 : Fin 5))
    rw [hidx5] at h
    exact ⟨Nat.card (MulAction.stabilizer (↥K) (0 : Fin 5)),
      by rw [mul_comm]; exact h.symm⟩
  exact eq_top_of_four_five_dvd_card h4 h5

private theorem stabilizer_comap_ne_top {m : ℕ} (hm : 2 ≤ m) (c : Fin (2 ^ m + 1)) :
    (MulAction.stabilizer (Equiv.Perm (Fin (2 ^ m + 1))) c).comap
      (alternatingGroup (Fin (2 ^ m + 1))).subtype ≠ ⊤ := by
  intro hB
  obtain ⟨d, hd⟩ : ∃ d : Fin (2 ^ m + 1), d ≠ c := by
    by_contra h
    push Not at h
    have h01 : (0 : Fin (2 ^ m + 1)) ≠ 1 := by
      intro e
      have := Fin.val_eq_of_eq e
      norm_num at this
    exact h01 ((h 0).trans (h 1).symm)
  have h3 : 3 ≤ Nat.card (Fin (2 ^ m + 1)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have htrans : MulAction.IsPretransitive
      ↥(alternatingGroup (Fin (2 ^ m + 1))) (Fin (2 ^ m + 1)) :=
    alternatingGroup.isPretransitive_of_three_le_card _ h3
  obtain ⟨g, hg⟩ := (MulAction.isPretransitive_iff _ _).mp htrans c d
  have hgB : g ∈ (MulAction.stabilizer (Equiv.Perm (Fin (2 ^ m + 1))) c).comap
      (alternatingGroup (Fin (2 ^ m + 1))).subtype := by rw [hB]; exact Subgroup.mem_top g
  rw [Subgroup.mem_comap] at hgB
  have hgc : ((g : ↥(alternatingGroup (Fin (2 ^ m + 1)))) :
      Equiv.Perm (Fin (2 ^ m + 1))) c = c := by
    simpa [Subgroup.smul_def] using MulAction.mem_stabilizer_iff.mp hgB
  have hgd : ((g : ↥(alternatingGroup (Fin (2 ^ m + 1)))) :
      Equiv.Perm (Fin (2 ^ m + 1))) c = d := by simpa [Subgroup.smul_def] using hg
  exact hd (hgd.symm.trans hgc)

private theorem eq_top_of_sylow_le_of_not_le_stabilizer {m : ℕ} (hm : 2 ≤ m)
    {T K : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))}
    (hT : IsSylowTwoOf T ⊤) (hTK : T ≤ K)
    {p : OddInv (Fin (2 ^ m + 1))}
    (hpCont : p.Contained (T.map (alternatingGroup (Fin (2 ^ m + 1))).subtype))
    (htr : ∀ x y, x ≠ p.ω → y ≠ p.ω → ∃ t ∈ T,
      (t : Equiv.Perm (Fin (2 ^ m + 1))) x = y)
    (hK : ¬ K ≤ (MulAction.stabilizer (Equiv.Perm (Fin (2 ^ m + 1))) p.ω).comap
      (alternatingGroup (Fin (2 ^ m + 1))).subtype) : K = ⊤ := by
  have hKpretrans : MulAction.IsPretransitive ↥K (Fin (2 ^ m + 1)) :=
    isPretransitive_of_orbit_eq_univ (orbit_eq_univ_of_not_le_stabilizer hTK htr hK)
  by_cases hm3 : 3 ≤ m
  · exact eq_top_of_pretransitive_of_three_le hm3 hTK hpCont hKpretrans
  · have hm2 : m = 2 := by omega
    subst hm2
    exact eq_top_of_pretransitive_alt_five hT hTK hKpretrans

private theorem exists_isUniqueMaxOver_alt_model {m : ℕ} (hm : 2 ≤ m)
    {T : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))} (hT : IsSylowTwoOf T ⊤) :
    ∃ B : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1))), IsUniqueMaxOver ⊤ T B := by
  classical
  let α := Fin (2 ^ m + 1)
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  have hodd : Odd (Fintype.card α) := by
    rw [show Fintype.card α = 2 ^ m + 1 from Fintype.card_fin _]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have h5 : 5 ≤ Fintype.card α := by
    rw [show Fintype.card α = 2 ^ m + 1 from Fintype.card_fin _]
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨p, hpfix, hpCont⟩ := exists_oddInv_of_sylow hodd h5 hT
  have htr : ∀ x y, x ≠ p.ω → y ≠ p.ω → ∃ t ∈ T,
      (t : Equiv.Perm α) x = y :=
    fun x y hx hy => exists_apply_eq_of_isSylowTwoOf_alt hm hT hpfix hx hy
  let B : Subgroup ↥A := (MulAction.stabilizer (Equiv.Perm α) p.ω).comap A.subtype
  have hTB : T ≤ B := by
    intro t ht
    exact Subgroup.mem_comap.mpr (MulAction.mem_stabilizer_iff.mpr (by simpa using hpfix t ht))
  have hBtop : B ≠ ⊤ := stabilizer_comap_ne_top hm p.ω
  have hBmax : IsMaxSubgroupIn ⊤ B := by
    refine ⟨lt_top_iff_ne_top.mpr hBtop, ?_⟩
    intro K hBK hKle
    by_contra hKne
    exact hKne (eq_top_of_sylow_le_of_not_le_stabilizer hm hT (hTB.trans hBK.le)
      hpCont htr (not_le_of_gt hBK))
  refine ⟨B, (isUniqueMaxOver_iff).2 ⟨hBmax, hTB, ?_⟩⟩
  intro N hNmax hTN
  have hNB : N ≤ B := by
    by_contra hNB
    exact (ne_of_lt hNmax.1) (eq_top_of_sylow_le_of_not_le_stabilizer hm hT hTN hpCont htr hNB)
  by_contra hNe
  exact hBtop (hNmax.2 B (lt_of_le_of_ne hNB hNe) le_top)

private theorem alt_normal_eq_top_of_sylow_le {m : ℕ} (hm : 2 ≤ m)
    {P K : Subgroup ↥(alternatingGroup (Fin (2 ^ m + 1)))}
    (hP : IsSylowTwoOf P ⊤) (hPK : P ≤ K) [K.Normal] : K = ⊤ := by
  classical
  let α := Fin (2 ^ m + 1)
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  have hSimple : IsSimpleGroup ↥A := alternatingGroup.isSimpleGroup (by
    change 5 ≤ Nat.card (Fin (2 ^ m + 1))
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥A _ hSimple K inferInstance with hbot | htop
  · exfalso
    have hPbot : P = ⊥ := le_bot_iff.mp (hbot ▸ hPK)
    have h2 : 2 ∣ Nat.card ↥A := by
      change 2 ∣ Nat.card (alternatingGroup (Fin (2 ^ m + 1)))
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h4 : 4 ≤ 2 ^ m + 1 := by
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega
      obtain ⟨k, hk⟩ := Nat.dvd_factorial (by norm_num : 0 < 4) h4
      rw [hk, show 4 * k / 2 = 2 * k by
        rw [show 4 * k = (2 * k) * 2 by ring, Nat.mul_div_cancel _ (by norm_num)]]
      exact dvd_mul_right 2 k
    have hidx : ¬ 2 ∣ P.index := by
      simpa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] using
        hP.2.2
    let P' : Sylow 2 ↥A := hP.2.1.toSylow hidx
    have hcoe : (P' : Subgroup ↥A) = P := IsPGroup.toSylow_coe hP.2.1 hidx
    have hne := Sylow.ne_bot_of_dvd_card P' h2
    rw [hcoe] at hne
    exact hne hPbot
  · exact htop

theorem exists_isUniqueMaxOver_of_mulEquiv_alt {m : ℕ} (hm : 2 ≤ m)
    {Ω : Type*} [Group Ω] [Finite Ω] {L T : Subgroup Ω}
    (e : ↥L ≃* alternatingGroup (Fin (2 ^ m + 1))) (hT : IsSylowTwoOf T L) :
    ∃ B : Subgroup Ω, IsUniqueMaxOver L T B := by
  obtain ⟨B₀, hB₀⟩ := exists_isUniqueMaxOver_alt_model hm
    (isSylowTwoOf_map_subgroupOf e hT)
  exact exists_isUniqueMaxOver_map_of_mulEquiv e hT B₀ hB₀

theorem eq_of_le_normalizer_of_mulEquiv_alt {m : ℕ} (hm : 2 ≤ m)
    {Ω : Type*} [Group Ω] [Finite Ω] {L T : Subgroup Ω}
    (e : ↥L ≃* alternatingGroup (Fin (2 ^ m + 1))) (hT : IsSylowTwoOf T L) {K : Subgroup Ω}
    (hTK : T ≤ K) (hKL : K ≤ L) (hLK : L ≤ Subgroup.normalizer (K : Set Ω)) : K = L :=
  eq_of_le_normalizer_of_mulEquiv e hT
    (fun _ hP _ hPK _hKn => alt_normal_eq_top_of_sylow_le hm hP hPK) hTK hKL hLK

end Alt

end CFSG.GroupTheory
