module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Base
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Clique

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Twin

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem exists_twin_of_mem_conjClass (s : SettingR r n R S t₀ K K' z u J t W) {M : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) :
    ∃ M' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) M, M' ≠ M := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := s.core.hyp
  have hf := s.data.frame
  obtain ⟨g, hg⟩ := TwinFrame.trans_conjClass _ K hf.mem M hM
  refine ⟨conjSub g K', ?_, ?_⟩
  · have := twinSet_conj hΩ.conjInvariant hf.hK' g
    rwa [hg] at this
  · intro h
    exact hf.hne (Generic.conjSub_injective g (h.trans hg.symm))

theorem twin_mem_omegaOfSet (s : SettingR r n R S t₀ K K' z u J t W) {M M' : Subgroup Y}
    (hM : M ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
      (twinSet (CoreAssembly.conjClass (tightCore R)) K))
    (hM' : M' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) M) (hne : M' ≠ M) :
    M' ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
      (twinSet (CoreAssembly.conjClass (tightCore R)) K) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have hz : IsUniqueInvolution K z := hf.hz
  have hMΩ : M ∈ Ω := hM.1
  obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMΩ
  have hm' : IsUniqueInvolution M' m := isUniqueInvolution_of_mem_twinSet hm hM'
  have hmz : m ≠ z := by
    intro h
    exact not_mem_twinSet_of_mem_omegaOfSet hK hz hM ⟨hMΩ, z, hz, h ▸ hm⟩
  have hnot : M' ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hz''⟩
    exact hmz ((hm'.eq hz'').trans (hz'.eq hz))
  have hKM : K ∈ omegaNbr Ω M :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hMΩ (hM.2 K (mem_twinSet_self hK hz))
  have hKM' : K ∈ KPerp Ω M' := by
    rw [← A7Q.Gen.kPerp_eq_of_twin hΩ hMΩ hM']
    exact Set.mem_insert_of_mem _ hKM
  have hKM'ne : K ≠ M' := by
    intro h
    apply hnot
    rw [← h]
    exact mem_twinSet_self hK hz
  have hKM'nbr : K ∈ omegaNbr Ω M' := (Set.mem_insert_iff.mp hKM').resolve_left hKM'ne
  have hM'K : M' ∈ omegaNbr Ω K :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hM'.1 hK hKM'nbr
  exact A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hK (Set.mem_insert_of_mem _ hM'K) hnot


theorem tightInO2_member (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (s : SettingR r n R S t₀ K K' z u J t W) {M : Subgroup Y} {m : Y}
    (hM : M ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
      (twinSet (CoreAssembly.conjClass (tightCore R)) K))
    (hm : IsUniqueInvolution M m) :
    ∃ hmc : m ∈ Subgroup.centralizer ({z} : Set Y),
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)))
        (⟨m, hmc⟩ : ↥(Subgroup.centralizer ({z} : Set Y)))) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hz : IsUniqueInvolution K z := hf.hz
  have hMtq : M ∈ tqMembers3 Ω z := tq_of_mem_omegaOfSet s hM
  obtain ⟨S₀, hStd₀⟩ := s.core.core
  have hRc : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hMΩ' : M ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc]
    exact hM.1
  obtain ⟨S_M, hStdM⟩ := exists_datum_atR hStd₀ hRc hMΩ' hm
  have hRcM : tightCore M = M := TwinVtx.tightCore_eq_of_mem hRc hMΩ'
  have hcl : CoreAssembly.conjClass M = Ω := TwinVtx.conjClass_eq_of_mem hM.1
  obtain ⟨M', hM'tw, hM'ne⟩ := exists_twin_of_mem_conjClass s hM.1
  have hM'tq : M' ∈ tqMembers3 Ω z :=
    tq_of_mem_omegaOfSet s (twin_mem_omegaOfSet s hM hM'tw hM'ne)
  have hmz : z * m = m * z :=
    commute_involution_of_conjSub_eq hm (mem_normalizer_iff_conjSub_eq.mp hMtq.2.1)
  have hmc : m ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hmz.symm
  refine ⟨hmc, ?_⟩
  exact inO2_cent_of_twin_R h4 hT hStdM hRcM (center_eq_bot_R s.core) hz.sq hz.ne_one
    (mem_centralizerModOdd_of_trivialOnQuot hMtq.2) hmc (K' := M')
    (by rw [hRcM, hcl]; exact hM'tw) (by rw [hRcM]; exact hM'ne) hM'tq.2

end Twin

section Transport

theorem tightInO2_of_cores {C : Type} [Group C] [Finite C] (X : Subgroup C) (x : X)
    (hle : ∀ y ∈ classicalInvolutionOddCore ↥X, (y : C) ∈ classicalInvolutionOddCore C)
    (h : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore C) (x : C))) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x) := by
  classical
  obtain ⟨P, hPn, hP2, hxP⟩ := h
  let ι : (↥X ⧸ classicalInvolutionOddCore ↥X) →* (C ⧸ classicalInvolutionOddCore C) :=
    QuotientGroup.map _ _ X.subtype (fun y hy => hle y hy)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : C) ∈ classicalInvolutionOddCore C := (QuotientGroup.eq_one_iff _).mp hq
      have hnorm : ((classicalInvolutionOddCore C).subgroupOf X).Normal := inferInstance
      have hodd : Odd (Nat.card ↥((classicalInvolutionOddCore C).subgroupOf X)) := by
        have h1 : Nat.card ↥(((classicalInvolutionOddCore C).subgroupOf X).map X.subtype) =
            Nat.card ↥((classicalInvolutionOddCore C).subgroupOf X) :=
          Subgroup.card_map_of_injective X.subtype_injective
        rw [Subgroup.subgroupOf_map_subtype] at h1
        rw [← h1]
        exact (CFSG.ComponentClassification.OddCore.odd_card C).of_dvd_nat
          (Subgroup.card_dvd_of_le inf_le_left)
      have hyN : y ∈ (classicalInvolutionOddCore C).subgroupOf X := hy
      have hle' : (classicalInvolutionOddCore C).subgroupOf X ≤ classicalInvolutionOddCore ↥X :=
        le_sSup ⟨hnorm, hodd⟩
      exact (QuotientGroup.eq_one_iff _).mpr (hle' hyN)
  refine ⟨P.comap ι, hPn.comap ι, hP2.comap_of_injective ι hinj, hxP⟩

end Transport

section SecE2

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem oddCore_coreHull_le' (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hc2 : IsPGroup 2 (Subgroup.zpowers z)) :
    ∀ y ∈ classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) z),
      (y : ↥(Subgroup.centralizer ({z} : Set Y))) ∈
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) := by
  intro y hy
  obtain ⟨y', hy', hyeq⟩ := oddCore_coreHull_le hΩ hc2 hy
  have : y' = (y : ↥(Subgroup.centralizer ({z} : Set Y))) := Subtype.ext hyeq
  rwa [this] at hy'

theorem hinO2_sec (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (s : SettingR r n R S t₀ K K' z u J t W) :
    ∀ L ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) z, ∀ ū,
      IsUniqueInvolution L ū →
      ∃ Q : Subgroup (↥(coreHull (CoreAssembly.conjClass (tightCore R)) z) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) z)),
        Q.Normal ∧ IsPGroup 2 ↥Q ∧ ū ∈ Q := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hz : IsUniqueInvolution K z := hf.hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_uniqueInvolution hz
  intro L hL ū hū
  obtain ⟨M, hM, rfl⟩ := TwinDisc.exists_of_mem_secFam hL
  obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM.1
  obtain ⟨htC, htY, hU⟩ := isUniqueInvolution_secImg hΩ hc2 hM hm
  have hūeq := hū.eq hU
  by_cases hmz : m = z
  ·
    subst hmz
    set e : ↥(coreHull Ω m) ⧸ classicalInvolutionOddCore ↥(coreHull Ω m) :=
      QuotientGroup.mk (⟨⟨m, htC⟩, htY⟩ : ↥(coreHull Ω m)) with he
    have hcomm : ∀ g : ↥(coreHull Ω m) ⧸ classicalInvolutionOddCore ↥(coreHull Ω m),
        g * e = e * g := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [he, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp g.1.2
    have hee : e * e = 1 := by
      have := hU.sq
      exact this
    have hne : e ≠ 1 := hU.ne_one
    refine ⟨Subgroup.zpowers e, ⟨fun n hn g => ?_⟩, isPGroup_zpowers_of_mul_self_eq_one hee hne, ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have h1 : g * e ^ k = e ^ k * g := ((show Commute g e from hcomm g).zpow_right k).eq
      rw [h1, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers e) k
    · rw [hūeq]
      exact Subgroup.mem_zpowers e
  · have hnot : M ∉ twinSet Ω K := by
      rintro ⟨-, z', hz', hz''⟩
      exact hmz ((hm.eq hz'').trans (hz'.eq hz))
    have hMo := mem_omegaOfSet_of_tq_z s hM hnot
    obtain ⟨hmc, hin⟩ := tightInO2_member h4 hT s hMo hm
    obtain ⟨P, hPn, hP2, hxP⟩ := tightInO2_of_cores (coreHull Ω z) ⟨⟨m, htC⟩, htY⟩
      (oddCore_coreHull_le' hΩ hc2) hin
    exact ⟨P, hPn, hP2, hūeq ▸ hxP⟩

end SecE2

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
