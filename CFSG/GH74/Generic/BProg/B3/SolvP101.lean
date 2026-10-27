module

public import CFSG.GH74.Generic.BProg.B3.SolvP101Comp
public import CFSG.GH74.Generic.BProg.B3.SolvBal513
public import CFSG.GH74.Generic.BProg.B3.SolvKGTable
public import CFSG.GH74.Generic.BProg.B3.SolvStabL34
public import CFSG.GH74.Generic.BProg.B3.SolvAssembly
public import CFSG.GH74.Generic.BProg.B3.ObsPump
public import CFSG.GH74.Generic.BProg.B1.PilotS5

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace SolvP101

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.GH74.GLS.Th2.Bal CFSG.Blueprint
open CFSG.ComponentClassification.Burgoyne (oddCoreIn)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_unstable
    (hyp : Hyp2 G) {x y : G} {K E : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)}
    {I0 I1 : Subgroup G} (hx : orderOf x = 2) (h : SolvAdm x y K E Lb Ib) (hI : SolvLift x y E Lb I0 I1)
    {d e : G} (hd : d ∈ closure ({x, y} : Set G)) (hd1 : d ≠ 1) (he : e ∈ E) (he1 : e ≠ 1)
    (hn : ¬ ⁅I0, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
      pPrimeCoreOf 2 (centralizer ({e} : Set G))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hdd, hdord, heord, hxe, hde, hI1, hI01⟩ := basic_facts hx h hI hd hd1 he he1
  obtain ⟨J, hJ, hdJ, hdfaith, hXeJ, hI1J, hnc⟩ := exists_comp_of_unstable' hx h hI hd hd1 he he1 hn
  set C : Subgroup G := centralizer ({e} : Set G) with hC
  set Xe : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ C with hXe
  set Jb : Subgroup (CentralizerBar e) := (J.subgroupOf C).map (piBar e) with hJb
  have hJbc : IsComponent Jb :=
    ((CFSG.ComponentClassification.PrimeComponentLift.prime_component_minimal_perfect_lift 2).2 _
      hJ.2).2.2
  have hnormiff : ∀ g' : ↥C, g' ∈ normalizer ((J.subgroupOf C : Subgroup ↥C) : Set ↥C) ↔
      (g' : G) ∈ normalizer (J : Set G) := by
    intro g'
    rw [← Subgroup.subgroupOf_normalizer_eq hJ.1]
    rfl
  set Nb : Subgroup (CentralizerBar e) := normalizer (Jb : Set (CentralizerBar e)) with hNb
  have hmapN : ∀ g : G, (hg : g ∈ C) → g ∈ normalizer (J : Set G) → piBar e ⟨g, hg⟩ ∈ Nb :=
    fun g hg hgJ => Subgroup.le_normalizer_map (piBar e) ⟨⟨g, hg⟩, (hnormiff _).2 hgJ, rfl⟩
  set ρ : ↥Nb →* MulAut (↥Jb ⧸ center ↥Jb) := rhoL Jb with hρ
  set B : Subgroup (MulAut (↥Jb ⧸ center ↥Jb)) := ρ.range with hB
  have hInn : (MulAut.conj : (↥Jb ⧸ center ↥Jb) →* MulAut (↥Jb ⧸ center ↥Jb)).range ≤ B :=
    CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp Jb
  have hq : IsQuasisimple ↥Jb := hJbc.1
  have hTgh : GHList (↥Jb ⧸ center ↥Jb) :=
    Generic.ghList_of_quasisimple hyp.simple hyp.nonab hyp.kgh heord hq
  have hTl34 : ¬ LieModel (↥Jb ⧸ center ↥Jb) .PSL 3 2 2 := by
    intro hL
    obtain ⟨eJ⟩ := B1.PilotS5.hat_equiv_imgBar hJ
    exact false_of_isL34Quotient hyp.gen4 heord hJ
      (CFSG.GH74.lieModel_of_mulEquiv (E2.centerQuotientEquiv eJ).symm hL)
  have hKG : SolvKG.KGAut (↥Jb ⧸ center ↥Jb) := SolvKG.kgAut_ghList hq.2.1 hq.2.2 hTgh hTl34
  set d0 : ↥C := ⟨d, hde⟩ with hd0
  have hd0ord : orderOf d0 = 2 := TwoThin.orderOf_mk_centralizer hde hdord
  set dN : ↥Nb := ⟨piBar e d0, hmapN d hde hdJ⟩ with hdN
  set t := ρ dN with ht
  have htB : t ∈ B := ⟨dN, rfl⟩
  have hdN2 : dN ^ 2 = 1 := by
    apply Subtype.ext
    show (piBar e d0) ^ 2 = 1
    rw [← map_pow, pow_two]
    have : d0 * d0 = 1 := Subtype.ext hdd
    rw [this, map_one]
  have ht1 : t ≠ 1 := by
    intro h1
    apply hdfaith
    have hc := (ObsPump.rhoL_eq_one_iff hJbc dN).1 h1
    refine TwoThin.mem_centralizerSection_of_map_eq hJ.1 (TwoThin.isPCompIn_two_iff.mp hJ).2 hde ?_
    intro m hm
    have hmJ : piBar e m ∈ Jb := ⟨m, hm, rfl⟩
    have := hc _ hmJ
    show piBar e (d0 * m * d0⁻¹) = piBar e m
    rw [map_mul, map_mul, map_inv]
    have h' : piBar e d0 * piBar e m = piBar e m * piBar e d0 := this
    rw [h']
    group
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [ht, ← map_pow, hdN2, map_one]) ht1
  have hdNord : orderOf dN = 2 := by
    refine orderOf_eq_prime hdN2 fun h1 => ht1 ?_
    rw [ht, h1, map_one]
  have hI1C : I1 ≤ C := fun i hi => (mem_inf.1 (hI1 hi)).2
  set ι : ↥I1 →* ↥Nb := ((piBar e).comp (Subgroup.inclusion hI1C)).codRestrict Nb
    (fun i => hmapN (i : G) (hI1C i.2) (hI1J i.2)) with hι
  set ψ : ↥I1 →* MulAut (↥Jb ⧸ center ↥Jb) := ρ.comp ι with hψ
  have hψ' : ∀ i, ψ i ∈ B ⊓ centralizer ({t} : Set (MulAut (↥Jb ⧸ center ↥Jb))) := by
    intro i
    refine mem_inf.2 ⟨⟨ι i, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, hψ, MonoidHom.comp_apply, ht, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show piBar e (Subgroup.inclusion hI1C i) * piBar e d0 = piBar e d0 * piBar e (Subgroup.inclusion hI1C i)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hid := (mem_inf.1 (hI1 i.2)).1
    rw [mem_centralizer_singleton_iff] at hid
    exact hid
  set Wn : Subgroup ↥Nb := ((Xe.subgroupOf C).map (piBar e)).comap Nb.subtype with hWn
  have hXeodd : Odd (Nat.card ↥Xe) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (Subgroup.card_dvd_of_le inf_le_left)
  have hWnodd : Odd (Nat.card ↥Wn) := by
    have h1 : Odd (Nat.card ↥(Xe.subgroupOf C)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Xe ≤ C)).toEquiv]
      exact hXeodd
    have h2 : Odd (Nat.card ↥((Xe.subgroupOf C).map (piBar e))) :=
      Odd.of_dvd_nat h1 (Subgroup.card_map_dvd (H := Xe.subgroupOf C) (piBar e))
    have h3 : Nat.card ↥Wn = Nat.card ↥(Wn.map Nb.subtype) :=
      (Subgroup.card_map_of_injective Nb.subtype_injective).symm
    rw [h3]
    exact Odd.of_dvd_nat h2 (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _))
  have hWnC : Wn ≤ centralizer ({dN} : Set ↥Nb) := by
    intro n hn
    obtain ⟨w', hw', hw'n⟩ := hn
    have hw'n' : piBar e w' = (n : CentralizerBar e) := hw'n
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (n : CentralizerBar e) * piBar e d0 = piBar e d0 * (n : CentralizerBar e)
    rw [← hw'n', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hw'd : (w' : G) ∈ centralizer ({d} : Set G) :=
      TwoThin.pPrimeCoreOf_le _ (mem_inf.1 (mem_subgroupOf.1 hw')).1
    rw [mem_centralizer_singleton_iff] at hw'd
    exact hw'd
  have hWnN : ∀ c ∈ centralizer ({dN} : Set ↥Nb), ∀ n ∈ Wn, c * n * c⁻¹ ∈ Wn := by
    intro c hc n hn
    have hcd : (c : CentralizerBar e) ∈ centralizer ({piBar e d0} : Set (CentralizerBar e)) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      exact congrArg Subtype.val hc
    rw [show piBar e d0 = QuotientGroup.mk' (pPrimeCore 2 ↥C) d0 from rfl,
      Balance.centralizer_quotient_eq hd0ord] at hcd
    obtain ⟨c0, hc0, hc0c⟩ := hcd
    obtain ⟨w', hw', hw'n⟩ := hn
    have hw'n' : piBar e w' = (n : CentralizerBar e) := hw'n
    have hc0' : c0 ∈ centralizer ({d0} : Set ↥C) := hc0
    have hc0d : (c0 : G) ∈ centralizer ({d} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc0' ⊢
      exact congrArg Subtype.val hc0'
    refine ⟨c0 * w' * c0⁻¹, mem_subgroupOf.2 (mem_inf.2 ⟨?_, ?_⟩), ?_⟩
    · exact TwoThin.pPrimeCoreOf_normalized _ hc0d (mem_inf.1 (mem_subgroupOf.1 hw')).1
    · exact (c0 * w' * c0⁻¹).2
    · show piBar e (c0 * w' * c0⁻¹) = ((c * n * c⁻¹ : ↥Nb) : CentralizerBar e)
      rw [map_mul, map_mul, map_inv]
      have hc0c' : piBar e c0 = (c : CentralizerBar e) := hc0c
      rw [hc0c', hw'n']
      rfl
  have hWnO : Wn ≤ pPrimeCoreOf 2 (centralizer ({dN} : Set ↥Nb)) :=
    SolvBal.le_pPrimeCoreOf_of_odd' hWnC hWnN hWnodd
  have h519 := SolvBal.map_pPrimeCoreOf_centralizer_le ρ (P := zpowers dN)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdNord, pow_one]))
  rw [MonoidHom.map_zpowers, Balance.centralizer_zpowers_eq, Balance.centralizer_zpowers_eq] at h519
  have hy : ∀ w (hw : w ∈ Xe), ρ ⟨piBar e ⟨w, (mem_inf.1 hw).2⟩, hmapN w _ (hXeJ hw)⟩ ∈ oddCoreIn B t := by
    intro w hw
    have hmem : (⟨piBar e ⟨w, (mem_inf.1 hw).2⟩, hmapN w _ (hXeJ hw)⟩ : ↥Nb) ∈ Wn :=
      ⟨⟨w, (mem_inf.1 hw).2⟩, mem_subgroupOf.2 hw, rfl⟩
    exact h519 ⟨_, hWnO hmem, rfl⟩
  have hcomm : ∀ (w : G) (hw : w ∈ Xe) (i : G) (hi : i ∈ I0),
      ψ ⟨i, hI01 hi⟩ * ρ ⟨piBar e ⟨w, (mem_inf.1 hw).2⟩, hmapN w _ (hXeJ hw)⟩ =
        ρ ⟨piBar e ⟨w, (mem_inf.1 hw).2⟩, hmapN w _ (hXeJ hw)⟩ * ψ ⟨i, hI01 hi⟩ := by
    intro w hw
    set yw := ρ ⟨piBar e ⟨w, (mem_inf.1 hw).2⟩, hmapN w _ (hXeJ hw)⟩ with hyw
    have hS : I0 ≤ ((centralizer ({yw} : Set (MulAut (↥Jb ⧸ center ↥Jb)))).comap ψ).map I1.subtype := by
      rw [← hI.res_I1]
      refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
      refine ⟨⟨v, hv⟩, ?_, rfl⟩
      show ψ ⟨v, hv⟩ ∈ centralizer ({yw} : Set (MulAut (↥Jb ⧸ center ↥Jb)))
      rw [mem_centralizer_singleton_iff]
      obtain ⟨k, hk⟩ := h2
      exact hKG B hInn t htB ht2 ↥I1 hI.sl23 ψ hψ' ⟨v, hv⟩ ⟨k, Subtype.ext hk⟩ yw (hy w hw)
    intro i hi
    obtain ⟨i', hi', hii'⟩ := hS hi
    have : i' = ⟨i, hI01 hi⟩ := Subtype.ext hii'
    rw [← this]
    have hi'' : ψ i' ∈ centralizer ({yw} : Set (MulAut (↥Jb ⧸ center ↥Jb))) := hi'
    rw [mem_centralizer_singleton_iff] at hi''
    exact hi''
  apply hnc
  have hle : ⁅I0, Xe⁆ ≤ ((centralizer (Jb : Set (CentralizerBar e))).comap (piBar e)).map C.subtype := by
    rw [Subgroup.commutator_le]
    intro i hi w hw
    have hiC : i ∈ C := hI1C (hI01 hi)
    have hwC : w ∈ C := (mem_inf.1 hw).2
    refine ⟨⁅(⟨i, hiC⟩ : ↥C), ⟨w, hwC⟩⁆, ?_, rfl⟩
    set iN : ↥Nb := ι ⟨i, hI01 hi⟩ with hiN
    set wN : ↥Nb := ⟨piBar e ⟨w, hwC⟩, hmapN w _ (hXeJ hw)⟩ with hwN
    have h1 : ρ ⁅iN, wN⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm w hw i hi
    have h2 := (ObsPump.rhoL_eq_one_iff hJbc ⁅iN, wN⁆).1 h1
    have h4 : ((⁅iN, wN⁆ : ↥Nb) : CentralizerBar e) = piBar e ⁅(⟨i, hiC⟩ : ↥C), ⟨w, hwC⟩⁆ := by
      rw [map_commutatorElement]
      rfl
    show piBar e ⁅(⟨i, hiC⟩ : ↥C), ⟨w, hwC⟩⁆ ∈ centralizer (Jb : Set (CentralizerBar e))
    rw [mem_centralizer_iff]
    intro z hz
    have h3 := h2 z hz
    rw [h4] at h3
    exact h3.symm
  rintro _ ⟨x0, hx0, rfl⟩ z hz
  obtain ⟨c, hc, hcx⟩ := hle (mem_subgroupOf.1 hx0)
  have : c = x0 := Subtype.ext hcx
  rw [← this]
  exact (mem_centralizer_iff.1 hc z hz).symm

theorem prop10_1_proved
    : Prop10_1Stmt := by
  intro G _ _ hyp x y K E Lb Ib I0 I1 hx _hK h hI d hd hd1 e he he1
  by_contra hn
  exact false_of_unstable hyp hx h hI hd hd1 he he1 hn

theorem stage1NontrivSolv_proved
    : B1.Stage1NontrivSolv :=
  stage1NontrivSolv_of_prop10_1 prop10_1_proved

end SolvP101

end CFSG.GH74.Generic.BProg.B3
