module

public import CFSG.GH74.Generic.BProg.B2.SDRGamma
public import CFSG.GH74.Generic.BProg.B2.SDRComp
public import CFSG.GH74.Generic.BProg.B2.Prop111
public import CFSG.GH74.Generic.BProg.B2.T3Rank
public import CFSG.GH74.Generic.BProg.B2.Thm2Basic
public import CFSG.GH74.GLS.C3.Layer1.PU3Thm5
public import CFSG.GH74.GLS.C3.Layer1.PU3Struct

public section

namespace CFSG.GH74.Generic.BProg.B2.SDR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B2
  CFSG.GH74.Uniqueness CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

@[expose] def Stage2SDRankC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    K ≤ M → Q ≤ M → Stage2Concl2C M → B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → IsMinSubnormalIn K M H →
      barIn M H = barIn M K → pRank 2 (CMbar M K) ≤ 1

theorem sdRank_of_core (hC : Stage2SDRankC) (hT2 : Stage2Thm2C) {G : Type} [Group G] [Finite G] {x : G}
    {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (h3 : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)) (hc1 : barIn M H = barIn M K) :
    pRank 2 (CMbar M K) ≤ 1 :=
  hC G x K A M P Q H hs h1.K_le h1.Q_le (hT2 G x K A M P Q H hs h1) h3 h1.H_min hc1

variable {G : Type} [Group G] [Finite G]

section PU3Device

open CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.PU3

theorem good_of_data {K M Q L : Subgroup G} (hKM : K ≤ M) (hQ : IsSylowOf 2 Q (CMbar M K))
    (hLcomp : IsPCompIn 2 M L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K) (hgam : gammaK 2 Q 1 ≤ M)
    (hKL : K ≤ L) (hsimp : IsSimpleGroup (kBar L)) (hnab : ∃ a b : kBar L, a * b ≠ b * a)
    (hrk : 2 ≤ pRank 2 ↥L) {m : G} (hm : m ∈ M) (hne : cj m L ≠ L) : Good M L := by
  refine ⟨hLcomp, ?_, ?_, hsimp, hnab, hrk⟩
  · intro R hRL hR2 hR1
    exact Th2.PU3Q.normalizer_le_of_le_L hLcomp (isSubnormalIn_of_comp hLcomp) hLeq hQ hgam hm hne
      hRL hR2 hR1
  · intro s hsM hs2 hsc
    have hsC : s ∈ CMbar M K := Th2.HY.mem_CMbar_of_comm hKM hsM (fun k hk => hsc k (hKL hk))
    have hzC : zpowers s ≤ CMbar M K := Subgroup.zpowers_le.2 hsC
    have hzp : IsPGroup 2 ↥(zpowers s) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2]; simp)
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hs2
      omega
    have hz1 : zpowers s ≠ ⊥ := fun h => hs1 (Subgroup.zpowers_eq_bot.1 h)
    exact (centralizer_singleton_le_normalizer_zpowers s).trans
      (Th2.PU3Q.normalizer_le_of_le_cmbar hQ hgam hzC hzp hz1)

theorem normal_of_pu3
    (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a) (hGen : Gen4 G) {K M Q L : Subgroup G}
    (hmax : IsCoatom M) (hKM : K ≤ M) (hQ : IsSylowOf 2 Q (CMbar M K)) (hL : IsMinSubnormalIn K M L)
    (hLcomp : IsPCompIn 2 M L) (hLeq : L = pPrimeCoreOf 2 L ⊔ K) (hgam : gammaK 2 Q 1 ≤ M)
    (hsimp : IsSimpleGroup (kBar L)) (hnab : ∃ a b : kBar L, a * b ≠ b * a) (hrk : 2 ≤ pRank 2 ↥L)
    (hOut : Group.IsSolvable (Outer (kBar L))) : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
  intro m hm l hl
  by_contra hml
  have hne : cj m L ≠ L := by
    intro heq
    have : m * l * m⁻¹ ∈ cj m L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
    rw [heq] at this
    exact hml this
  have hg1 : Good M L := good_of_data hKM hQ hLcomp hLeq hgam hL.1 hsimp hnab hrk hm hne
  have hcjM : cj m M = M := C3.Layer1.Thm1.map_conj_eq_self_of_mem hm
  have hg2 : Good M (cj m L) := by
    have := hg1.conj m
    rwa [hcjM] at this
  have hne' : L ≠ cj m L := fun h => hne h.symm
  have hOut₂ : Group.IsSolvable (Outer (kBar (cj m L))) := by
    have := hOut
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (Th2.Obs.kBarConjEquiv m L)
  have hcfg : Cfg M L (cj m L) :=
    ⟨hmax, hg1, hg2, hne', fun L' hL' => only_of_good hGen hg1 hg2 hne' hL',
      ⟨m, hm, rfl⟩, perf_of_good hGen hg1 hg2 hne' ⟨m, hm, rfl⟩ hOut hOut₂⟩
  exact cfg_false hG hnon hcfg
    (fun _ _ hX hcov => covering hcfg hX hcov) (fun _ _ hX hcov => covering hcfg.symm hX hcov)

end PU3Device

theorem stage2SDRankC :
    Stage2SDRankC := by
  intro G _ _ x K A M P Q H hs hKM hQM h2 h3 hH hc1
  by_contra hcon
  have h2' : Stage2Concl2 M := h2.toConcl2
  have hsyl : IsSylowOf 2 Q (CMbar M K) := T3Rank.isSylowOf_CMbar hs hKM hH hc1
  have hQ2 : 2 ≤ pRank 2 ↥Q := by
    rw [← Thm2Comp.pRank_eq_pRank_sylow hsyl]; omega
  have hJ : ∀ y ∈ Q, orderOf y = 2 → centralizer ({y} : Set G) ≤ M := fun y hy hy2 =>
    centralizer_le_M_of_mem_Q hs hKM hQM h2' hy hy2
  have hgam : gammaK 2 Q 1 ≤ M := gammaK_le_of_thm2C h2 hQM hsyl.isPGroup hJ
  obtain ⟨hcomp, hLeq⟩ := isPCompIn_of_c1 hs hKM hH hc1
  obtain ⟨hsimp, hnab, hrk, hOut⟩ :=
    kBar_data_of_shape3 hH.1 hLeq (TwoThin.isQuasisimple_hat hs.pair.1.1.1.2.2) h3.qShape3
  have hnorm := normal_of_pu3 hs.hyp.simple hs.hyp.nonab hs.hyp.gen4 hs.maxM hKM hsyl hH hcomp hLeq hgam
    hsimp hnab hrk hOut
  have hQ' : IsSylowOf 2 Q (CMK M H) := by rw [CMK_eq_CMbar hH.1 hcomp hc1 hnorm]; exact hsyl
  obtain ⟨T, hT, hQT⟩ : ∃ T : Subgroup G, IsSylowOf 2 T M ∧ Q ≤ T := by
    obtain ⟨S, hS⟩ := (hsyl.isPGroup.comap_subtype (K := M)).exists_le_sylow
    refine ⟨(S : Subgroup M).map M.subtype, ⟨S, rfl⟩, fun q hq => ?_⟩
    exact ⟨⟨q, hQM hq⟩, hS hq, rfl⟩
  obtain ⟨g, hg, hgr⟩ := C3.Layer1.exists_conj_inter_rank_two_normal hs.hyp.simple hs.hyp.nonab
    hs.maxM.1 hcomp.1 hnorm hsimp hnab hQ' hT hQT hQ2 hgam
  exact false_of_conj_inter h2 hQM hJ hg hgr

end CFSG.GH74.Generic.BProg.B2.SDR
