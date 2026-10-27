module

public import CFSG.Quasithin.H13.L32A58b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A53c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace T53

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.T53.Ctx_F4

variable {T L V V₂ Y : Subgroup G} (C : Ctx_F4 G T L V V₂ Y)
include C

theorem isSolvable_cH_F4 (h4 : Lemma14_7_4_two_three_F4) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    Group.IsSolvable ↥(cH T L V V₂ Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) with hRdef
  have hRQ : pCoreOf 2 (hY T L V₂ Y) = R := C.pCoreOf_hY_eq_F4 h4 hQ
  have hTH : T ≤ hY T L V₂ Y := le_sup_right
  have hRc : R ≤ cH T L V V₂ Y := inf_le_inf_right _ hTH
  have hRn : (R.subgroupOf (cH T L V V₂ Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRc, ← hRQ]
    exact inf_le_left.trans (le_normalizer_pCoreOf 2 _)

  have hsyl : IsSylowIn 2 R (cH T L V V₂ Y) := by
    have hS := C.isSylowTwoOf_T_F4 (K := hY T L V₂ Y) le_sup_right
    have hn : ((cH T L V V₂ Y).subgroupOf (hY T L V₂ Y)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, CFSG.Quasithin.H13.L32A.T53.Ctx.le_normalizer_centralizer_vH le_rfl hg⟩
    have hsub : IsSubnormal (cH T L V V₂ Y) (hY T L V₂ Y) := A4.subnormal_of_normal inf_le_left hn
    have := F6.isSylowIn_inf_of_isSubnormal hsub hS
    have e : T ⊓ cH T L V V₂ Y = R := by
      rw [hRdef, ← inf_assoc, inf_eq_left.mpr hTH]
    rwa [e] at this
  have hR2 : IsPGroup 2 ↥(R.subgroupOf (cH T L V V₂ Y)) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRc).symm
  have : Group.IsNilpotent ↥(R.subgroupOf (cH T L V V₂ Y)) := hR2.isNilpotent
  have hodd : Odd (Nat.card (↥(cH T L V V₂ Y) ⧸ R.subgroupOf (cH T L V V₂ Y))) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.not_even_iff_odd.mp fun he => hsyl.2.2 (even_iff_two_dvd.mp he)
  have : Group.IsSolvable (↥(cH T L V V₂ Y) ⧸ R.subgroupOf (cH T L V V₂ Y)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_subgroup_quotient (R.subgroupOf (cH T L V V₂ Y))

theorem isSolvable_of_le_cH_F4 (h4 : Lemma14_7_4_two_three_F4) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {N : Subgroup G} (hN : N ≤ cH T L V V₂ Y) : Group.IsSolvable ↥N := by
  have := C.isSolvable_cH_F4 h4 hQ
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hN)
    (Subgroup.inclusion_injective hN)

theorem not_le_centralizer_of_mem_cComp_F4 (h4 : Lemma14_7_4_two_three_F4)
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y)) :
    ¬ K ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := fun hKC =>
  not_isSolvable_of_mem_cComp hK (C.isSolvable_of_le_cH_F4 h4 hQ (le_inf (le_of_mem_cComp hK) hKC))

theorem faithful_of_mem_cComp_F4 (h4 : Lemma14_7_4_two_three_F4) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    (h36 : A36ForSQTK) {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y)) :
    quasithinIsFaithfulLocal T K := by
  have hT := C.hyp.fsu.sylow
  have hH : InH ((hT.1.toSylow hT.2 : Sylow 2 G) : Subgroup G) (hY T L V₂ Y) := by
    rw [IsPGroup.toSylow_coe]
    exact ⟨le_sup_right, hQ⟩
  have htfae := lemma_1_2_10_of_a36 C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h36
    (hT.1.toSylow hT.2) hH hK
  have hc : ⁅vH T L V V₂ Y, K⁆ ≠ ⊥ := by
    intro hc
    apply C.not_le_centralizer_of_mem_cComp_F4 h4 hQ hK
    rw [Subgroup.commutator_comm] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have h2 : ∃ W, IsTwoReducedIn (hY T L V₂ Y) W ∧ ⁅W, K⁆ ≠ ⊥ :=
    ⟨vH T L V V₂ Y, C.isTwoReducedIn_vH_F4 hQ, hc⟩
  have h := (htfae.out 2 1).mp h2
  rwa [IsPGroup.toSylow_coe] at h

theorem quot_of_mem_cComp_F4 (h4 : Lemma14_7_4_two_three_F4) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    (h36 : A36ForSQTK) (h1434 : Lemma1434One_F4) {K : Subgroup G}
    (hK : K ∈ cComp (hY T L V₂ Y)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* GL32) := by
  rcases h1434 G T L C.hyp.hyp K (C.faithful_of_mem_cComp_F4 h4 hQ h36 hK) with h5 | h3
  · exact Or.inl h5
  · exact Or.inr (CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 h3)

theorem pCoreOf_eq_of_mem_cComp_F4 (h4 : Lemma14_7_4_two_three_F4) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (hY T L V₂ Y))
    (hiso : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* GL32)) :
    pCoreOf 2 K = K ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ hY T L V₂ Y := le_of_mem_cComp hK
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 K) ?_
    calc pCoreOf 2 K ≤ pCoreOf 2 (hY T L V₂ Y) :=
          A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
      _ = T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) := C.pCoreOf_hY_eq_F4 h4 hQ
      _ ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := inf_le_right
  · set N := K ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) with hNdef
    have hNK : N ≤ K := inf_le_left
    have hNs : Group.IsSolvable ↥N :=
      C.isSolvable_of_le_cH_F4 h4 hQ (inf_le_inf_right _ hKH)
    have hNn : (N.subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNK]
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, CFSG.Quasithin.H13.L32A.T53.Ctx.le_normalizer_centralizer_vH hKH hg⟩
    have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rcases hiso with h5 | h3
      · obtain ⟨e⟩ := h5
        have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
        exact (MulEquiv.isSimpleGroup_congr e).mpr this
      · obtain ⟨e⟩ := h3
        exact G58.isSimpleGroup_of_gl32 e
    have hpn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
    have hmn : ((N.subgroupOf K).map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K).map π) with hb | ht
    · intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥K) ∈ N.subgroupOf K := hx
      have h1 : π ⟨x, hx.1⟩ = 1 := by
        have := Subgroup.mem_map_of_mem π hx'
        rw [hb, Subgroup.mem_bot] at this
        exact this
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (mem_pCore_two_iff' _).mp h1
    · exfalso

      have hNs' : Group.IsSolvable ↥(N.subgroupOf K) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hNK).injective
      have hsurj : Function.Surjective (π.comp (N.subgroupOf K).subtype) := by
        intro q
        have hq : q ∈ (N.subgroupOf K).map π := ht ▸ Subgroup.mem_top q
        obtain ⟨y, hy, rfl⟩ := hq
        exact ⟨⟨y, hy⟩, rfl⟩
      have : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := Group.isSolvable_of_surjective hsurj
      have : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := by
        have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
          rw [CFSG.pCore_eq_open]
          exact CFSG.LieType.BorelTits.pCore_isPGroup 2
        have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := h2.isNilpotent
        infer_instance
      exact not_isSolvable_of_mem_cComp hK
        (Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 ↥K))

end Ctx_F4

end T53

end CFSG.Quasithin.H13.L32A
