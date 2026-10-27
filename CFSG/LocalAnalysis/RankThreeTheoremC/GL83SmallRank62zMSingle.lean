module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1XComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zMSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xLift
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem k631m_faithful {f : ℕ} (hf : f.Prime) {J P N : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hPJ : P ≤ J) (hP : IsPGroup f P) (hPs : ¬ f ∣ (P.subgroupOf J).index)
    (hPc : IsMulCommutative P) (hNJ : J ≤ normalizer (N : Set G)) (hN : ¬ f ∣ Nat.card N)
    {g : G} (hg : g ∈ P) (hc : ∀ j ∈ J, ⁅g, j⁆ ∈ N) : g = 1 := by
  have : Fact f.Prime := ⟨hf⟩
  have hNn : ((N ⊓ J).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact fun j hj => i183_mem_normalizer_inf (hNJ hj) (Subgroup.le_normalizer hj)
  set N' := (N ⊓ J).subgroupOf J with hN'
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJ
  have hK : commutator (↥J ⧸ N') = ⊤ := Group.IsPerfect.commutator_eq_top
  let π : ↥J →* ↥J ⧸ N' := QuotientGroup.mk' N'
  have hPp : IsPGroup f (P.subgroupOf J) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
  have hQp : IsPGroup f ((P.subgroupOf J).map π) := hPp.map π
  have hQi : ¬ f ∣ ((P.subgroupOf J).map π).index := fun hd =>
    hPs (hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hQc : IsMulCommutative ((P.subgroupOf J).map π) := by
    refine IsMulCommutative.of_comm ?_
    rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
    refine Subtype.ext ?_
    have hxy := hPc.is_comm.comm (⟨(x : G), hx⟩ : ↥P) ⟨(y : G), hy⟩
    have hxy1 : (x : G) * y = y * x := congrArg Subtype.val hxy
    have hxy' : x * y = y * x := Subtype.ext hxy1
    show π x * π y = π y * π x
    rw [← map_mul, ← map_mul, hxy']
  have hgJ : g ∈ J := hPJ hg
  set z : ↥J ⧸ N' := QuotientGroup.mk ⟨g, hgJ⟩ with hz
  have hzQ : z ∈ (P.subgroupOf J).map π := ⟨⟨g, hgJ⟩, hg, rfl⟩
  have hzc : z ∈ center (↥J ⧸ N') := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective k
    rw [hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN',
      Subgroup.mem_subgroupOf]
    have hj1 : (j : G)⁻¹ ∈ J := J.inv_mem j.2
    have hcj := N.inv_mem (hc _ hj1)
    have e : (((j * ⟨g, hgJ⟩)⁻¹ * (⟨g, hgJ⟩ * j) : ↥J) : G) =
        g⁻¹ * ⁅g, (j : G)⁻¹⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    refine Subgroup.mem_inf.mpr ⟨k631m_conj_mem (hNJ (J.inv_mem hgJ)) hcj, ?_⟩
    have hcJ : ⁅g, (j : G)⁻¹⁆ ∈ J := by
      simp only [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hgJ hj1) (J.inv_mem hgJ)) (J.inv_mem hj1)
    exact J.mul_mem (J.mul_mem (J.inv_mem hgJ) (J.inv_mem hcJ)) (J.inv_mem (J.inv_mem hgJ))
  have hz1 : z = 1 := by
    by_contra hz1
    obtain ⟨n, hn⟩ := hQp ⟨z, hzQ⟩
    have hzn : z ^ f ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hord : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.mp h1)
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hord
    have hrf : r = f := by
      have h1 : r ∣ f ^ n := hrd.trans (orderOf_dvd_of_pow_eq_one hzn)
      exact (Nat.prime_dvd_prime_iff_eq hr hf).mp (hr.dvd_of_dvd_pow h1)
    have hfd : f ∣ orderOf z := hrf ▸ hrd
    have hfin : orderOf z ≠ 0 := (orderOf_pos z).ne'
    have hwo : orderOf (z ^ (orderOf z / f)) = f := orderOf_pow_orderOf_div hfin hfd
    have hwc : z ^ (orderOf z / f) ∈ center (↥J ⧸ N') := Subgroup.pow_mem _ hzc _
    have hwf : (z ^ (orderOf z / f)) ^ f = 1 := by
      have := pow_orderOf_eq_one (z ^ (orderOf z / f))
      rwa [hwo] at this
    have hw1 := lift62x_center_eq_one hK hf hQp hQi hQc hwc hwf
    rw [hw1, orderOf_one] at hwo
    exact hf.one_lt.ne hwo
  have hgN' : (⟨g, hgJ⟩ : ↥J) ∈ N' := (QuotientGroup.eq_one_iff _).1 hz1
  have hgN : g ∈ N := (Subgroup.mem_inf.mp ((Subgroup.mem_subgroupOf).1 hgN')).1
  exact k631a_eq_one_of_mem_inf hP ((Nat.Prime.coprime_iff_not_dvd hf).2 hN) hg hgN

omit [Finite G] in
theorem k631m_isMulCommutative_of_le {P Q : Subgroup G} (hQ : IsMulCommutative Q) (hPQ : P ≤ Q) :
    IsMulCommutative P :=
  ⟨⟨fun x y => by
    have h := hQ.is_comm.comm ⟨(x : G), hPQ x.2⟩ ⟨(y : G), hPQ y.2⟩
    have h1 : (x : G) * y = y * x := congrArg Subtype.val h
    exact Subtype.ext h1⟩⟩

theorem k631m_single_component {f : ℕ} (hSch : CatalogueRelativeB.CatalogueSchreier)
    {u a : G} {Q J₁ : Subgroup G}
    (hLu : LayerHyp f (centralizer ({u} : Set G)) Q) (hKa : IsKGroup ↥(centralizer ({a} : Set G)))
    (hQs : ¬ f ∣ Q.index) (huQ : u ∈ Q) (hu : u ^ f = 1) (haQ : a ∈ Q)
    (hJ₁ : GLAPComponent f (centralizer ({u} : Set G)) J₁)
    (ha : a ∈ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) :
    ∃ J J₀ : Subgroup G, GLAPComponent f (centralizer ({a} : Set G)) J ∧ J₀ ≤ J ∧ J₀ ≤ J₁ ∧
      Q ⊓ J₁ ≤ J₀ ∧
      ∀ g ∈ Q ⊓ J₁, (∀ j ∈ J₀, ⁅g, j⁆ ∈ GLAPPrimeCoreOf f (centralizer ({a} : Set G))) → g = 1 := by
  have hf : f.Prime := hLu.prime
  have : Fact f.Prime := ⟨hf⟩
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hLu.comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQa : Q ≤ centralizer ({a} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hQcomm a haQ x hx).symm
  have hhyp : k631aHyp f (centralizer ({a} : Set G)) Q :=
    ⟨hf, hLu.ne_two, hKa, hQa, hLu.pgroup,
      fun hd => hQs (hd.trans (Subgroup.relIndex_dvd_index_of_le hQa)), hLu.comm⟩
  have haf : IsPGroup f (zpowers a) := hLu.pgroup.to_le (zpowers_le.mpr haQ)
  obtain ⟨J₀, hJ₀, hJ₀J₁, hJ₀elts⟩ := k631b_exists_J0 hf haf hJ₁ ha
  have hQJ₀ : Q ⊓ J₁ ≤ J₀ := by
    rintro x ⟨hxQ, hxJ⟩
    exact hJ₀elts x hxJ (hQcomm a haQ x hxQ) (hLu.pgroup.to_le (zpowers_le.mpr hxQ))
  have hEX : zpowers u ≤ centralizer ({a} : Set G) := zpowers_le.mpr (hQa huQ)
  have hKa' : CFSG.Open.IsKGroup ↥(centralizer ({a} : Set G)) := fun K L _ _ hs _ =>
    hKa K (L.subgroupOf K) hs
  obtain ⟨𝒞, hC1, hC2, -, hC4⟩ := input18_3_4_of_schreier hSch G (centralizer ({a} : Set G)) hKa' f
    hf (zpowers u) hEX (k631b_isElemAbelian_zpowers hu) J₀ hJ₀
  have hsingle : ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, L = L' := by
    intro L hL L' hL'
    obtain ⟨e, he, rfl⟩ := hC4 L hL L' hL'
    exact (gLBConj_eq_of_mem_normalizer
      (k631a_normalized hhyp (hC1 L hL) ((zpowers_le.mpr huQ) he))).symm
  have hJ₀le : J₀ ≤ ⨆ L ∈ 𝒞, L := by
    rw [hC2]
    refine le_trans (le_of_eq (gLBConj_one J₀).symm) ?_
    exact le_iSup₂ (f := fun (g : G) (_ : g ∈ GLAPLayer f (centralizer ({a} : Set G))) =>
      GLBConj g J₀) (1 : G) (one_mem _)
  have hne : 𝒞.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, le_bot_iff] at hJ₀le
    exact k631m_ne_bot hJ₀ hJ₀le
  obtain ⟨J, hJmem⟩ := hne
  have hJle : (⨆ L ∈ 𝒞, L) ≤ J := iSup₂_le fun L hL => (hsingle L hL J hJmem).le
  have hJC : GLAPComponent f (centralizer ({a} : Set G)) J := hC1 J hJmem
  refine ⟨J, J₀, hJC, hJ₀le.trans hJle, hJ₀J₁, hQJ₀, ?_⟩
  intro g hg hfa
  have hs1 : ¬ f ∣ ((Q ⊓ J₁).subgroupOf J₁).index :=
    k631a_comp_sylow (k631a_hyp_of_layer hLu) hJ₁
  have hs0 : ¬ f ∣ ((Q ⊓ J₁).subgroupOf J₀).index := by
    intro hd
    apply hs1
    have e : (Q ⊓ J₁).relIndex J₀ * J₀.relIndex J₁ = (Q ⊓ J₁).relIndex J₁ :=
      Subgroup.relIndex_mul_relIndex _ _ _ hQJ₀ hJ₀J₁
    exact hd.trans (Dvd.intro _ e)
  exact k631m_faithful hf (glaPComponent_perfect hJ₀) hQJ₀ (hLu.pgroup.to_le inf_le_left) hs0
    (k631m_isMulCommutative_of_le hLu.comm inf_le_left)
    ((hJ₀le.trans hJle).trans (hJC.1.trans (le_normalizer_glaPPrimeCoreOf f _)))
    (not_dvd_card_glaPPrimeCoreOf hf _) hg hfa

end CFSG.LocalAnalysis.RankThreeTheoremC
