module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Ctx
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE.Statement
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Apply
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSignalizer

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

open scoped Pointwise in
theorem pt_sylow_abelian [Fact p.Prime] (hl : PtPoint p P M x) (Q : Sylow p G) :
    IsMulCommutative (Q : Subgroup G) := by
  have hPab := hl.abel
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hmem : ∀ y : G, y ∈ ((g • P : Sylow p G) : Subgroup G) ↔
      g⁻¹ * y * g ∈ (P : Subgroup G) := fun y => by
    change y ∈ MulAut.conj g • (P : Subgroup G) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := hPab.is_comm.comm ⟨_, (hmem a).mp a.2⟩ ⟨_, (hmem b).mp b.2⟩
  have h2 : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := congrArg Subtype.val h
  have h3 : g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ =
      g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h2]
  simpa [mul_assoc] using h3

theorem pt_pGroup_abelian [Fact p.Prime] (hl : PtPoint p P M x) :
    ∀ Q : Subgroup G, IsPGroup p Q → IsMulCommutative Q := by
  intro Q hQ
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hSab := pt_sylow_abelian hl S
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := hSab.is_comm.comm ⟨a, hQS a.2⟩ ⟨b, hQS b.2⟩
  have h2 := congrArg Subtype.val h
  exact h2

theorem pt_pRank_bot {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) :
    Open.pRank q (⊥ : Subgroup X) = 0 := by
  obtain ⟨E, hE, -, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained q hq (⊥ : Subgroup X)
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hEcard
  by_contra hne
  have := Nat.one_lt_pow hne hq.one_lt
  omega

theorem pt_data_abelian [Fact p.Prime] (hIA : KFactInnerAction) (h715 : GL83.I_7_13_1)
    (hKe : KEStatement) (hG : FrobGlobal G) (hl : PtPoint p P M x) :
    ∃ (n : ℕ) (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)),
      PPointReduced p M x R K ∧ Nonempty (K ≃* PSL(2, GaloisField p n)) ∧ 3 ≤ n ∧
      IsPGroup p (centralizer (K : Set (RedCent p x))) ∧
      IsCyclic (centralizer (K : Set (RedCent p x))) ∧
      (R : Subgroup (RedCent p x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
          (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  have hS : D1Global G := ⟨hG.simple, hG.nonab, hG.kProper, hG.charTwo, hG.rank, hG.pre⟩
  haveI : IsSimpleGroup G := hG.simple
  obtain ⟨R, K, hRK, hReq⟩ := hl.point.exists_pPointReduced hG.fullCore hl.loc
  obtain ⟨hzc, hzp⟩ := hl.point.central_xbar hl.loc
  have hcatC := hl.point.catalogSimpleSections hS hp
  have hpg := hRK.isPGroup_centralizer hzc hzp
  have hcyc := hRK.isCyclic_centralizer hzc hzp
  haveI hKn : K.Normal := hRK.normal
  have hab := isMulCommutative_sylow_quotient (p := p) (N := centralizer ({x} : Set G))
    (pt_pGroup_abelian hl)
  have hRab : IsMulCommutative (R : Subgroup (RedCent p x)) := hab R
  have hZ : center K = ⊥ :=
    GL83Generic5MComp.center_eq_bot_of_isComponentOf_of_abelian hRK.red.core_eq_bot hab
      hRK.component
  have hquot : IsSimpleGroup (↥K ⧸ center ↥K) := hRK.component.2.2.2
  have eK : ↥K ≃* (↥K ⧸ center ↥K) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hsimple : IsSimpleGroup ↥K := by
    haveI := hquot
    exact MulEquiv.isSimpleGroup eK
  have hnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab'⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
        K hRK.component.2.2
    refine ⟨eK.symm a, eK.symm b, fun h => hab' ?_⟩
    have := congrArg eK h
    simpa using this
  have hcatK : IsCatalogGroup ↥K := hcatC.simple_subgroup K hsimple hnonab
  obtain ⟨S, hSmap⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hSR : ∀ g ∈ (S : Subgroup ↥K), (g : RedCent p x) ∈ (R : Subgroup (RedCent p x)) := by
    intro g hg
    have : (g : RedCent p x) ∈ (S : Subgroup ↥K).map K.subtype := ⟨g, hg, rfl⟩
    rw [hSmap] at this
    exact this.1
  have hSab : IsMulCommutative (S : Subgroup ↥K) := by
    have := hRab
    exact IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (setLike_mul_comm (hSR a a.2) (hSR b b.2)))
  have hP4 : 4 ≤ Open.pRank p (P : Subgroup G) := four_le_pRank_sylow hl.loc.beta P
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro g hg
    rw [mem_centralizer_singleton_iff]
    have h := hl.abel.is_comm.comm (⟨x, hl.point.mem⟩ : (P : Subgroup G)) ⟨g, hg⟩
    exact (congrArg Subtype.val h).symm
  have hQ4 : 4 ≤ Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) := by
    rw [inf_eq_left.mpr hPC]
    exact hP4
  have hOcop : p.Coprime (Nat.card (primeComplementCore (G := centralizer ({x} : Set G)) p)) :=
    primeComplementCore_coprime p
  have hC4 : 4 ≤ Open.pRank p (R : Subgroup (RedCent p x)) := by
    rw [hReq, pRank_map_mk_eq_pRank_map_subtype hp
      (primeComplementCore (G := centralizer ({x} : Set G)) p) hOcop,
      map_subgroupOf_eq_of_le (inf_le_right : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤
        centralizer ({x} : Set G))]
    exact hQ4
  have hrank3 : 3 ≤ Open.pRank p (⊤ : Subgroup (MulAut ↥K)) := by
    have := pRank_le_one_add_pRank_mulAut hp hcyc (R : Subgroup (RedCent p x))
    omega
  have hKrank2 : 2 ≤ Open.pRank p (⊤ : Subgroup ↥K) := by
    by_contra hlt
    have hle : Open.pRank p (⊤ : Subgroup ↥K) ≤ 1 := by omega
    have := (h715 p hp hp2 ↥K hsimple hnonab hcatK hle).2
    omega
  have hSrank : Open.pRank p (S : Subgroup ↥K) = Open.pRank p (⊤ : Subgroup ↥K) :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp S
  have hSne : (S : Subgroup ↥K) ≠ ⊥ := by
    intro hbot
    rw [hbot, pt_pRank_bot hp] at hSrank
    omega
  have hψinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) :=
    conj_injective_of_center_eq_bot hZ
  have hS3 : 3 ≤ Open.pRank p (S : Subgroup ↥K) := by
    obtain ⟨E, hER, hEel, hEcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (R : Subgroup (RedCent p x))
    have himg :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank
        p hp (MulAut.conjNormal : RedCent p x →* MulAut ↥K) hEel _ hEcard
    have hker : (MulAut.conjNormal : RedCent p x →* MulAut ↥K).ker =
        centralizer (K : Set (RedCent p x)) := by
      ext g
      exact mem_ker_conjNormal
    rw [hker] at himg
    have h1 : Open.pRank p (centralizer (K : Set (RedCent p x))) ≤ 1 :=
      pRank_le_one_of_isCyclic hp hcyc
    have hle : E.map (MulAut.conjNormal : RedCent p x →* MulAut ↥K) ≤
        (S : Subgroup ↥K).map (MulAut.conj : ↥K →* MulAut ↥K) := by
      rintro _ ⟨r, hrE, rfl⟩
      have hrp : r ^ p = 1 := hEel.2 r hrE
      obtain ⟨g, hgS, hg⟩ := hIA p hp hp2 ↥K hsimple hnonab hcatK S hSne hSab
        (MulAut.conjNormal r) ⟨1, by rw [pow_one, ← map_pow, hrp, map_one]⟩
        (fun g hg => by
          rw [← MulAut.conjNormal_val, ← map_mul, ← map_mul]
          congr 1
          exact setLike_mul_comm (hER hrE) (hSR g hg))
      exact ⟨g, hgS, hg.symm⟩
    have h3 := CFSG.SectionRank.pRank_mono hp.one_lt hle
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _ hψinj] at h3
    omega
  have hnc : ¬ IsCyclic ((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x)) := by
    rw [← hSmap]
    intro hc
    have h1 := pRank_le_one_of_isCyclic hp hc
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
      K.subtype_injective] at h1
    omega
  have hzR := mem_sylow_of_mem_center hzc hzp R
  have hzK : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ ∉ K := by
    intro hzK
    have hz1 := GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer hZ hzK
      (mem_centralizer_iff.mpr fun k _ => mem_center_iff.mp hzc k)
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hzcK : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ ∈ centralizer (K : Set (RedCent p x)) :=
    mem_centralizer_iff.mpr fun k _ => mem_center_iff.mp hzc k
  obtain ⟨hN, hKX₀⟩ := hRK.red.rankOne_principle hRK.component hnc hzR hzK hzp hzcK
  have hΓ : GLBCore p 1 (S : Subgroup ↥K) ≠ ⊤ := by
    refine kc_glbCore_ne_top (H := (redCentM p M x ⊓ K).subgroupOf K) ?_ ?_
    · intro htop
      refine hRK.not_le fun k hk => ?_
      have : (⟨k, hk⟩ : ↥K) ∈ (redCentM p M x ⊓ K).subgroupOf K := htop ▸ mem_top _
      exact (mem_subgroupOf.mp this).1
    · intro Q hQS hQ1
      intro n hn
      have hU : Q.map K.subtype ≤ (R : Subgroup (RedCent p x)) ⊓ K := by
        rw [← hSmap]
        exact Subgroup.map_mono hQS
      have hU1 : Q.map K.subtype ≠ ⊥ := by
        intro hbot
        have hQbot : Q = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective Q K.subtype_injective).mp hbot
        rw [hQbot, pt_pRank_bot hp] at hQ1
        omega
      have hnorm : (n : RedCent p x) ∈ K ⊓ normalizer
          ((Q.map K.subtype : Subgroup (RedCent p x)) : Set (RedCent p x)) :=
        ⟨n.2, Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩⟩
      exact mem_subgroupOf.mpr ⟨hN _ hU hU1 hnorm, n.2⟩
  obtain ⟨n, hn3, ⟨e⟩⟩ := hKe ↥K hsimple hnonab hcatK p hl.p5 S hSab hS3 hΓ
  exact ⟨n, R, K, hRK, ⟨e⟩, hn3, hpg, hcyc, hReq⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
