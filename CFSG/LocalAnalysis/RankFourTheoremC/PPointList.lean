module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCentral
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsPPoint.catalogSimpleSections {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
    (hS : D1Global G) (hp : p.Prime) (h : IsPPoint p P M x) :
    CatalogSimpleSections (RedCent p x) := by
  have hx1 : x ≠ 1 := by
    intro hx
    have := h.elem.2.1
    rw [hx, orderOf_one] at this
    exact hp.one_lt.ne this
  have hC : centralizer ({x} : Set G) ≠ ⊤ := by
    intro htop
    have hxz : x ∈ center G := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({x} : Set G) := htop ▸ mem_top g
      exact mem_centralizer_singleton_iff.mp this
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hb | ht
    · exact hx1 (by simpa [hb] using hxz)
    · obtain ⟨a, b, hab⟩ := hS.nonab
      exact hab ((mem_center_iff.mp (ht ▸ mem_top a) b).symm)
  exact (catalogSimpleSections_of_isKProper hS.kProper _ hC).quotient _

namespace PPointReduced

variable {p : ℕ} {M : Subgroup G} {x : G} {R : Sylow p (RedCent p x)}
  {K : Subgroup (RedCent p x)}

theorem center_eq_bot [Fact p.Prime] (hp2 : p ≠ 2) (h24 : GL83ComponentPCoreTrivial)
    (hcat : CatalogSimpleSections (RedCent p x)) (h : PPointReduced p M x R K) :
    center K = ⊥ := by
  have hpc : CFSG.pCore p K = ⊥ := h24 (RedCent p x) hcat p R K Fact.out hp2
    h.red.three_le_pRank h.component fun hle => h.not_le (hle.trans h.red.weakCore_le)
  have hZp : IsPGroup p (center K) := by
    intro z
    have hzK : ((z : K) : RedCent p x) ∈ K ⊓ centralizer (K : Set (RedCent p x)) := by
      refine ⟨(z : K).2, mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨k, hk⟩)
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := RedCent p x))
      ⟨_, inf_centralizer_le_pCore h.red.core_eq_bot h.normal hzK⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hle : center K ≤ CFSG.pCore p K := le_sSup ⟨inferInstance, hZp⟩
  rw [hpc] at hle
  exact le_bot_iff.mp hle

theorem exists_type [Fact p.Prime] (hp2 : p ≠ 2) (h24 : GL83NongenerationList)
    (hcat : CatalogSimpleSections (RedCent p x)) (h : PPointReduced p M x R K)
    {z : RedCent p x} (hz : z ∈ center (RedCent p x)) (hzp : orderOf z = p) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ⧸ center K ≃* i.Group) ∧ GL83Type24 p i ∧
      (GL83OuterType24 p i ∨ ∀ g ∈ (R : Subgroup (RedCent p x)), g ^ p = 1 →
        g ∈ K ⊔ centralizer (K : Set (RedCent p x))) := by
  refine h24 (RedCent p x) hcat p R K Fact.out hp2 h.red.three_le_pRank h.component h.normal ?_
    fun hle => h.not_le (hle.trans h.fullCore)
  have hz1 : z ≠ 1 := by
    intro hz1
    rw [hz1, orderOf_one] at hzp
    exact (Fact.out : p.Prime).one_lt.ne hzp
  intro hbot
  have hzR : z ∈ (R : Subgroup (RedCent p x)) ⊓ centralizer (K : Set (RedCent p x)) :=
    ⟨mem_sylow_of_mem_center hz hzp R, mem_centralizer_iff.mpr fun k _ => mem_center_iff.mp hz k⟩
  rw [hbot] at hzR
  exact hz1 (mem_bot.mp hzR)

theorem exists_equiv_type [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hcat : CatalogSimpleSections (RedCent p x))
    (h : PPointReduced p M x R K) {z : RedCent p x} (hz : z ∈ center (RedCent p x))
    (hzp : orderOf z = p) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ≃* i.Group) ∧ GL83Type24 p i ∧
      (GL83OuterType24 p i ∨ ∀ g ∈ (R : Subgroup (RedCent p x)), g ^ p = 1 →
        g ∈ K ⊔ centralizer (K : Set (RedCent p x))) := by
  obtain ⟨i, ⟨e⟩, hi, hio⟩ := h.exists_type hp2 h244 hcat hz hzp
  have hZ := h.center_eq_bot hp2 h243 hcat
  exact ⟨i, ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩, hi, hio⟩

end PPointReduced

end CFSG.LocalAnalysis.RankFourTheoremC
