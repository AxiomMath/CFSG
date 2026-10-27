module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCfg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxPConstr
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem kx_exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {A T : Subgroup G}
    (hT : IsPGroup p T) (hAT : A < T) :
    ∃ x ∈ T, x ∈ Subgroup.normalizer (A : Set G) ∧ x ∉ A := by
  have hne : A.subgroupOf T ≠ ⊤ := fun htop =>
    absurd (fun x hxT => (Subgroup.mem_subgroupOf.mp (htop ▸ trivial : (⟨x, hxT⟩ : T) ∈
      A.subgroupOf T))) (not_le_of_gt hAT)
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hlt : A.subgroupOf T < Subgroup.normalizer ((A.subgroupOf T : Subgroup T) : Set T) :=
    hnc _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, ?_, fun hxA => hxnot (Subgroup.mem_subgroupOf.mpr hxA)⟩
  have hxsub : x ∈ (Subgroup.normalizer (A : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hAT.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem dvd_card_of_isPGroup_ne_bot {f : ℕ} [Fact f.Prime] {E : Subgroup G} (hE : IsPGroup f E)
    (h1 : E ≠ ⊥) : f ∣ Nat.card E :=
  hE.card_eq_or_dvd.resolve_left fun h => h1 (Subgroup.card_eq_one.mp h)

theorem le_of_stronglyEmbedded_of_inf_ne_bot {f : ℕ} [Fact f.Prime] {M E : Subgroup G}
    (hs : GLBStronglyEmbedded f M) (hE : IsPGroup f E) (hEM : E ⊓ M ≠ ⊥) : E ≤ M := by
  by_contra hnot
  have hlt : E ⊓ M < E := lt_of_le_of_ne inf_le_left (fun h => hnot (h ▸ inf_le_right))
  obtain ⟨x, hxE, hxN, hxn⟩ := kx_exists_mem_normalizer_not_mem_of_lt hE hlt
  have hdvd : f ∣ Nat.card (E ⊓ M : Subgroup G) :=
    dvd_card_of_isPGroup_ne_bot (hE.to_inf_left) hEM
  exact hxn ⟨hxE, normalizer_le_of_stronglyEmbedded hs inf_le_right hdvd hxN⟩

theorem normalizer_le_of_stronglyEmbedded_sub {f : ℕ} [Fact f.Prime] {M E S₀ : Subgroup G}
    (hs : GLBStronglyEmbedded f M) (hE : IsPGroup f E) (hEM : E ⊓ M ≠ ⊥) (hS₀E : S₀ ≤ E)
    (hS₀ : S₀ ≠ ⊥) : normalizer (S₀ : Set G) ≤ M :=
  normalizer_le_of_stronglyEmbedded hs (hS₀E.trans (le_of_stronglyEmbedded_of_inf_ne_bot hs hE hEM))
    (dvd_card_of_isPGroup_ne_bot (hE.to_le hS₀E) hS₀)

theorem exists_isSylowOf_ge {f : ℕ} [Fact f.Prime] {L X : Subgroup G} (hXL : X ≤ L)
    (hX : IsPGroup f X) : ∃ E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf f E L ∧ X ≤ E := by
  have hX' : IsPGroup f (X.subgroupOf L) := hX.comap_subtype
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  refine ⟨(Q : Subgroup L).map L.subtype, ⟨Q, rfl⟩, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hXL]
  exact Subgroup.map_mono hQ

theorem dvd_relIndex_of_mem_sdiff {p : ℕ} [Fact p.Prime] {H N : Subgroup G}
    (hs : S622IsSimpleSection H N) {z : G} (hzH : z ∈ H) (hzN : z ∉ N) (hzp : z ^ p = 1) :
    p ∣ N.relIndex H := by
  haveI hNn : (N.subgroupOf H).Normal := hs.2.1
  set z' : ↥H := ⟨z, hzH⟩ with hz'
  have hq1 : (QuotientGroup.mk z' : ↥H ⧸ N.subgroupOf H) ≠ 1 := by
    intro h
    exact hzN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hqp : (QuotientGroup.mk z' : ↥H ⧸ N.subgroupOf H) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : z' ^ p = 1 := Subtype.ext (by simpa using hzp)
    rw [this]
    rfl
  have hord : orderOf (QuotientGroup.mk z' : ↥H ⧸ N.subgroupOf H) = p := orderOf_eq_prime hqp hq1
  have : orderOf (QuotientGroup.mk z' : ↥H ⧸ N.subgroupOf H) ∣
      Nat.card (↥H ⧸ N.subgroupOf H) := orderOf_dvd_natCard _
  rw [hord] at this
  exact this

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem stronglyEmbedded (hL613 : L613) (c : KxCfg p P M x z T S L) {H N : Subgroup G}
    (hHL : H ≤ L) (hHM : H ≤ M) (hs : S622IsSimpleSection H N) (hzH : z ∈ H) (hzN : z ∉ N)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) (hfd : f ∣ N.relIndex H) :
    GLBStronglyEmbedded f M := by
  haveI : Fact p.Prime := ⟨c.conf.config.prime⟩
  have hS := c.conf.config.situation
  have hx := c.conf.config.point
  have hz := c.conf.config.central
  have hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp hz.centralizes g hg
  have hnpc := not_isPConstrained_of_section P hS.sylow_le hz.mem hzc hz.pow_eq_one hHM hs hzH hzN
  have hpd : p ∣ N.relIndex H := dvd_relIndex_of_mem_sdiff hs hzH hzN hz.pow_eq_one
  exact hL613 G p P M x z hS hx hz hnpc H N (le_inf hHM (hHL.trans c.le_C)) hs hpd f hf hf2 hfp hfd

end KxCfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
