module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverPerfectFree

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.QuasithinUnique CFSG.Open
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.HallHigman
open scoped commutatorElement

section Image

variable {W : Type} [Group W] [Finite W]

theorem coverOk_image (L A : Subgroup W) (hs : IsPSolvable 3 ↥A) (hr : Open.pRank 3 A ≤ 1) :
    CoverOk ((A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  classical
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  set X : Subgroup ↥L := A.subgroupOf L with hX
  set ψ : ↥X →* ↥L ⧸ Z := q.comp X.subtype with hψ
  have hrange : ψ.range = X.map q := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ψ.ker ≤ Subgroup.center ↥X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : ↥L) ∈ Z := by
      rw [hψ, MonoidHom.comp_apply, hqdef] at hx
      exact (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxZ (g : ↥L))
  have hrX : Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 1 := by
    have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 3 Nat.prime_three X
    have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three
      (A ⊓ L) L inf_le_right
    rw [Subgroup.inf_subgroupOf_right] at h2
    have h3 := CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt (inf_le_left : A ⊓ L ≤ A)
    rw [h1, hX, h2]
    omega
  refine ⟨fun V hVC hVp h3 => ?_, fun E hEC hel hcard => ?_⟩
  · obtain ⟨W', hW'p, hW'le, hW'map⟩ :=
      CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hVp (hrange ▸ hVC)
    set V' : Subgroup W := (W'.map X.subtype).map L.subtype with hV'
    have hV'A : V' ≤ A := by
      rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact x.2
    have hV'p : ⁅V', V'⁆ = V' := by
      rw [hV', ← Subgroup.map_commutator, ← Subgroup.map_commutator, hW'p]
    have hcard : Nat.card V' = Nat.card W' := by
      rw [hV', Subgroup.card_map_of_injective L.subtype_injective,
        Subgroup.card_map_of_injective X.subtype_injective]
    refine perfectFree_of_pSolvable_pRank_le_one hs hr hV'A hV'p ?_
    rw [hcard]
    refine h3.trans ?_
    rw [← hW'map]
    exact Subgroup.card_map_dvd _ _
  · exact false_of_lift_elemAbelian ψ hrX (hrange ▸ hEC) hel hcard

end Image

section Ctx

variable {W : Type} [Group W] [Finite W]

structure CoverCtx (L S₀ A₁ A₂ : Subgroup W) : Prop where
  syl : IsSylowTwoOf S₀ L
  cov : CoveredByTwo L S₀ A₁ A₂
  ok₁ : CoverOk ((A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
  ok₂ : CoverOk ((A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem exists_conj_borelQuotient {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      (S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) = (posUnipotent D).map π' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSS⟩ := Lie.exists_sylow_of_isSylowTwoOf hS
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  set T : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := S.mapSurjective hqs with hT
  have hTc : (T : Subgroup (↥L ⧸ Subgroup.center ↥L)) = (S : Subgroup ↥L).map q := by
    rw [hT, Sylow.coe_mapSurjective]
  obtain ⟨π', hπ', hker, hTπ⟩ := h.exists_conj_eq T
  refine ⟨π', ⟨h.ct, h.extras, h.pGroup, hπ', h.odd, h.torus_pow,
    fun z hz => h.ker_central z (hker ▸ hz), fun z hz => h.ker_pow z (hker ▸ hz)⟩, ?_⟩
  rw [← hTπ, hTc, hSS]

theorem CoverCtx.cover {L S₀ A₁ A₂ : Subgroup W} (ctx : CoverCtx L S₀ A₁ A₂)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      ∀ i, (rankOne D.rootGroup i).map π' ≤
          (A₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∨
        (rankOne D.rootGroup i).map π' ≤
          (A₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  obtain ⟨π', h', hT⟩ := exists_conj_borelQuotient ctx.syl h
  exact ⟨π', h', fun i => cover_of_borelQuotient ctx.syl ctx.cov h' hT i⟩

theorem CoverCtx.false_of_node {L S₀ A₁ A₂ : Subgroup W} (ctx : CoverCtx L S₀ A₁ A₂)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) {i : Fin D.rank}
    (h3 : HasOrderThree D i)
    (hperf : ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i) : False := by
  obtain ⟨π', h', hcov⟩ := ctx.cover h
  have hker : π'.ker ≤ Subgroup.center K := fun z hz => h'.ker_central z hz
  rcases hcov i with h1 | h1
  · exact false_of_node_perfect ctx.ok₁ h3 hker hperf h1
  · exact false_of_node_perfect ctx.ok₂ h3 hker hperf h1

theorem CoverCtx.false_of_three_nodes {L S₀ A₁ A₂ : Subgroup W} (ctx : CoverCtx L S₀ A₁ A₂)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) (hM : M = 1)
    {exc : Fin D.rank → Fin D.rank → Prop} (hL : TwoLevi D exc)
    (h3 : ∀ i, HasOrderThree D i)
    (hS3 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hexc : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V)
    {i j l : Fin D.rank} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  obtain ⟨π', h', hcov⟩ := ctx.cover h
  have hinj : Function.Injective π' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have := h'.ker_pow z hz
    rw [hM, pow_one] at this
    exact this
  exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.false_of_three_nodes h' hL h3 hS3
    (fun a b hab => by
      obtain ⟨V, hVle, hVp, hV3⟩ := hexc a b hab
      exact ⟨V, hVle, hVp, by rwa [Subgroup.card_map_of_injective hinj]⟩)
    hinj ctx.ok₁ ctx.ok₂ hcov hij hil hjl

end Ctx

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
