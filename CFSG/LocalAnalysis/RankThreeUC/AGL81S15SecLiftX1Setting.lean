module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521SecLiftPart
import CFSG.Quasithin.H13.NQS1312H
import CFSG.Quasithin.H13.LocDblCriterion
import CFSG.Quasithin.H13.NQCatA314ShortMap
import CFSG.Quasithin.Background.SimsD1TransBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSetup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_pow_two_pow_mem_of_mem_normal_sup {L : Subgroup X} (hLn : L.Normal)
    (hT : IsPGroup 2 T) {x : X} (hx : x ∈ L ⊔ T) : ∃ k : ℕ, x ^ 2 ^ k ∈ L := by
  haveI := hLn
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hl1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).2 hl
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.ker_mk' L, MonoidHom.mem_ker, map_pow, map_mul, hl1, one_mul, ← map_pow,
    htk, map_one]

theorem le_of_isShort2_of_normal_sup {L : Subgroup X} (hLn : L.Normal) (hT : IsPGroup 2 T)
    {Y : Subgroup ↥(L ⊔ T)} (hY : IsShort2 Y) : Y ≤ L.subgroupOf (L ⊔ T) := by
  haveI := hLn
  let N : Subgroup ↥Y := (L.subgroupOf (L ⊔ T)).subgroupOf Y
  haveI : N.Normal := Subgroup.normal_subgroupOf
  have h2 : IsPGroup 2 (↥Y ⧸ N) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_normal_sup hLn hT (y : ↥(L ⊔ T)).2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      simpa [N, Subgroup.mem_subgroupOf] using hk
  have hNtop : N = ⊤ := hY.1 N h2
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥Y) ∈ N := hNtop ▸ Subgroup.mem_top _
  simpa [N, Subgroup.mem_subgroupOf] using hmem

theorem noXBlock_sup_of_normal (hX : GNSetting X T) {L : Subgroup X} (hLn : L.Normal) :
    ∀ Y : Subgroup ↥(L ⊔ T), IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hY hB
  haveI := hLn
  have hYL := le_of_isShort2_of_normal_sup hLn hX.sylow.2.1 hB.1
  have h1 : IsSubnormal (Y.map (L ⊔ T).subtype) (L ⊔ T) := by
    have h := IsSubnormal.map (L ⊔ T).subtype hY
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hY'L : Y.map (L ⊔ T).subtype ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hYL hy)
  have h2 : IsSubnormal (Y.map (L ⊔ T).subtype) L := by
    have h := h1.inf_of_le (le_sup_left : L ≤ L ⊔ T)
    rwa [inf_eq_left.2 hY'L] at h
  have hLsub : IsSubnormal L ⊤ :=
    IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
  refine hX.noXBlock _ (h2.trans hLsub) ⟨?_, ?_⟩
  · exact CFSG.QuasithinUnique.Setup.Wreath.IsShort2.map_of_injective _
      (L ⊔ T).subtype_injective hB.1
  · rcases hB.2 with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · exact Or.inl ⟨n, hn,
        CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective' _ (L ⊔ T).subtype_injective h⟩
    · exact Or.inr ⟨n, hn, (CFSG.Quasithin.SimsD1.TransBlock.isAltType_map_iff _
        (L ⊔ T).subtype_injective Y (2 * n + 1)).mpr h⟩

theorem gnSetting_sup_of_normal (hX : GNSetting X T) {L : Subgroup X} (hLn : L.Normal) :
    GNSetting ↥(L ⊔ T) (T.subgroupOf (L ⊔ T)) where
  kGroup := CFSG.IsKGroup.subgroup hX.kGroup (L ⊔ T)
  sylow := CFSG.Quasithin.H13.LocDbl.isSylowTwoOf_subgroupOf_top
    (CFSG.Quasithin.H13.U3.NLine.isSylowTwoOf_of_le_top hX.sylow le_sup_right)
  charTwo := charTwo_top_of_le hX.charTwo
    ((CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans le_sup_right) le_top
  noXBlock := noXBlock_sup_of_normal hX hLn

theorem relIndex_two_pow_of_sup_eq_top {L : Subgroup X} (hT : IsPGroup 2 T) (hLn : L.Normal)
    (htop : L ⊔ T = ⊤) (C : Subgroup X) : ∃ k : ℕ, (L ⊓ C).relIndex C = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hLn
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  have h3 : L.index = L.relIndex T := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_left]
  have hdvd : (L ⊓ C).relIndex C ∣ 2 ^ n := by
    rw [Subgroup.inf_relIndex_right, ← hn]
    exact (Subgroup.relIndex_dvd_index_of_normal L C).trans (h3 ▸ Subgroup.relIndex_dvd_card L T)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

theorem gnA_le_map_normalizer_two_of_sup_eq_top {T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls)
    (hLn : L.Normal) (htop : L ⊔ T = ⊤) :
    gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) :=
  gnA_le_map_normalizer_two_of_relIndex_two_pow hX hg hL hLn
    (relIndex_two_pow_of_sup_eq_top hX.sylow.2.1 hLn htop _)

theorem sup_subgroupOf_sup_eq_top (L T : Subgroup X) :
    L.subgroupOf (L ⊔ T) ⊔ T.subgroupOf (L ⊔ T) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

end CFSG.LocalAnalysis.RankThreeUC.S15
