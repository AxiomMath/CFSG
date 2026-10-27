module

public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Red

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

abbrev Red (X : Type) [Group X] : Type := X ⧸ primeComplementCore (G := X) 3

abbrev pr (X : Type) [Group X] : X →* Red X := QuotientGroup.mk' (primeComplementCore (G := X) 3)

section

variable {X : Type} [Group X] [Finite X]

theorem core_red : primeComplementCore (G := Red X) 3 = ⊥ :=
  primeComplementCore_quotient_eq_bot 3

theorem catalog_red (h : CFSG.AGLEmbedding.CatalogSimpleSections X) :
    CFSG.AGLEmbedding.CatalogSimpleSections (Red X) :=
  h.quotient _

theorem not_dvd_core : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)

theorem ker_pr : (pr X).ker = primeComplementCore (G := X) 3 :=
  QuotientGroup.ker_mk' _

theorem inf_core_eq_bot {S : Subgroup X} (hS : IsPGroup 3 S) :
    S ⊓ primeComplementCore (G := X) 3 = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd not_dvd_core hS

theorem injOn_pr {S : Subgroup X} (hS : IsPGroup 3 S) {a b : X} (ha : a ∈ S) (hb : b ∈ S)
    (h : pr X a = pr X b) : a = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (G := X) (p := 3)
    (N := primeComplementCore (G := X) 3) not_dvd_core hS
  have := @hinj ⟨a, ha⟩ ⟨b, hb⟩ h
  exact congrArg Subtype.val this

theorem card_map {S : Subgroup X} (hS : IsPGroup 3 S) :
    Nat.card (S.map (pr X)) = Nat.card S := by
  refine (Nat.card_eq_of_bijective
    (fun s : S => (⟨pr X s, ⟨s, s.2, rfl⟩⟩ : S.map (pr X))) ⟨?_, ?_⟩).symm
  · intro a b h
    exact Subtype.ext (injOn_pr hS a.2 b.2 (congrArg Subtype.val h))
  · rintro ⟨_, ⟨s, hs, rfl⟩⟩
    exact ⟨⟨s, hs⟩, rfl⟩

theorem sylow_map {S : Subgroup X} (hS : IsSylowOf 3 S ⊤) : IsSylowOf 3 (S.map (pr X)) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp hS
  refine isSylowOf_iff.mpr ⟨le_top, hp.map (pr X), ?_⟩
  rw [Subgroup.relIndex_top_right] at hidx ⊢
  exact fun h => hidx (h.trans (Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective _)))

theorem isPGroup_zpowers {u : X} {n : ℕ} (h : u ^ 3 ^ n = 1) : IsPGroup 3 (zpowers u) := by
  intro g
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp g.2
  refine ⟨n, Subtype.ext ?_⟩
  show (g : X) ^ 3 ^ n = 1
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem lift_centralizer {u : X} {n : ℕ} (h : u ^ 3 ^ n = 1) {y : Red X}
    (hy : y * pr X u = pr X u * y) : ∃ c : X, c * u = u * c ∧ pr X c = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcent := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (G := X) (p := 3)
    (N := primeComplementCore (G := X) 3) not_dvd_core (isPGroup_zpowers h)
  have hyc : y ∈ centralizer (((zpowers u).map (pr X) : Subgroup (Red X)) : Set (Red X)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    rw [map_zpow]
    exact (Commute.zpow_left (show Commute (pr X u) y from hy.symm) i).eq
  rw [hcent] at hyc
  obtain ⟨c, hc, rfl⟩ := hyc
  exact ⟨c, (mem_centralizer_iff.mp hc u (mem_zpowers u)).symm, rfl⟩

end

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Red
