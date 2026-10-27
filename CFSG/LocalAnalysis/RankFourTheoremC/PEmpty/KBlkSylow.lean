module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkStep
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkQS
public import CFSG.CGT.PushingUp.ResidualTwo
public import CFSG.CGT.PushingUpLit.BlocksCommuteCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkSL2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_inf_of_isSubnormal' {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) {H : Subgroup X}
    (hH : H.IsSubnormal) : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

theorem isSylowTwoOf_inf_block {N S Y : Subgroup G} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S N)
    (hY : IsBlockOfInX N Y) : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ Y) Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSN, hS2, hSi⟩ := hS
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf N) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, hS2.comap_subtype, by rw [Subgroup.relIndex_top_right]; exact hSi⟩
  have key := isSylowOf_inf_of_isSubnormal' hP hY.2.1
  have e : S.subgroupOf N ⊓ Y.subgroupOf N = (S ⊓ Y).subgroupOf N :=
    (Subgroup.comap_inf _ _ _).symm
  rw [e] at key
  have h2 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N).2 key
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 (inf_le_right.trans hY.1), inf_eq_left.2 hY.1] at h2
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h2
  exact h2

theorem pCoreOf_block_le {N S Y : Subgroup G} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S N)
    (hY : IsBlockOfInX N Y) : pCoreOf 2 Y ≤ S := by
  have hYN := hY.1
  have h1 : oTwoIn (Y.subgroupOf N) = (Y.subgroupOf N) ⊓ CFSG.pCore 2 ↥N :=
    oTwoIn_eq_inf_pCore hY.2.1
  have h2 : pCoreOf 2 Y = (oTwoIn (Y.subgroupOf N)).map N.subtype := by
    have hp := CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hYN)
    show (CFSG.pCore 2 ↥Y).map Y.subtype = _
    rw [← hp, oTwoIn_eq_map, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h2, h1]
  refine le_trans (Subgroup.map_mono inf_le_right) ?_
  exact pCoreOf_le_of_isSylowTwoOf hS

theorem block_le_of_normalizes {N S Y : Subgroup G} {z : G} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S N)
    (hNp : ¬ p ∣ Nat.card N) (hY : IsBlockOfInX N Y) (hzS : z ∈ normalizer (S : Set G))
    (hzp : z ^ p = 1) (hzY : z ∈ normalizer (Y : Set G)) :
    Y ≤ S ⊔ (N ⊓ centralizer ({z} : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set H : Subgroup G := S ⊔ (N ⊓ centralizer ({z} : Set G)) with hH
  let σ : MulAut ↥Y := Y.normalizerMonoidHom ⟨z, hzY⟩
  have hσ : ∀ y : ↥Y, ((σ y : ↥Y) : G) = z * y * z⁻¹ := fun y => rfl
  have hσp : σ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨z, hzY⟩ : ↥(normalizer (Y : Set G))) ^ p = 1 := Subtype.ext (by simpa using hzp)
    rw [this, map_one]
  set N' : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hN'
  have hN : ∀ n ∈ N', σ n ∈ N' := by
    intro n hn
    have hfix := (inferInstance : (CFSG.pCore 2 ↥Y).Characteristic).fixed σ
    have : n ∈ (CFSG.pCore 2 ↥Y).comap σ.toMonoidHom := by rw [hfix]; exact hn
    exact Subgroup.mem_comap.mp this
  have hcopY : ¬ p ∣ Nat.card Y := fun h => hNp (h.trans (Subgroup.card_dvd_of_le hY.1))
  have hcopN' : ¬ p ∣ Nat.card N' := fun h => hcopY (h.trans (Subgroup.card_subgroup_dvd_card N'))
  have hO2 : pCoreOf 2 Y ≤ S := pCoreOf_block_le hS hY
  have hN'S : ∀ n ∈ N', (n : G) ∈ S := fun n hn => hO2 ⟨n, hn, rfl⟩
  have hfixmem : ∀ c : ↥Y, σ c = c → (c : G) ∈ N ⊓ centralizer ({z} : Set G) := by
    intro c hc
    refine ⟨hY.1 c.2, ?_⟩
    have h1 := hσ c
    rw [hc] at h1
    show (c : G) ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c : G) * z = (z * c * z⁻¹) * z := by rw [← h1]
      _ = z * c := by group
  rcases hY.2.2.2 with ⟨n, hn1, hnat⟩ | ⟨n, hn1, hnat⟩
  ·
    obtain ⟨φ, -⟩ := hnat
    have hm : (2 * n + 1) = 3 ∨ 5 ≤ 2 * n + 1 := by omega
    have h1 := quotAut_eq_one_alt hp hp5 σ hσp N' hN hcopY hm φ
    intro g hg
    set y : ↥Y := ⟨g, hg⟩
    have hy : quotAut σ N' hN (y : ↥Y ⧸ N') = (y : ↥Y ⧸ N') := by rw [h1]; rfl
    obtain ⟨c, hcσ, hcy⟩ := exists_fixed_of_quotAut_fixed σ hσp N' hN hcopN' y hy
    have hn' : c⁻¹ * y ∈ N' := by simpa using N'.inv_mem hcy
    have hg' : g = (c : G) * ((c⁻¹ * y : ↥Y) : G) := by simp [y]
    rw [hg']
    exact H.mul_mem (Subgroup.mem_sup_right (hfixmem c hcσ))
      (Subgroup.mem_sup_left (hN'S _ hn'))
  ·
    have hn2 : 2 ≤ n := by
      by_contra h
      have h1 : n = 1 := by omega
      subst h1
      exact CFSG.CGT.PushingUp.not_isNaturalSLTwoModule_one hY.2.2.1 hnat
    obtain ⟨φ, -⟩ := hnat
    have hK := benderType_of_sl hn2 φ
    have hTfin := isSylowTwoOf_inf_block hS hY
    set T : Subgroup ↥Y := (S ⊓ Y).subgroupOf Y with hT
    have hNT : N' ≤ T := fun n hn => Subgroup.mem_subgroupOf.mpr ⟨hN'S n hn, n.2⟩
    have hTσ : ∀ t ∈ T, σ t ∈ T := by
      intro t ht
      have htS : (t : G) ∈ S := (Subgroup.mem_subgroupOf.mp ht).1
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, (σ t).2⟩
      rw [hσ]
      exact (Subgroup.mem_normalizer_iff.mp hzS t).mp htS
    have hcl := closure_fixed_sup_sylow hp hp2 σ hσp N' hN hcopY hK T hNT
      hTfin.2.1.comap_subtype hTfin.2.2 hTσ
    have hsub : ({c : ↥Y | σ c = c} ∪ (T : Set ↥Y)) ⊆ (H.subgroupOf Y : Set ↥Y) := by
      rintro c (hc | hc)
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (hfixmem c hc))
      · exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hc).1)
    intro g hg
    have hmem : (⟨g, hg⟩ : ↥Y) ∈ Subgroup.closure ({c : ↥Y | σ c = c} ∪ (T : Set ↥Y)) := by
      rw [hcl]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.closure_le _).mpr hsub hmem)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
