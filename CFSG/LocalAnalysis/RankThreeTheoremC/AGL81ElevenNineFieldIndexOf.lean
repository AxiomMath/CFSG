module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenNine
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeReduceKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding.ParabPrime Subgroup
open CFSG.HardMathSupport.Curtis.Coordinator CFSG.HardMathSupport.Cooperstein.Proving
open scoped commutatorElement

theorem exists_inv_mul_mem_of_not_dvd_relIndex {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [hp : Fact p.Prime] {C J S B : Subgroup Y} [C.Normal] (hS : ¬ p ∣ S.relIndex J)
    (hB : IsPGroup p B) (hSB : S ≤ B) (hBJ : B ≤ J ⊔ C) : ∀ g ∈ B, ∃ s ∈ S, s⁻¹ * g ∈ C := by
  set f := QuotientGroup.mk' C
  have hC : C.map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have h1 : B.map f ≤ J.map f := by
    have := Subgroup.map_mono (f := f) hBJ
    rwa [Subgroup.map_sup, hC, sup_bot_eq] at this
  have h2 : S.map f ≤ B.map f := Subgroup.map_mono hSB
  have h3 : ¬ p ∣ (S.map f).relIndex (J.map f) := by
    rw [← Subgroup.relIndex_comap]
    exact fun hd => hS (hd.trans (Subgroup.relIndex_dvd_of_le_left J (Subgroup.le_comap_map f S)))
  obtain ⟨n, hn⟩ := (hB.map f).index ((S.map f).subgroupOf (B.map f))
  have h5 := Subgroup.relIndex_mul_relIndex (S.map f) (B.map f) (J.map f) h2 h1
  have h6 : (S.map f).relIndex (B.map f) = 1 := by
    have hn' : (S.map f).relIndex (B.map f) = p ^ n := hn
    rcases n with _ | n
    · simpa using hn'
    · refine absurd ?_ h3
      rw [← h5, hn']
      exact (dvd_pow_self p (Nat.succ_ne_zero n)).mul_right _
  have h7 : B.map f ≤ S.map f := Subgroup.relIndex_eq_one.mp h6
  intro g hg
  obtain ⟨s, hs, hsg⟩ := h7 (Subgroup.mem_map_of_mem f hg)
  exact ⟨s, hs, QuotientGroup.eq.mp hsg⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_mul_mem_of_not_dvd_relIndex' {p : ℕ} [Fact p.Prime]
    {Y C J S B : Subgroup G} (hCY : C ≤ Y) (hJY : J ≤ Y) (hBY : B ≤ Y)
    (hCn : (C.subgroupOf Y).Normal) (hS : ¬ p ∣ S.relIndex J) (hB : IsPGroup p B) (hSB : S ≤ B)
    (hBJ : B ≤ J ⊔ C) : ∀ g ∈ B, ∃ s ∈ S, s⁻¹ * g ∈ C := by
  have hS' : ¬ p ∣ (S.subgroupOf Y).relIndex (J.subgroupOf Y) := by
    rwa [Subgroup.relIndex_subgroupOf hJY]
  have hB' : IsPGroup p (B.subgroupOf Y) := hB.comap_subtype
  have hSB' : S.subgroupOf Y ≤ B.subgroupOf Y := fun x hx => hSB hx
  have hBJ' : B.subgroupOf Y ≤ J.subgroupOf Y ⊔ C.subgroupOf Y := by
    rw [← Subgroup.subgroupOf_sup hJY hCY]
    exact fun x hx => hBJ hx
  intro g hg
  obtain ⟨s, hs, hsg⟩ := exists_inv_mul_mem_of_not_dvd_relIndex hS' hB' hSB' hBJ'
    ⟨g, hBY hg⟩ hg
  exact ⟨s, hs, hsg⟩

theorem centModTwo_normal (J : Subgroup G) :
    ((RankOne.centModTwo J).subgroupOf (Subgroup.normalizer (J : Set G))).Normal := by
  refine ⟨fun c hc n => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hc ⊢
  have hn := n.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine RankOne.mem_centModTwo (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn c.2)
    (Subgroup.inv_mem _ hn)) fun x hx => ?_
  have hy : (n : G)⁻¹ * x * n ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
    simpa using this
  have h1 := RankOne.comm_of_mem_centModTwo hc _ hy
  have hO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hn
  have h2 := (Subgroup.mem_normalizer_iff.mp hO _).mp h1
  have e : (n : G) * c * (n : G)⁻¹ * x * ((n : G) * c * (n : G)⁻¹)⁻¹ * x⁻¹ =
      (n : G) * ((c : G) * ((n : G)⁻¹ * x * n) * (c : G)⁻¹ * ((n : G)⁻¹ * x * n)⁻¹) *
        (n : G)⁻¹ := by
    group
  rw [e]
  exact h2

theorem AGL81ElevenNineData.split_of_inner {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {L W : Subgroup G} {a₀ : G}
    (hd : AGL81ElevenNineData p P M H Q K L W a₀) {j : G} (hj : j ∈ jZero H L)
    (hjy : ∀ y ∈ jZero H L, ⁅j⁻¹ * a₀, y⁆ ∈ pCoreOf 2 (jZero H L)) :
    ∀ g ∈ Subgroup.zpowers a₀ ⊔ (W ⊓ jZero H L), ∃ u ∈ W ⊓ jZero H L,
      ∀ y ∈ jZero H L, ⁅u⁻¹ * g, y⁆ ∈ pCoreOf 2 (jZero H L) := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
  haveI : Fact p.Prime := ⟨hesc.prime⟩
  set J := jZero H L with hJdef
  set Y := Subgroup.normalizer (J : Set G)
  obtain ⟨hWp, hWHM, hWmax⟩ := hd.sylow
  have hHMY : H ⊓ M ≤ Y := (RankOne.le_normalizer_inf hd.normal).trans (le_normalizer_jZero H L)
  have hJHM : J ≤ H ⊓ M := (jZero_le H L).trans
    (le_inf inf_le_left (inf_le_right.trans hd.block.toIsTwoPrimeComponent.le))
  have hWsyl : CFSG.ABGLocalTools.IsSylowOf p W (H ⊓ M) := by
    obtain ⟨Q', hQ'⟩ := (hWp.comap_subtype (K := H ⊓ M)).exists_le_sylow
    refine ⟨Q', hWmax _ (Q'.isPGroup'.map _) (Subgroup.map_subtype_le _) fun w hw => ?_⟩
    exact ⟨⟨w, hWHM hw⟩, hQ' (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  have hWJ := hWsyl.inf_of_le_normalizer hJHM hHMY
  have hidx : ¬ p ∣ (W ⊓ J).relIndex J :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hWJ).2.2
  have ha₀W := hd.mem
  have hBW : Subgroup.zpowers a₀ ⊔ (W ⊓ J) ≤ W :=
    sup_le (Subgroup.zpowers_le.mpr ha₀W) inf_le_left
  have hCY : RankOne.centModTwo J ⊓ Y ≤ Y := inf_le_right
  have hCn : ((RankOne.centModTwo J ⊓ Y).subgroupOf Y).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact centModTwo_normal J
  have hjY : j ∈ Y := Subgroup.le_normalizer hj
  have ha₀Y : a₀ ∈ Y := hHMY (hWHM ha₀W)
  have hjY' : j⁻¹ * a₀ ∈ Y := Y.mul_mem (Y.inv_mem hjY) ha₀Y
  have hjC : j⁻¹ * a₀ ∈ RankOne.centModTwo J ⊓ Y := ⟨RankOne.mem_centModTwo hjY'
    fun x hx => by
      have := hjy x hx
      rwa [commutatorElement_def] at this, hjY'⟩
  have hBJ : Subgroup.zpowers a₀ ⊔ (W ⊓ J) ≤ J ⊔ (RankOne.centModTwo J ⊓ Y) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (inf_le_right.trans le_sup_left)
    have e : a₀ = j * (j⁻¹ * a₀) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hj hjC
  have hsplit := exists_inv_mul_mem_of_not_dvd_relIndex' hCY Subgroup.le_normalizer
    (hBW.trans (hWHM.trans hHMY)) hCn hidx (hWp.to_le hBW) le_sup_right hBJ
  intro g hg
  obtain ⟨u, hu, hug⟩ := hsplit g hg
  refine ⟨u, hu, fun y hy => ?_⟩
  rw [commutatorElement_def]
  exact RankOne.comm_of_mem_centModTwo hug.1 y hy

theorem hasNormalIndex_of_quotient {M : Subgroup G} {p : ℕ}
    {N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hN : N.Normal) (hNi : N.index = p) :
    HasNormalIndex M p := by
  set f := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have he : ((N.comap f).map M.subtype).subgroupOf M = N.comap f :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  refine ⟨(N.comap f).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [he]
    exact hN.comap f
  · rw [he, Subgroup.index_comap_of_surjective N (QuotientGroup.mk'_surjective _)]
    exact hNi

end CFSG.LocalAnalysis.RankThreeTheoremC
