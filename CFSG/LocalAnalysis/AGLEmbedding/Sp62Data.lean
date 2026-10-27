module

public import CFSG.LocalAnalysis.AGLEmbedding.G28Data
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

structure Sp62InSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ V₀ : Subgroup Y) : Prop where
  card_T : Nat.card T = 3 ^ 4
  T_le : T ≤ V₀
  V_le : V₀ ≤ Y₀
  V_perfect : ⁅V₀, V₀⁆ = V₀
  V_normal : Y₀ ≤ Subgroup.normalizer (V₀ : Set Y)
  V_index : V₀.relIndex Y₀ ≤ 2
  V_iso : ∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V₀ →* CatGroup d), IsUFourTwoIndex d ∧
    Function.Bijective ψ
  V_quasi : ∀ W : Subgroup Y, W ≤ Y₀ → V₀ ≤ Subgroup.normalizer (W : Set Y) →
    V₀ ≤ W ∨ ⁅W, V₀⁆ = ⊥
  V_centralizer : Y₀ ⊓ Subgroup.centralizer (V₀ : Set Y) = ⊥
  dichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ V₀ ≤ W
  centralizer_le : Y₀ ⊓ Subgroup.centralizer (T : Set Y) ≤ T

@[expose] def KFactSp62Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [Fact (Nat.Prime 3)] (K : Subgroup Y)
    (d : TauCeti.ValidLieTypeIndex), IsSpSixTwoIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      ¬ HasKlingenData 3 T Y₀ → ∃ V₀ : Subgroup Y, Sp62InSitu (T : Subgroup Y) Y₀ V₀

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Piece

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

theorem u42Piece_of_map_eq {T V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hS : Sp62InSitu T (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      V₀) {V : Subgroup G} (hVK : V ≤ H ⊓ M) (hVV : ⁅V, V⁆ = V)
    (hVmap : (V.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = V₀) :
    U42Piece (H ⊓ M) (GLBPrimeCore 3 H) V := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set N := GLBPrimeCore 3 H with hN
  have hVH : V ≤ H := hVK.trans inf_le_left
  refine ⟨hVV, hVK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hVN
    have hbot : V₀ = ⊥ := by
      rw [← hVmap, eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_bot.mpr ((mem_glbPrimeCore_iff_mk_eq_one (p := 3) v).mp
        (hVN (Subgroup.mem_subgroupOf.mp hv)))
    have hT : T = ⊥ := le_bot_iff.mp (hbot ▸ hS.T_le)
    have hc := hS.card_T
    rw [hT, Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro k hk
    rw [sup_glbPrimeCore_eq_preimage hVH hVmap]
    refine mem_normalizer_comap_map hk.1 (hS.V_normal ?_)
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
  ·
    have hKH : H ⊓ M ≤ H := inf_le_left
    rw [sup_glbPrimeCore_eq_preimage hVH hVmap, ← Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective, Subgroup.relIndex_comap]
    exact hS.V_index
  ·
    obtain ⟨d, ψ₀, hd, hψ₀⟩ := hS.V_iso
    have hθmem : ∀ v : V, π (Subgroup.inclusion hVH v) ∈ V₀ := fun v => by
      rw [← hVmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr v.2)
    let θ : V →* V₀ := (π.comp (Subgroup.inclusion hVH)).codRestrict V₀ hθmem
    have hθ : Function.Surjective θ := by
      intro w
      have hw : (w : H ⧸ primeComplementCore (G := H) 3) ∈ (V.subgroupOf H).map π :=
        hVmap ▸ w.2
      obtain ⟨v, hv, hvw⟩ := hw
      exact ⟨⟨v, Subgroup.mem_subgroupOf.mp hv⟩, Subtype.ext hvw⟩
    refine ⟨d, ψ₀.comp θ, hd, hψ₀.2.comp hθ, ?_⟩
    have hker : (ψ₀.comp θ).ker.map V.subtype ≤ N := by
      rintro _ ⟨v, hv, rfl⟩
      have h1 : ψ₀ (θ v) = ψ₀ 1 := by rw [map_one]; exact hv
      have h2 : θ v = 1 := hψ₀.1 h1
      have h3 : π (Subgroup.inclusion hVH v) = 1 := congrArg Subtype.val h2
      exact (mem_glbPrimeCore_iff_mk_eq_one (p := 3) (Subgroup.inclusion hVH v)).mpr h3
    have hc : Nat.card ((ψ₀.comp θ).ker.map V.subtype) = Nat.card (ψ₀.comp θ).ker :=
      Subgroup.card_map_of_injective V.subtype_injective
    exact Nat.Coprime.coprime_dvd_right (hc ▸ Subgroup.card_dvd_of_le hker)
      (glbPrimeCore_coprime 3 H)
  ·
    intro W hWK hVW
    have hWH : W ≤ H := hWK.trans inf_le_left
    set Wb := (W.subgroupOf H).map π with hWb
    have hWbY : Wb ≤ ((H ⊓ M).subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.comap_mono hWK)
    have hVWb : V₀ ≤ Subgroup.normalizer (Wb : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [← hVmap]
      rintro _ ⟨v, hv, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨v * w * v⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
        exact (Subgroup.mem_normalizer_iff.mp (hVW (Subgroup.mem_subgroupOf.mp hv)) w).mp
          (Subgroup.mem_subgroupOf.mp hw)
      · rintro ⟨w, hw, hwx⟩
        refine ⟨v⁻¹ * w * v, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hVW ((V.subgroupOf H).inv_mem hv : v⁻¹ ∈ _))
            w).mp (Subgroup.mem_subgroupOf.mp hw)
          simpa using this
        · rw [map_mul, map_mul, map_inv, hwx]
          group
    rcases hS.V_quasi Wb hWbY hVWb with h1 | h1
    · left
      exact le_sup_glbPrimeCore_of_map_le hVH (hVmap ▸ h1)
    · right
      rw [Subgroup.commutator_le]
      intro w hw v hv
      have hc : ⁅π ⟨w, hWH hw⟩, π ⟨v, hVH hv⟩⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator
          (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hw : (⟨w, hWH hw⟩ : H) ∈ _))
          (hVmap ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hv :
            (⟨v, hVH hv⟩ : H) ∈ V.subgroupOf H) : π ⟨v, hVH hv⟩ ∈ V₀)
        rw [h1, Subgroup.mem_bot] at this
        exact this
      have := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⁅(⟨w, hWH hw⟩ : H), ⟨v, hVH hv⟩⁆).mpr
        (by rw [map_commutatorElement]; exact hc)
      simpa [commutatorElement_def] using this
  ·
    intro g hgK hgV
    have hgH : g ∈ H := hgK.1
    have hgC : π ⟨g, hgH⟩ ∈ ((H ⊓ M).subgroupOf H).map π ⊓
        Subgroup.centralizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      refine ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hgK), ?_⟩
      show π ⟨g, hgH⟩ ∈ Subgroup.centralizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3))
      rw [Subgroup.mem_centralizer_iff, ← hVmap]
      rintro _ ⟨v, hv, rfl⟩
      have h1 := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) (⟨g, hgH⟩ * v * ⟨g, hgH⟩⁻¹ * v⁻¹)).mp
        (by simpa using hgV v (Subgroup.mem_subgroupOf.mp hv))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hS.V_centralizer, Subgroup.mem_bot] at hgC
    exact (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⟨g, hgH⟩).mpr hgC

end Piece

end CFSG.AGLEmbedding
