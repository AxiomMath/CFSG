module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem perfectSectionsAltSqC_of_le (hc : D1IbAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hJ : J ≤ barM M (H ⊓ M)) : PerfectSectionsAltSqC p J := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hc.normal_K
  intro V hVJ hVp
  set B := barM M (H ⊓ M)
  obtain ⟨θ, hθk, hθ⟩ := exists_barM_hom_of hc.phase
  have hVB : V ≤ B := hVJ.trans hJ
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hCn : C.Normal := Subgroup.normal_centralizer
  set θV : ↥V →* H ⧸ primeComplementCore (G := H) p := θ.comp (Subgroup.inclusion hVB)
  have hUp : ⁅θV.range, θV.range⁆ = θV.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    have h1 : ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⊤ := by
      apply Subgroup.map_injective V.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hVp]
    exact h1
  have hUX : θV.range ≤ d1X0 p M H := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨m, hm, hmx⟩ := hVB v.2
    have hmA := Subgroup.mem_subgroupOf.mp hm
    have hx : Subgroup.inclusion hVB v = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmx ▸ hVB v.2⟩ :=
      Subtype.ext hmx.symm
    change θ (Subgroup.inclusion hVB v) ∈ _
    rw [hx, hθ m hmA.1]
    exact ⟨⟨m, hmA.1⟩, Subgroup.mem_subgroupOf.mpr hmA, rfl⟩
  have hUKC : θV.range ≤ K ⊔ C :=
    le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hUp) hc.out
  set ρ := QuotientGroup.mk' K
  set g := ρ.comp θV
  set N := g.ker
  set σ := QuotientGroup.mk' C
  set f₀ := σ.comp θV
  obtain ⟨T₁, hT₁, -⟩ := hc.data.exists_sylow
  set Γ := GLBCore p 1 (T₁ : Subgroup K)
  have hKX := hc.inf_d1X0_eq hT₁
  set ψ : ↥Γ →* (H ⧸ primeComplementCore (G := H) p) ⧸ C := σ.comp (K.subtype.comp Γ.subtype)
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun k hk1 => ?_
    have hkC : ((k : K) : H ⧸ primeComplementCore (G := H) p) ∈ C :=
      (QuotientGroup.eq_one_iff _).mp hk1
    have hmem : ((k : K) : H ⧸ primeComplementCore (G := H) p) ∈ K ⊓ C := ⟨(k : K).2, hkC⟩
    rw [hc.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have hf₀ψ : f₀.range ≤ ψ.range := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨k, hk, c, hcC, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp (hUKC ⟨v, rfl⟩)
    have hkX : k ∈ d1X0 p M H := by
      have h1 := (d1X0 p M H).mul_mem (hUX ⟨v, rfl⟩)
        ((d1X0 p M H).inv_mem (hc.centralizer_le_d1X0 hcC))
      rwa [← hkc, mul_inv_cancel_right] at h1
    obtain ⟨γ, hγ, hγk⟩ : k ∈ Γ.map K.subtype := hKX ▸ ⟨hk, hkX⟩
    refine ⟨⟨γ, hγ⟩, ?_⟩
    change σ (γ : H ⧸ primeComplementCore (G := H) p) = σ (θV v)
    have hc1 : σ c = 1 := (QuotientGroup.eq_one_iff c).mpr hcC
    rw [← hkc, map_mul, hc1, mul_one]
    exact congrArg σ hγk
  set V' : Subgroup ↥Γ := f₀.range.comap ψ
  have hV'map : V'.map ψ = f₀.range := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun x hx => ?_
    obtain ⟨γ, hγ⟩ := hf₀ψ hx
    exact ⟨γ, show ψ γ ∈ f₀.range from hγ ▸ hx, hγ⟩
  have hf₀p : ⁅f₀.range, f₀.range⁆ = f₀.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective V.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hVp]
  have hV'p : ⁅V', V'⁆ = V' :=
    Subgroup.map_injective hψ (by rw [Subgroup.map_commutator, hV'map, hf₀p])
  obtain ⟨f₁, hf₁⟩ := (hΓ (↥K) p hp hc.five_le hc.alt T₁).2 V' hV'p
  let e : ↥V' ≃* ↥f₀.range :=
    (V'.equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr hV'map)
  set f := f₁.comp (e.symm.toMonoidHom.comp f₀.rangeRestrict)
  have hfker : f.ker = f₀.ker := by
    ext v
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      have h1 := hf₁ (h.trans (map_one f₁).symm)
      have h2 : f₀.rangeRestrict v = 1 := by
        have := congrArg e h1
        simpa using this
      exact congrArg Subtype.val h2
    · intro h
      have h2 : f₀.rangeRestrict v = 1 := Subtype.ext h
      rw [h2, map_one, map_one]
  refine ⟨N, inferInstance, ?_, f, ?_⟩
  ·
    rw [Subgroup.index_ker]
    refine not_sq_dvd_of_card_le fun Q hQ hQp => ?_
    set ι : ↥C →* (H ⧸ primeComplementCore (G := H) p) ⧸ K := ρ.comp C.subtype
    have hι : Function.Injective ι := by
      refine (injective_iff_map_eq_one ι).mpr fun c hc1 => ?_
      have hcK : (c : H ⧸ primeComplementCore (G := H) p) ∈ K := (QuotientGroup.eq_one_iff _).mp hc1
      have hmem : (c : H ⧸ primeComplementCore (G := H) p) ∈ K ⊓ C := ⟨hcK, c.2⟩
      rw [hc.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hQι : Q ≤ ι.range := by
      intro x hx
      obtain ⟨v, rfl⟩ := hQ hx
      obtain ⟨k, hk, c, hcC, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp (hUKC ⟨v, rfl⟩)
      refine ⟨⟨c, hcC⟩, ?_⟩
      change ρ c = ρ (θV v)
      have hk1 : ρ k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      rw [← hkc, map_mul, hk1, one_mul]
    set Q' := Q.comap ι
    have hQ'map : Q'.map ι = Q := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun x hx => ?_
      obtain ⟨c, hc'⟩ := hQι hx
      exact ⟨c, show ι c ∈ Q from hc' ▸ hx, hc'⟩
    have hQ'p : IsPGroup p Q' := hQp.comap_of_injective ι hι
    have h1 := D1OneSmallData.card_le_of_le_centralizer hc.data hc.card_R_le
      (Subgroup.map_subtype_le Q') (hQ'p.map C.subtype)
    rw [Subgroup.card_map_of_injective C.subtype_injective] at h1
    rw [← hQ'map, Subgroup.card_map_of_injective hι]
    exact h1
  ·
    have hle : f.ker ⊓ N ≤ θV.ker := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
      rw [hfker, MonoidHom.mem_ker] at hv1
      rw [MonoidHom.mem_ker] at hv2 ⊢
      have hC' : θV v ∈ C := (QuotientGroup.eq_one_iff _).mp hv1
      have hK' : θV v ∈ K := (QuotientGroup.eq_one_iff _).mp hv2
      have hmem : θV v ∈ K ⊓ C := ⟨hK', hC'⟩
      rwa [hc.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    have hθV : θV.ker.map (Subgroup.inclusion hVB) ≤ θ.ker := by
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    have h1 : Nat.card θV.ker ∣ Nat.card θ.ker := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hVB)]
      exact Subgroup.card_dvd_of_le hθV
    exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hle).trans h1) hθk

theorem perfectSectionsAltSqC_block (hc : D1IbAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    PerfectSectionsAltSqC p (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := by
  refine hc.perfectSectionsAltSqC_of_le hΓ (barM_mono ?_)
  rw [hc.phase.normalizer_twoCore_H]
  exact inf_le_inf_left H hL.le

end D1IbAltConfig

end CFSG.AGLEmbedding
