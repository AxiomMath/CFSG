module

public import CFSG.LocalAnalysis.OddStandard.ONanFusClasses
public import CFSG.LocalAnalysis.OddStandard.ONanSylowTransfer2

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
  CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem xE_sq : xE * xE = zc := by decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem xel_mem : xel v1 v2 v3 ∈ alpP v1 v2 v3 s t := by
  rw [← AlpEmb.φ_xE D.E]
  exact AlpEmb.φ_mem D.E xE

theorem xel_sq : xel v1 v2 v3 * xel v1 v2 v3 = invRep v1 v2 v3 s t 0 := by
  rw [← AlpEmb.φ_xE D.E, ← map_mul, xE_sq, AlpEmb.φ_zc D.E]
  rfl

theorem card_P0 :
    Nat.card ↥(alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G)) = 256 := by
  rw [AlpEmb.inf_centralizer_x_eq D.E D.hF, AlpEmb.card_map D.E, card_subE_max D.hF]

theorem isSylowOf_P0 : IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G))
    (centralizer ({xel v1 v2 v3} : Set G)) := by
  refine isSylowOf_of_card_le D.isSylowOf_P D.xel_mem fun g hg => ?_
  rw [D.card_P0]
  set y := g⁻¹ * xel v1 v2 v3 * g with hy
  have hy2 : y * y ≠ 1 := by
    intro h
    apply D.rep_ne_one 0
    calc invRep v1 v2 v3 s t 0 = g * (y * y) * g⁻¹ := by rw [hy, ← D.xel_sq]; group
      _ = 1 := by rw [h]; group
  have hnc : ¬ alpP v1 v2 v3 s t ≤ centralizer ({y} : Set G) := by
    intro h
    have hc : ∀ c ∈ alpP v1 v2 v3 s t, c * y = y * c := fun c hc =>
      mem_centralizer_singleton_iff.1 (h hc)
    rcases (AlpEmb.centre_alpP D.E D.hF hg).1 hc with h1 | h1
    · apply hy2
      rw [h1, mul_one]
    · apply hy2
      rw [h1]
      exact D.rep_sq 0
  set C := alpP v1 v2 v3 s t ⊓ centralizer ({y} : Set G) with hC
  have h1 := relIndex_mul_card (H := C) (K := alpP v1 v2 v3 s t)
  rw [inf_of_le_left inf_le_left, AlpEmb.card_alpP D.E] at h1
  have hr1 : C.relIndex (alpP v1 v2 v3 s t) ≠ 1 := by
    intro h
    rw [relIndex_eq_one] at h
    exact hnc (le_trans h inf_le_right)
  have hr0 : C.relIndex (alpP v1 v2 v3 s t) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    omega
  have hr2 : 2 ≤ C.relIndex (alpP v1 v2 v3 s t) := by omega
  nlinarith

theorem exists_sylow_quot (hQ : f2QuotCheck = true) :
    ∃ T : Sylow 2 (centralizer ({xel v1 v2 v3} : Set G) ⧸ zpowers (zIn (xel v1 v2 v3))),
      Nonempty (↥(T : Subgroup (centralizer ({xel v1 v2 v3} : Set G) ⧸
        zpowers (zIn (xel v1 v2 v3)))) ≃* SylSL3_4) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x := xel v1 v2 v3 with hx
  set K := centralizer ({x} : Set G) with hK
  set P0 := alpP v1 v2 v3 s t ⊓ K with hP0
  obtain ⟨Q, hQ'⟩ := D.isSylowOf_P0.exists_sylow_eq_subgroupOf
  obtain ⟨ψ, hψs, hψk⟩ := AlpEmb.exists_hom_P0 D.E D.hF hQ
  set N := zpowers (zIn x) with hN
  set π := QuotientGroup.mk' N with hπ
  refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective N), ⟨?_⟩⟩
  have hmemQ : ∀ q : ↥(Q : Subgroup K), ((q : K) : G) ∈ P0 := fun q =>
    Subgroup.mem_subgroupOf.1 ((SetLike.ext_iff.1 hQ' (q : K)).1 q.2)
  let ι : ↥(Q : Subgroup K) →* ↥P0 :=
    { toFun := fun q => ⟨((q : K) : G), hmemQ q⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let χ : ↥(Q : Subgroup K) →* TcM := ψ.comp ι
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨p, hp⟩ := hψs y
    have hpK : (p : G) ∈ K := p.2.2
    have hpQ : (⟨(p : G), hpK⟩ : K) ∈ (Q : Subgroup K) :=
      (SetLike.ext_iff.1 hQ' _).2 (Subgroup.mem_subgroupOf.2 p.2)
    exact ⟨⟨⟨p, hpK⟩, hpQ⟩, hp⟩
  have hmemN : ∀ k : K, k ∈ N ↔ (k : G) ∈ zpowers x := by
    intro k
    rw [hN, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn]; rfl⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by rw [← hn]; rfl)⟩
  have hker : χ.ker = (π.comp (Q : Subgroup K).subtype).ker := by
    ext q
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show ψ (ι q) = 1 ↔ π (q : K) = 1
    rw [hψk, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemN]
    rfl
  have hrange : (Q : Subgroup K).map π = (π.comp (Q : Subgroup K).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [Sylow.coe_mapSurjective]
  exact (MulEquiv.subgroupCongr hrange).trans
    ((QuotientGroup.quotientKerEquivRange _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        ((QuotientGroup.quotientKerEquivOfSurjective χ hχs).trans sylLCongr.symm)))

end FusCtx

end CFSG.OddStandard.ONanRec
