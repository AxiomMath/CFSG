module

public import CFSG.LocalAnalysis.OddStandard.GH71.HBarCent

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71


theorem cover_centralizer_bar (h : Ctx71 G z S U u) {H : Subgroup G} (hSH : S ≤ H)
    (hcov : Covers H (Cen z) (pPrimeCoreOf 2 (Cen z)))
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly) :
    IsDoubleCoverOfAlt ↥(centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H))) 11 := by
  have hzH : z ∈ H := hSH h.ctx.z_mem
  set K := H ⊓ Cen z with hK
  set πM := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z))
  set πH := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let ψ : ↥K →* HBar (Cen z) := πM.comp (Subgroup.inclusion (inf_le_right : K ≤ Cen z))
  let φ : ↥K →* HBar H := πH.comp (Subgroup.inclusion (inf_le_left : K ≤ H))
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hOM : H ⊓ Cen z ≤ normalizer (pPrimeCoreOf 2 (Cen z) : Set G) := fun y hy =>
      le_normalizer_pPrimeCoreOf' _ hy.2
    obtain ⟨a, ha, c, hc, hac⟩ := (covers_iff hOM).mp hcov m hm
    refine ⟨⟨a, ha⟩, ?_⟩
    have hcM : c ∈ Cen z := pPrimeCoreOf_le' _ hc
    have e : (⟨m, hm⟩ : ↥(Cen z)) = ⟨a, ha.2⟩ * ⟨c, hcM⟩ := Subtype.ext hac
    show πM ⟨a, ha.2⟩ = πM ⟨m, hm⟩
    rw [e, map_mul]
    obtain ⟨c', hc', hc'e⟩ := hc
    have : (⟨c, hcM⟩ : ↥(Cen z)) = c' := Subtype.ext hc'e.symm
    have h1 : πM c' = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    rw [this, h1, mul_one]
  have hker : ψ.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show πM ⟨x, x.2.2⟩ = 1 ↔ πH ⟨x, x.2.1⟩ = 1
    constructor
    · intro hx
      have hx' : (⟨x, x.2.2⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
        (QuotientGroup.eq_one_iff _).mp hx
      have hxO : (x : G) ∈ pPrimeCoreOf 2 (Cen z) ⊓ H := ⟨⟨_, hx', rfl⟩, x.2.1⟩
      obtain ⟨y, hy, hye⟩ := h.inf_pPrimeCoreOf_le hSH hbar hxO
      have : (⟨x, x.2.1⟩ : ↥H) = y := Subtype.ext hye.symm
      rw [this]
      exact (QuotientGroup.eq_one_iff _).mpr hy
    · intro hx
      have hx' : (⟨x, x.2.1⟩ : ↥H) ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hx
      have hxO : (x : G) ∈ pPrimeCoreOf 2 H ⊓ Cen z := ⟨⟨_, hx', rfl⟩, x.2.2⟩
      have hle : pPrimeCoreOf 2 H ⊓ Cen z ≤ pPrimeCoreOf 2 (Cen z) := by
        refine le_pPrimeCoreOf_of_covers hcov inf_le_right
          (odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' H)) ?_
        intro y hy
        exact inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pPrimeCoreOf' H hy.1, le_normalizer hy.2⟩
      obtain ⟨y, hy, hye⟩ := hle hxO
      have : (⟨x, x.2.2⟩ : ↥(Cen z)) = y := Subtype.ext hye.symm
      rw [this]
      exact (QuotientGroup.eq_one_iff _).mpr hy
  have hrange : φ.range = centralizer ({zBar H hzH} : Set (HBar H)) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [mem_centralizer_singleton_iff]
      show πH ⟨x, x.2.1⟩ * πH ⟨z, hzH⟩ = πH ⟨z, hzH⟩ * πH ⟨x, x.2.1⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp x.2.2)
    · intro y hy
      obtain ⟨⟨w, hwH⟩, hw, rfl⟩ := centralizer_bar_le hzH h.orderOf_z hy
      exact ⟨⟨w, hwH, Subgroup.mem_subgroupOf.mp hw⟩, rfl⟩
  let e : HBar (Cen z) ≃* ↥(centralizer ({zBar H hzH} : Set (HBar H))) :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)))
  exact L121.isDoubleCoverOfAlt_of_mulEquiv e h.cover

end Ctx71

end CFSG.OddStandard.GH71
