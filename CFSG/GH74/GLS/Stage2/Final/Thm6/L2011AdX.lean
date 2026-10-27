module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdH
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdBarPerf
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdPair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mkH_of_orderOf {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx2 : orderOf x = 2) :
    orderOf (mkH H ⟨x, hxH⟩) = 2 :=
  orderOf_mk_eq_two H (by rw [Subgroup.orderOf_mk]; exact hx2)

theorem PairG.toPairX {x : G} {K₁ K₂ : Subgroup G} {q : ℕ} (h : PairG x K₁ K₂ q) {H : Subgroup G}
    (hxH : x ∈ H) (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H) :
    PairX (mkH H ⟨x, hxH⟩) (barIn H K₁) (barIn H K₂) := by
  have hx2 := orderOf_mkH_of_orderOf hxH h.ord
  have hmem : ∀ {K : Subgroup G}, x ∈ K → K ≤ H → mkH H ⟨x, hxH⟩ ∈ barIn H K :=
    fun hxK hKH => ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
  have hle : ∀ {K : Subgroup G}, K ≤ centralizer ({x} : Set G) → K ≤ H →
      barIn H K ≤ centralizer ({mkH H ⟨x, hxH⟩} : Set (HBar H)) := by
    intro K hKC hKH
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKC (Subgroup.mem_subgroupOf.mp hk))
    rw [← map_mul, ← map_mul]
    exact congrArg (mkH H) (Subtype.ext this)
  refine ⟨?_, ?_, hmem h.mem₁ hK₁H, hmem h.mem₂ hK₂H, hle h.le₁ hK₁H, hle h.le₂ hK₂H, ?_,
    isComponent_barIn hxH h.ord hK₁H h.le₁ h.quasi₁ h.sub₁,
    isComponent_barIn hxH h.ord hK₂H h.le₂ h.quasi₂ h.sub₂,
    cent_barIn hxH h.ord hK₁H h.le₁ h.quasi₁ h.mem₁ h.sl₁ h.odd h.five,
    cent_barIn hxH h.ord hK₂H h.le₂ h.quasi₂ h.mem₂ h.sl₂ h.odd h.five, ?_⟩
  · have := pow_orderOf_eq_one (mkH H ⟨x, hxH⟩)
    rwa [hx2, pow_two] at this
  · intro h1
    rw [h1, orderOf_one] at hx2
    omega
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (mkH H) (Subtype.ext (h.comm a (Subgroup.mem_subgroupOf.mp ha) b
      (Subgroup.mem_subgroupOf.mp hb)))
  · intro M hM hMp
    exact perf_bar hxH h.ord hK₁H hK₂H h.perf hMp hM

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
