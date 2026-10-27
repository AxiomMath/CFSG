module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RFin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RCy
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RDp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RPn

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Sec7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto79

theorem sec7_of_stages (hA : Sec7A) (hB : Sec7B) (hC : Sec7C) : Sec7 := by
  intro G _ _ L hS hL c h5
  have a : c.Upto74 := hA G L hS hL c h5
  have b := hB G L hS hL c h5 a
  have h6 : c.Upto76 := ⟨⟨a, b.1⟩, b.2⟩
  have d := hC G L hS hL c h5 h6
  exact ⟨⟨⟨h6, d.1⟩, d.2.1⟩, d.2.2⟩

theorem conjSub_inf_of_mem_normalizer {G : Type} [Group G] {t : G} {B : Subgroup G}
    (ht : t ∈ normalizer (B : Set G)) (A : Subgroup G) :
    conjSub t (A ⊓ B) = conjSub t A ⊓ B := by
  ext x
  rw [mem_conjSub_iff', Subgroup.mem_inf, mem_conjSub_iff']
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    exact ⟨⟨y, hyA, rfl⟩, (Subgroup.mem_normalizer_iff.mp ht y).mp hyB⟩
  · rintro ⟨⟨y, hyA, rfl⟩, hxB⟩
    exact ⟨y, ⟨hyA, (Subgroup.mem_normalizer_iff.mp ht y).mpr hxB⟩, rfl⟩

theorem sec7WreathRT_of (h : Sec7) : Sec7WreathRT := by
  intro G _ _ L hS hL c h5 _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, _⟩, _⟩, _⟩, _⟩, h76⟩, h77⟩, h78⟩, h79⟩ := h G L hS hL c h5
  obtain ⟨L1, hL1⟩ : ∃ L1 : Subgroup G, IsCompPre c.s L1 := h77.2.resolve_right h78
  have hdir := isInternalDirect_sylow (h79 L1 hL1).1 h77.1
  have ht : c.s.t ∈ normalizer (P7 c.e : Set G) := c.t_mem_normalizer_P7 h5.2.1 h71
  refine ⟨P7 c.e, ⁅L1, L1⁆ ⊓ P7 c.e, ⟨?_, ?_⟩, h76.2.2.1⟩
  · simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  · rw [conjSub_inf_of_mem_normalizer ht]
    exact hdir

@[expose] def Sec7NT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto79 → c.s.R ≠ c.s.T →
      ∃ P1 P0 : Subgroup G, IsSylowIn 2 ⊤ P1 ∧ P0 ≤ P1 ∧ P1 ≤ normalizer (P0 : Set G) ∧
        P1 = P0 ⊔ zpowers c.s.t ∧ ∀ x : G, IsConj c.s.t x → x ∉ P0

theorem sec7SylowNT_of (hNT : Sec7NT) (h7 : Sec7) : Sec7SylowNT := by
  intro G _ _ L hS hL c h5 hRT
  obtain ⟨P1, P0, hsyl, hle, hnorm, hsplit, hext⟩ :=
    hNT G L hS hL c h5 (h7 G L hS hL c h5) hRT
  exact ⟨P1, P0, hsyl, hle, secProp_cyclic_of_sup_zpowers hle hnorm hsplit,
    fun x hx => hext x hx.2.1⟩

theorem sec7False_of (hB : Sec3Inputs) (h7 : Sec7) (hNT : Sec7NT) : Sec7False :=
  sec7False_of_split (sec7SylowRT_of hB (sec7WreathRT_of h7)) (sec7SylowNT_of hNT h7)

end CFSG.OddStandard.HigherRank.YamadaG23
