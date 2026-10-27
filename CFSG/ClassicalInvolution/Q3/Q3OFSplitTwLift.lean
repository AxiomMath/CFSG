module

public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwKlein
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwPar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3PP
open scoped MatrixGroups

section Model


structure ParityData (c : CompData) (N : Subgroup c.G) : Prop where
  fund : KindFund3 c
  conj : FundConjClosed3 c
  single : ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R
  central : N ≤ Subgroup.center c.G
  std : ∃ R₀ ∈ c.fund, ∃ r₀ ∈ R₀, r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ ∃ W₀ : Set c.G,
    (∀ w ∈ W₀, (∃ a : c.G, w = a * r₀ * a⁻¹) ∧ w * r₀ * w⁻¹ * r₀⁻¹ ∈ N) ∧
    ∃ ζ ∈ N, r₀ * ζ ∈ Subgroup.closure (Set.image2 (· * ·) (insert r₀ W₀) (insert r₀ W₀))

end Model

section Edge


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

theorem parityAt_of_parityData (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) {N : Subgroup (D.kind i).G}
    (hN : N ≤ (D.hom i).ker) (hnA1 : D.kind i ≠ CompData.sl23) (hP : ParityData (D.kind i) N) :
    ParityAt K K₁ z₁ z₂ := by
  classical
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₁ : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  have hOY : classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁) = ⊥ :=
    Q3DB.classicalInvolutionOddCore_locLayer_eq_bot hΩ.conjInvariant
      (involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁)
  obtain ⟨i₁, hi₁⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₁, hK₁, rfl⟩)
  have hu₁' : z₁ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₁ h.cls₁.mem
  have hA1 : D.kind i₁ = CompData.sl23 :=
    kind_eq_sl23_of_ubar_central D hK₁ h.cls₁ hu₁' (ubar_mem_center_at_self hu₁') i₁ hi₁
  have hne : i₁ ≠ i := by
    intro heq
    subst heq
    have hKK : K₁ = K₂ := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ⟨hK₁, hi₁⟩ ⟨hK₂, hi⟩
    have hcl₂ : IsClassicalMember3 K₁ z₂ := hKK ▸ h.cls₂
    exact h.ne (involution_unique3 h.cls₁ hcl₂)
  have hcK₁ : ∀ {M : Subgroup G} {m : G}, M ∈ compMembers3 (conjClass3 K) z₁ D i →
      IsClassicalMember3 M m → K₁ ≤ Subgroup.centralizer ({m} : Set G) := by
    intro M m hM hm y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne ⟨hK₁, hi₁⟩ hM y hy m hm.mem
  set L := locLayer (conjClass3 K) z₁ with hL
  let π : ↥L →* locQuot (conjClass3 K) z₁ :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥L)
  have hπinj : Function.Injective π := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ classicalInvolutionOddCore ↥L := QuotientGroup.eq.mp hab
    rw [hOY, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  let e : ↥L ≃* locQuot (conjClass3 K) z₁ :=
    MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩
  let Φ : (D.kind i).G →* G := L.subtype.comp (e.symm.toMonoidHom.comp (D.hom i))
  have hΦ : ∀ (a : (D.kind i).G) (y : ↥L), π y = D.hom i a → Φ a = (y : G) := by
    intro a y hy
    show ((e.symm (D.hom i a) : ↥L) : G) = y
    rw [← hy]
    exact congrArg Subtype.val (e.symm_apply_apply y)
  have hΦN : ∀ n ∈ N, Φ n = 1 := by
    intro n hn
    have h1 : D.hom i n = 1 := hN hn
    show ((e.symm (D.hom i n) : ↥L) : G) = 1
    rw [h1, map_one]
    rfl
  obtain ⟨R, hNm, hRf, hNR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D ⟨hK₂, hi⟩
  have hu' : z₂ ∈ L := le_centralizingLayer hK₂ h.cls₂.mem
  have hclN : IsClassicalMember3 (locImg (conjClass3 K) z₁ K₂) (π ⟨z₂, hu'⟩) :=
    (h.cls₂.subgroupOf (le_centralizingLayer hK₂)).map_oddQuotient
  have h24 : Nat.card (R.map (D.hom i)) = 24 := by
    rw [← hNR]
    exact D.card_eq _ (mem_locFamily_iff.mpr ⟨K₂, hNm, rfl⟩)
  obtain ⟨huniqR, hinjR⟩ := fund_facts hP.fund (D.hom i) (D.ker_le_center i) hRf h24
  have hmemN : π ⟨z₂, hu'⟩ ∈ R.map (D.hom i) := by
    rw [← hNR]
    exact hclN.mem
  obtain ⟨r, hrR, hr⟩ := hmemN
  have hu2 : (⟨z₂, hu'⟩ : ↥L) * ⟨z₂, hu'⟩ = 1 :=
    Subtype.ext (Q3NT.mul_self_eq_one_of_orderOf_eq_two h.cls₂.orderOf_eq_two)
  have hr2 : r * r = 1 := hinjR _ (R.mul_mem hrR hrR) _ R.one_mem (by
    rw [map_mul, hr, ← map_mul, hu2, map_one, map_one])
  have hr1 : r ≠ 1 := by
    intro h1
    apply hclN.ne_one
    rw [← hr, h1, map_one]
  obtain ⟨R₀, hR₀f, r₀, hr₀R, hr₀2, hr₀1, W₀, hW₀, ζ, hζN, hrel⟩ := hP.std
  obtain ⟨g, hg⟩ := hP.single R₀ hR₀f R hRf
  have hr₀' : g * r₀ * g⁻¹ ∈ R := hg ▸ conj_mem_conjSub hr₀R
  have hcsq : (g * r₀ * g⁻¹) * (g * r₀ * g⁻¹) = 1 := by
    calc (g * r₀ * g⁻¹) * (g * r₀ * g⁻¹) = g * (r₀ * r₀) * g⁻¹ := by group
      _ = 1 := by rw [hr₀2]; group
  have hcne : g * r₀ * g⁻¹ ≠ 1 := by
    intro h1
    apply hr₀1
    have : r₀ = g⁻¹ * (g * r₀ * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hrdef : r = g * r₀ * g⁻¹ := huniqR r hrR _ hr₀' hr2 hcsq hr1 hcne
  let Ψ : (D.kind i).G →* G := Φ.comp (MulAut.conj g).toMonoidHom
  have hΨ : ∀ a, Ψ a = Φ (g * a * g⁻¹) := fun a => rfl
  have hΨN : ∀ n ∈ N, Ψ n = 1 := by
    intro n hn
    have hnc : g * n * g⁻¹ = n := by
      have := Subgroup.mem_center_iff.mp (hP.central hn) g
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [this]
        _ = n := by group
    rw [hΨ, hnc]
    exact hΦN n hn
  have hΨr : Ψ r₀ = z₂ := by
    rw [hΨ, ← hrdef]
    exact hΦ r ⟨z₂, hu'⟩ hr.symm
  have hW : ∀ w₀ ∈ W₀, (∃ M ∈ conjClass3 K, IsClassicalMember3 M (Ψ w₀)) ∧ Ψ w₀ ≠ z₁ ∧
      K₁ ≤ Subgroup.centralizer ({Ψ w₀} : Set G) ∧ Ψ w₀ * z₂ = z₂ * Ψ w₀ := by
    intro w₀ hw₀
    obtain ⟨⟨a₀, ha₀⟩, hcomm⟩ := hW₀ w₀ hw₀
    obtain ⟨b, hb⟩ : ∃ b : (D.kind i).G, b = g * a₀ * g⁻¹ := ⟨_, rfl⟩
    have hwdef : g * w₀ * g⁻¹ = b * r * b⁻¹ := by
      rw [ha₀, hrdef, hb]
      group
    have hbR : b * r * b⁻¹ ∈ conjSub b R := conj_mem_conjSub hrR
    have hbf : conjSub b R ∈ (D.kind i).fund := hP.conj R hRf b
    have hbsq : (b * r * b⁻¹) * (b * r * b⁻¹) = 1 := by
      calc (b * r * b⁻¹) * (b * r * b⁻¹) = b * (r * r) * b⁻¹ := by group
        _ = 1 := by rw [hr2]; group
    have hbne : b * r * b⁻¹ ≠ 1 := by
      intro h1
      apply hr1
      have : r = b⁻¹ * (b * r * b⁻¹) * b := by group
      rw [this, h1]
      group
    obtain ⟨M, hMm, -, hMR⟩ := exists_corr_conj3 hΩ ⟨hNm, hRf, hNR⟩ b hbf
    obtain ⟨m, hm⟩ := hΩ.classical M hMm.1
    have hm' : m ∈ L := le_centralizingLayer hMm hm.mem
    have hπm := mk_involution_eq_of_corr hP.fund hMm hm hMR hbf hbR hbsq hbne hm'
    have hΨw : Ψ w₀ = m := by
      rw [hΨ, hwdef]
      exact hΦ _ ⟨m, hm'⟩ hπm
    have hMrange : M ∈ compMembers3 (conjClass3 K) z₁ D i := by
      refine ⟨hMm, ?_⟩
      rw [hMR]
      exact Subgroup.map_le_range _ _
    have hne1 : Ψ w₀ ≠ z₁ := by
      intro h1
      rw [hΨw] at h1
      have hm1 : IsClassicalMember3 M z₁ := h1 ▸ hm
      exact hnA1 (kind_eq_sl23_of_ubar_central D hMm hm1 hu₁' (ubar_mem_center_at_self hu₁') i
        hMrange.2)
    refine ⟨⟨M, hMm.1, by rw [hΨw]; exact hm⟩, hne1, by rw [hΨw]; exact hcK₁ hMrange hm, ?_⟩
    have h1 : Ψ (w₀ * r₀ * w₀⁻¹ * r₀⁻¹) = 1 := hΨN _ hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hΨr] at h1
    have h2 : Ψ w₀ * z₂ * (Ψ w₀)⁻¹ = z₂ := mul_inv_eq_one.mp h1
    calc Ψ w₀ * z₂ = Ψ w₀ * z₂ * (Ψ w₀)⁻¹ * Ψ w₀ := by group
      _ = z₂ * Ψ w₀ := by rw [h2]
  refine ⟨Ψ '' W₀, ?_, ?_⟩
  · rintro _ ⟨w₀, hw₀, rfl⟩
    exact hW w₀ hw₀
  · have h1 : z₂ ∈ (Subgroup.closure (Set.image2 (· * ·) (insert r₀ W₀) (insert r₀ W₀))).map Ψ := by
      refine ⟨r₀ * ζ, hrel, ?_⟩
      rw [map_mul, hΨr, hΨN ζ hζN, mul_one]
    rw [MonoidHom.map_closure, Set.image_image2_distrib (map_mul Ψ), Set.image_insert_eq,
      hΨr] at h1
    exact h1

end Edge

end CFSG.ClassicalInvolution.Q3.Q3OF
