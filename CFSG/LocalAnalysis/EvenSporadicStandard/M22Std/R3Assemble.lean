module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Sig1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Sig2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SigPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Cos
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Wr
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngine6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCensusPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCentOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Engine

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std CFSG.ABGLocalTools CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

set_option quotPrecheck false in
local notation "Hc" => centralizer ({z} : Set G)

namespace OutSetup

variable {F' L1' N' : Subgroup G} (S : OutSetup L z F' L1' N')

include S

omit [Finite G] in
theorem exists_conj_of_conj_zbar {P : Subgroup G} (hP : IsPGroup 2 P) (hL1P : L1' ≤ P)
    (hzP : z ∈ P) (hPX : P ≤ normalizer (L1' : Set G)) {x : G} (hxP : x ∈ P) (hx2 : x * x = 1)
    {s : P} (hxs : (QuotientGroup.mk ⟨s * x * (s : G)⁻¹, by
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPX s.2) (hPX hxP))
        (Subgroup.inv_mem _ (hPX s.2))⟩ : Xbar L1') = QuotientGroup.mk S.zX) :
    ∃ t ∈ P, x = t⁻¹ * z * t := by
  have hx'P : (s : G) * x * (s : G)⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem s.2 hxP) (P.inv_mem s.2)
  have hx'2 : ((s : G) * x * (s : G)⁻¹) * ((s : G) * x * (s : G)⁻¹) = 1 := by
    calc ((s : G) * x * (s : G)⁻¹) * ((s : G) * x * (s : G)⁻¹)
        = (s : G) * (x * x) * (s : G)⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hyz : (s : G) * x * (s : G)⁻¹ * z ∈ normalizer (L1' : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPX s.2) (hPX hxP))
      (Subgroup.inv_mem _ (hPX s.2))) S.zX.2
  have hodd : Odd (orderOf (QuotientGroup.mk ⟨(s : G) * x * (s : G)⁻¹ * z, hyz⟩ : Xbar L1')) := by
    have : (QuotientGroup.mk ⟨(s : G) * x * (s : G)⁻¹ * z, hyz⟩ : Xbar L1') = 1 := by
      have h1 : (⟨(s : G) * x * (s : G)⁻¹ * z, hyz⟩ : ↥(normalizer (L1' : Set G))) =
          ⟨(s : G) * x * (s : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPX s.2) (hPX hxP))
            (Subgroup.inv_mem _ (hPX s.2))⟩ * S.zX := rfl
      rw [h1, QuotientGroup.mk_mul, hxs]
      have hz2 : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
      rw [← QuotientGroup.mk_mul, hz2]
      exact QuotientGroup.mk_one _
    rw [this, orderOf_one]
    exact odd_one
  obtain ⟨t, htP, hxt⟩ := S.exists_conj_of_odd_image hP hL1P hzP hx'P hx'2 hyz hodd
  refine ⟨t * s, P.mul_mem htP s.2, ?_⟩
  calc x = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * s := by group
    _ = (s : G)⁻¹ * (t⁻¹ * z * t) * s := by rw [hxt]
    _ = (t * s)⁻¹ * z * (t * s) := by group

end OutSetup


theorem OuterSituation.false_of_outerWr [IsSimpleGroup G]
    (hS : OuterSituation G L z t T₁ F tb Q x L1) (hz : z ∈ normalizer (L1 : Set G))
    (hWr : OuterWr (Xbar L1) (QuotientGroup.mk ⟨z, hz⟩)) : False := by
  classical
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  obtain ⟨B, hBidx, hzB, hBL, hOC⟩ := hWr
  have D := hS.data
  have hz2 : z * z = 1 := Sup.one.z_mul_self
  have hz1 : z ≠ 1 := Sup.one.z_ne_one
  have hcr : CentRank z := hS.one.centRank_of_rankFour (m22_rankFour hS.sporadic) hS.rel
  have hCG := hS.card_centralizer_z
  obtain ⟨A, a, hLA, hAH, hzA, hAz, hidx, -, haA, haL, ha2, haT, haN, haX, hy⟩ :=
    hS.exists_sigma_data autSylowEngine6_m22 autSylowCensus_m22 autSylowE32X_m22
  have hTX := hS.T_le_normalizer
  have hTsyl : IsSylowOf 2 (T₁.map (Subgroup.subtype Hc)) Hc :=
    isSylowOf_iff.2 ⟨D.cfg.T_le, D.cfg.T_pgroup, D.T_relIndex_odd⟩
  obtain ⟨P, hPsyl, hTP, hPC⟩ := exists_sylow_ge_of_sylow hTX hTsyl
  have hzH : z ∈ Hc := mem_centralizer_singleton_iff.2 rfl
  have hzT : z ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G) :=
    (D.mem_T_iff hzH).2 D.zH_mem_T₁
  have hzP : z ∈ P := hTP hzT
  have hP2 : IsPGroup 2 P := hPsyl.isPGroup
  have hPX : P ≤ normalizer (L1 : Set G) := hPsyl.le
  have hL1P : L1 ≤ P := Sup.L1_le_of_isSylowOf hPsyl
  have hTyl : IsSylowOf 2 (P ⊓ Hc) Hc := by
    rw [hPC]
    exact hTsyl
  let ρ : ↥(normalizer (L1 : Set G)) →* Xbar L1 :=
    QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  obtain ⟨Q', hQ'⟩ := hPsyl.exists_sylow_eq_subgroupOf
  let Pb : Sylow 2 (Xbar L1) := Q'.mapSurjective hρsurj
  have hPb : (Pb : Subgroup (Xbar L1)) = (P.subgroupOf (normalizer (L1 : Set G))).map ρ := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hmemPb : ∀ q : Xbar L1, q ∈ (Pb : Subgroup (Xbar L1)) ↔
      ∃ p : ↥(normalizer (L1 : Set G)), (p : G) ∈ P ∧ ρ p = q := by
    intro q
    rw [hPb]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  have hmemPb' : ∀ (g : G) (hg : g ∈ normalizer (L1 : Set G)), g ∈ P →
      (QuotientGroup.mk ⟨g, hg⟩ : Xbar L1) ∈ (Pb : Subgroup (Xbar L1)) := fun g hg hgP =>
    (hmemPb _).2 ⟨⟨g, hg⟩, hgP, rfl⟩
  set zb : Xbar L1 := QuotientGroup.mk ⟨z, hz⟩ with hzbdef
  have hzbPb : zb ∈ (Pb : Subgroup (Xbar L1)) := hmemPb' z hz hzP
  have hmk_mul : ∀ (g h : G) (hg : g ∈ normalizer (L1 : Set G)) (hh : h ∈ normalizer (L1 : Set G)),
      (QuotientGroup.mk ⟨g * h, Subgroup.mul_mem _ hg hh⟩ : Xbar L1) =
        QuotientGroup.mk ⟨g, hg⟩ * QuotientGroup.mk ⟨h, hh⟩ := fun g h hg hh => rfl
  have hmk_sq : ∀ (g : G) (hg : g ∈ normalizer (L1 : Set G)), g * g = 1 →
      (QuotientGroup.mk ⟨g, hg⟩ : Xbar L1) * QuotientGroup.mk ⟨g, hg⟩ = 1 := by
    intro g hg hg2
    rw [← QuotientGroup.mk_mul]
    have : (⟨g, hg⟩ : ↥(normalizer (L1 : Set G))) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
    rw [this]
    exact QuotientGroup.mk_one _
  obtain ⟨y0, hy0X, hy0a, hy0B⟩ : ∃ y0 : G, ∃ _ : y0 ∈ normalizer (L1 : Set G),
      (y0 = a ∨ y0 = z * a) ∧ (QuotientGroup.mk ⟨y0, ‹y0 ∈ normalizer (L1 : Set G)›⟩ :
        Xbar L1) ∉ B := by
    by_cases hB : (QuotientGroup.mk ⟨a, haX⟩ : Xbar L1) ∈ B
    · refine ⟨z * a, Subgroup.mul_mem _ hz haX, Or.inr rfl, fun h => hzB ?_⟩
      have h1 : (QuotientGroup.mk ⟨z * a, Subgroup.mul_mem _ hz haX⟩ : Xbar L1) =
          zb * QuotientGroup.mk ⟨a, haX⟩ := hmk_mul z a hz haX
      rw [h1] at h
      have := B.mul_mem h (B.inv_mem hB)
      rwa [mul_inv_cancel_right] at this
    · exact ⟨a, haX, Or.inl rfl, hB⟩
  have hy0facts := hy y0 hy0a
  have hzc : ∀ g ∈ A, z * g = g * z := fun g hg =>
    (mem_centralizer_singleton_iff.1 (hAH hg)).symm
  have hy02 : y0 * y0 = 1 := by
    rcases hy0a with h | h <;> rw [h]
    · exact ha2
    · calc z * a * (z * a) = z * (a * z) * a := by group
        _ = z * (z * a) * a := by rw [← hzc a haA]
        _ = (z * z) * (a * a) := by group
        _ = 1 := by rw [hz2, ha2, one_mul]
  have hy0z : y0 * z = z * y0 := by
    rcases hy0a with h | h <;> rw [h]
    · exact (hzc a haA).symm
    · calc z * a * z = z * (a * z) := by group
        _ = z * (z * a) := by rw [← hzc a haA]
  have hy0T : y0 ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G) := by
    rcases hy0a with h | h <;> rw [h]
    · exact haT
    · exact Subgroup.mul_mem _ hzT haT
  have hy0P : y0 ∈ P := hTP hy0T
  set yb0 : Xbar L1 := QuotientGroup.mk ⟨y0, hy0X⟩ with hyb0def
  have hyb02 : yb0 * yb0 = 1 := hmk_sq y0 hy0X hy02
  have hyb0P : yb0 ∈ (Pb : Subgroup (Xbar L1)) := hmemPb' y0 hy0X hy0P
  have hyb0C : yb0 ∈ centralizer ({zb} : Set (Xbar L1)) := by
    rw [mem_centralizer_singleton_iff, ← hmk_mul y0 z hy0X hz, ← hmk_mul z y0 hz hy0X]
    exact congrArg QuotientGroup.mk (Subtype.ext hy0z)
  have hyb0S : yb0 ∉ zpowers zb ⊔ (commutator ↥(centralizer ({zb} : Set (Xbar L1)))).map
      (centralizer ({zb} : Set (Xbar L1))).subtype := by
    have hrho := hS.rho_not_mem_sup_commutator hz hLA hAH hzA haA haL haX
    rcases hy0a with h | h
    · have e : yb0 = QuotientGroup.mk ⟨a, haX⟩ := congrArg QuotientGroup.mk (Subtype.ext h)
      rw [e]
      exact hrho
    · have e : yb0 = zb * QuotientGroup.mk ⟨a, haX⟩ := by
        have := hmk_mul z a hz haX
        rw [← this]
        exact congrArg QuotientGroup.mk (Subtype.ext h)
      intro hmem
      rw [e] at hmem
      refine hrho ?_
      have hzbmem : zb ∈ zpowers zb ⊔ (commutator ↥(centralizer ({zb} : Set (Xbar L1)))).map
          (centralizer ({zb} : Set (Xbar L1))).subtype :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers zb)
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzbmem) hmem
      rwa [inv_mul_cancel_left] at this
  obtain ⟨hOC1, hFC⟩ := hOC (Pb : Subgroup (Xbar L1)) Pb.isPGroup' Pb.not_dvd_index hzbPb yb0
    hyb0P hyb02 hy0B hyb0C hyb0S
  have hfus : ∀ w ∈ P, w * w = 1 → w ∉ P ⊓ preimageX L1 B → IsConj z w →
      ∃ s ∈ P, w = s⁻¹ * z * s := by
    intro w hwP hw2 hwS hwc
    have hwX : w ∈ normalizer (L1 : Set G) := hPX hwP
    have hwB : (QuotientGroup.mk ⟨w, hwX⟩ : Xbar L1) ∉ B := fun h =>
      hwS (Subgroup.mem_inf.2 ⟨hwP, mem_preimageX_iff.2 ⟨hwX, h⟩⟩)
    have hwb2 := hmk_sq w hwX hw2
    have hwbP : (QuotientGroup.mk ⟨w, hwX⟩ : Xbar L1) ∈ (Pb : Subgroup (Xbar L1)) :=
      hmemPb' w hwX hwP
    have hconjP : ∃ c ∈ (Pb : Subgroup (Xbar L1)),
        (QuotientGroup.mk ⟨w, hwX⟩ : Xbar L1) = c⁻¹ * zb * c := by
      rcases hOC1 _ hwbP hwb2 hwB with h | ⟨c, hcP, hwc'⟩
      · exact h
      · obtain ⟨s, hsP, hsρ⟩ := (hmemPb c).1 hcP
        have hx'X : (s : G) * w * (s : G)⁻¹ ∈ normalizer (L1 : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ s.2 hwX) (Subgroup.inv_mem _ s.2)
        have hx'P : (s : G) * w * (s : G)⁻¹ ∈ P :=
          P.mul_mem (P.mul_mem hsP hwP) (P.inv_mem hsP)
        have hx'2 : ((s : G) * w * (s : G)⁻¹) * ((s : G) * w * (s : G)⁻¹) = 1 := by
          calc ((s : G) * w * (s : G)⁻¹) * ((s : G) * w * (s : G)⁻¹)
              = (s : G) * (w * w) * (s : G)⁻¹ := by group
            _ = 1 := by rw [hw2]; group
        have hx'ρ : (QuotientGroup.mk ⟨(s : G) * w * (s : G)⁻¹, hx'X⟩ : Xbar L1) = yb0 := by
          have h1 : (QuotientGroup.mk ⟨(s : G) * w * (s : G)⁻¹, hx'X⟩ : Xbar L1) =
              ρ s * QuotientGroup.mk ⟨w, hwX⟩ * (ρ s)⁻¹ := rfl
          rw [h1, hsρ, hwc']
          group
        have hl : y0⁻¹ * ((s : G) * w * (s : G)⁻¹) ∈ L1 := by
          refine Sup.mem_L1_of_mem_centralizer hP2 hL1P (P.mul_mem (P.inv_mem hy0P) hx'P) ?_
          have h2 : (QuotientGroup.mk ⟨y0, hy0X⟩ : Xbar L1) =
              QuotientGroup.mk ⟨(s : G) * w * (s : G)⁻¹, hx'X⟩ := hx'ρ.symm
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
          exact h2
        have hx'eq : (s : G) * w * (s : G)⁻¹ = y0 * (y0⁻¹ * ((s : G) * w * (s : G)⁻¹)) := by
          group
        have hyl2 : (y0 * (y0⁻¹ * ((s : G) * w * (s : G)⁻¹))) *
            (y0 * (y0⁻¹ * ((s : G) * w * (s : G)⁻¹))) = 1 := by
          rw [← hx'eq]
          exact hx'2
        have hU : Nat.card ↥(centralizer ({y0} : Set G) ⊓ L1) = 16 :=
          le_antisymm hy0facts.1 (Sup.sixteen_le_card_centralizer_L1 hy0X hy02)
        have hy0N : ∀ m, m ∈ L1 ↔ y0 * m * y0⁻¹ ∈ L1 := fun m =>
          Subgroup.mem_normalizer_iff.1 hy0X m
        obtain ⟨m, hmL, hmconj⟩ := exists_mem_conj_mul Sup.L1_comm Sup.L1_sq Sup.L1_card hy02
          hy0N hU hl hyl2
        have hyc : IsConj z y0 := by
          have h1 : IsConj z ((s : G) * w * (s : G)⁻¹) := hwc.trans (isConj_iff.2 ⟨s, rfl⟩)
          refine h1.trans (isConj_iff.2 ⟨m⁻¹, ?_⟩)
          rw [hx'eq, ← hmconj]
          group
        obtain ⟨k, hk, l'', hl'', hkl⟩ := hy0facts.2 hyc
        have hIC : IsConj zb yb0 := by
          refine isConj_iff.2 ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            QuotientGroup.eq, Subgroup.mem_subgroupOf]
          show ((k * z * k⁻¹)⁻¹ * y0 : G) ∈ centralizer (L1 : Set G)
          rw [hkl]
          have : (y0 * l'')⁻¹ * y0 = l''⁻¹ := by group
          rw [this]
          exact mem_centralizer_iff.2 fun w' hw' => Sup.L1_comm w' hw' l''⁻¹ (L1.inv_mem hl'')
        obtain ⟨c', hc'P, hyc'⟩ := hFC hIC
        exact ⟨c' * c, Pb.mul_mem hc'P hcP, by rw [hwc', hyc']; group⟩
    obtain ⟨c, hcP, hwc⟩ := hconjP
    obtain ⟨s, hsP, hsρ⟩ := (hmemPb c).1 hcP
    refine Sup.exists_conj_of_conj_zbar hP2 hL1P hzP hPX hwP hw2 (s := ⟨(s : G), hsP⟩) ?_
    have h1 : ∀ hxX : (s : G) * w * (s : G)⁻¹ ∈ normalizer (L1 : Set G),
        (QuotientGroup.mk ⟨(s : G) * w * (s : G)⁻¹, hxX⟩ : Xbar L1) =
          ρ s * QuotientGroup.mk ⟨w, hwX⟩ * (ρ s)⁻¹ := fun hxX => rfl
    calc _ = ρ s * QuotientGroup.mk ⟨w, hwX⟩ * (ρ s)⁻¹ := h1 _
      _ = c * (c⁻¹ * zb * c) * c⁻¹ := by rw [hsρ, hwc]
      _ = zb := by group
  have hidx2 : (P ⊓ preimageX L1 B).relIndex P = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨z, hzP⟩, fun b => ?_⟩
    have hbX : (b : G) ∈ normalizer (L1 : Set G) := hPX b.2
    have hbzX : (b : G) * z ∈ normalizer (L1 : Set G) := Subgroup.mul_mem _ hbX hz
    have key : ((b : G) * z ∈ preimageX L1 B) ↔ ¬ ((b : G) ∈ preimageX L1 B) := by
      have e : (QuotientGroup.mk ⟨(b : G) * z, hbzX⟩ : Xbar L1) =
          QuotientGroup.mk ⟨(b : G), hbX⟩ * zb := hmk_mul _ _ hbX hz
      have h1 := Subgroup.mul_mem_iff_of_index_two hBidx
        (a := (QuotientGroup.mk ⟨(b : G), hbX⟩ : Xbar L1)) (b := zb)
      rw [mem_preimageX_iff, mem_preimageX_iff]
      constructor
      · rintro ⟨hg, h⟩ ⟨hg', h'⟩
        rw [e] at h
        exact hzB ((h1.1 h).1 h')
      · intro h
        refine ⟨hbzX, ?_⟩
        rw [e, h1]
        exact iff_of_false (fun h' => h ⟨hbX, h'⟩) hzB
    show Xor (b * ⟨z, hzP⟩ ∈ (P ⊓ preimageX L1 B).subgroupOf P)
      (b ∈ (P ⊓ preimageX L1 B).subgroupOf P)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
    by_cases hB : (b : G) ∈ preimageX L1 B
    · exact Or.inr ⟨⟨b.2, hB⟩, fun h => key.1 h.2 hB⟩
    · exact Or.inl ⟨⟨P.mul_mem b.2 hzP, key.2 hB⟩, fun h => hB h.2⟩
  have hz0' : z ∉ P ⊓ preimageX L1 B := fun h =>
    hzB (mem_preimageX_iff.1 (Subgroup.mem_inf.1 h).2).2
  obtain ⟨g, hg⟩ := exists_conj_mem_of_fusion_conj hS.std.nonabelian hz2 hz1 hP2 hzP hTyl
    inf_le_left hidx2 hz0' hfus
  obtain ⟨hgP, hgB⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgX, hgB'⟩ := mem_preimageX_iff.1 hgB
  have hgc : IsConj z (g⁻¹ * z * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  have hg2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  exact Sup.false_of_base hcr hCG hS.K.not_conj hBL hP2 hL1P hPX hgP hg2 hgc hgB'

end CFSG.EvenSporadicStandard.M22Std
