module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Assemble

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools CFSG.EvenSporadicStandard.M23Std CFSG.Blueprint.NativeSporadic

@[expose] def OuterWr1 (Xb : Type) [Group Xb] [Finite Xb] (zb : Xb) (Eh B : Subgroup Xb) : Prop :=
  zb ∈ Eh ∧ centralizer ({zb} : Set Xb) ≤ Eh ∧ B ≤ Eh ∧ zb ∉ B ∧
    (∀ x ∈ Eh, x ∈ B ∨ x * zb ∈ B) ∧
    (∀ q ∈ B, q * q = 1 → q ≠ 1 → 128 ∣ Nat.card (centralizer ({q} : Set Xb))) ∧
    ∀ P : Subgroup Xb, IsSylowOf 2 P Eh → zb ∈ P →
      ∀ y ∈ P, y * y = 1 → y ∉ B → ∃ c ∈ P, y = c⁻¹ * zb * c

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

set_option quotPrecheck false in
local notation "Hc" => centralizer ({z} : Set G)

omit [Finite G] in
theorem preimageX_le_normalizer {B : Subgroup (Xbar L1)} :
    preimageX L1 B ≤ normalizer (L1 : Set G) := fun _ hg => (mem_preimageX_iff.1 hg).1

theorem isSylowOf_map_preimageX {P : Subgroup G} {Eh : Subgroup (Xbar L1)}
    (hP : IsSylowOf 2 P (preimageX L1 Eh)) :
    IsSylowOf 2 ((P.subgroupOf (normalizer (L1 : Set G))).map
      (QuotientGroup.mk'
        ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G))))) Eh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))
    with hρ
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hPN : P ≤ normalizer (L1 : Set G) := hP.le.trans preimageX_le_normalizer
  have hPY : IsSylowOf 2 (P.subgroupOf (normalizer (L1 : Set G))) (Eh.comap ρ) := by
    have h1 : P = (P.subgroupOf (normalizer (L1 : Set G))).map
        (normalizer (L1 : Set G)).subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPN]
    have hP' : IsSylowOf 2
        ((P.subgroupOf (normalizer (L1 : Set G))).map (normalizer (L1 : Set G)).subtype)
        ((Eh.comap ρ).map (normalizer (L1 : Set G)).subtype) := by
      rw [← h1]
      exact hP
    exact (isSylowOf_map_subtype_iff _).1 hP'
  rw [isSylowOf_iff] at hPY ⊢
  obtain ⟨hle, hp, hidx⟩ := hPY
  have hker : ρ.ker ≤ Eh.comap ρ := fun y hy => by
    rw [MonoidHom.mem_ker] at hy
    show ρ y ∈ Eh
    rw [hy]
    exact Eh.one_mem
  refine ⟨?_, hp.map ρ, ?_⟩
  · calc (P.subgroupOf (normalizer (L1 : Set G))).map ρ ≤ (Eh.comap ρ).map ρ :=
        Subgroup.map_mono hle
      _ = Eh := Subgroup.map_comap_eq_self_of_surjective hsurj Eh
  · have h3 : ((P.subgroupOf (normalizer (L1 : Set G))).map ρ).relIndex Eh =
        ((P.subgroupOf (normalizer (L1 : Set G))) ⊔ ρ.ker).relIndex (Eh.comap ρ) := by
      conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Eh]
      rw [Subgroup.relIndex_map_map, sup_eq_left.2 hker]
    rw [h3]
    intro hd
    exact hidx (hd.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_left))

namespace OutSetup

variable {F' L1' N' : Subgroup G} (S : OutSetup L z F' L1' N')

include S

omit [Finite G] in
theorem L1_le_of_isSylowOf' {K P : Subgroup G} (hL1K : L1' ≤ K)
    (hKN : K ≤ normalizer (L1' : Set G)) (hP : IsSylowOf 2 P K) : L1' ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hnormal : (L1'.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL1K).2 hKN
  have hpg : IsPGroup 2 (L1'.subgroupOf K) := S.isPGroup_L1.comap_subtype
  have hle := IsPGroup.le_sylow_of_normal (N := L1'.subgroupOf K) hpg Q
  intro l hl
  have h1 : (⟨l, hL1K hl⟩ : ↥K) ∈ L1'.subgroupOf K := hl
  have h2 := hle h1
  rw [hQ] at h2
  exact h2

end OutSetup

theorem OuterSituation.false_of_outerWr1 [IsSimpleGroup G]
    (hS : OuterSituation G L z t T₁ F tb Q x L1) (hz : z ∈ normalizer (L1 : Set G))
    {Eh B : Subgroup (Xbar L1)} (hWr : OuterWr1 (Xbar L1) (QuotientGroup.mk ⟨z, hz⟩) Eh B) :
    False := by
  classical
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  obtain ⟨hzEh, hCEh, hBEh, hzB, hBEhz, hBL, hFus⟩ := hWr
  have D := hS.data
  have hz2 : z * z = 1 := Sup.one.z_mul_self
  have hz1 : z ≠ 1 := Sup.one.z_ne_one
  have hcr : CentRank z := hS.one.centRank_of_rankFour (m22_rankFour hS.sporadic) hS.rel
  have hCG := hS.card_centralizer_z
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
  set zb : Xbar L1 := QuotientGroup.mk ⟨z, hz⟩ with hzbdef
  have hTX := hS.T_le_normalizer
  have hTsyl : IsSylowOf 2 (T₁.map (Subgroup.subtype Hc)) Hc :=
    isSylowOf_iff.2 ⟨D.cfg.T_le, D.cfg.T_pgroup, D.T_relIndex_odd⟩
  have hTX1 : (T₁.map (Subgroup.subtype Hc) : Subgroup G) ≤ preimageX L1 Eh := by
    intro t' ht'
    obtain ⟨ht'H, -⟩ : t' ∈ Hc ∧ t' ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G) :=
      ⟨D.cfg.T_le ht', ht'⟩
    refine mem_preimageX_iff.2 ⟨hTX ht', hCEh ?_⟩
    rw [mem_centralizer_singleton_iff, hzbdef, ← hmk_mul t' z (hTX ht') hz,
      ← hmk_mul z t' hz (hTX ht')]
    exact congrArg QuotientGroup.mk (Subtype.ext (mem_centralizer_singleton_iff.1 ht'H))
  obtain ⟨P, hPsyl, hTP, hPC⟩ := exists_sylow_ge_of_sylow hTX1 hTsyl
  have hzH : z ∈ Hc := mem_centralizer_singleton_iff.2 rfl
  have hzT : z ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G) :=
    (D.mem_T_iff hzH).2 D.zH_mem_T₁
  have hzP : z ∈ P := hTP hzT
  have hP2 : IsPGroup 2 P := hPsyl.isPGroup
  have hPX1 : P ≤ preimageX L1 Eh := hPsyl.le
  have hPX : P ≤ normalizer (L1 : Set G) := hPX1.trans preimageX_le_normalizer
  have hL1X1 : L1 ≤ preimageX L1 Eh := fun l hl =>
    mem_preimageX_iff.2 ⟨Subgroup.le_normalizer hl, by rw [rho_L1 Sup hl]; exact Eh.one_mem⟩
  have hL1P : L1 ≤ P := Sup.L1_le_of_isSylowOf' hL1X1 preimageX_le_normalizer hPsyl
  have hTyl : IsSylowOf 2 (P ⊓ Hc) Hc := by
    rw [hPC]
    exact hTsyl
  let ρ : ↥(normalizer (L1 : Set G)) →* Xbar L1 :=
    QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))
  have hPb := isSylowOf_map_preimageX hPsyl
  set Pb : Subgroup (Xbar L1) := (P.subgroupOf (normalizer (L1 : Set G))).map ρ with hPbdef
  have hmemPb : ∀ q : Xbar L1, q ∈ Pb ↔
      ∃ p : ↥(normalizer (L1 : Set G)), (p : G) ∈ P ∧ ρ p = q := by
    intro q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  have hmemPb' : ∀ (g : G) (hg : g ∈ normalizer (L1 : Set G)), g ∈ P →
      (QuotientGroup.mk ⟨g, hg⟩ : Xbar L1) ∈ Pb := fun g hg hgP =>
    (hmemPb _).2 ⟨⟨g, hg⟩, hgP, rfl⟩
  have hzbPb : zb ∈ Pb := hmemPb' z hz hzP
  have hfus : ∀ w ∈ P, w * w = 1 → w ∉ P ⊓ preimageX L1 B → IsConj z w →
      ∃ s ∈ P, w = s⁻¹ * z * s := by
    intro w hwP hw2 hwS _
    have hwX : w ∈ normalizer (L1 : Set G) := hPX hwP
    have hwB : (QuotientGroup.mk ⟨w, hwX⟩ : Xbar L1) ∉ B := fun h =>
      hwS (Subgroup.mem_inf.2 ⟨hwP, mem_preimageX_iff.2 ⟨hwX, h⟩⟩)
    have hwb2 := hmk_sq w hwX hw2
    have hwbP : (QuotientGroup.mk ⟨w, hwX⟩ : Xbar L1) ∈ Pb := hmemPb' w hwX hwP
    obtain ⟨c, hcP, hwc⟩ := hFus Pb hPb hzbPb _ hwbP hwb2 hwB
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
    have hbE : (QuotientGroup.mk ⟨(b : G), hbX⟩ : Xbar L1) ∈ Eh :=
      (mem_preimageX_iff.1 (hPX1 b.2)).2
    have key : ((b : G) * z ∈ preimageX L1 B) ↔ ¬ ((b : G) ∈ preimageX L1 B) := by
      have e : (QuotientGroup.mk ⟨(b : G) * z, hbzX⟩ : Xbar L1) =
          QuotientGroup.mk ⟨(b : G), hbX⟩ * zb := hmk_mul _ _ hbX hz
      rw [mem_preimageX_iff, mem_preimageX_iff]
      constructor
      · rintro ⟨hg, h⟩ ⟨hg', h'⟩
        rw [e] at h
        exact hzB (by simpa using B.mul_mem (B.inv_mem h') h)
      · intro h
        refine ⟨hbzX, ?_⟩
        rw [e]
        rcases hBEhz _ hbE with h' | h'
        · exact absurd ⟨hbX, h'⟩ h
        · exact h'
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
