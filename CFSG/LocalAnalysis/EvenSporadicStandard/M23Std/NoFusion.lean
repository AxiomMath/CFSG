module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoFusionBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.OrbitCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralWeak

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem false_of_isConj_mem_preimage (hnc : ∀ x ∈ L1, ¬ IsConj z x) (hRank : RankFour L)
    (hL2 : ¬ 256 ∣ Nat.card L) {N1 N2 : Subgroup (Ybar L1)} (hnorm : (N1 ⊔ N2).Normal)
    (hSq : ∀ S' : Subgroup G, IsSylowOf 2 S' (centralizer ({z} : Set G)) →
      ∃ a ∈ S', ∃ b ∈ S', a * a * (b * b) ≠ b * b * (a * a))
    (hD8 : ∀ T : Subgroup (Ybar L1), IsSylowOf 2 T (N1 ⊔ N2) → ∀ y ∈ T, y * y = 1 →
      16 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set (Ybar L1))) ∧
        (Nat.card ↥(T ⊓ centralizer ({y} : Set (Ybar L1))) = 16 →
          ∀ g ∈ T ⊓ centralizer ({y} : Set (Ybar L1)), g * g = 1))
    {y : G} (hy : y ∈ preimageY L1 (N1 ⊔ N2)) (hy2 : y * y = 1) (hconj : IsConj z y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyX, hyN⟩ := mem_preimageY.1 hy
  have hyL : y ∉ L1 := fun h => hnc y h hconj
  have hy1 : y ≠ 1 := fun h => hyL (h ▸ L1.one_mem)
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hy2g : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo]; norm_num)
  have hy2g' : IsPGroup 2 ((zpowers y).subgroupOf (normalizer (L1 : Set G))) :=
    hy2g.comap_subtype
  obtain ⟨Q, hQ⟩ := hy2g'.exists_le_sylow
  set P : Subgroup G := (Q : Subgroup ↥(normalizer (L1 : Set G))).map
    (normalizer (L1 : Set G)).subtype with hPdef
  have hPsyl : IsSylowOf 2 P (normalizer (L1 : Set G)) := ⟨Q, rfl⟩
  have hyP : y ∈ P :=
    ⟨⟨y, hyX⟩, hQ (Subgroup.mem_subgroupOf.2 (mem_zpowers y)), rfl⟩
  have hPX : P ≤ normalizer (L1 : Set G) := hPsyl.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hPsyl
  have hP2 : IsPGroup 2 P := hPsyl.isPGroup
  set X := normalizer (L1 : Set G) with hXdef
  set N := N1 ⊔ N2 with hNdef
  have hSylY : IsSylowOf 2 ((P.subgroupOf X).map (piY L1)) ⊤ := by
    obtain ⟨R', hR'⟩ := hPsyl.exists_sylow_eq_subgroupOf
    have h1 : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
    have h2 : ¬ 2 ∣ (P.subgroupOf X).index := by
      have := R'.not_dvd_index
      rwa [hR'] at this
    exact isSylowOf_map_top (piY L1) (piY_surjective L1) h1 h2
  set T : Subgroup (Ybar L1) := (P.subgroupOf X).map (piY L1) ⊓ N with hT
  have hTsyl : IsSylowOf 2 T N :=
    hSylY.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hnorm])
  set X0 : Subgroup G := preimageY L1 N with hX0
  set R : Subgroup G := P ⊓ X0 with hR
  have hyR : y ∈ R := mem_inf.2 ⟨hyP, hy⟩
  have hL1R : L1 ≤ R := le_inf hL1P (fun l hl => (mem_preimageY_iff
    (Subgroup.le_normalizer hl)).2 (by
      rw [S.piY_eq_one_of_mem_L1 hl (Subgroup.le_normalizer hl)]
      exact one_mem _))
  have hπL1 : ∀ l ∈ L1, ∀ hl : l ∈ X, piY L1 ⟨l, hl⟩ = 1 := fun l hl hlX =>
    S.piY_eq_one_of_mem_L1 hl hlX
  have hL1X0 : L1 ≤ X0 := fun l hl =>
    (mem_preimageY_iff (Subgroup.le_normalizer hl)).2 (by
      rw [hπL1 l hl]
      exact one_mem _)
  have hRT : ∀ r ∈ R, ∀ hr : r ∈ X, piY L1 ⟨r, hr⟩ ∈ T := fun r hr hrX =>
    mem_inf.2 ⟨⟨⟨r, hrX⟩, Subgroup.mem_subgroupOf.2 (mem_inf.1 hr).1, rfl⟩,
      (mem_preimageY_iff hrX).1 (mem_inf.1 hr).2⟩
  have hTR : ∀ t ∈ T, ∃ r ∈ R, ∃ hr : r ∈ X, piY L1 ⟨r, hr⟩ = t := by
    intro t ht
    obtain ⟨hmem, htN⟩ := mem_inf.1 ht
    obtain ⟨⟨r, hrX⟩, hrP, rfl⟩ := hmem
    exact ⟨r, mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hrP, (mem_preimageY_iff hrX).2 htN⟩, hrX, rfl⟩
  set yb : Ybar L1 := piY L1 ⟨y, hyX⟩ with hyb
  have hybT : yb ∈ T := hRT y hyR hyX
  have hyb2 : yb * yb = 1 := by
    rw [hyb, ← map_mul]
    have : (⟨y, hyX⟩ : ↥X) * ⟨y, hyX⟩ = 1 := Subtype.ext (by simpa using hy2)
    rw [this, map_one]
  obtain ⟨hc16, hexp⟩ := hD8 T hTsyl yb hybT hyb2
  set CT : Subgroup (Ybar L1) := T ⊓ centralizer ({yb} : Set (Ybar L1)) with hCT
  set W : Subgroup G := L1 ⊓ centralizer ({y} : Set G) with hW
  have hW16 : Nat.card W = 16 := S.card_centralizer_L1_of_isConj hRank hyX hy2 hyL hconj
  set H : Subgroup G := R ⊓ preimageY L1 CT with hH
  have hHX : H ≤ X := inf_le_left.trans (inf_le_left.trans hPX)
  have hL1H : L1 ≤ H := fun l hl => mem_inf.2 ⟨hL1R hl, (mem_preimageY_iff
    (Subgroup.le_normalizer hl)).2 (by
      rw [hπL1 l hl]
      exact one_mem _)⟩
  let f : ↥H →* Ybar L1 := (piY L1).comp (Subgroup.inclusion hHX)
  have hker : L1.subgroupOf H ≤ f.ker := by
    intro a ha
    exact hπL1 (a : G) (Subgroup.mem_subgroupOf.1 ha) (hHX a.2)
  have hrange : CT ≤ f.range := by
    intro t ht
    obtain ⟨r, hrR, hrX, hrt⟩ := hTR t (mem_inf.1 ht).1
    exact ⟨⟨r, mem_inf.2 ⟨hrR, (mem_preimageY_iff hrX).2 (hrt ▸ ht)⟩⟩, hrt⟩
  have hL1card : Nat.card ↥(L1.subgroupOf H) = 256 := by
    rw [← S.L1_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1H).toEquiv
  have hHcard : 256 * Nat.card CT ≤ Nat.card H := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 : 256 ≤ Nat.card f.ker := hL1card ▸ Subgroup.card_le_of_le hker
    have h3 : Nat.card CT ≤ Nat.card f.range := Subgroup.card_le_of_le hrange
    calc 256 * Nat.card CT ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul h2 h3
      _ = Nat.card H := h1
  have hmap : ∀ r ∈ H, y⁻¹ * (r * y * r⁻¹) ∈ W := by
    intro r hr
    obtain ⟨hrR, hrCT⟩ := mem_inf.1 hr
    obtain ⟨hrP, -⟩ := mem_inf.1 hrR
    have hrX : r ∈ X := hPX hrP
    have hπr : piY L1 ⟨r, hrX⟩ ∈ CT := (mem_preimageY_iff hrX).1 hrCT
    have hcomm : piY L1 ⟨r, hrX⟩ * yb = yb * piY L1 ⟨r, hrX⟩ :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 hπr).2
    have hy'P : r * y * r⁻¹ ∈ P := P.mul_mem (P.mul_mem hrP hyP) (P.inv_mem hrP)
    have hy'X : r * y * r⁻¹ ∈ X := hPX hy'P
    have hyy'P : y⁻¹ * (r * y * r⁻¹) ∈ P := P.mul_mem (P.inv_mem hyP) hy'P
    have hyy'X : y⁻¹ * (r * y * r⁻¹) ∈ X := X.mul_mem (X.inv_mem hyX) hy'X
    have hπ : piY L1 ⟨y⁻¹ * (r * y * r⁻¹), hyy'X⟩ = 1 := by
      have : (⟨y⁻¹ * (r * y * r⁻¹), hyy'X⟩ : ↥X) =
          (⟨y, hyX⟩ : ↥X)⁻¹ * ((⟨r, hrX⟩ : ↥X) * ⟨y, hyX⟩ * (⟨r, hrX⟩ : ↥X)⁻¹) := rfl
      rw [this, map_mul, map_inv, map_mul, map_mul, map_inv]
      calc (piY L1 ⟨y, hyX⟩)⁻¹ * (piY L1 ⟨r, hrX⟩ * piY L1 ⟨y, hyX⟩ * (piY L1 ⟨r, hrX⟩)⁻¹)
          = yb⁻¹ * ((piY L1 ⟨r, hrX⟩ * yb) * (piY L1 ⟨r, hrX⟩)⁻¹) := rfl
        _ = yb⁻¹ * ((yb * piY L1 ⟨r, hrX⟩) * (piY L1 ⟨r, hrX⟩)⁻¹) := by rw [hcomm]
        _ = 1 := by group
    have hl : y⁻¹ * (r * y * r⁻¹) ∈ L1 := S.mem_L1_of_piY_eq_one hP2 hL1P hyy'P hyy'X hπ
    have hy'2 : r * y * r⁻¹ * (r * y * r⁻¹) = 1 := by
      calc r * y * r⁻¹ * (r * y * r⁻¹) = r * (y * y) * r⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    refine S.mem_centralizer_of_involution_mul hy2 hl ?_
    rw [show y * (y⁻¹ * (r * y * r⁻¹)) = r * y * r⁻¹ by group]
    exact hy'2
  have hHle := card_le_mul_card_centralizer hmap
  rw [hW16] at hHle
  set Cy : Subgroup G := H ⊓ centralizer ({y} : Set G) with hCy
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 hconj
  have hz' : z = c₀⁻¹ * y * c₀ := by rw [← hc₀]; group
  have h128 : 128 ∣ Nat.card L :=
    (S.nd.N_two).trans (Subgroup.card_dvd_of_le (inf_le_right : normalizer (F : Set G) ⊓ L ≤ L))
  set K : Subgroup G := Cy.map (MulAut.conj c₀⁻¹).toMonoidHom with hK
  have hKC : K ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨σ, hσ, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hσy : σ * y = y * σ := mem_centralizer_singleton_iff.1 (mem_inf.1 hσ).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c₀⁻¹ * σ * c₀ * z = c₀⁻¹ * (σ * y) * c₀ := by rw [hz']; group
      _ = c₀⁻¹ * (y * σ) * c₀ := by rw [hσy]
      _ = z * (c₀⁻¹ * σ * c₀) := by rw [hz']; group
  have hCyP : Cy ≤ P := (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hKp : IsPGroup 2 K := (hP2.to_le hCyP).map _
  have hKcard : Nat.card K = Nat.card Cy :=
    Subgroup.card_map_of_injective (MulAut.conj c₀⁻¹).injective
  have hCy256 : Nat.card Cy ≤ 256 := by
    rw [← hKcard]
    exact card_two_subgroup_le_centralizer S.one hL2 h128 hKp hKC
  have hc : Nat.card CT = 16 ∧ Nat.card Cy = 256 := by
    have : 256 * Nat.card CT ≤ 16 * Nat.card Cy := by
      calc 256 * Nat.card CT ≤ Nat.card H := hHcard
        _ ≤ 16 * Nat.card Cy := hHle
    omega
  have hexp' := hexp hc.1
  have hsq : ∀ σ ∈ Cy, σ * σ ∈ W := by
    intro σ hσ
    obtain ⟨hσH, hσy⟩ := mem_inf.1 hσ
    obtain ⟨hσR, hσCT⟩ := mem_inf.1 hσH
    have hσP : σ ∈ P := (mem_inf.1 hσR).1
    have hσX : σ ∈ X := hPX hσP
    have hπσ : piY L1 ⟨σ, hσX⟩ ∈ CT := (mem_preimageY_iff hσX).1 hσCT
    have h1 := hexp' _ hπσ
    have hσσP : σ * σ ∈ P := P.mul_mem hσP hσP
    have hσσX : σ * σ ∈ X := X.mul_mem hσX hσX
    have hπ : piY L1 ⟨σ * σ, hσσX⟩ = 1 := by
      have : (⟨σ * σ, hσσX⟩ : ↥X) = ⟨σ, hσX⟩ * ⟨σ, hσX⟩ := rfl
      rw [this, map_mul]
      exact h1
    have hL : σ * σ ∈ L1 := S.mem_L1_of_piY_eq_one hP2 hL1P hσσP hσσX hπ
    refine mem_inf.2 ⟨hL, mem_centralizer_singleton_iff.2 ?_⟩
    have hcy : σ * y = y * σ := mem_centralizer_singleton_iff.1 hσy
    calc σ * σ * y = σ * (σ * y) := by group
      _ = σ * (y * σ) := by rw [hcy]
      _ = (σ * y) * σ := by group
      _ = (y * σ) * σ := by rw [hcy]
      _ = y * (σ * σ) := by group
  have hKsyl : IsSylowOf 2 K (centralizer ({z} : Set G)) := by
    rw [isSylowOf_iff]
    refine ⟨hKC, hKp, ?_⟩
    have hCL : Nat.card (centralizer ({z} : Set G)) = Nat.card L * 2 := by
      rw [centralizer_z_eq S.one]
      exact card_sup_zpowers S.one le_rfl
    have h1 := Subgroup.relIndex_mul_card K (centralizer ({z} : Set G))
    rw [inf_of_le_left hKC, hKcard, hc.2, hCL] at h1
    obtain ⟨m, hm⟩ := h128
    have hmodd : Odd m := by
      by_contra hodd
      exact hL2 ⟨m / 2, by rcases Nat.even_or_odd m with ⟨k, hk⟩ | ho
                           · omega
                           · exact absurd ho hodd⟩
    rw [hm] at h1
    have : K.relIndex (centralizer ({z} : Set G)) = m := by omega
    rw [this]
    exact fun h => (Nat.not_even_iff_odd.2 hmodd) (even_iff_two_dvd.2 h)
  obtain ⟨a₀, ha₀, b₀, hb₀, hne⟩ := hSq K hKsyl
  obtain ⟨a, ha, rfl⟩ := ha₀
  obtain ⟨b, hb, rfl⟩ := hb₀
  apply hne
  have hab : a * a * (b * b) = b * b * (a * a) :=
    S.L1_comm _ (mem_inf.1 (hsq a ha)).1 _ (mem_inf.1 (hsq b hb)).1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc c₀⁻¹ * a * c₀ * (c₀⁻¹ * a * c₀) * (c₀⁻¹ * b * c₀ * (c₀⁻¹ * b * c₀))
      = c₀⁻¹ * (a * a * (b * b)) * c₀ := by group
    _ = c₀⁻¹ * (b * b * (a * a)) * c₀ := by rw [hab]
    _ = c₀⁻¹ * b * c₀ * (c₀⁻¹ * b * c₀) * (c₀⁻¹ * a * c₀ * (c₀⁻¹ * a * c₀)) := by group

end Setup

end CFSG.EvenSporadicStandard.M23Std
