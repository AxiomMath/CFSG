module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Cyc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private lemma conj_mem_centralizer_of_mem_normalizer {G : Type} [Group G] {L : Subgroup G}
    {h p : G} (hh : h ∈ Subgroup.normalizer (L : Set G))
    (hp : p ∈ Subgroup.centralizer (L : Set G)) :
    h * p * h⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hp ⊢
  intro l hl
  have hl' : h⁻¹ * l * h ∈ L := (Subgroup.mem_normalizer_iff''.mp hh l).mp hl
  calc l * (h * p * h⁻¹) = h * ((h⁻¹ * l * h) * p) * h⁻¹ := by group
    _ = h * (p * (h⁻¹ * l * h)) * h⁻¹ := by rw [hp (h⁻¹ * l * h) hl']
    _ = (h * p * h⁻¹) * l := by group

private theorem isSylowIn_map_subtype {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (P : Sylow 2 ↥V) : IsSylowIn 2 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

theorem s3_sylow_cent (hS : HRSetting G L)
    (hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t) :
    IsSylowIn 2 (centralizer (L : Set G)) (zpowers s.t) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer (L : Set G)
  have htC : s.t ∈ C := s.t_mem
  have hztC : zpowers s.t ≤ C := Subgroup.zpowers_le.mpr s.t_mem
  have hP₀pg : IsPGroup 2 ((zpowers s.t).subgroupOf C) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hztC).toEquiv, Nat.card_zpowers,
      s.t_order, pow_one]
  obtain ⟨P₁, hP₀P₁⟩ := hP₀pg.exists_le_sylow
  let P : Subgroup G := (P₁ : Subgroup ↥C).map C.subtype
  have hPsylow : IsSylowIn 2 C P := isSylowIn_map_subtype (V := C) P₁
  have hPpg : IsPGroup 2 P := P₁.isPGroup'.map C.subtype
  have hPC : P ≤ C := Subgroup.map_subtype_le (P₁ : Subgroup ↥C)
  have htP : s.t ∈ P := by
    refine Subgroup.mem_map.mpr ⟨⟨s.t, htC⟩, hP₀P₁ ?_, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using Subgroup.zpow_mem_zpowers s.t 1
  haveI : IsCyclic ↥P := cyc_of_isPGroup_cent hS hPpg hPC
  have hPH : P ≤ s.H := by
    intro p hp
    change p ∈ centralizer ({s.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact congrArg Subtype.val (mul_comm' (⟨s.t, htP⟩ : ↥P) ⟨p, hp⟩)
  obtain ⟨h, hhH, hconjT⟩ :=
    exists_conj_le_isSylowIn (V := centralizer ({s.t} : Set G)) (P := s.T) (Q := P)
      s.sylow_T hPpg hPH
  have hhN : h ∈ normalizer (L : Set G) := s3_H_le_N s hS hhH
  have hconjC : conjSub h P ≤ C := by
    intro x hx
    change x ∈ P.map (MulAut.conj h).toMonoidHom at hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    change h * p * h⁻¹ ∈ centralizer (L : Set G)
    exact conj_mem_centralizer_of_mem_normalizer hhN (hPC hp)
  have hconj_inf : conjSub h P ≤ s.T ⊓ C := le_inf hconjT hconjC
  have hconj_zt : conjSub h P ≤ zpowers s.t := by
    rw [← hQ]
    exact hconj_inf
  have hcard_conj : Nat.card ↥(conjSub h P) ≤ 2 := by
    calc Nat.card ↥(conjSub h P) ≤ Nat.card ↥(zpowers s.t) := Subgroup.card_le_of_le hconj_zt
      _ = 2 := by rw [Nat.card_zpowers, s.t_order]
  have hcardP_le : Nat.card ↥P ≤ 2 := by
    have hmap : Nat.card ↥(conjSub h P) = Nat.card ↥P := by
      simpa only [conjSub] using
        Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (K := P)
          (MulAut.conj h).injective
    exact hmap ▸ hcard_conj
  have hztP : zpowers s.t ≤ P := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, rfl⟩
    exact P.zpow_mem htP k
  have hcardP_ge : 2 ≤ Nat.card ↥P := by
    calc 2 = Nat.card ↥(zpowers s.t) := by rw [Nat.card_zpowers, s.t_order]
      _ ≤ Nat.card ↥P := Subgroup.card_le_of_le hztP
  have hcardP : Nat.card ↥P = 2 := le_antisymm hcardP_le hcardP_ge
  have hPeq : P = zpowers s.t :=
    (Subgroup.eq_of_le_of_card_ge hztP (by rw [hcardP, Nat.card_zpowers, s.t_order])).symm
  change IsSylowIn 2 C (zpowers s.t)
  rw [← hPeq]
  exact hPsylow

end CFSG.OddStandard.HigherRank.YamadaG23
