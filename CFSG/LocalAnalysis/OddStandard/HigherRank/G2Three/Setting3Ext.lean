module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Setting3

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

private theorem isSylowIn_map_subtype {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (P : Sylow 2 ↥V) : IsSylowIn 2 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

private theorem eq_of_isSylowIn_of_isPGroup_of_le {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {V P Q : Subgroup G} (hP : IsSylowIn p V P) (hQ : IsPGroup p Q)
    (hQV : Q ≤ V) (hPQ : P ≤ Q) : P = Q := by
  have hprod : P.relIndex Q * Q.relIndex V = P.relIndex V :=
    Subgroup.relIndex_mul_relIndex (H := P) (K := Q) (L := V) hPQ hQV
  have hdvd : P.relIndex Q ∣ P.relIndex V := ⟨Q.relIndex V, hprod.symm⟩
  obtain ⟨n, hn⟩ := hQ.index (P.subgroupOf Q)
  have hrel : P.relIndex Q = p ^ n := by
    rw [Subgroup.relIndex]
    exact hn
  have hodd : ¬ p ∣ P.relIndex Q := fun hp => hP.2.2 (hp.trans hdvd)
  have hn0 : n = 0 := by
    by_contra h0
    exact hodd (hrel.symm ▸ dvd_pow_self p h0)
  have hone : P.relIndex Q = 1 := by rw [hrel, hn0, pow_zero]
  exact le_antisymm hPQ (Subgroup.relIndex_eq_one.mp hone)

private theorem normalizer_le_normalizer_centralizer {G : Type} [Group G] {R : Subgroup G} :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hr' : x⁻¹ * r * x ∈ R := (Subgroup.mem_normalizer_iff''.mp hx r).mp hr
    calc r * (x * c * x⁻¹)
        = x * ((x⁻¹ * r * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * r * x)) * x⁻¹ := by rw [hc _ hr']
      _ = (x * c * x⁻¹) * r := by group
  · intro hc
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (R : Set G) := Subgroup.inv_mem _ hx
    have hmem : x⁻¹ * (x * c * x⁻¹) * (x⁻¹)⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro r hr
      have hr' : x * r * x⁻¹ ∈ R := by
        simpa only [inv_inv] using (Subgroup.mem_normalizer_iff''.mp hxinv r).mp hr
      calc r * (x⁻¹ * (x * c * x⁻¹) * (x⁻¹)⁻¹)
          = x⁻¹ * ((x * r * x⁻¹) * (x * c * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * c * x⁻¹) * (x * r * x⁻¹)) * x := by rw [hc _ hr']
        _ = (x⁻¹ * (x * c * x⁻¹) * (x⁻¹)⁻¹) * r := by group
    have hsimp : x⁻¹ * (x * c * x⁻¹) * (x⁻¹)⁻¹ = c := by group
    rwa [hsimp] at hmem

theorem nonempty_ext {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : HRSetting G L)
    (s : Setting3 G L) : Nonempty (Ext s) := by
  classical
  obtain ⟨hLH, -, hHnorm⟩ := Setup.normal_centralizer hS s.t_mem s.t_order
  let X : Subgroup G := L ⊔ (s.H ⊓ Subgroup.centralizer (L : Set G))
  have hRX : s.R ≤ X := s.sylow_R.1
  have hT_normalizes_X : s.T ≤ Subgroup.normalizer (X : Set G) := by
    intro x hx
    have hxH : x ∈ s.H := s.sylow_T.1 hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hHnorm hxH
    have hxH' : x ∈ Subgroup.normalizer (s.H : Set G) := Subgroup.le_normalizer hxH
    have hxCL : x ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G)) :=
      normalizer_le_normalizer_centralizer hxL
    have hxCHL : x ∈ Subgroup.normalizer (s.H ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
      inf_normalizer_le_normalizer_inf (H := s.H) (K := Subgroup.centralizer (L : Set G))
        ⟨hxH', hxCL⟩
    exact inf_normalizer_le_normalizer_sup (H := L)
      (K := s.H ⊓ Subgroup.centralizer (L : Set G)) ⟨hxL, hxCHL⟩
  have hR_le : s.R ≤ s.T ⊓ X := le_inf s.R_le_T hRX
  have hR_eq : s.R = s.T ⊓ X :=
    eq_of_isSylowIn_of_isPGroup_of_le (V := X) (P := s.R) (Q := s.T ⊓ X)
      s.sylow_R (IsPGroup.to_inf_left s.sylow_T.2.1) inf_le_right hR_le
  have hT_normalizes_R : s.T ≤ Subgroup.normalizer (s.R : Set G) := by
    intro x hx
    have hxT : x ∈ Subgroup.normalizer (s.T : Set G) := Subgroup.le_normalizer hx
    have hxX : x ∈ Subgroup.normalizer (X : Set G) := hT_normalizes_X hx
    rw [hR_eq, Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp hxT y),
      (Subgroup.mem_normalizer_iff.mp hxX y)]
  have hT_normalizes_cenR : s.T ≤ Subgroup.normalizer (cen s.R : Set G) := by
    intro x hx
    have hxR : x ∈ Subgroup.normalizer (s.R : Set G) := hT_normalizes_R hx
    have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (s.R : Set G)) :=
      normalizer_le_normalizer_centralizer hxR
    have h := inf_normalizer_le_normalizer_inf (H := s.R)
      (K := Subgroup.centralizer (s.R : Set G)) ⟨hxR, hxC⟩
    simpa only [cen] using h
  let N : Subgroup G := Subgroup.normalizer (cen s.R : Set G)
  have hTN : s.T ≤ N := hT_normalizes_cenR
  have hsub : IsPGroup 2 (s.T.subgroupOf N) := s.sylow_T.2.1.comap_subtype (K := N)
  obtain ⟨P, hPle⟩ := hsub.exists_le_sylow
  let T₁ : Subgroup G := (P : Subgroup ↥N).map N.subtype
  have hsylow : IsSylowIn 2 N T₁ := isSylowIn_map_subtype P
  have hTle : s.T ≤ T₁ := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hTN hx⟩, hPle (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hN : N = Subgroup.normalizer (cen s.R : Set G) := rfl
  exact ⟨{ T₁ := T₁, sylow := hN ▸ hsylow, T_le := hTle }⟩

end CFSG.OddStandard.HigherRank.G2Three.Setting3
