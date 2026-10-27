module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_two {H N : Subgroup G} {t : G} (htH : t ∈ H) (htN : t ∉ N)
    (hsplit : ∀ b ∈ H, b ∈ N ∨ b * t ∈ N) : N.relIndex H = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htH⟩, fun b => ?_⟩
  have key : (b : G) ∈ N ∨ (b : G) * t ∈ N := hsplit b b.2
  have hmem : ∀ c : H, c ∈ N.subgroupOf H ↔ (c : G) ∈ N := fun c => mem_subgroupOf
  rw [hmem, hmem]
  show Xor ((b : G) * t ∈ N) ((b : G) ∈ N)
  rcases key with h1 | h1
  · refine Or.inr ⟨h1, fun h2 => htN ?_⟩
    have := N.mul_mem (N.inv_mem h1) h2
    simpa using this
  · refine Or.inl ⟨h1, fun h2 => htN ?_⟩
    have := N.mul_mem (N.inv_mem h2) h1
    simpa using this

theorem exists_sylow_le_centralizer {t u : G} (ht : orderOf t = 2) (hu : orderOf u = 2)
    (hut : u * t = t * u) (hiso : ∀ t' ∈ fusedSet u t, t' = t) :
    ∃ P : Sylow 2 G, t ∈ P ∧ u ∈ P ∧ (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := centralizer ({t} : Set G) with hM
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  have huM : u ∈ M := mem_centralizer_singleton_iff.2 hut
  let tM : M := ⟨t, htM⟩
  let uM : M := ⟨u, huM⟩
  have htM2 : orderOf tM = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have huM2 : orderOf uM = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hpu : IsPGroup 2 (zpowers uM) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huM2, pow_one])
  obtain ⟨T0, hT0u⟩ := hpu.exists_le_sylow
  have huT0 : uM ∈ T0 := hT0u (mem_zpowers uM)
  have hpt : IsPGroup 2 (zpowers tM) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htM2, pow_one])
  have hcen : zpowers tM ≤ center M := by
    rw [zpowers_le]
    refine mem_center_iff.2 fun g => Subtype.ext ?_
    exact mem_centralizer_singleton_iff.1 g.2
  have hnorm : (zpowers tM).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n = n * g := mem_center_iff.1 (hcen hn) g
    rw [h1, mul_inv_cancel_right]
    exact hn
  have htT0 : tM ∈ T0 := hpt.le_sylow_of_normal T0 (mem_zpowers tM)
  set T : Subgroup G := (T0 : Subgroup M).map M.subtype with hT
  have hTp : IsPGroup 2 T := T0.isPGroup'.map M.subtype
  have hTM : T ≤ M := map_subtype_le _
  have htT : t ∈ T := ⟨tM, htT0, rfl⟩
  have huT : u ∈ T := ⟨uM, huT0, rfl⟩
  have memT : ∀ g : M, g ∈ (T0 : Subgroup M) ↔ (g : G) ∈ T := fun g =>
    ⟨fun hg => ⟨g, hg, rfl⟩, fun ⟨g', hg', e⟩ => by
      have : g' = g := Subtype.ext e
      exact this ▸ hg'⟩
  obtain ⟨P, hTP⟩ := hTp.exists_le_sylow
  have hPT : (P : Subgroup G) ≤ T := by
    by_contra hnot
    have hlt : T < P := lt_of_le_of_ne hTP (fun e => hnot e.ge)
    have hnil : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
    have hH : T.subgroupOf P < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
      exact fun h => hnot h
    obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hH)
    set xg : G := (x : G) with hxg
    have hxP : xg ∈ P := x.2
    have hxT : xg ∉ T := fun h => hxn (mem_subgroupOf.2 h)
    have hconj : ∀ y ∈ T, xg * y * xg⁻¹ ∈ T := by
      intro y hy
      have hyH : (⟨y, hTP hy⟩ : P) ∈ T.subgroupOf P := mem_subgroupOf.2 hy
      have := (mem_normalizer_iff.1 hx _).1 hyH
      exact mem_subgroupOf.1 this
    have hconj' : ∀ y ∈ T, xg⁻¹ * y * xg ∈ T := by
      intro y hy
      have hyP : y ∈ P := hTP hy
      have hmemP : xg⁻¹ * y * xg ∈ P :=
        P.mul_mem (P.mul_mem (P.inv_mem hxP) hyP) hxP
      have hyH : (⟨y, hyP⟩ : P) ∈ T.subgroupOf P := mem_subgroupOf.2 hy
      have e : x * (⟨xg⁻¹ * y * xg, hmemP⟩ : P) * x⁻¹ = ⟨y, hyP⟩ :=
        Subtype.ext (by show xg * (xg⁻¹ * y * xg) * xg⁻¹ = y; group)
      have := (mem_normalizer_iff.1 hx ⟨xg⁻¹ * y * xg, hmemP⟩).2 (e ▸ hyH)
      exact mem_subgroupOf.1 this
    have hyu : (xg * u * xg⁻¹) * t = t * (xg * u * xg⁻¹) :=
      mem_centralizer_singleton_iff.1 (hTM (hconj u huT))
    have hyt : (xg * t * xg⁻¹) * t = t * (xg * t * xg⁻¹) :=
      mem_centralizer_singleton_iff.1 (hTM (hconj t htT))
    have hmem : xg⁻¹ * t * xg ∈ fusedSet u t := by
      refine ⟨isConj_iff.2 ⟨xg⁻¹, by simp⟩, ?_, ?_⟩
      · calc xg⁻¹ * t * xg * u = xg⁻¹ * (t * (xg * u * xg⁻¹)) * xg := by group
          _ = xg⁻¹ * ((xg * u * xg⁻¹) * t) * xg := by rw [← hyu]
          _ = u * (xg⁻¹ * t * xg) := by group
      · calc xg⁻¹ * t * xg * t = xg⁻¹ * (t * (xg * t * xg⁻¹)) * xg := by group
          _ = xg⁻¹ * ((xg * t * xg⁻¹) * t) * xg := by rw [← hyt]
          _ = t * (xg⁻¹ * t * xg) := by group
    have h1 := hiso _ hmem
    have hxM : xg ∈ M := by
      refine mem_centralizer_singleton_iff.2 ?_
      calc xg * t = xg * (xg⁻¹ * t * xg) := by rw [h1]
        _ = t * xg := by group
    let x' : M := ⟨xg, hxM⟩
    have hx'n : x' ∈ normalizer (T0 : Subgroup M) := by
      refine mem_normalizer_iff.2 fun g => ?_
      constructor
      · intro hg
        rw [memT] at hg ⊢
        exact hconj _ hg
      · intro hg
        rw [memT] at hg ⊢
        have := hconj' _ hg
        have e : xg⁻¹ * ((x' * g * x'⁻¹ : M) : G) * xg = (g : G) := by
          show xg⁻¹ * (xg * (g : G) * xg⁻¹) * xg = (g : G)
          group
        rw [e] at this
        exact this
    have hP2 : IsPGroup 2 ((zpowers xg).comap M.subtype) :=
      (P.isPGroup'.to_le (zpowers_le.2 hxP)).comap_of_injective M.subtype M.subtype_injective
    have hx'z : x' ∈ (zpowers xg).comap M.subtype := mem_zpowers xg
    have hfin := hP2.inf_normalizer_sylow T0
    have hx'T0 : x' ∈ (zpowers xg).comap M.subtype ⊓ (T0 : Subgroup M) := by
      rw [← hfin]
      exact ⟨hx'z, hx'n⟩
    exact hxT ((memT x').1 hx'T0.2)
  have hTeq : (P : Subgroup G) ≤ M := hPT.trans hTM
  exact ⟨P, hTP htT, hTP huT, hTeq⟩

end CFSG.EvenSporadicStandard.Solomon78
