module

public import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

private theorem map_ne_bot_clift {G : Type*} [Group G] {r : ℕ} [Fact r.Prime]
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) {U : Subgroup G} (hU : U ≠ ⊥) (hUr : IsPGroup r U) :
    U.map (QuotientGroup.mk' Z) ≠ ⊥ := by
  intro hbot
  apply hU
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx1 : QuotientGroup.mk' Z x = 1 :=
    MonoidHom.mem_ker.mp ((Subgroup.map_eq_bot_iff U).mp hbot hx)
  obtain ⟨n, hn⟩ := hUr ⟨x, hx⟩
  have hxn : x ^ r ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxbot : x ∈ (⊥ : Subgroup G) :=
    mem_of_mk_mem_map Z hZ hZr (Q := ⊥) IsPGroup.of_bot
      (by rw [Subgroup.map_bot]; simpa using hx1) hxn
  simpa using hxbot

private theorem pCoreOf_normalizer_le_comap_clift {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) {U : Subgroup G} (hUr : IsPGroup r U)
    {Pbar : Subgroup (G ⧸ Z)}
    (hcorebar : pCoreOf r (Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))) ≤
      pCoreOf r Pbar) :
    pCoreOf r (Subgroup.normalizer (U : Set G)) ≤ pCoreOf r (Pbar.comap (QuotientGroup.mk' Z)) := by
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hNU : Subgroup.normalizer (U : Set G) =
      (Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
        (QuotientGroup.mk' Z) :=
    normalizer_eq_comap_normalizer_map Z hZ hZr hUr
  have hmap : (pCoreOf r (Subgroup.normalizer (U : Set G))).map (QuotientGroup.mk' Z) ≤
      (pCoreOf r (Pbar.comap (QuotientGroup.mk' Z))).map (QuotientGroup.mk' Z) := by
    refine (map_pCoreOf_le (QuotientGroup.mk' Z) (Subgroup.normalizer (U : Set G))).trans ?_
    have hmap2 : (Subgroup.normalizer (U : Set G)).map (QuotientGroup.mk' Z) =
        Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) := by
      rw [hNU, Subgroup.map_comap_eq_self_of_surjective hπ]
    rw [hmap2]
    exact hcorebar.trans (pCoreOf_le_map_pCoreOf_comap Z hZ hZr Pbar)
  intro x hx
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup r (Subgroup.normalizer (U : Set G))) ⟨x, hx⟩
  exact mem_of_mk_mem_map Z hZ hZr (pCoreOf_isPGroup r (Pbar.comap (QuotientGroup.mk' Z)))
    (hmap (Subgroup.mem_map_of_mem _ hx)) (by simpa using congrArg Subtype.val hn)

theorem Holds.of_quotient {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) (h : Holds (G ⧸ Z) r) : Holds G r := by
  intro U hU hUr
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  obtain ⟨Sbar, Pbar, hPbar, hNbar, hcorebar, -, hSbar⟩ :=
    h (U.map (QuotientGroup.mk' Z)) (map_ne_bot_clift Z hZ hZr hU hUr)
      (hUr.map (QuotientGroup.mk' Z))
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ r Sbar
  have hSmap : ((S : Subgroup G).map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) =
      ((Sbar : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) := by
    have h : ((S : Subgroup G).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) =
        (Sbar : Subgroup (G ⧸ Z)) := by
      have h' := congrArg (fun x : Sylow r (G ⧸ Z) => (x : Subgroup (G ⧸ Z))) hS
      rwa [Sylow.coe_mapSurjective] at h'
    exact congrArg (fun x : Subgroup (G ⧸ Z) => (x : Set (G ⧸ Z))) h
  refine conclusion_of_core r U hUr S (Pbar.comap (QuotientGroup.mk' Z)) ?_ ?_ ?_ ?_
  · intro htop
    apply hPbar
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ Pbar, htop,
      Subgroup.map_top_of_surjective _ hπ]
  · rw [normalizer_eq_comap_normalizer_map Z hZ hZr hUr]
    exact Subgroup.comap_mono hNbar
  · exact pCoreOf_normalizer_le_comap_clift Z hZ hZr hUr hcorebar
  · rw [normalizer_eq_comap_normalizer_map Z hZ hZr S.isPGroup', hSmap]
    exact Subgroup.comap_mono hSbar

theorem Holds.of_quotient_center {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (hZr : Nat.Coprime (Nat.card (Subgroup.center G)) r)
    (h : Holds (G ⧸ Subgroup.center G) r) : Holds G r :=
  Holds.of_quotient (Subgroup.center G) le_rfl hZr h

end CFSG.LieType.BorelTits
