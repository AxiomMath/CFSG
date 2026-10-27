module

public import CFSG.Foundations.KCoreOpen

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

private theorem chevTools_mem_sup_eq_mul {G : Type} [Group G] {K A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) {y : G} (hy : y ∈ K ⊔ A) :
    ∃ a ∈ A, ∃ k ∈ K, y = a * k := by
  rw [sup_comm] at hy
  have h : y ∈ (↑(A ⊔ K) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A K hA] at h
  obtain ⟨a, ha, k, hk, hak⟩ := Set.mem_mul.1 h
  exact ⟨a, ha, k, hk, hak.symm⟩

private theorem chevTools_normal_subgroupOf_sup {G : Type} [Group G] {K A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) : (K.subgroupOf (K ⊔ A)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le Subgroup.le_normalizer hA)

private theorem chevTools_isSolvable_quotient_pGroup {Y Pg : Type} [Group Y] [Group Pg]
    [Finite Pg] {p : ℕ} [Fact p.Prime] (N : Subgroup Y) [N.Normal] (hP : IsPGroup p Pg)
    (φ : Pg →* Y ⧸ N) (hφ : Function.Surjective φ) : Group.IsSolvable (Y ⧸ N) := by
  haveI := hP.isNilpotent
  exact Group.isSolvable_of_surjective hφ

private theorem chevTools_isSolvable_quotient_sup {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G))
    (hp : IsPGroup p ↥A) [(K.subgroupOf (K ⊔ A)).Normal] :
    Group.IsSolvable (↥(K ⊔ A) ⧸ K.subgroupOf (K ⊔ A)) := by
  refine chevTools_isSolvable_quotient_pGroup (K.subgroupOf (K ⊔ A)) hp
    ((QuotientGroup.mk' (K.subgroupOf (K ⊔ A))).comp
      (Subgroup.inclusion (le_sup_right : A ≤ K ⊔ A))) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf (K ⊔ A)) q
  obtain ⟨a, ha, k, hk, hyak⟩ := chevTools_mem_sup_eq_mul hA y.2
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  refine QuotientGroup.eq.2 ?_
  rw [Subgroup.mem_subgroupOf]
  change (a : G)⁻¹ * (y : G) ∈ K
  rw [hyak, inv_mul_cancel_left]
  exact hk

private theorem chevTools_le_of_perfect_quotient {Y : Type} [Group Y] (N : Subgroup Y) [N.Normal]
    [Group.IsSolvable (Y ⧸ N)] (P : Subgroup Y) (hperf : ⁅P, P⁆ = P) : P ≤ N := by
  have hM : ⁅P.map (QuotientGroup.mk' N), P.map (QuotientGroup.mk' N)⁆ =
      P.map (QuotientGroup.mk' N) := by
    rw [← Subgroup.map_commutator, hperf]
  have hM0 : P.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra h
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot h
    rw [hM] at hlt
    exact lt_irrefl _ hlt
  intro x hx
  have hxM : QuotientGroup.mk' N x ∈ P.map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hM0, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hxM
  exact (QuotientGroup.eq_one_iff x).1 hxM

private theorem chevTools_isKGroup_of_hom {X Q : Type} [Group X] [Group Q] (f : X →* Q)
    (hk : CFSG.Open.IsKGroup ↥f.ker) [Group.IsSolvable Q] : CFSG.Open.IsKGroup X := by
  intro M R _ _ hs hnonab
  let π : M →* M ⧸ R.subgroupOf M := QuotientGroup.mk' (R.subgroupOf M)
  let ρ : M →* Q := f.comp M.subtype
  have hMn : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hmapn : (ρ.ker.map π).Normal := hMn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with hbot | htop
  · exfalso
    have hle : ρ.ker ≤ π.ker := by
      intro m hm
      have hmem : π m ∈ ρ.ker.map π := Subgroup.mem_map_of_mem π hm
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
    have hker : ρ.rangeRestrict.ker ≤ π.ker := by
      rwa [MonoidHom.ker_rangeRestrict]
    let φ : ρ.range →* M ⧸ R.subgroupOf M :=
      MonoidHom.liftOfSurjective ρ.rangeRestrict hsurj ⟨π, hker⟩
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) y
      exact ⟨ρ.rangeRestrict m, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
    have hsolv : Group.IsSolvable (M ⧸ R.subgroupOf M) := Group.isSolvable_of_surjective hφ
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  · let K' : Subgroup ↥f.ker := M.comap f.ker.subtype
    let ι : K' →* M :=
      { toFun := fun k => ⟨k.1.1, k.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Surjective (π.comp ι) := by
      intro y
      have hy : y ∈ ρ.ker.map π := by rw [htop]; trivial
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
      have hmk : (m : X) ∈ f.ker := hm
      exact ⟨⟨⟨m, hmk⟩, m.2⟩, rfl⟩
    exact hk.isCatalogGroup_of_surjective K' hnonab (π.comp ι) hφ

private theorem chevTools_isKGroup_sup_of_prime {G : Type} [Group G] [Finite G] {p : ℕ}
    (hpr : p.Prime) {K A : Subgroup G} (hK : CFSG.Open.IsKGroup ↥K)
    (hA : A ≤ Subgroup.normalizer (K : Set G)) (hp : IsPGroup p ↥A) :
    CFSG.Open.IsKGroup ↥(K ⊔ A) := by
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI := chevTools_normal_subgroupOf_sup hA
  have hN : CFSG.Open.IsKGroup ↥(K.subgroupOf (K ⊔ A)) :=
    hK.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ A)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ A)).injective
  have hk : CFSG.Open.IsKGroup ↥(QuotientGroup.mk' (K.subgroupOf (K ⊔ A)) :
      ↥(K ⊔ A) →* ↥(K ⊔ A) ⧸ K.subgroupOf (K ⊔ A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN
  haveI := chevTools_isSolvable_quotient_sup hA hp
  exact chevTools_isKGroup_of_hom (QuotientGroup.mk' (K.subgroupOf (K ⊔ A))) hk

private theorem chevTools_perfect_le_of_sup_of_prime {G : Type} [Group G] [Finite G] {p : ℕ}
    (hpr : p.Prime) {K A L : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G))
    (hp : IsPGroup p ↥A) (hL : L ≤ K ⊔ A) (hperf : ⁅L, L⁆ = L) : L ≤ K := by
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI := chevTools_normal_subgroupOf_sup hA
  haveI := chevTools_isSolvable_quotient_sup hA hp
  have hPperf : ⁅L.subgroupOf (K ⊔ A), L.subgroupOf (K ⊔ A)⁆ = L.subgroupOf (K ⊔ A) := by
    apply Subgroup.map_injective (K ⊔ A).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hL]
    exact hperf
  have hle := chevTools_le_of_perfect_quotient (K.subgroupOf (K ⊔ A))
    (L.subgroupOf (K ⊔ A)) hPperf
  intro x hx
  have hxs : (⟨x, hL hx⟩ : ↥(K ⊔ A)) ∈ L.subgroupOf (K ⊔ A) := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_subgroupOf.1 (hle hxs)

theorem chevTools_isKGroup_sup {G : Type} [Group G] [Finite G] {p : ℕ} (hpr : p.Prime)
    {K A : Subgroup G} (hK : CFSG.Open.IsKGroup ↥K) (hA : A ≤ Subgroup.normalizer (K : Set G))
    (hp : IsPGroup p ↥A) : CFSG.Open.IsKGroup ↥(K ⊔ A) :=
  chevTools_isKGroup_sup_of_prime hpr hK hA hp

theorem chevTools_perfect_le_of_sup {G : Type} [Group G] [Finite G] {p : ℕ} (hpr : p.Prime)
    {K A L : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G)) (hp : IsPGroup p ↥A)
    (hL : L ≤ K ⊔ A) (hperf : ⁅L, L⁆ = L) : L ≤ K :=
  chevTools_perfect_le_of_sup_of_prime hpr hA hp hL hperf

end CFSG.LocalAnalysis.GLTheoremA
