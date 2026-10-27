module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped Pointwise

section CoreFree

variable {X : Type*} [Group X]

theorem eq_bot_of_normal_le_map_normalCore (Y : Subgroup X)
    (N : Subgroup (X ⧸ Y.normalCore)) [N.Normal]
    (hN : N ≤ Y.map (QuotientGroup.mk' Y.normalCore)) : N = ⊥ := by
  have h1 : N.comap (QuotientGroup.mk' Y.normalCore) ≤ Y := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hN hx
    have h2 : y⁻¹ * x ∈ Y.normalCore := QuotientGroup.eq.mp hyx
    have h3 : x = y * (y⁻¹ * x) := by group
    rw [h3]
    exact Y.mul_mem hy (Y.normalCore_le h2)
  have h4 : N.comap (QuotientGroup.mk' Y.normalCore) ≤ Y.normalCore :=
    Subgroup.normal_le_normalCore.mpr h1
  refine (Subgroup.eq_bot_iff_forall N).mpr fun n hn => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y.normalCore n
  exact (QuotientGroup.eq_one_iff x).mpr (h4 hn)

theorem pCore_quotient_normalCore_eq_bot [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X)
    (Y : Subgroup X) (hS : (S : Subgroup X) ≤ Y) : CFSG.pCore p (X ⧸ Y.normalCore) = ⊥ := by
  have hsurj := QuotientGroup.mk'_surjective Y.normalCore
  have h1 : CFSG.pCore p (X ⧸ Y.normalCore) ≤
      ((S.mapSurjective hsurj : Sylow p (X ⧸ Y.normalCore)) : Subgroup (X ⧸ Y.normalCore)) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup _
  rw [Sylow.coe_mapSurjective] at h1
  exact eq_bot_of_normal_le_map_normalCore Y _ (h1.trans (Subgroup.map_mono hS))

theorem mem_of_conj_le [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X) {Y : Subgroup X}
    (hN : normalizer ((S : Subgroup X) : Set X) ≤ Y) {g : X}
    (hg : ∀ s ∈ (S : Subgroup X), g * s * g⁻¹ ∈ Y) : g ∈ Y := by
  have hSY : (S : Subgroup X) ≤ Y := Subgroup.le_normalizer.trans hN
  have hmem : ∀ z : X, z ∈ ((g • S : Sylow p X) : Subgroup X) ↔ g⁻¹ * z * g ∈ (S : Subgroup X) := by
    intro z
    change z ∈ MulAut.conj g • (S : Subgroup X) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  have hS'Y : ((g • S : Sylow p X) : Subgroup X) ≤ Y := by
    intro x hx
    simpa [mul_assoc] using hg _ ((hmem x).mp hx)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y (S.subtype hSY) ((g • S).subtype hS'Y)
  have key : ∀ x : Y, ((x : X) ∈ ((g • S : Sylow p X) : Subgroup X)) ↔
      ((y : X)⁻¹ * (x : X) * (y : X) ∈ (S : Subgroup X)) := by
    intro x
    have h2 : x ∈ ((y • S.subtype hSY : Sylow p Y) : Subgroup Y) ↔
        x ∈ (((g • S).subtype hS'Y : Sylow p Y) : Subgroup Y) := by rw [hy]
    have h3 : x ∈ ((y • S.subtype hSY : Sylow p Y) : Subgroup Y) ↔
        y⁻¹ * x * y ∈ ((S.subtype hSY : Sylow p Y) : Subgroup Y) := by
      change x ∈ MulAut.conj y • ((S.subtype hSY : Sylow p Y) : Subgroup Y) ↔ _
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    rw [h3] at h2
    rw [Sylow.coe_subtype, Sylow.coe_subtype, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      at h2
    exact h2.symm
  have hn : (y : X)⁻¹ * g ∈ normalizer ((S : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have h1 : g * s * g⁻¹ ∈ Y := hg s hs
      have h2 := (key ⟨_, h1⟩).mp ((hmem _).mpr (by simpa [mul_assoc] using hs))
      simpa [mul_assoc] using h2
    · intro hs
      have hx : g * s * g⁻¹ ∈ Y := by
        have h1 : (y : X) * ((y : X)⁻¹ * g * s * ((y : X)⁻¹ * g)⁻¹) * (y : X)⁻¹ ∈ Y :=
          Y.mul_mem (Y.mul_mem y.2 (hSY hs)) (Y.inv_mem y.2)
        simpa [mul_assoc] using h1
      have h2 := (key ⟨_, hx⟩).mpr (by simpa [mul_assoc] using hs)
      simpa [mul_assoc] using (hmem _).mp h2
  have h5 : g = (y : X) * ((y : X)⁻¹ * g) := by group
  rw [h5]
  exact Y.mul_mem y.2 (hN hn)

theorem normalizer_map_le_map [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X)
    (N Y : Subgroup X) [N.Normal] (hNY : N ≤ Y)
    (hN : normalizer ((S : Subgroup X) : Set X) ≤ Y) :
    normalizer (((S : Subgroup X).map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
      Set (X ⧸ N)) ≤ Y.map (QuotientGroup.mk' N) := by
  intro z hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
  have hSY : (S : Subgroup X) ≤ Y := Subgroup.le_normalizer.trans hN
  refine ⟨g, mem_of_conj_le S hN fun s hs => ?_, rfl⟩
  have h1 : QuotientGroup.mk' N s ∈ (S : Subgroup X).map (QuotientGroup.mk' N) :=
    ⟨s, hs, rfl⟩
  obtain ⟨s', hs', hs'e⟩ := (Subgroup.mem_normalizer_iff.mp hz _).mp h1
  have h3 : s'⁻¹ * (g * s * g⁻¹) ∈ N := by
    have h4 : (QuotientGroup.mk' N) s' = (QuotientGroup.mk' N) (g * s * g⁻¹) := by
      rw [hs'e]
      simp
    exact QuotientGroup.eq.mp h4
  have h5 : g * s * g⁻¹ = s' * (s'⁻¹ * (g * s * g⁻¹)) := by group
  rw [h5]
  exact Y.mul_mem (hSY hs') (hNY h3)

theorem center_quotient_normalCore_eq_bot [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X)
    (Y : Subgroup X) (hN : normalizer ((S : Subgroup X) : Set X) ≤ Y) :
    Subgroup.center (X ⧸ Y.normalCore) = ⊥ := by
  refine eq_bot_of_normal_le_map_normalCore Y _ fun z hz => ?_
  refine normalizer_map_le_map S Y.normalCore Y Y.normalCore_le hN ?_
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.center_le_centralizer _ hz)

theorem dvd_card_quotient_normalCore [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X)
    (Y : Subgroup X) (hN : normalizer ((S : Subgroup X) : Set X) ≤ Y) (hne : Y ≠ ⊤) :
    p ∣ Nat.card (X ⧸ Y.normalCore) := by
  by_contra hp
  have h1 : (S : Subgroup X).map (QuotientGroup.mk' Y.normalCore) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
    obtain ⟨s, hs, rfl⟩ := hz
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hs⟩
    have h2 : orderOf (QuotientGroup.mk' Y.normalCore s) ∣ p ^ n := by
      have : (QuotientGroup.mk' Y.normalCore s) ^ (p ^ n) = 1 := by
        rw [← map_pow]
        have : s ^ (p ^ n) = 1 := by
          have := congrArg Subtype.val hn
          simpa using this
        rw [this, map_one]
      exact orderOf_dvd_of_pow_eq_one this
    have h3 : orderOf (QuotientGroup.mk' Y.normalCore s) ∣ Nat.card (X ⧸ Y.normalCore) :=
      orderOf_dvd_natCard _
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Fact.out).mp h2
    have hk0 : k = 0 := by
      by_contra hk0
      exact hp ((dvd_pow_self p hk0).trans (hk' ▸ h3))
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  have h2 : Y.map (QuotientGroup.mk' Y.normalCore) = ⊤ := by
    refine top_unique fun z _ => ?_
    refine normalizer_map_le_map S Y.normalCore Y Y.normalCore_le hN ?_
    rw [h1, Subgroup.mem_normalizer_iff]
    intro w
    simp [Subgroup.mem_bot]
  apply hne
  have h3 := congrArg (Subgroup.comap (QuotientGroup.mk' Y.normalCore)) h2
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr Y.normalCore_le,
    Subgroup.comap_top] at h3

end CoreFree

section Ker

variable {G : Type} [Group G] [Finite G] {M H Q : Subgroup G} {p : ℕ} [Fact p.Prime]

theorem normalizer_subgroupOf_le_subgroupOf (hQH : Q ≤ H) (hN : normalizer (Q : Set G) ≤ M) :
    normalizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) ≤ (M ⊓ H).subgroupOf H := by
  intro x hx
  refine Subgroup.mem_subgroupOf.mpr ⟨hN ?_, x.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_normalizer_iff] at hx
  by_cases hgH : g ∈ H
  · have h := hx ⟨g, hgH⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    simpa using h
  · have h1 : g ∉ Q := fun h => hgH (hQH h)
    have h2 : (x : G) * g * (x : G)⁻¹ ∉ Q := by
      intro h
      apply hgH
      have h3 := H.mul_mem (H.mul_mem (H.inv_mem x.2) (hQH h)) x.2
      simpa [mul_assoc] using h3
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem pCore_quotKer_eq_bot (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hQM : Q ≤ M) :
    CFSG.pCore p (QuotKer M H) = ⊥ := by
  obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
  refine pCore_quotient_normalCore_eq_bot S ((M ⊓ H).subgroupOf H) ?_
  rw [hS]
  exact fun x hx => Subgroup.mem_subgroupOf.mpr ⟨hQM (Subgroup.mem_subgroupOf.mp hx), x.2⟩

theorem center_quotKer_eq_bot (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hN : normalizer (Q : Set G) ≤ M) : Subgroup.center (QuotKer M H) = ⊥ := by
  obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
  refine center_quotient_normalCore_eq_bot S ((M ⊓ H).subgroupOf H) ?_
  rw [hS]
  exact normalizer_subgroupOf_le_subgroupOf hQ.le hN

theorem dvd_card_quotKer (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hN : normalizer (Q : Set G) ≤ M) (hH : ¬ H ≤ M) : p ∣ Nat.card (QuotKer M H) := by
  obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
  refine dvd_card_quotient_normalCore S ((M ⊓ H).subgroupOf H) ?_ ?_
  · rw [hS]
    exact normalizer_subgroupOf_le_subgroupOf hQ.le hN
  · intro htop
    apply hH
    intro x hx
    have : (⟨x, hx⟩ : ↥H) ∈ (M ⊓ H).subgroupOf H := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

end Ker

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
