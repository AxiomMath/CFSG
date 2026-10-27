module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AI
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G]

private theorem open_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hperf, hsimple⟩ := h
  haveI : Group.IsPerfect A := ⟨hperf⟩
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := hsimple
  exact ⟨(Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top,
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).symm.isSimpleGroup⟩

theorem y6f4a_standard_lift [Finite G] {g : G} (hg : orderOf g = 2)
    {K : Subgroup ↥(centralizer ({g} : Set G))} [K.Normal] (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKc : centralizer (K : Set ↥(centralizer ({g} : Set G))) = zpowers (y6f4aG g))
    (hperf : ∀ B : Subgroup ↥(centralizer ({g} : Set G)), Group.IsPerfect ↥B → B ≤ K)
    (h4 : 4 ∣ Nat.card ↥K) :
    ∃ A : Subgroup G, Nonempty (↥A ⧸ center ↥A ≃* ↥K ⧸ center ↥K) ∧
      CFSG.Open.standardComponentIsStandard A ∧
      ∀ S : Sylow 2 ↥(centralizer (A : Set G)), Nat.card S = 2 := by
  let C : Subgroup G := centralizer ({g} : Set G)
  let A : Subgroup G := K.map C.subtype
  let e : ↥K ≃* ↥A := Subgroup.equivMapOfInjective K C.subtype C.subtype_injective
  have hKcC : centralizer (K : Set ↥C) = zpowers (y6f4aG g) := hKc
  have hAmem : ∀ a : G, a ∈ A ↔ ∃ k : ↥C, k ∈ K ∧ C.subtype k = a := by
    intro a
    change a ∈ K.map C.subtype ↔ ∃ k : ↥C, k ∈ K ∧ C.subtype k = a
    exact Subgroup.mem_map
  have hA : CFSG.Open.IsQuasisimple ↥A := open_isQuasisimple_of_mulEquiv e hKq
  have hτA : g ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨k, _hk, rfl⟩ := (hAmem a).mp ha
    exact Subgroup.mem_centralizer_singleton_iff.mp k.2
  have hN : centralizer ({g} : Set G) ≤ normalizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨k, hk, rfl⟩ := (hAmem a).mp ha
      refine (hAmem (x * C.subtype k * x⁻¹)).mpr
        ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨x, hx⟩, ?_⟩
      show C.subtype (⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹) = x * C.subtype k * x⁻¹
      simp only [map_mul, map_inv]
      rfl
    · intro ha
      obtain ⟨k, hk, hk_eq⟩ := (hAmem (x * a * x⁻¹)).mp ha
      have hk' : (⟨x, hx⟩ : ↥C)⁻¹ * k * ⟨x, hx⟩ ∈ K := by
        simpa only [inv_inv] using
          Subgroup.Normal.conj_mem inferInstance k hk (⟨x, hx⟩ : ↥C)⁻¹
      refine (hAmem a).mpr ⟨⟨x, hx⟩⁻¹ * k * ⟨x, hx⟩, hk', ?_⟩
      show C.subtype (⟨x, hx⟩⁻¹ * k * ⟨x, hx⟩) = a
      rw [show C.subtype (⟨x, hx⟩⁻¹ * k * ⟨x, hx⟩) = x⁻¹ * C.subtype k * x by
        simp only [map_mul, map_inv]
        rfl, hk_eq]
      group
  have hC : centralizer (A : Set G) ⊓ centralizer ({g} : Set G) = zpowers g := by
    apply le_antisymm
    · intro x hx
      have hxA : x ∈ centralizer (A : Set G) := hx.1
      have hxC : x ∈ C := hx.2
      have hxc : (⟨x, hxC⟩ : ↥C) ∈ centralizer (K : Set ↥C) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hxA (k : G) ((hAmem (k : G)).mpr ⟨k, hk, rfl⟩)
      rw [hKcC] at hxc
      have hxmap : x ∈ (zpowers (y6f4aG g)).map C.subtype :=
        Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hxc, rfl⟩
      rwa [MonoidHom.map_zpowers, show C.subtype (y6f4aG g) = g from rfl] at hxmap
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨hτA, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hperfA : ∀ B : Subgroup G, B ≤ centralizer ({g} : Set G) → Group.IsPerfect ↥B → B ≤ A := by
    intro B hBC hB
    haveI : Group.IsPerfect ↥B := hB
    have hperfB : Group.IsPerfect ↥(B.subgroupOf C) := by
      have hsurj : Function.Surjective
          ((Subgroup.subgroupOfEquivOfLe hBC).symm : ↥B → ↥(B.subgroupOf C)) :=
        fun y => ⟨(Subgroup.subgroupOfEquivOfLe hBC) y, by simp⟩
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hBC).symm.toMonoidHom) hsurj
    have hleK : B.subgroupOf C ≤ K := hperf _ hperfB
    intro b hb
    exact (hAmem b).mpr
      ⟨⟨b, hBC hb⟩, hleK (by rw [Subgroup.mem_subgroupOf]; exact hb), rfl⟩
  have h4A : 4 ∣ Nat.card ↥A := by
    rw [← Nat.card_congr e.toEquiv]
    exact h4
  have hstd := y6f4a_standard_of_invol (X := G) (τ := g) (A := A) hg hA hτA hN hC hperfA h4A
  exact ⟨A, ⟨QuotientGroup.congr (Subgroup.center ↥A) (Subgroup.center ↥K) e.symm
    (Subgroup.map_center_eq e.symm)⟩, hstd.1, hstd.2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
