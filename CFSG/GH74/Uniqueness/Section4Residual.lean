module

public import CFSG.GH74.Uniqueness.Section4Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

section OddClosure

variable {G : Type*} [Group G]

instance closure_odd_normal : (Subgroup.closure {y : G | Odd (orderOf y)}).Normal where
  conj_mem n hn g := by
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      change Odd (orderOf (MulAut.conj g x))
      rw [MulEquiv.orderOf_eq]
      exact hx
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa [mul_assoc] using Subgroup.inv_mem _ hx

theorem isPGroup_two_quotient_closure_odd [Finite G] :
    IsPGroup 2 (G ⧸ Subgroup.closure {y : G | Odd (orderOf y)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem _ fun x hx => ?_
  exact Subgroup.subset_closure (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hx))

theorem hom_eq_one_of_closure_odd_eq_top {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q)
    (h : Subgroup.closure {y : G | Odd (orderOf y)} = ⊤) (f : G →* Q) (g : G) : f g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.closure {y : G | Odd (orderOf y)} ≤ f.ker := by
    rw [Subgroup.closure_le]
    intro y hy
    by_contra hne
    have hd : 2 ∣ orderOf (f y) := hQ.dvd_orderOf hne
    have hd' : 2 ∣ orderOf y := hd.trans (orderOf_map_dvd f y)
    exact (Nat.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr hd')
  rw [h] at hle
  exact hle (Subgroup.mem_top g)

theorem sylow_le_commutator_of_closure_odd_eq_top [Finite G]
    (h : Subgroup.closure {y : G | Odd (orderOf y)} = ⊤) (P : Sylow 2 G) :
    (P : Subgroup G) ≤ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (↥(P : Subgroup G) ⧸ (P : Subgroup G).focalSubgroupOf) :=
    P.2.to_quotient _
  have hsurj := Subgroup.transferFocal_surjective P
  intro x hx
  have h1 : ((⟨x, hx⟩ : (P : Subgroup G)) : ↥(P : Subgroup G) ⧸ (P : Subgroup G).focalSubgroupOf)
      = 1 := by
    obtain ⟨g, hg⟩ := hsurj (((⟨x, hx⟩ : (P : Subgroup G)) :
      ↥(P : Subgroup G) ⧸ (P : Subgroup G).focalSubgroupOf))
    rw [← hg]
    exact hom_eq_one_of_closure_odd_eq_top hQ h _ g
  have h2 : (⟨x, hx⟩ : (P : Subgroup G)) ∈ (P : Subgroup G).focalSubgroupOf :=
    (QuotientGroup.eq_one_iff _).mp h1
  exact (P : Subgroup G).focalSubgroup_le_commutator (Subgroup.mem_subgroupOf.mp h2)

theorem closure_odd_eq_top_of_sylow_le [Finite G] (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≤ Subgroup.closure {y : G | Odd (orderOf y)}) :
    Subgroup.closure {y : G | Odd (orderOf y)} = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_two_quotient_closure_odd (G := G))
  have hidx : (Subgroup.closure {y : G | Odd (orderOf y)}).index = 2 ^ n := by
    rw [Subgroup.index_eq_card]
    exact hn
  have hdvd := Subgroup.index_dvd_of_le hP
  have hnd : ¬ 2 ∣ (P : Subgroup G).index := P.not_dvd_index
  cases n with
  | zero => exact Subgroup.index_eq_one.mp (by simpa using hidx)
  | succ n =>
    exact absurd (dvd_trans (by rw [hidx]; exact dvd_pow_self 2 (Nat.succ_ne_zero n)) hdvd) hnd

theorem closure_odd_eq_top_of_sylow_le_commutator [Finite G] (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≤ commutator G) :
    Subgroup.closure {y : G | Odd (orderOf y)} = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.closure {y : G | Odd (orderOf y)} with hN
  have hQ : IsPGroup 2 (G ⧸ N) := isPGroup_two_quotient_closure_odd
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hPtop : (P : Subgroup G).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := hQ.to_subgroup ⊤
    exact top_unique (h1.le_sylow_of_normal (P.mapSurjective hπ))
  have hperf : commutator (G ⧸ N) = ⊤ := by
    rw [eq_top_iff, ← hPtop]
    calc (P : Subgroup G).map (QuotientGroup.mk' N)
        ≤ (commutator G).map (QuotientGroup.mk' N) := Subgroup.map_mono hP
      _ = commutator (G ⧸ N) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          MonoidHom.range_eq_top_of_surjective _ hπ]
  have : Group.IsPerfect (G ⧸ N) := Group.isPerfect_def.mpr hperf
  have : Group.IsNilpotent (G ⧸ N) := hQ.isNilpotent
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ N := by
    by_contra hcon
    exact hne ((Subgroup.eq_top_iff' N).mpr fun g => by_contra fun hg => hcon ⟨g, hg⟩)
  have : Nontrivial (G ⧸ N) :=
    ⟨⟨(g : G ⧸ N), 1, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩⟩
  exact Group.IsPerfect.not_isNilpotent (G ⧸ N) ‹_›

end OddClosure

section Fusion

variable {X : Type} [Group X] {M : Subgroup X}

theorem commutator_inf_sylow_le_of_controlsFusion [Finite X] {p : ℕ} [Fact p.Prime]
    (T : Sylow p X) (hTM : (T : Subgroup X) ≤ M) (hM : ControlsFusion M (T : Subgroup X)) :
    commutator X ⊓ (T : Subgroup X) ≤ ⁅M, M⁆ := by
  rw [Subgroup.commutator_inf_eq_focalSubgroup T, Subgroup.focalSubgroup_def,
    Subgroup.closure_le]
  rintro g ⟨hgT, x, hxT, u, rfl⟩
  have hy : u * x * u⁻¹ ∈ (T : Subgroup X) := by
    have h1 : x⁻¹ * ⁅x, u⁆ ∈ (T : Subgroup X) :=
      (T : Subgroup X).mul_mem ((T : Subgroup X).inv_mem hxT) hgT
    have e : u * x * u⁻¹ = (x⁻¹ * ⁅x, u⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (T : Subgroup X).inv_mem h1
  obtain ⟨m, hmM, hm⟩ := hM {x} (Set.singleton_subset_iff.mpr hxT) {u * x * u⁻¹}
    (Set.singleton_subset_iff.mpr hy) ⟨u⁻¹, by simp [conjSet]⟩
  have hm' : m⁻¹ * x * m = u * x * u⁻¹ := by
    simpa [conjSet] using hm
  have e : ⁅x, u⁆ = ⁅x, m⁻¹⁆ := by
    have h1 : ⁅x, u⁆ = x * (u * x * u⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1, ← hm']
    simp only [commutatorElement_def]
    group
  rw [SetLike.mem_coe, e]
  exact Subgroup.commutator_mem_commutator (hTM hxT) (M.inv_mem hmM)

theorem map_subtype_closure_odd (H : Subgroup X) :
    (Subgroup.closure {y : H | Odd (orderOf y)}).map H.subtype =
      Subgroup.closure {y : X | y ∈ H ∧ Odd (orderOf y)} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa [Subgroup.orderOf_coe] using hy⟩
  · rintro ⟨hxH, hxodd⟩
    exact ⟨⟨x, hxH⟩, by simpa using hxodd, rfl⟩

theorem closure_odd_eq_top_iff_map (H : Subgroup X) :
    Subgroup.closure {y : H | Odd (orderOf y)} = ⊤ ↔
      Subgroup.closure {y : X | y ∈ H ∧ Odd (orderOf y)} = H := by
  rw [← map_subtype_closure_odd, ← Subgroup.map_subtype_inj, Subgroup.map_top,
    Subgroup.range_subtype]

end Fusion

section Lemma42b

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.closure_odd_eq_iff (S : ZDSetup X Z M) :
    Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} = M ↔
      Subgroup.closure {y : X | Odd (orderOf y)} = ⊤ := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨T, hTM, hzT, hcomm⟩ := S.exists_sylow_central hz hzM
  have hfus := S.controlsFusion_sylow hz hzM hTM hzT hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    refine closure_odd_eq_top_of_sylow_le T ?_
    calc (T : Subgroup X) ≤ M := hTM
      _ = Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} := h.symm
      _ ≤ Subgroup.closure {y : X | Odd (orderOf y)} :=
        Subgroup.closure_mono fun y hy => hy.2
  · intro h
    have h1 : (T : Subgroup X) ≤ commutator X := sylow_le_commutator_of_closure_odd_eq_top h T
    have h2 : (T : Subgroup X) ≤ ⁅M, M⁆ := fun t ht =>
      commutator_inf_sylow_le_of_controlsFusion T hTM hfus ⟨h1 ht, ht⟩
    rw [← closure_odd_eq_top_iff_map]
    refine closure_odd_eq_top_of_sylow_le_commutator (T.subtype hTM) ?_
    rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subtype_commutator,
      map_subtype_sylow_subtype T hTM]
    exact h2

theorem ZDSetup.closure_odd_ne_top_of_not_mem (S : ZDSetup X Z M) {u : X} (huM : u ∈ M)
    (hu : u ∉ Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)}) :
    Subgroup.closure {y : X | Odd (orderOf y)} ≠ ⊤ := fun h =>
  hu (by rw [S.closure_odd_eq_iff.mpr h]; exact huM)

end Lemma42b

end CFSG.GH74.Uniqueness
