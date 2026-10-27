module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Generic

theorem perfectCore_range_inf_centralizer_map {B H : Type*} [Group B] [Group H] [Finite B]
    [Finite H] (Φ : B →* H) (hker : Φ.ker ≤ center B) (A : Subgroup B) :
    perfectCore (Φ.range ⊓ centralizer (A.map Φ : Set H)) =
      (perfectCore (centralizer (A : Set B))).map Φ := by
  have hT : (Φ.range ⊓ centralizer (A.map Φ : Set H)).comap Φ =
      LinearPilot.twistedFix (fun a : A => MulAut.conj (a : B)) Φ.ker hker := by
    ext x
    rw [mem_comap, LinearPilot.mem_twistedFix, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨-, h⟩ a
      have h1 := h (Φ a) ⟨a, a.2, rfl⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, MulAut.conj_apply, map_mul, map_mul, map_inv, h1]
      group
    · intro h
      refine ⟨⟨x, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      have h1 := h ⟨a, ha⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      calc Φ a * Φ x = Φ a * Φ x * (Φ a)⁻¹ * (Φ x)⁻¹ * (Φ x * Φ a) := by group
        _ = Φ x * Φ a := by rw [h1, one_mul]
  have hfix : LinearPilot.fixAll (fun a : A => MulAut.conj (a : B)) = centralizer (A : Set B) := by
    ext x
    rw [LinearPilot.mem_fixAll, mem_centralizer_iff]
    constructor
    · intro h a ha
      have h1 := h ⟨a, ha⟩
      rw [MulAut.conj_apply] at h1
      calc a * x = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h1]
    · intro h a
      rw [MulAut.conj_apply, h a a.2]
      group
  rw [← Subgroup.map_comap_eq_self (inf_le_left : _ ≤ Φ.range), ← CFSG.Quasithin.map_perfectCore,
    hT, LinearPilot.perfectCore_twistedFix, hfix]

theorem ct_inf_centralizer_map_subtype_eq {A : Type*} [Group A] {H : Subgroup A}
    (X : Subgroup H) :
    H ⊓ centralizer ((X.map H.subtype : Subgroup A) : Set A) =
      (centralizer (X : Set H)).map H.subtype := by
  ext y
  rw [mem_inf, mem_map]
  constructor
  · rintro ⟨hyH, hy⟩
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    rw [mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact mem_centralizer_iff.1 hy z ⟨z, hz, rfl⟩
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 hy' z hz)

end Generic

section Levi

variable {K : Type} [Field K] [CharP K 2] {N ε : ℕ}

theorem ctEmbed_rootTorusHom_apply_self (l : Fin N) (κ : Kˣ) (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    ((ctEmbed ε (rootTorusHom K N l κ) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (q2Coord N ε w) (q2Coord N ε w) =
        if w = Sum.inl (Sum.inl l) then (κ : K) else
          if w = Sum.inl (Sum.inr l) then ((κ⁻¹ : Kˣ) : K) else 1 := by
  rw [rootTorusHom_apply, ctEmbed_diagSp_apply_self]
  rcases w with (u | u) | i
  · by_cases h : u = l
    · subst h
      simp
    · simp [h]
  · by_cases h : u = l
    · subst h
      simp
    · simp [h]
  · simp

theorem perfectCore_q2Block_inf_centralizer_rootTorus [Finite K] (hK : 4 ≤ Nat.card K)
    {k l : Fin N} (h2 : 2 ≤ ((planeCoordsQ2 ε ({k, l} : Finset (Fin N)))ᶜ).card) :
    perfectCore (q2Block ε K {k} ⊓ centralizer
      (((rootTorusSp K l).map (ctEmbed ε) : Subgroup (SpecialLinearGroup (Fin (2 * N + ε)) K)) :
        Set (SpecialLinearGroup (Fin (2 * N + ε)) K))) = q2Block ε K {k, l} := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  have hκ1 : (κ : K) ≠ 1 := fun h => hκ (by
    have : κ = 1 := Units.ext h
    rw [this, one_mul])
  have hκi : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun h => hκ (by
    have h1 : κ = κ⁻¹ := Units.ext h
    calc κ * κ = κ * κ⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel κ)
  have hκi1 : ((κ⁻¹ : Kˣ) : K) ≠ 1 := fun h => hκ1 (by
    have : κ⁻¹ = 1 := Units.ext h
    rw [inv_eq_one] at this
    rw [this, Units.val_one])
  refine LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (Finset.compl_subset_compl.2 (planeCoordsQ2_mono (by simp))) _ ?_ ?_ ?_
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le h2 hK)
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩ i j hij
    exact ctEmbed_diagSp_apply_ne _ hij
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩ i hi j hj
    obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective i
    obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective j
    rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2] at hi hj
    rw [ctEmbed_rootTorusHom_apply_self, ctEmbed_rootTorusHom_apply_self,
      ite_eq_right (fun h => hi (by subst h; simp)), ite_eq_right (fun h => hi (by subst h; simp)),
      ite_eq_right (fun h => hj (by subst h; simp)), ite_eq_right (fun h => hj (by subst h; simp))]
  · intro i hi j hj hij hIJ
    refine ⟨ctEmbed ε (rootTorusHom K N l κ), ⟨_, ⟨κ, rfl⟩, rfl⟩, ?_⟩
    obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective i
    obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective j
    have hww : w ≠ w' := fun h => hij (h ▸ rfl)
    rw [ctEmbed_rootTorusHom_apply_self, ctEmbed_rootTorusHom_apply_self]
    simp only [Finset.mem_compl, q2Coord_mem_planeCoordsQ2, not_not] at hi hj hIJ
    have hl : ∀ v : (Fin N ⊕ Fin N) ⊕ Fin ε, ¬ InPlanes (ε := ε) {k} v →
        InPlanes (ε := ε) {k, l} v → v = Sum.inl (Sum.inl l) ∨ v = Sum.inl (Sum.inr l) := by
      intro v hv1 hv2
      rcases v with (u | u) | e
      · simp only [inPlanes_inl, planeOf_inl, Finset.mem_insert, Finset.mem_singleton] at hv1 hv2
        rcases hv2 with h | h
        · exact absurd h hv1
        · exact Or.inl (by rw [h])
      · simp only [inPlanes_inl, planeOf_inr, Finset.mem_insert, Finset.mem_singleton] at hv1 hv2
        rcases hv2 with h | h
        · exact absurd h hv1
        · exact Or.inr (by rw [h])
      · exact absurd hv2 (not_inPlanes_inr _ _)
    rcases hIJ with h | h
    · rcases hl w hi h with rfl | rfl <;>
        by_cases h1 : w' = Sum.inl (Sum.inl l) <;> by_cases h2 : w' = Sum.inl (Sum.inr l) <;>
          simp_all [eq_comm]
    · rcases hl w' hj h with rfl | rfl <;>
        by_cases h1 : w = Sum.inl (Sum.inl l) <;> by_cases h2 : w = Sum.inl (Sum.inr l) <;>
          simp_all [eq_comm]

end Levi

section Overlap

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {N ε : ℕ} {e : L ≃* StatedSp N K}

omit [Finite G] in
theorem CtLinParam.map_rootTorus_eq {k : Fin N} (P : CtLinParam ε e k) {l : Fin N}
    (hkl : k ≠ l) :
    (((rootTorusSp K l).map (ctEmbed ε)).subgroupOf (q2Block ε K {k})).map P.Φ =
      modelToG e (rootTorusSp K l) := by
  have hX : ∀ y ∈ rootTorusSp K l, y ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
    intro y hy
    have h1 : y ∈ spBlock K ({l} : Finset (Fin N)) := by
      rw [spBlock_singleton]
      exact rootTorusSp_le_longRootSp2 l hy
    exact spBlock_mono (by simpa using hkl) h1
  ext g
  constructor
  · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
    have hx : x = ⟨ctEmbed ε y, ctEmbed_mem_q2Block_iff.2 (hX y hy)⟩ := Subtype.ext hyx.symm
    rw [hx, P.N1 y (hX y hy)]
    exact UnitaryPilot.symm_mem_modelToG e hy
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    exact ⟨⟨ctEmbed ε y, ctEmbed_mem_q2Block_iff.2 (hX y hy)⟩, ⟨y, hy, rfl⟩, P.N1 y (hX y hy)⟩

theorem CtLinParam.map_overlap_eq [Finite K] (hK : 4 ≤ Nat.card K) {k : Fin N}
    (P : CtLinParam ε e k) {l : Fin N} (hkl : k ≠ l)
    (h2 : 2 ≤ ((planeCoordsQ2 ε ({k, l} : Finset (Fin N)))ᶜ).card) :
    ((q2Block ε K {k, l}).subgroupOf (q2Block ε K {k})).map P.Φ =
      centralizerPerfectCore (modelToG e (rootTorusSp K k) ⊔ modelToG e (rootTorusSp K l)) := by
  rw [F4Pilot.centralizerPerfectCore_sup,
    show centralizerPerfectCore (modelToG e (rootTorusSp K k)) = neighbourCore e k from rfl,
    ← P.range_eq, ← P.map_rootTorus_eq hkl,
    perfectCore_range_inf_centralizer_map P.Φ P.ker_le]
  congr 1
  apply Subgroup.map_injective (q2Block ε K {k}).subtype_injective
  have hXle : (rootTorusSp K l).map (ctEmbed ε) ≤ q2Block ε K {k} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : y ∈ spBlock K ({l} : Finset (Fin N)) := by
      rw [spBlock_singleton]
      exact rootTorusSp_le_longRootSp2 l hy
    exact ctEmbed_mem_q2Block_iff.2 (spBlock_mono (by simpa using hkl) h1)
  have hA : (((rootTorusSp K l).map (ctEmbed ε)).subgroupOf (q2Block ε K {k})).map
      (q2Block ε K {k}).subtype = (rootTorusSp K l).map (ctEmbed ε) := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hXle]
  have hB : ((q2Block ε K {k, l}).subgroupOf (q2Block ε K {k})).map (q2Block ε K {k}).subtype =
      q2Block ε K {k, l} := by
    rw [subgroupOf_map_subtype,
      inf_eq_left.mpr (q2Block_anti (by simp : ({k} : Finset (Fin N)) ⊆ {k, l}))]
  rw [hB, CFSG.Quasithin.map_perfectCore, ← ct_inf_centralizer_map_subtype_eq, hA,
    perfectCore_q2Block_inf_centralizer_rootTorus hK h2]

end Overlap

end CFSG.SeitzReduction.SymplecticPilot
