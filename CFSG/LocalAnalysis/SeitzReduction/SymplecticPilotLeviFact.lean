module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCoresMonomial
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresAbstract
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTablesSp6

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll)

section PlaneCoords

variable {n : ℕ}

@[expose] def planeOf : Fin n ⊕ Fin n → Fin n := Sum.elim id id

@[simp] theorem planeOf_inl (i : Fin n) : planeOf (Sum.inl i : Fin n ⊕ Fin n) = i := rfl

@[simp] theorem planeOf_inr (i : Fin n) : planeOf (Sum.inr i : Fin n ⊕ Fin n) = i := rfl

@[simp] theorem planeOf_par (a : Fin n ⊕ Fin n) : planeOf (par a) = planeOf a := by
  rcases a with i | i <;> rfl

theorem mem_coords_planeOf (a : Fin n ⊕ Fin n) : a ∈ coords (planeOf a) := by
  rcases a with i | i
  · exact inl_mem_coords i
  · exact inr_mem_coords i

theorem planeOf_eq_of_mem_coords {k : Fin n} {a : Fin n ⊕ Fin n} (ha : a ∈ coords k) :
    planeOf a = k := by
  rcases mem_coords.1 ha with rfl | rfl <;> rfl

@[expose] def planeCoords (N : Finset (Fin n)) : Set (Fin n ⊕ Fin n) :=
  {a | planeOf a ∈ N}

theorem mem_planeCoords {N : Finset (Fin n)} {a : Fin n ⊕ Fin n} :
    a ∈ planeCoords N ↔ planeOf a ∈ N :=
  Iff.rfl

theorem parClosed_planeCoords (N : Finset (Fin n)) : ParClosed (planeCoords N) := by
  intro a ha
  rw [mem_planeCoords, planeOf_par]
  exact ha

theorem planeCoords_mono {I N : Finset (Fin n)} (h : I ⊆ N) : planeCoords I ⊆ planeCoords N :=
  fun _ ha => h ha

theorem planeCoords_singleton (k : Fin n) : planeCoords {k} = coords k := by
  ext a
  rw [mem_planeCoords, Finset.mem_singleton]
  exact ⟨fun h => h ▸ mem_coords_planeOf a, planeOf_eq_of_mem_coords⟩

theorem planeCoords_compl (N : Finset (Fin n)) : planeCoords Nᶜ = (planeCoords N)ᶜ := by
  ext a
  simp [mem_planeCoords]

theorem planeCoords_subset_compl_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J) :
    planeCoords J ⊆ (planeCoords I)ᶜ := fun _ ha ha' =>
  Finset.disjoint_left.1 h ha' ha

theorem range_sumMap_eq_planeCoords {m : ℕ} {σ : Fin m → Fin n} {N : Finset (Fin n)}
    (hσ : Set.range σ = N) : Set.range (Sum.map σ σ) = planeCoords N := by
  ext a
  rw [mem_planeCoords, ← Finset.mem_coe, ← hσ]
  rcases a with i | i
  · constructor
    · rintro ⟨x | x, hx⟩
      · exact ⟨x, Sum.inl_injective hx⟩
      · exact absurd hx Sum.inr_ne_inl
    · rintro ⟨x, hx⟩
      exact ⟨Sum.inl x, by rw [Sum.map_inl, hx, planeOf_inl]⟩
  · constructor
    · rintro ⟨x | x, hx⟩
      · exact absurd hx Sum.inl_ne_inr
      · exact ⟨x, Sum.inr_injective hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨Sum.inr x, by rw [Sum.map_inr, hx, planeOf_inr]⟩

end PlaneCoords

section Blocks

variable (F : Type) [Field F] {n : ℕ}

@[expose] def spBlock (N : Finset (Fin n)) : Subgroup (StatedSp n F) :=
  suppGroup (planeCoords N)

variable {F}

theorem mem_spBlock {N : Finset (Fin n)} {x : StatedSp n F} :
    x ∈ spBlock F N ↔ IsSupp (planeCoords N) (mat n F x) :=
  Iff.rfl

theorem spBlock_mono {I N : Finset (Fin n)} (h : I ⊆ N) : spBlock F I ≤ spBlock F N :=
  suppGroup_mono (planeCoords_mono h)

theorem spBlock_singleton (k : Fin n) : spBlock F {k} = longRootSp2 F n k := by
  rw [spBlock, planeCoords_singleton, longRootSp2_eq_suppGroup]

theorem spBlock_compl_singleton (k : Fin n) : spBlock F ({k}ᶜ : Finset (Fin n)) = complSp F k := by
  rw [spBlock, planeCoords_compl, planeCoords_singleton, complSp]

theorem commute_of_mem_spBlock_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J)
    {x y : StatedSp n F} (hx : x ∈ spBlock F I) (hy : y ∈ spBlock F J) : Commute x y :=
  commute_suppGroup_compl hx (suppGroup_mono (planeCoords_subset_compl_of_disjoint h) hy)

@[expose] noncomputable def planeEnum (N : Finset (Fin n)) : Fin N.card → Fin n :=
  N.orderEmbOfFin rfl

theorem planeEnum_injective (N : Finset (Fin n)) : Function.Injective (planeEnum N) :=
  (N.orderEmbOfFin rfl).injective

theorem range_planeEnum (N : Finset (Fin n)) : Set.range (planeEnum N) = N :=
  Finset.range_orderEmbOfFin N rfl

theorem spBlock_eq_range_spEmbed (N : Finset (Fin n)) :
    spBlock F N = (spEmbed (K := F) (planeEnum N) (planeEnum_injective N)).range := by
  rw [range_spEmbed, range_sumMap_eq_planeCoords (range_planeEnum N), spBlock]

@[expose] noncomputable def spBlockEquiv (N : Finset (Fin n)) : StatedSp N.card F ≃* spBlock F N :=
  (MonoidHom.ofInjective (spEmbed_injective (K := F) (planeEnum_injective N))).trans
    (MulEquiv.subgroupCongr (spBlock_eq_range_spEmbed N).symm)

theorem isPerfect_statedSp_of_four_le (hF : 4 ≤ Nat.card F) (m : ℕ) :
    Group.IsPerfect (StatedSp m F) := by
  have := CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F m (Or.inl (Or.inr hF))
  exact Group.IsPerfect.ofSurjective
    (f := (CFSG.LieType.Universal.Symplectic.equivStatedSp m F).toMonoidHom)
    (CFSG.LieType.Universal.Symplectic.equivStatedSp m F).surjective

theorem commutator_spBlock_eq (hF : 4 ≤ Nat.card F) (N : Finset (Fin n)) :
    ⁅spBlock F N, spBlock F N⁆ = spBlock F N := by
  have := isPerfect_statedSp_of_four_le hF N.card
  rw [spBlock_eq_range_spEmbed]
  exact CFSG.SeitzReduction.F4Pilot.commutator_range_eq_of_isPerfect _

theorem center_spBlock_eq_bot [CharP F 2] (N : Finset (Fin n)) : center (spBlock F N) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : (spBlockEquiv N).symm z ∈ center (StatedSp N.card F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply (spBlockEquiv N).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (spBlockEquiv N g)
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hz'
  rw [← MulEquiv.apply_symm_apply (spBlockEquiv N) z, hz', map_one]

end Blocks

section Conj

variable {F : Type} [Field F] {n : ℕ}

theorem diagSpEntry_mul_diagSpEntry_inv (s : Fin n → Fˣ) (a : Fin n ⊕ Fin n) :
    diagSpEntry s a * diagSpEntry s⁻¹ a = 1 := by
  rcases a with i | i <;> simp

theorem conj_diagSp_mem_suppGroup {S : Set (Fin n ⊕ Fin n)} (s : Fin n → Fˣ) {x : StatedSp n F}
    (hx : x ∈ suppGroup S) : diagSp F n s * x * (diagSp F n s)⁻¹ ∈ suppGroup S := by
  intro a b hab
  rw [← map_inv, map_mul, map_mul, mat_diagSp, mat_diagSp, mul_diagonal, diagonal_mul, hx a b hab]
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq, mul_one, diagSpEntry_mul_diagSpEntry_inv]
  · rw [Matrix.one_apply_ne h, mul_zero, zero_mul]

theorem diagSp_mem_normalizer_suppGroup (S : Set (Fin n ⊕ Fin n)) (s : Fin n → Fˣ) :
    diagSp F n s ∈ normalizer ((suppGroup S : Subgroup (StatedSp n F)) : Set (StatedSp n F)) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_diagSp_mem_suppGroup s, fun h => ?_⟩
  have := conj_diagSp_mem_suppGroup s⁻¹ h
  rwa [map_inv, inv_inv, show (diagSp F n s)⁻¹ * (diagSp F n s * x * (diagSp F n s)⁻¹) *
    diagSp F n s = x by group] at this

@[expose] noncomputable def conjDiagSp (N : Finset (Fin n)) (s : Fin n → Fˣ) :
    MulAut (spBlock F N) :=
  (spBlock F N).normalizerMonoidHom ⟨diagSp F n s, diagSp_mem_normalizer_suppGroup _ s⟩

theorem coe_conjDiagSp_apply (N : Finset (Fin n)) (s : Fin n → Fˣ) (x : spBlock F N) :
    ((conjDiagSp N s x : spBlock F N) : StatedSp n F) = diagSp F n s * x * (diagSp F n s)⁻¹ :=
  rfl

end Conj

section LeviFact

variable {F : Type} [Field F] {n : ℕ}

theorem mat_eq_zero_of_mem_spBlock_inf_centralizer {N I : Finset (Fin n)}
    {D : Set (Fin n → Fˣ)}
    (hsep : ∀ a ∈ planeCoords N, ∀ b ∈ planeCoords N, a ≠ b →
      (a ∉ planeCoords I ∨ b ∉ planeCoords I) → ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b)
    {x : StatedSp n F} (hx : x ∈ spBlock F N ⊓ centralizer (diagSp F n '' D))
    {a : Fin n ⊕ Fin n} (ha : a ∉ planeCoords I) {b : Fin n ⊕ Fin n} (hba : b ≠ a) :
    mat n F x a b = 0 ∧ mat n F x b a = 0 := by
  obtain ⟨hxN, hxD⟩ := mem_inf.1 hx
  by_cases hN : a ∈ planeCoords N ∧ b ∈ planeCoords N
  · obtain ⟨s, hs, hne⟩ := hsep a hN.1 b hN.2 hba.symm (Or.inl ha)
    have hc : Commute x (diagSp F n s) :=
      ((mem_centralizer_iff.1 hxD) _ ⟨s, hs, rfl⟩).symm
    exact ⟨(commute_diagSp_iff x s).1 hc a b hne, (commute_diagSp_iff x s).1 hc b a (Ne.symm hne)⟩
  · refine ⟨?_, ?_⟩
    · rw [hxN a b hN, Matrix.one_apply_ne hba.symm]
    · rw [hxN b a (fun h => hN ⟨h.2, h.1⟩), Matrix.one_apply_ne hba]

theorem spBlock_le_centralizer_of_const {I : Finset (Fin n)} {D : Set (Fin n → Fˣ)}
    (hconst : ∀ s ∈ D, ∀ a ∈ planeCoords I, ∀ b ∈ planeCoords I,
      diagSpEntry s a = diagSpEntry s b) :
    spBlock F I ≤ centralizer (diagSp F n '' D) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  exact (commute_diagSp_of_mem_suppGroup (hconst s hs) hx).eq.symm

theorem perfectCore_spBlock_inf_centralizer_eq [Finite F] {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (D : Set (Fin n → Fˣ))
    (hconst : ∀ s ∈ D, ∀ a ∈ planeCoords I, ∀ b ∈ planeCoords I,
      diagSpEntry s a = diagSpEntry s b)
    (hsep : ∀ a ∈ planeCoords N, ∀ b ∈ planeCoords N, a ≠ b →
      (a ∉ planeCoords I ∨ b ∉ planeCoords I) → ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b)
    (hperf : ⁅spBlock F I, spBlock F I⁆ = spBlock F I) :
    perfectCore (spBlock F N ⊓ centralizer (diagSp F n '' D)) = spBlock F I := by
  set P := spBlock F N ⊓ centralizer (diagSp F n '' D)
  have hPC : ⁅P, P⁆ ≤ spBlock F I :=
    CFSG.SeitzReduction.F4Pilot.commutator_le_suppGroup fun x hx a ha b hba =>
      mat_eq_zero_of_mem_spBlock_inf_centralizer hsep hx ha hba
  refine le_antisymm ?_ (le_perfectCore_of_perfect (le_inf (spBlock_mono hIN)
    (spBlock_le_centralizer_of_const hconst)) hperf)
  calc perfectCore P = ⁅perfectCore P, perfectCore P⁆ := (perfectCore_perfect P).symm
    _ ≤ ⁅P, P⁆ := commutator_mono (perfectCore_le P) (perfectCore_le P)
    _ ≤ spBlock F I := hPC

theorem perfectCore_fixAll_conjDiagSp [Finite F] {N I : Finset (Fin n)} (hIN : I ⊆ N)
    {ι' : Type*} (s : ι' → (Fin n → Fˣ))
    (hconst : ∀ j, ∀ a ∈ planeCoords I, ∀ b ∈ planeCoords I,
      diagSpEntry (s j) a = diagSpEntry (s j) b)
    (hsep : ∀ a ∈ planeCoords N, ∀ b ∈ planeCoords N, a ≠ b →
      (a ∉ planeCoords I ∨ b ∉ planeCoords I) → ∃ j, diagSpEntry (s j) a ≠ diagSpEntry (s j) b)
    (hperf : ⁅spBlock F I, spBlock F I⁆ = spBlock F I) :
    perfectCore (fixAll fun j => conjDiagSp N (s j)) =
      (spBlock F I).subgroupOf (spBlock F N) := by
  have hmap : (fixAll fun j => conjDiagSp N (s j)).map (spBlock F N).subtype =
      spBlock F N ⊓ centralizer (diagSp F n '' Set.range s) := by
    ext x
    simp only [mem_map, mem_inf, coe_subtype, mem_centralizer_iff, Set.mem_image, Set.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun j => ?_⟩
      have h := congrArg Subtype.val (mem_fixAll.1 hy j)
      rw [coe_conjDiagSp_apply] at h
      calc diagSp F n (s j) * (y : StatedSp n F) =
            diagSp F n (s j) * (y : StatedSp n F) * (diagSp F n (s j))⁻¹ * diagSp F n (s j) := by
              group
        _ = (y : StatedSp n F) * diagSp F n (s j) := by rw [h]
    · rintro ⟨hxN, hx⟩
      refine ⟨⟨x, hxN⟩, mem_fixAll.2 fun j => Subtype.ext ?_, rfl⟩
      rw [coe_conjDiagSp_apply]
      change diagSp F n (s j) * x * (diagSp F n (s j))⁻¹ = x
      rw [hx j, mul_inv_cancel_right]
  apply Subgroup.map_injective (spBlock F N).subtype_injective
  rw [CFSG.Quasithin.map_perfectCore, hmap, subgroupOf_map_subtype,
    inf_of_le_left (spBlock_mono hIN)]
  refine perfectCore_spBlock_inf_centralizer_eq hIN _
    (by rintro _ ⟨j, rfl⟩; exact hconst j) (fun a ha b hb hab hI => ?_) hperf
  obtain ⟨j, hj⟩ := hsep a ha b hb hab hI
  exact ⟨s j, ⟨j, rfl⟩, hj⟩

end LeviFact

section Lift

variable {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}

@[expose] def liftParam (ι : K →+* F) (t : Fin n → Kˣ) : Fin n → Fˣ :=
  fun i => Units.map (ι : K →* F) (t i)

theorem diagSpEntry_liftParam (ι : K →+* F) (t : Fin n → Kˣ) (a : Fin n ⊕ Fin n) :
    diagSpEntry (liftParam ι t) a = ι (diagSpEntry t a) := by
  rcases a with i | i
  · rfl
  · simp only [diagSpEntry_inr, liftParam, ← map_inv]
    rfl

theorem diagSpEntry_eq_one_of_mem_planeTorusParam {I : Finset (Fin n)} {t : Fin n → Kˣ}
    (ht : t ∈ planeTorusParam K I) {a : Fin n ⊕ Fin n} (ha : a ∈ planeCoords I) :
    diagSpEntry t a = 1 := by
  rcases a with i | i
  · rw [diagSpEntry_inl, ht i ha, Units.val_one]
  · rw [diagSpEntry_inr, ht i ha, inv_one, Units.val_one]

theorem exists_mem_planeTorusParam_diagSpEntry_ne {κ : Kˣ} (hκ : κ * κ ≠ 1)
    {I : Finset (Fin n)} {a b : Fin n ⊕ Fin n} (hab : a ≠ b)
    (hI : a ∉ planeCoords I ∨ b ∉ planeCoords I) :
    ∃ t ∈ planeTorusParam K I, diagSpEntry t a ≠ diagSpEntry t b := by
  have hmem : ∀ i : Fin n, i ∉ I → Pi.mulSingle i κ ∈ planeTorusParam K I := fun i hi j hj => by
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [hji]
  rcases hI with ha | hb
  · exact ⟨_, hmem _ ha, diagSpEntry_mulSingle_ne hκ hab (Or.inl (mem_coords_planeOf a))⟩
  · exact ⟨_, hmem _ hb, diagSpEntry_mulSingle_ne hκ hab (Or.inr (mem_coords_planeOf b))⟩

theorem perfectCore_spBlock_inf_centralizer_planeTorus [Finite F] (ι : K →+* F) {κ : Kˣ}
    (hκ : κ * κ ≠ 1) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hperf : ⁅spBlock F I, spBlock F I⁆ = spBlock F I) :
    perfectCore (spBlock F N ⊓
        centralizer (diagSp F n '' (liftParam ι '' (planeTorusParam K I : Set (Fin n → Kˣ))))) =
      spBlock F I := by
  refine perfectCore_spBlock_inf_centralizer_eq hIN _ ?_ (fun a _ b _ hab hI => ?_) hperf
  · rintro _ ⟨t, ht, rfl⟩ a ha b hb
    rw [diagSpEntry_liftParam, diagSpEntry_liftParam,
      diagSpEntry_eq_one_of_mem_planeTorusParam ht ha,
      diagSpEntry_eq_one_of_mem_planeTorusParam ht hb]
  · obtain ⟨t, ht, hne⟩ := exists_mem_planeTorusParam_diagSpEntry_ne hκ hab hI
    refine ⟨liftParam ι t, ⟨t, ht, rfl⟩, ?_⟩
    rw [diagSpEntry_liftParam, diagSpEntry_liftParam]
    exact fun h => hne (ι.injective h)

theorem perfectCore_spBlock_inf_centralizer_planeTorusSp [Finite F] (hF : 4 ≤ Nat.card F)
    {N I : Finset (Fin n)} (hIN : I ⊆ N) :
    perfectCore (spBlock F N ⊓ centralizer (planeTorusSp F I : Set (StatedSp n F))) =
      spBlock F I := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hF
  have h := perfectCore_spBlock_inf_centralizer_planeTorus (RingHom.id F) hκ hIN
    (commutator_spBlock_eq hF I)
  have hset : (diagSp F n '' (liftParam (RingHom.id F) ''
      (planeTorusParam F I : Set (Fin n → Fˣ)))) = (planeTorusSp F I : Set (StatedSp n F)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨t, ht, rfl⟩, rfl⟩
  rw [hset] at h
  exact h

end Lift

end CFSG.SeitzReduction.SymplecticPilot
