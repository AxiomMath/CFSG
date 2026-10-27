module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorus
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n m : ℕ}

section Units

theorem exists_units_mul_self_ne_one_of_four_le (hK : 4 ≤ Nat.card K) :
    ∃ κ : Kˣ, κ * κ ≠ 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact LinearPilot.exists_units_mul_self_ne_one hK

theorem units_ne_one_of_mul_self_ne_one {κ : Kˣ} (hκ : κ * κ ≠ 1) : κ ≠ 1 := by
  rintro rfl
  exact hκ (mul_one 1)

theorem units_ne_inv_of_mul_self_ne_one {κ : Kˣ} (hκ : κ * κ ≠ 1) : κ ≠ κ⁻¹ := by
  intro h
  apply hκ
  calc κ * κ = κ * κ⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel κ

end Units

section Split

variable {k : Fin n} {κ : Kˣ}

theorem diagSpEntry_mulSingle_ne (hκ : κ * κ ≠ 1) {a b : Fin n ⊕ Fin n} (hab : a ≠ b)
    (h : a ∈ coords k ∨ b ∈ coords k) :
    diagSpEntry (Pi.mulSingle k κ) a ≠ diagSpEntry (Pi.mulSingle k κ) b := by
  have h1 : (κ : K) ≠ 1 := fun e => units_ne_one_of_mul_self_ne_one hκ (Units.ext e)
  have h2 : ((κ⁻¹ : Kˣ) : K) ≠ 1 := fun e =>
    units_ne_one_of_mul_self_ne_one hκ (inv_eq_one.1 (Units.ext e))
  have h3 : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun e =>
    units_ne_inv_of_mul_self_ne_one hκ (Units.ext e)
  have key : ∀ {a b : Fin n ⊕ Fin n}, a ≠ b → a ∈ coords k →
      diagSpEntry (Pi.mulSingle k κ) a ≠ diagSpEntry (Pi.mulSingle k κ) b := by
    intro a b hab ha
    rcases mem_coords.1 ha with rfl | rfl
    · rw [diagSpEntry_mulSingle_inl_self]
      by_cases hb : b ∈ coords k
      · rcases mem_coords.1 hb with rfl | rfl
        · exact absurd rfl hab
        · rw [diagSpEntry_mulSingle_inr_self]
          exact h3
      · rw [diagSpEntry_mulSingle_of_not_mem k κ hb]
        exact h1
    · rw [diagSpEntry_mulSingle_inr_self]
      by_cases hb : b ∈ coords k
      · rcases mem_coords.1 hb with rfl | rfl
        · rw [diagSpEntry_mulSingle_inl_self]
          exact Ne.symm h3
        · exact absurd rfl hab
      · rw [diagSpEntry_mulSingle_of_not_mem k κ hb]
        exact h2
  rcases h with ha | hb
  · exact key hab ha
  · exact Ne.symm (key (Ne.symm hab) hb)

theorem mat_apply_eq_zero_of_commute_rootTorusHom (hκ : κ * κ ≠ 1) {x : StatedSp n K}
    (hx : x * rootTorusHom K n k κ = rootTorusHom K n k κ * x) {a b : Fin n ⊕ Fin n}
    (hab : a ≠ b) (h : a ∈ coords k ∨ b ∈ coords k) : mat n K x a b = 0 := by
  have e := congrFun (congrFun (congrArg (mat n K) hx) a) b
  rw [map_mul, map_mul, rootTorusHom_apply, mat_diagSp, mul_diagonal, diagonal_mul] at e
  have hne := diagSpEntry_mulSingle_ne hκ hab h
  have : mat n K x a b * (diagSpEntry (Pi.mulSingle k κ) b -
      diagSpEntry (Pi.mulSingle k κ) a) = 0 := by
    rw [mul_sub, e]
    ring
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hne))

theorem exists_eq_mul_of_commute_rootTorusHom (hκ : κ * κ ≠ 1) {x : StatedSp n K}
    (hx : x * rootTorusHom K n k κ = rootTorusHom K n k κ * x) :
    ∃ u : Kˣ, ∃ y ∈ complSp K k, x = rootTorusHom K n k u * y := by
  have hzero : ∀ {a b : Fin n ⊕ Fin n}, a ≠ b → (a ∈ coords k ∨ b ∈ coords k) →
      mat n K x a b = 0 := fun hab h => mat_apply_eq_zero_of_commute_rootTorusHom hκ hx hab h
  have hlr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  have hdet := det_stdBlock_eq_one x k fun c hc =>
    hzero (fun e => hc (e ▸ inl_mem_coords k)) (Or.inr (inl_mem_coords k))
  rw [Matrix.det_fin_two] at hdet
  simp only [stdBlock, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at hdet
  rw [hzero hlr (Or.inl (inl_mem_coords k)), zero_mul, sub_zero] at hdet
  set a := mat n K x (Sum.inl k) (Sum.inl k) with ha
  set b := mat n K x (Sum.inr k) (Sum.inr k) with hb
  have hba : b * a = 1 := by rw [mul_comm]; exact hdet
  refine ⟨⟨a, b, hdet, hba⟩, (rootTorusHom K n k ⟨a, b, hdet, hba⟩)⁻¹ * x, ?_, by group⟩
  rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  have htk : t ∈ coords k := by simpa using ht
  rw [map_mul, ← map_inv, rootTorusHom_apply, mat_diagSp, diagonal_mul]
  rcases mem_coords.1 htk with rfl | rfl
  · by_cases hr : r = Sum.inl k
    · subst hr
      simp [← ha, hba]
    · rw [hzero hr (Or.inr (inl_mem_coords k)), mul_zero, one_apply_ne hr]
  · by_cases hr : r = Sum.inr k
    · subst hr
      simp [← hb, hdet]
    · rw [hzero hr (Or.inr (inr_mem_coords k)), mul_zero, one_apply_ne hr]

end Split

section Centralizer

theorem rootTorusSp_le_centralizer_self (k : Fin n) :
    rootTorusSp K k ≤ centralizer (rootTorusSp K k : Set (StatedSp n K)) := by
  rintro _ ⟨u, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨v, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem complSp_le_centralizer_rootTorusSp (k : Fin n) :
    complSp K k ≤ centralizer (rootTorusSp K k : Set (StatedSp n K)) :=
  (complSp_le_centralizer_longRootSp2 k).trans (centralizer_le (rootTorusSp_le_longRootSp2 k))

theorem disjoint_rootTorusSp_complSp (k : Fin n) : Disjoint (rootTorusSp K k) (complSp K k) :=
  (disjoint_longRootSp2_complSp k).mono_left (rootTorusSp_le_longRootSp2 k)

theorem exists_eq_mul_of_mem_centralizer {k : Fin n} {κ : Kˣ} (hκ : κ * κ ≠ 1)
    {X : Subgroup (StatedSp n K)} (hX : rootTorusHom K n k κ ∈ X) {x : StatedSp n K}
    (hx : x ∈ centralizer (X : Set (StatedSp n K))) :
    ∃ u : Kˣ, ∃ y ∈ complSp K k, x = rootTorusHom K n k u * y :=
  exists_eq_mul_of_commute_rootTorusHom hκ (mem_centralizer_iff.1 hx _ hX).symm

theorem centralizer_rootTorusSp_of_mul_self_ne_one {κ : Kˣ} (hκ : κ * κ ≠ 1) (k : Fin n) :
    centralizer (rootTorusSp K k : Set (StatedSp n K)) = rootTorusSp K k ⊔ complSp K k ∧
      Disjoint (rootTorusSp K k) (complSp K k) := by
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (rootTorusSp_le_centralizer_self k)
    (complSp_le_centralizer_rootTorusSp k)), disjoint_rootTorusSp_complSp k⟩
  obtain ⟨u, y, hy, rfl⟩ := exists_eq_mul_of_mem_centralizer hκ
    (rootTorusHom_mem_rootTorusSp k κ) hx
  exact mul_mem (mem_sup_left ⟨u, rfl⟩) (mem_sup_right hy)

theorem centralizer_rootTorusSp (hK : 4 ≤ Nat.card K) (k : Fin n) :
    centralizer (rootTorusSp K k : Set (StatedSp n K)) = rootTorusSp K k ⊔ complSp K k ∧
      Disjoint (rootTorusSp K k) (complSp K k) := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact centralizer_rootTorusSp_of_mul_self_ne_one hκ k

theorem commutator_mem_of_eq_mul {G : Type*} [Group G] {A D : Subgroup G}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hAD : ∀ a ∈ A, ∀ d ∈ D, Commute a d) {g g' : G}
    (hg : ∃ a ∈ A, ∃ d ∈ D, g = a * d) (hg' : ∃ a ∈ A, ∃ d ∈ D, g' = a * d) :
    g * g' * g⁻¹ * g'⁻¹ ∈ D := by
  obtain ⟨a, ha, d, hd, rfl⟩ := hg
  obtain ⟨a', ha', d', hd', rfl⟩ := hg'
  have hX : Commute a (d * a' * d' * d⁻¹) :=
    (((hAD a ha d hd).mul_right (hA a ha a' ha')).mul_right (hAD a ha d' hd')).mul_right
      (hAD a ha d hd).inv_right
  have hY : Commute a' (d * d' * d⁻¹ * d'⁻¹) :=
    ((((hAD a' ha' d hd).mul_right (hAD a' ha' d' hd')).mul_right
      (hAD a' ha' d hd).inv_right).mul_right (hAD a' ha' d' hd').inv_right)
  have e1 : a * d * (a' * d') * (a * d)⁻¹ * (a' * d')⁻¹ =
      (a * (d * a' * d' * d⁻¹) * a⁻¹) * d'⁻¹ * a'⁻¹ := by group
  have e2 : d * a' * d' * d⁻¹ * d'⁻¹ * a'⁻¹ = a' * (d * d' * d⁻¹ * d'⁻¹) * a'⁻¹ := by
    have h1 : d * a' = a' * d := (hAD a' ha' d hd).eq.symm
    calc d * a' * d' * d⁻¹ * d'⁻¹ * a'⁻¹ = (d * a') * d' * d⁻¹ * d'⁻¹ * a'⁻¹ := rfl
      _ = a' * d * d' * d⁻¹ * d'⁻¹ * a'⁻¹ := by rw [h1]
      _ = a' * (d * d' * d⁻¹ * d'⁻¹) * a'⁻¹ := by group
  rw [e1, hX.mul_inv_cancel, e2, hY.mul_inv_cancel]
  exact mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')

theorem commutator_mem_complSp_of_mem_centralizer {k : Fin n} {κ : Kˣ} (hκ : κ * κ ≠ 1)
    {X : Subgroup (StatedSp n K)} (hX : rootTorusHom K n k κ ∈ X) {g g' : StatedSp n K}
    (hg : g ∈ centralizer (X : Set (StatedSp n K)))
    (hg' : g' ∈ centralizer (X : Set (StatedSp n K))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ complSp K k := by
  refine commutator_mem_of_eq_mul (A := rootTorusSp K k)
    (fun a ha a' ha' => mem_centralizer_iff.1 (rootTorusSp_le_centralizer_self k ha') a ha)
    (fun a ha d hd => (mem_centralizer_iff.1 (complSp_le_centralizer_rootTorusSp k hd) a ha))
    ?_ ?_
  · obtain ⟨u, y, hy, rfl⟩ := exists_eq_mul_of_mem_centralizer hκ hX hg
    exact ⟨_, ⟨u, rfl⟩, y, hy, rfl⟩
  · obtain ⟨u, y, hy, rfl⟩ := exists_eq_mul_of_mem_centralizer hκ hX hg'
    exact ⟨_, ⟨u, rfl⟩, y, hy, rfl⟩

theorem center_statedSp_eq_bot [CharP K 2] (m : ℕ) : Subgroup.center (StatedSp m K) = ⊥ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine eq_bot_iff.2 fun x _ => (Subgroup.mem_bot).2 (Subtype.ext (Units.ext ?_))
    ext a
    exact a.elim (fun i => i.elim0) (fun i => i.elim0)
  · have : NeZero m := ⟨by omega⟩
    rw [CFSG.LieType.Universal.Symplectic.center_eq]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.spScalars_eq_bot_of_charTwo

theorem eq_one_of_mem_complSp_of_mem_centralizer [CharP K 2] {k : Fin (m + 1)}
    {y : StatedSp (m + 1) K} (hy : y ∈ complSp K k)
    (hyc : y ∈ centralizer (complSp K k : Set (StatedSp (m + 1) K))) : y = 1 := by
  set z := (complSpEquiv (K := K) k).symm ⟨y, hy⟩ with hz
  have hzc : z ∈ Subgroup.center (StatedSp m K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply (complSpEquiv (K := K) k).injective
    rw [map_mul, map_mul, hz, MulEquiv.apply_symm_apply]
    exact Subtype.ext (mem_centralizer_iff.1 hyc _ (complSpEquiv k g).2)
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hzc
  have := congrArg (fun w => ((complSpEquiv (K := K) k w : complSp K k) : StatedSp (m + 1) K)) hzc
  simpa [hz] using this

theorem centralizer_rootTorusSp_inf_centralizer_complSp [CharP K 2] (hK : 4 ≤ Nat.card K)
    (k : Fin (m + 1)) :
    centralizer (rootTorusSp K k : Set (StatedSp (m + 1) K)) ⊓
        centralizer (complSp K k : Set (StatedSp (m + 1) K)) = rootTorusSp K k := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  refine le_antisymm (fun x hx => ?_) (le_inf (rootTorusSp_le_centralizer_self k) ?_)
  · obtain ⟨u, y, hy, rfl⟩ := exists_eq_mul_of_mem_centralizer hκ
      (rootTorusHom_mem_rootTorusSp k κ) hx.1
    have hu : rootTorusHom K (m + 1) k u ∈ centralizer (complSp K k : Set (StatedSp (m + 1) K)) :=
      mem_centralizer_iff.2 fun d hd =>
        (mem_centralizer_iff.1 (complSp_le_centralizer_rootTorusSp k hd) _ ⟨u, rfl⟩).symm
    have hyc : y ∈ centralizer (complSp K k : Set (StatedSp (m + 1) K)) := by
      have := mul_mem (inv_mem hu) hx.2
      rwa [inv_mul_cancel_left] at this
    rw [eq_one_of_mem_complSp_of_mem_centralizer hy hyc, mul_one]
    exact ⟨u, rfl⟩
  · intro x hx
    exact mem_centralizer_iff.2 fun d hd =>
      (mem_centralizer_iff.1 (complSp_le_centralizer_rootTorusSp k hd) x hx).symm

end Centralizer

section Layer

theorem isQuasisimple_complSp (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (k : Fin (m + 1)) :
    CFSG.IsQuasisimple (complSp K k) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (complSpEquiv k)
    (CFSG.LieType.Universal.Symplectic.isQuasisimple m K hm (Or.inl (Or.inr hK)))

theorem isQuasisimple_map_complSp {G : Type*} [Group G] {L : Subgroup G} (hK : 4 ≤ Nat.card K)
    (hm : 1 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    CFSG.IsQuasisimple (((complSp K k).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((complSp K k).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((complSp K k).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective))
    (isQuasisimple_complSp hK hm k)

theorem isQuasisimple_open_map_complSp {G : Type*} [Group G] {L : Subgroup G}
    (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    CFSG.Open.IsQuasisimple (((complSp K k).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_complSp hK hm e k).1.commutator_eq_top,
    (isQuasisimple_map_complSp hK hm e k).2.1⟩

theorem layer_centralizer_of_mem (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) {k : Fin (m + 1)} {κ : Kˣ}
    (hκ : κ * κ ≠ 1) {X : Subgroup (StatedSp (m + 1) K)} (hX : rootTorusHom K (m + 1) k κ ∈ X)
    (hDX : complSp K k ≤ centralizer (X : Set (StatedSp (m + 1) K))) :
    inSubgroup layer (centralizer (X : Set (StatedSp (m + 1) K))) = complSp K k :=
  LinearPilot.inSubgroup_layer_eq_of_commutator_mem hDX
    (fun _ hg _ hg' => commutator_mem_complSp_of_mem_centralizer hκ hX hg hg')
    (isQuasisimple_complSp hK hm k)

theorem layer_centralizer_rootTorusSp (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (k : Fin (m + 1)) :
    inSubgroup layer (centralizer (rootTorusSp K k : Set (StatedSp (m + 1) K))) =
      complSp K k := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact layer_centralizer_of_mem hK hm hκ (rootTorusHom_mem_rootTorusSp k κ)
    (complSp_le_centralizer_rootTorusSp k)

theorem layer_inf_centralizer_of_mem {G : Type*} [Group G] {L : Subgroup G}
    (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (e : L ≃* StatedSp (m + 1) K) {k : Fin (m + 1)} {κ : Kˣ}
    (hκ : κ * κ ≠ 1) {X : Subgroup (StatedSp (m + 1) K)} (hX : rootTorusHom K (m + 1) k κ ∈ X)
    (hDX : complSp K k ≤ centralizer (X : Set (StatedSp (m + 1) K))) :
    inSubgroup layer
        (L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((complSp K k).map e.symm.toMonoidHom).map L.subtype :=
  LinearPilot.inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e hDX
    (fun _ hg _ hg' => commutator_mem_complSp_of_mem_centralizer hκ hX hg hg')
    (isQuasisimple_complSp hK hm k)

theorem layer_inf_centralizer_rootTorusSp {G : Type*} [Group G] {L : Subgroup G}
    (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    inSubgroup layer
        (L ⊓ centralizer ((((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype :
          Subgroup G) : Set G)) =
      ((complSp K k).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact LinearPilot.inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e
    (complSp_le_centralizer_rootTorusSp k)
    (fun _ hg _ hg' => commutator_mem_complSp_of_mem_centralizer hκ
      (rootTorusHom_mem_rootTorusSp k κ) hg hg')
    (isQuasisimple_complSp hK hm k)

end Layer

section Siegel

variable {s : Kˣ}

theorem diagSp_const_mem_siegelTorus (s : Kˣ) : diagSp K n (fun _ => s) ∈ siegelTorus K n :=
  ⟨s, rfl⟩

theorem mat_apply_eq_zero_of_commute_siegel (hs : s * s ≠ 1) {x : StatedSp n K}
    (hx : x * diagSp K n (fun _ => s) = diagSp K n (fun _ => s) * x) (i j : Fin n) :
    mat n K x (Sum.inl i) (Sum.inr j) = 0 ∧ mat n K x (Sum.inr i) (Sum.inl j) = 0 := by
  have h3 : (s : K) ≠ ((s⁻¹ : Kˣ) : K) := fun e =>
    units_ne_inv_of_mul_self_ne_one hs (Units.ext e)
  have key : ∀ a b, mat n K x a b *
      (diagSpEntry (fun _ : Fin n => s) b - diagSpEntry (fun _ : Fin n => s) a) = 0 := by
    intro a b
    have e := congrFun (congrFun (congrArg (mat n K) hx) a) b
    rw [map_mul, map_mul, mat_diagSp, mul_diagonal, diagonal_mul] at e
    rw [mul_sub, e]
    ring
  refine ⟨(mul_eq_zero.1 (key _ _)).resolve_right ?_, (mul_eq_zero.1 (key _ _)).resolve_right ?_⟩
  · rw [diagSpEntry_inl, diagSpEntry_inr]
    exact sub_ne_zero.2 h3.symm
  · rw [diagSpEntry_inl, diagSpEntry_inr]
    exact sub_ne_zero.2 h3

theorem mem_siegelLeviGL_of_commute (hs : s * s ≠ 1) {x : StatedSp n K}
    (hx : x * diagSp K n (fun _ => s) = diagSp K n (fun _ => s) * x) :
    x ∈ siegelLeviGL K n := by
  have hz := mat_apply_eq_zero_of_commute_siegel hs hx
  set M := mat n K x with hM
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    exact (hz i j).1
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact (hz i j).2
  have hMb : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [h12, h21]
  have hsym := mat_transpose_mul_gram_mul x
  rw [← hM, hMb, ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply] at hsym
  have hAD : (M.toBlocks₁₁)ᵀ * M.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₁₂ hsym
    simpa using this
  have hDA : (M.toBlocks₂₂)ᵀ * M.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.transpose hAD
    simpa [Matrix.transpose_mul] using this
  refine ⟨⟨M.toBlocks₁₁, (M.toBlocks₂₂)ᵀ, mul_eq_one_comm.1 hDA, hDA⟩, mat_injective ?_⟩
  rw [mat_leviEmbedGL, ← hM]
  conv_rhs => rw [hMb]
  congr 1

theorem siegelLeviGL_le_centralizer_siegelTorus :
    siegelLeviGL K n ≤ centralizer (siegelTorus K n : Set (StatedSp n K)) := by
  rintro _ ⟨A, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  change leviEmbedGL K n (TauCeti.diagGL fun _ : Fin n => s) * leviEmbedGL K n A =
    leviEmbedGL K n A * leviEmbedGL K n (TauCeti.diagGL fun _ : Fin n => s)
  rw [← map_mul, ← map_mul, TauCeti.diagGL_const,
    Subgroup.mem_center_iff.1 (TauCeti.scalar_mem_center s) A]

theorem centralizer_siegelTorus_of_mul_self_ne_one (hs : s * s ≠ 1) :
    centralizer (siegelTorus K n : Set (StatedSp n K)) = siegelLeviGL K n :=
  le_antisymm (fun _ hx => mem_siegelLeviGL_of_commute hs
      (mem_centralizer_iff.1 hx _ (diagSp_const_mem_siegelTorus s)).symm)
    siegelLeviGL_le_centralizer_siegelTorus

theorem centralizer_siegelTorus (hK : 4 ≤ Nat.card K) :
    centralizer (siegelTorus K n : Set (StatedSp n K)) = siegelLeviGL K n := by
  obtain ⟨s, hs⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact centralizer_siegelTorus_of_mul_self_ne_one hs

theorem commutator_mem_siegelLevi {g g' : StatedSp n K} (hg : g ∈ siegelLeviGL K n)
    (hg' : g' ∈ siegelLeviGL K n) : g * g' * g⁻¹ * g'⁻¹ ∈ siegelLevi K n := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨B, rfl⟩ := hg'
  have hdet : Matrix.det ((A * B * A⁻¹ * B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_inv_cancel_comm, mul_inv_cancel, Units.val_one]
  refine ⟨⟨_, hdet⟩, ?_⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  change leviEmbedGL K n (Matrix.SpecialLinearGroup.toGL ⟨_, hdet⟩) = _
  congr 1
  exact Units.ext rfl

theorem isQuasisimple_siegelLevi (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) :
    CFSG.IsQuasisimple (siegelLevi K n) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv siegelLeviEquiv
    (LinearPilot.isQuasisimple_specialLinearGroup_of_le hn (Or.inr hK))

theorem isQuasisimple_map_siegelLevi {G : Type*} [Group G] {L : Subgroup G}
    (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp n K) :
    CFSG.IsQuasisimple (((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((siegelLevi K n).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((siegelLevi K n).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective))
    (isQuasisimple_siegelLevi hK hn)

theorem isQuasisimple_open_map_siegelLevi {G : Type*} [Group G] {L : Subgroup G}
    (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp n K) :
    CFSG.Open.IsQuasisimple (((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_siegelLevi hK hn e).1.commutator_eq_top,
    (isQuasisimple_map_siegelLevi hK hn e).2.1⟩

theorem layer_centralizer_siegelTorus (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) :
    inSubgroup layer (centralizer (siegelTorus K n : Set (StatedSp n K))) = siegelLevi K n := by
  rw [centralizer_siegelTorus hK]
  exact LinearPilot.inSubgroup_layer_eq_of_commutator_mem siegelLevi_le_siegelLeviGL
    (fun _ hg _ hg' => commutator_mem_siegelLevi hg hg') (isQuasisimple_siegelLevi hK hn)

theorem layer_inf_centralizer_siegelTorus {G : Type*} [Group G] {L : Subgroup G}
    (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp n K) :
    inSubgroup layer
        (L ⊓ centralizer ((((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype :
          Subgroup G) : Set G)) =
      ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype := by
  have hC := centralizer_siegelTorus (n := n) hK
  exact LinearPilot.inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e
    (siegelLevi_le_siegelLeviGL.trans hC.ge)
    (fun _ hg _ hg' => commutator_mem_siegelLevi (hC ▸ hg) (hC ▸ hg'))
    (isQuasisimple_siegelLevi hK hn)

end Siegel

end CFSG.SeitzReduction.SymplecticPilot
