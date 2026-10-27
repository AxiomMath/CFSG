module

public import CFSG.LieType.Ree.LargeReeRootInvolution
public import CFSG.LieType.Ree.FixedBruhatDecomposition
public import CFSG.LieType.Chevalley.GraphFixedSchreier
public import CFSG.LieType.Chevalley.IntrinsicSimplePairs

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section General

variable {τ : Tag}

theorem commute_pinnedX_of_forall_not_isRoot
    (R : Type) [CommRing R]
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • α + b • β)) (c d : R) :
    Commute (pinnedX τ R α c) (pinnedX τ R β d) := by
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hα hβ hne hne'
  have hnil : commPairs τ α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
    obtain ⟨h1, h2, hr⟩ := (hmem p).1 hp
    exact h p.1 p.2 h1 h2 hr
  have hF' := hF R c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at hF'
  exact hF'

theorem pinnedX_list_prod_injective_neg
    {R : Type} [CommRing R] (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot τ α ∧ height α < 0) (c c' : (Fin τ.rank → ℤ) → R)
    (heq : (L.map fun α => pinnedX τ R α (c α)).prod =
      (L.map fun α => pinnedX τ R α (c' α)).prod) :
    ∀ α ∈ L, c α = c' α := by
  have h := congrArg (fun g : (Module.End R (RootModule τ R))ˣ =>
    (g : Module.End R (RootModule τ R))) heq
  rw [coe_list_prod_pinnedX c L fun α hα => (hL α hα).1,
    coe_list_prod_pinnedX c' L fun α hα => (hL α hα).1] at h
  have key := RootOperatorFamily.prod_eltOr_injective_of_ring (rootOperatorFamily τ)
    (φ := AddMonoidHom.mk' (fun v => -height (τ := τ) v) fun u v => by
      simp only [height, Pi.add_apply, Finset.sum_add_distrib, neg_add])
    L hnd (fun γ hγ => ⟨(hL γ hγ).1, by
      have := (hL γ hγ).2
      change 0 < -height γ
      omega⟩) _ _ h
  intro α hα
  have h1 := congrArg (((rootOperatorFamily τ).pinnedFamilySign α : R) * ·) (key α hα)
  simp only [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self, one_mul] at h1
  exact h1

theorem pinnedX_mul_pinnedX_inj
    {R : Type} [CommRing R] {α β : Fin τ.rank → ℤ}
    (hsign : (IsRoot τ α ∧ 0 < height α) ∧ (IsRoot τ β ∧ 0 < height β) ∨
      (IsRoot τ α ∧ height α < 0) ∧ (IsRoot τ β ∧ height β < 0))
    (hne : α ≠ β) {c d c' d' : R}
    (h : pinnedX τ R α c * pinnedX τ R β d = pinnedX τ R α c' * pinnedX τ R β d') :
    c = c' ∧ d = d' := by
  classical
  have hnd : [α, β].Nodup := by simp [hne]
  have hprod : ∀ x y : R,
      ([α, β].map fun γ => pinnedX τ R γ (if γ = α then x else y)).prod =
        pinnedX τ R α x * pinnedX τ R β y := fun x y => by
    simp [hne.symm]
  have heq : ([α, β].map fun γ => pinnedX τ R γ (if γ = α then c else d)).prod =
      ([α, β].map fun γ => pinnedX τ R γ (if γ = α then c' else d')).prod := by
    rw [hprod, hprod, h]
  have key : ∀ γ ∈ [α, β], (if γ = α then c else d) = (if γ = α then c' else d') := by
    rcases hsign with ⟨hα, hβ⟩ | ⟨hα, hβ⟩
    · exact pinnedX_list_prod_injective _ hnd (by simp [hα, hβ]) _ _ heq
    · exact pinnedX_list_prod_injective_neg _ hnd (by simp [hα, hβ]) _ _ heq
  have h1 := key α (by simp)
  have h2 := key β (by simp)
  simp only [ite_true, hne.symm, ite_false] at h1 h2
  exact ⟨h1, h2⟩

end General

namespace ReeTag

abbrev largeReeI1 : Fin F4.tag.rank := ⟨0, by decide⟩

abbrev largeReeI4 : Fin F4.tag.rank := ⟨3, by decide⟩

theorem largeRee_A1_data : F4.perm largeReeI1 = largeReeI4 ∧ F4.perm largeReeI4 = largeReeI1 ∧
    F4.tag.cartan largeReeI1 largeReeI1 = 2 ∧ F4.tag.cartan largeReeI4 largeReeI1 = 0 ∧
    largeReeI1 ≠ largeReeI4 := by
  decide

theorem largeRee_relationExponent (a : ℕ) :
    F4.relationExponent a largeReeI1 = 2 ^ a ∧ F4.relationExponent a largeReeI4 = 2 * 2 ^ a := by
  refine ⟨?_, ?_⟩
  · rw [relationExponent, ite_eq_left (by decide)]
    rfl
  · rw [relationExponent, ite_eq_right (by decide), pow_succ, mul_comm]
    rfl

theorem largeRee_not_isRoot
    : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ¬ IsRoot F4.tag (a • (Pi.single largeReeI1 1 : Fin F4.tag.rank → ℤ) +
      b • (Pi.single largeReeI4 1 : Fin F4.tag.rank → ℤ)) :=
  forall_not_isRoot_of_check (k := largeReeI1) (l := largeReeI4)
    (fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num)
    (fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num) (by simp) (by simp)
    f4Single_not_isRoot

variable {K : Type} [Field K]

theorem largeRee_commute_xx
    (c d : K) :
    Commute (xUnit F4.tag K largeReeI1 c) (xUnit F4.tag K largeReeI4 d) := by
  have h := commute_pinnedX_of_forall_not_isRoot K (isRoot_single _ largeReeI1)
    (isRoot_single _ largeReeI4) (by decide) (by decide)
    (fun a b ha hb => largeRee_not_isRoot a b (by omega) (by omega)) c d
  rwa [pinnedX_single, pinnedX_single] at h

theorem largeRee_commute_yy
    (c d : K) :
    Commute (yUnit F4.tag K largeReeI1 c) (yUnit F4.tag K largeReeI4 d) := by
  have hnr : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot F4.tag
      (a • (-Pi.single largeReeI1 1 : Fin F4.tag.rank → ℤ) +
        b • (-Pi.single largeReeI4 1 : Fin F4.tag.rank → ℤ)) := by
    intro a b ha hb hr
    have h' := IsRoot.neg hr
    rw [smul_neg, smul_neg, ← neg_add, neg_neg] at h'
    exact largeRee_not_isRoot a b (by omega) (by omega) h'
  have h := commute_pinnedX_of_forall_not_isRoot K (isRoot_neg_single _ largeReeI1)
    (isRoot_neg_single _ largeReeI4) (by decide) (by decide) hnr c d
  rwa [pinnedX_neg_single, pinnedX_neg_single] at h

theorem largeRee_x_inj
    {c d c' d' : K}
    (h : xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 d =
      xUnit F4.tag K largeReeI1 c' * xUnit F4.tag K largeReeI4 d') : c = c' ∧ d = d' := by
  rw [← pinnedX_single, ← pinnedX_single, ← pinnedX_single, ← pinnedX_single] at h
  refine pinnedX_mul_pinnedX_inj (Or.inl ⟨⟨isRoot_single _ _, ?_⟩, isRoot_single _ _, ?_⟩)
    (by decide) h <;> rw [height_single] <;> exact one_pos

theorem largeRee_y_inj
    {c d c' d' : K}
    (h : yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 d =
      yUnit F4.tag K largeReeI1 c' * yUnit F4.tag K largeReeI4 d') : c = c' ∧ d = d' := by
  rw [← pinnedX_neg_single, ← pinnedX_neg_single, ← pinnedX_neg_single,
    ← pinnedX_neg_single] at h
  refine pinnedX_mul_pinnedX_inj (Or.inr ⟨⟨isRoot_neg_single _ _, ?_⟩,
    isRoot_neg_single _ _, ?_⟩) (by decide) h <;> rw [height_neg, height_single] <;>
    exact neg_one_lt_zero

variable (K) in
@[expose] def largeReeRankOne
    (i : Fin F4.tag.rank) : SL2 K →* ModGL F4.tag K :=
  (exceptional_ordinary_rank_one_central_image F4.tag K i).choose

theorem largeReeRankOne_uSL
    (i : Fin F4.tag.rank) (c : K) :
    largeReeRankOne K i (uSL c) = xUnit F4.tag K i c :=
  (exceptional_ordinary_rank_one_central_image F4.tag K i).choose_spec.1 c

theorem largeReeRankOne_vSL
    (i : Fin F4.tag.rank) (c : K) :
    largeReeRankOne K i (vSL c) = yUnit F4.tag K i c :=
  (exceptional_ordinary_rank_one_central_image F4.tag K i).choose_spec.2.1 c

theorem largeReeRankOne_HSL
    (i : Fin F4.tag.rank) (u : Kˣ) :
    largeReeRankOne K i (HSL u) = torusElt F4.tag K i u :=
  (exceptional_ordinary_rank_one_central_image F4.tag K i).choose_spec.2.2.1 u

theorem largeReeRankOne_WSL
    (i : Fin F4.tag.rank) :
    largeReeRankOne K i WSL = weylElt F4.tag K i 1 :=
  (exceptional_ordinary_rank_one_central_image F4.tag K i).choose_spec.2.2.2.1

theorem largeReeRankOne_range
    (i : Fin F4.tag.rank) :
    (largeReeRankOne K i).range =
      Subgroup.closure (Set.range (xUnit F4.tag K i) ∪ Set.range (yUnit F4.tag K i)) :=
  (exceptional_ordinary_rank_one_central_image F4.tag K i).choose_spec.2.2.2.2.1

theorem eq_largeReeRankOne
    {ρ' : SL2 K →* ModGL F4.tag K} {i : Fin F4.tag.rank}
    (hu : ∀ c, ρ' (uSL c) = xUnit F4.tag K i c) (hH : ∀ u, ρ' (HSL u) = torusElt F4.tag K i u)
    (hW : ρ' WSL = weylElt F4.tag K i 1) : ρ' = largeReeRankOne K i :=
  SL2_hom_ext (fun s => by rw [hu, largeReeRankOne_uSL]) (fun u => by rw [hH, largeReeRankOne_HSL])
    (by rw [hW, largeReeRankOne_WSL])

theorem commute_largeReeRankOne
    (g g' : SL2 K) :
    Commute (largeReeRankOne K largeReeI1 g) (largeReeRankOne K largeReeI4 g') := by
  have hgen : ∀ x ∈ Set.range (xUnit F4.tag K largeReeI1) ∪ Set.range (yUnit F4.tag K largeReeI1),
      ∀ y ∈ Set.range (xUnit F4.tag K largeReeI4) ∪ Set.range (yUnit F4.tag K largeReeI4),
        Commute x y := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · exact largeRee_commute_xx c d
    · exact commute_xUnit_yUnit_of_ne' (by decide) c d
    · exact (commute_xUnit_yUnit_of_ne' (by decide) d c).symm
    · exact largeRee_commute_yy c d
  have hle : Subgroup.closure
      (Set.range (xUnit F4.tag K largeReeI1) ∪ Set.range (yUnit F4.tag K largeReeI1)) ≤
      Subgroup.centralizer (Subgroup.closure
        (Set.range (xUnit F4.tag K largeReeI4) ∪ Set.range (yUnit F4.tag K largeReeI4)) :
          Set (ModGL F4.tag K)) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hle' : Subgroup.closure
        (Set.range (xUnit F4.tag K largeReeI4) ∪ Set.range (yUnit F4.tag K largeReeI4)) ≤
        Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).2 fun y hy z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hgen z hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun y hy => (hle' hy x rfl).symm
  have hg : largeReeRankOne K largeReeI1 g ∈ (largeReeRankOne K largeReeI1).range := ⟨g, rfl⟩
  have hg' : largeReeRankOne K largeReeI4 g' ∈ (largeReeRankOne K largeReeI4).range := ⟨g', rfl⟩
  rw [largeReeRankOne_range] at hg hg'
  exact ((Subgroup.mem_centralizer_iff.1 (hle hg)) _ hg').symm

variable [CharP K F4.prime]

variable (K) in
@[expose] def largeReeRhoHom (a : ℕ) : K →+* K :=
  haveI : CharP K 2 := ‹CharP K F4.prime›
  iterateFrobenius K 2 a

theorem largeReeRhoHom_apply (a : ℕ) (c : K) : largeReeRhoHom K a c = c ^ 2 ^ a := by
  have : CharP K 2 := ‹CharP K F4.prime›
  exact iterateFrobenius_def (p := 2) a c

variable (K) in
@[expose] def largeReeA1Hom
    (a : ℕ) : SL2 K →* ModGL F4.tag K where
  toFun g := largeReeRankOne K largeReeI1 g *
    largeReeRankOne K largeReeI4 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) g)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    exact (commute_largeReeRankOne h _).mul_mul_mul_comm _ _

variable (a : ℕ)

theorem largeReeA1Hom_apply
    (g : SL2 K) : largeReeA1Hom K a g = largeReeRankOne K largeReeI1 g *
    largeReeRankOne K largeReeI4 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) g) :=
  rfl

theorem largeReeA1Hom_uSL
    (c : K) :
    largeReeA1Hom K a (uSL c) =
      xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) := by
  rw [largeReeA1Hom_apply, map_uSL, largeReeRankOne_uSL, largeReeRankOne_uSL,
    largeReeRhoHom_apply]

theorem largeReeA1Hom_vSL
    (c : K) :
    largeReeA1Hom K a (vSL c) =
      yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 (c ^ 2 ^ a) := by
  rw [largeReeA1Hom_apply, map_vSL, largeReeRankOne_vSL, largeReeRankOne_vSL,
    largeReeRhoHom_apply]

theorem largeReeA1Hom_HSL
    (u : Kˣ) :
    largeReeA1Hom K a (HSL u) = torusElt F4.tag K largeReeI1 u *
      torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) := by
  rw [largeReeA1Hom_apply, map_HSL, largeReeRankOne_HSL, largeReeRankOne_HSL]

theorem largeReeA1Hom_WSL :
    largeReeA1Hom K a WSL = weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1 := by
  rw [largeReeA1Hom_apply, map_WSL, largeReeRankOne_WSL, largeReeRankOne_WSL]

section Fixed

variable [Finite K]

variable (K) in
@[expose] def largeReeA1Y
    : Subgroup (ModGL F4.tag K) :=
  rootSpan F4.tag K (Neg.neg '' F4.fixedOrbitRoots ⟨0, by decide⟩) ⊓ F4.reeGamma K a

variable (K) in
@[expose] def largeReeA1M
    : Subgroup (ModGL F4.tag K) :=
  F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ ⊔ largeReeA1Y K a

omit [Field K] [CharP K F4.prime] [Finite K] in
theorem F4_fixedOrbitRoots_zero :
    F4.fixedOrbitRoots ⟨0, by decide⟩ = {Pi.single largeReeI1 1, Pi.single largeReeI4 1} := by
  rw [fixedOrbitRoots_eq_list]
  have e : F4.fixedOrbitRootList ⟨0, by decide⟩ =
      [Pi.single largeReeI4 1, Pi.single largeReeI1 1] := by
    decide
  ext x
  rw [Set.mem_ofPred_eq, e]
  simp [or_comm]

omit [CharP K F4.prime] [Finite K] in
theorem exists_eq_of_mem_rootSpan_pos
    {g : ModGL F4.tag K}
    (hg : g ∈ rootSpan F4.tag K (F4.fixedOrbitRoots ⟨0, by decide⟩)) :
    ∃ c d : K, xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 d = g := by
  let S : Subgroup (ModGL F4.tag K) :=
    { carrier := {g | ∃ c d : K, xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 d = g}
      one_mem' := ⟨0, 0, by rw [xUnit_zero, xUnit_zero, mul_one]⟩
      mul_mem' := by
        rintro _ _ ⟨c, d, rfl⟩ ⟨c', d', rfl⟩
        refine ⟨c + c', d + d', ?_⟩
        rw [xUnit_add, xUnit_add]
        exact (largeRee_commute_xx c' d).mul_mul_mul_comm _ _
      inv_mem' := by
        rintro _ ⟨c, d, rfl⟩
        refine ⟨-c, -d, ?_⟩
        rw [xUnit_neg, xUnit_neg, mul_inv_rev]
        exact ((largeRee_commute_xx c d).inv_inv).eq }
  have hle : rootSpan F4.tag K (F4.fixedOrbitRoots ⟨0, by decide⟩) ≤ S := by
    rw [F4_fixedOrbitRoots_zero]
    refine iSup₂_le fun α hα => ?_
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    rcases hα with rfl | rfl
    · exact ⟨c, 0, by rw [xUnit_zero, mul_one, pinnedX_single]⟩
    · exact ⟨0, c, by rw [xUnit_zero, one_mul, pinnedX_single]⟩
  exact hle hg

omit [CharP K F4.prime] [Finite K] in
theorem exists_eq_of_mem_rootSpan_neg
    {g : ModGL F4.tag K}
    (hg : g ∈ rootSpan F4.tag K (Neg.neg '' F4.fixedOrbitRoots ⟨0, by decide⟩)) :
    ∃ c d : K, yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 d = g := by
  let S : Subgroup (ModGL F4.tag K) :=
    { carrier := {g | ∃ c d : K, yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 d = g}
      one_mem' := ⟨0, 0, by rw [yUnit_zero, yUnit_zero, mul_one]⟩
      mul_mem' := by
        rintro _ _ ⟨c, d, rfl⟩ ⟨c', d', rfl⟩
        refine ⟨c + c', d + d', ?_⟩
        rw [yUnit_add, yUnit_add]
        exact (largeRee_commute_yy c' d).mul_mul_mul_comm _ _
      inv_mem' := by
        rintro _ ⟨c, d, rfl⟩
        refine ⟨-c, -d, ?_⟩
        rw [yUnit_neg, yUnit_neg, mul_inv_rev]
        exact ((largeRee_commute_yy c d).inv_inv).eq }
  have hle : rootSpan F4.tag K (Neg.neg '' F4.fixedOrbitRoots ⟨0, by decide⟩) ≤ S := by
    rw [F4_fixedOrbitRoots_zero, Set.image_insert_eq, Set.image_singleton]
    refine iSup₂_le fun α hα => ?_
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    rcases hα with rfl | rfl
    · exact ⟨c, 0, by rw [yUnit_zero, mul_one, pinnedX_neg_single]⟩
    · exact ⟨0, c, by rw [yUnit_zero, one_mul, pinnedX_neg_single]⟩
  exact hle hg

variable {a}

theorem coe_reeFixedOrbitUnipotent_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) =
      Set.range fun c : K =>
        xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) := by
  obtain ⟨ρ, σ, hρ, hσ, hρσ, -, -, -⟩ := large_Ree_field_powers a K hK
  have hfix : ∀ c : K, (c ^ 2 ^ a) ^ (2 * 2 ^ a) = c := fun c => by
    rw [← hρ, ← hσ]
    exact congrArg (fun e : K ≃+* K => e c) hρσ
  obtain ⟨p1, p4, -, -, -⟩ := largeRee_A1_data
  obtain ⟨e1, e4⟩ := largeRee_relationExponent a
  ext g
  constructor
  · intro hg
    obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨c, d, rfl⟩ := exists_eq_of_mem_rootSpan_pos hgS
    have hga : xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 d ∈
        adjointGroup F4.tag K := mul_mem (xUnit_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _)
    have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ hga
    have e : (⟨_, hga⟩ : adjointGroup F4.tag K) = xElement largeReeI1 c * xElement largeReeI4 d :=
      rfl
    rw [e, map_mul, finiteReeAut_xElement, finiteReeAut_xElement, p1, p4, e1, e4] at hF
    have hF' : xUnit F4.tag K largeReeI1 (d ^ (2 * 2 ^ a)) * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) =
        xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 d :=
      (largeRee_commute_xx _ _).eq.trans hF
    obtain ⟨-, h2⟩ := largeRee_x_inj hF'
    exact ⟨c, by rw [← h2]⟩
  · rintro ⟨c, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [F4_fixedOrbitRoots_zero]
      refine mul_mem ?_ ?_ <;> rw [← pinnedX_single] <;> exact pinnedX_mem_rootSpan (by simp) _
    · exact mem_reeGamma_mul (x := xElement largeReeI1 c) (y := xElement largeReeI4 (c ^ 2 ^ a))
        (by rw [finiteReeAut_xElement, p1, e1])
        (by rw [finiteReeAut_xElement, p4, e4, hfix]) (largeRee_commute_xx _ _)

theorem coe_largeReeA1Y
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (largeReeA1Y K a : Set (ModGL F4.tag K)) =
      Set.range fun c : K =>
        yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 (c ^ 2 ^ a) := by
  obtain ⟨ρ, σ, hρ, hσ, hρσ, -, -, -⟩ := large_Ree_field_powers a K hK
  have hfix : ∀ c : K, (c ^ 2 ^ a) ^ (2 * 2 ^ a) = c := fun c => by
    rw [← hρ, ← hσ]
    exact congrArg (fun e : K ≃+* K => e c) hρσ
  obtain ⟨p1, p4, -, -, -⟩ := largeRee_A1_data
  obtain ⟨e1, e4⟩ := largeRee_relationExponent a
  ext g
  constructor
  · intro hg
    obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨c, d, rfl⟩ := exists_eq_of_mem_rootSpan_neg hgS
    have hga : yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 d ∈
        adjointGroup F4.tag K := mul_mem (yUnit_mem_adjointGroup _ _) (yUnit_mem_adjointGroup _ _)
    have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ hga
    have e : (⟨_, hga⟩ : adjointGroup F4.tag K) = yElement largeReeI1 c * yElement largeReeI4 d :=
      rfl
    rw [e, map_mul, finiteReeAut_yElement, finiteReeAut_yElement, p1, p4, e1, e4] at hF
    have hF' : yUnit F4.tag K largeReeI1 (d ^ (2 * 2 ^ a)) * yUnit F4.tag K largeReeI4 (c ^ 2 ^ a) =
        yUnit F4.tag K largeReeI1 c * yUnit F4.tag K largeReeI4 d :=
      (largeRee_commute_yy _ _).eq.trans hF
    obtain ⟨-, h2⟩ := largeRee_y_inj hF'
    exact ⟨c, by rw [← h2]⟩
  · rintro ⟨c, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [F4_fixedOrbitRoots_zero, Set.image_insert_eq, Set.image_singleton]
      refine mul_mem ?_ ?_ <;> rw [← pinnedX_neg_single] <;> exact pinnedX_mem_rootSpan (by simp) _
    · exact mem_reeGamma_mul (x := yElement largeReeI1 c) (y := yElement largeReeI4 (c ^ 2 ^ a))
        (by rw [finiteReeAut_yElement, p1, e1])
        (by rw [finiteReeAut_yElement, p4, e4, hfix]) (largeRee_commute_yy _ _)

theorem largeReeA1Hom_range
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (largeReeA1Hom K a).range = largeReeA1M K a := by
  rw [range_eq_sl2RootX_sup_sl2RootY, largeReeA1M]
  congr 1
  · ext g
    rw [mem_sl2RootX, ← SetLike.mem_coe, coe_reeFixedOrbitUnipotent_zero hK]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_uSL a c).symm.trans hc⟩,
      fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_uSL a c).trans hc⟩⟩
  · ext g
    rw [mem_sl2RootY, ← SetLike.mem_coe, coe_largeReeA1Y hK]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_vSL a c).symm.trans hc⟩,
      fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_vSL a c).trans hc⟩⟩

end Fixed

omit [CharP K F4.prime] in
theorem canonicalRep_F4_fixedOrbitElement_zero :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) =
      weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1 := by
  have hred : (coxeterSystem F4.tag).IsReduced (F4.fixedOrbitWord ⟨0, by decide⟩) := by
    change (coxeterSystem F4.tag).length (F4.fixedOrbitElement ⟨0, by decide⟩) =
      (F4.fixedOrbitWord ⟨0, by decide⟩).length
    rw [length_fixedOrbitElement, ncard_fixedOrbitRoots]
    rfl
  rw [fixedOrbitElement, canonicalRep_wordProd hred]
  change ([largeReeI1, largeReeI4].map fun i => weylElt F4.tag K i 1).prod = _
  rw [List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one]

omit [CharP K F4.prime] in
theorem weylElt_mul_weylElt_not_mem_borelGroup :
    weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1 ∉ borelGroup F4.tag K := by
  rw [← canonicalRep_F4_fixedOrbitElement_zero]
  intro h
  have h1 : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
      bruhatCell F4.tag K 1 :=
    mem_bruhatCell.2 ⟨_, h, 1, one_mem _, by rw [canonicalRep_one, mul_one, mul_one]⟩
  exact Set.disjoint_left.1 (disjoint_bruhatCell (fixedOrbitElement_ne_one _))
    (canonicalRep_mem_bruhatCell _) h1

theorem eq_one_of_largeReeA1Hom_eq_one
    {g : SL2 K} (hg : largeReeA1Hom K a g = 1) : g = 1 := by
  have h2 := F4_two_eq_zero (K := K)
  obtain ⟨-, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} F4.tag K
  have hXU : ∀ c : K, xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) ∈
      posUnipotent F4.tag K := fun c =>
    mul_mem (xUnit_mem_posUnipotent _ _) (xUnit_mem_posUnipotent _ _)
  have hXB : ∀ c : K, xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a) ∈
      borelGroup F4.tag K := fun c => Subgroup.mem_sup_right (hXU c)
  have hHT : ∀ u : Kˣ, torusElt F4.tag K largeReeI1 u *
      torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) ∈
        torusGroup F4.tag K := fun u =>
    mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc] at hg ⊢
    generalize Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc) = u at hg ⊢
    generalize (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 = b at hg ⊢
    rw [map_mul, largeReeA1Hom_HSL, largeReeA1Hom_uSL] at hg
    have hX := eq_inv_of_mul_eq_one_right hg
    have hX1 : xUnit F4.tag K largeReeI1 b * xUnit F4.tag K largeReeI4 (b ^ 2 ^ a) ∈
        torusGroup F4.tag K ⊓ posUnipotent F4.tag K :=
      Subgroup.mem_inf.2 ⟨hX ▸ inv_mem (hHT u), hXU b⟩
    rw [hHU, Subgroup.mem_bot] at hX1
    have hb0 : b = 0 := by
      have h' : xUnit F4.tag K largeReeI1 b * xUnit F4.tag K largeReeI4 (b ^ 2 ^ a) =
          xUnit F4.tag K largeReeI1 0 * xUnit F4.tag K largeReeI4 0 := by
        rw [hX1, xUnit_zero, xUnit_zero, mul_one]
      exact (largeRee_x_inj h').1
    have hH1 : torusElt F4.tag K largeReeI1 u *
        torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) = 1 :=
      inv_eq_one.1 (hX.symm.trans hX1)
    obtain ⟨-, -, c11, c41, -⟩ := largeRee_A1_data
    have hconj : xUnit F4.tag K largeReeI1 1 = xUnit F4.tag K largeReeI1 ((u : K) ^ 2) := by
      have e1 := (simple_torus_root_conjugation F4.tag K largeReeI1 largeReeI1 u 1).1
      have e4 := (simple_torus_root_conjugation F4.tag K largeReeI4 largeReeI1
        (Units.map (largeReeRhoHom K a).toMonoidHom u) 1).1
      rw [c11] at e1
      rw [c41, zpow_zero, Units.val_one, one_mul] at e4
      calc xUnit F4.tag K largeReeI1 1 =
            (torusElt F4.tag K largeReeI1 u *
              torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u)) *
              xUnit F4.tag K largeReeI1 1 *
              (torusElt F4.tag K largeReeI1 u *
                torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u))⁻¹ := by
            rw [hH1, one_mul, inv_one, mul_one]
        _ = torusElt F4.tag K largeReeI1 u *
              (torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u) *
                xUnit F4.tag K largeReeI1 1 *
                (torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom u))⁻¹) *
              (torusElt F4.tag K largeReeI1 u)⁻¹ := by group
        _ = xUnit F4.tag K largeReeI1 ((u : K) ^ 2) := by
            rw [e4, e1]
            simp
    have hsq : (u : K) ^ 2 = 1 :=
      ((exceptional_ordinary_rank_one_central_image F4.tag K largeReeI1).choose_spec.2.2.2.2.2.2.1
        hconj).symm
    have hu1 : u = 1 := by
      have h0 : ((u : K) - 1) ^ 2 = 0 := by linear_combination hsq - ((u : K) - 1) * h2
      exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))
    have hH : HSL (1 : Kˣ) = 1 :=
      SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])
    have hU : uSL (0 : K) = 1 :=
      SL2_ext (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL])
    rw [hb0, hu1, hH, hU, mul_one]
  · rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc, map_mul, map_mul, map_mul, largeReeA1Hom_uSL,
      largeReeA1Hom_HSL, largeReeA1Hom_WSL, largeReeA1Hom_uSL] at hg
    exfalso
    refine weylElt_mul_weylElt_not_mem_borelGroup (K := K) ?_
    generalize hx₁ : xUnit F4.tag K largeReeI1 ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0) * xUnit F4.tag K largeReeI4
        (((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 ^ a) =
          x₁ at hg
    generalize hx₂ : xUnit F4.tag K largeReeI1 ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0) * xUnit F4.tag K largeReeI4
        (((g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 ^ a) =
          x₂ at hg
    generalize hh : torusElt F4.tag K largeReeI1
        (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
          (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) *
        torusElt F4.tag K largeReeI4 (Units.map (largeReeRhoHom K a).toMonoidHom
          (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
            (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc))) = h at hg
    have hx₁B : x₁ ∈ borelGroup F4.tag K := hx₁ ▸ hXB _
    have hx₂B : x₂ ∈ borelGroup F4.tag K := hx₂ ▸ hXB _
    have hhB : h ∈ borelGroup F4.tag K := hh ▸ Subgroup.mem_sup_left (hHT _)
    have e : weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1 =
        h⁻¹ * x₁⁻¹ * x₂⁻¹ := by
      calc weylElt F4.tag K largeReeI1 1 * weylElt F4.tag K largeReeI4 1 =
            h⁻¹ * x₁⁻¹ * (x₁ * h * (weylElt F4.tag K largeReeI1 1 *
              weylElt F4.tag K largeReeI4 1) * x₂) * x₂⁻¹ := by group
        _ = h⁻¹ * x₁⁻¹ * x₂⁻¹ := by rw [hg, mul_one]
    rw [e]
    exact mul_mem (mul_mem (inv_mem hhB) (inv_mem hx₁B)) (inv_mem hx₂B)

theorem large_Ree_A1_pair_automorphism_bound
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) =
      Set.range (fun c : K => xUnit F4.tag K ⟨0, by decide⟩ c *
        xUnit F4.tag K ⟨3, by decide⟩ (c ^ 2 ^ a)) ∧
    (largeReeA1Y K a : Set (ModGL F4.tag K)) =
      Set.range (fun c : K => yUnit F4.tag K ⟨0, by decide⟩ c *
        yUnit F4.tag K ⟨3, by decide⟩ (c ^ 2 ^ a)) ∧
    (∀ (ρ' : SL2 K →* ModGL F4.tag K) (i : Fin F4.tag.rank),
      (∀ c, ρ' (uSL c) = xUnit F4.tag K i c) → (∀ u, ρ' (HSL u) = torusElt F4.tag K i u) →
        ρ' WSL = weylElt F4.tag K i 1 → ρ' = largeReeRankOne K i) ∧
    (∃ R : SL2 K ≃* largeReeA1M K a,
      (∀ g, (R g : ModGL F4.tag K) = largeReeRankOne K ⟨0, by decide⟩ g *
        largeReeRankOne K ⟨3, by decide⟩ (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) g)) ∧
      (∀ c, (R (uSL c) : ModGL F4.tag K) =
        xUnit F4.tag K ⟨0, by decide⟩ c * xUnit F4.tag K ⟨3, by decide⟩ (c ^ 2 ^ a)) ∧
      ∀ c, (R (vSL c) : ModGL F4.tag K) =
        yUnit F4.tag K ⟨0, by decide⟩ c * yUnit F4.tag K ⟨3, by decide⟩ (c ^ 2 ^ a)) ∧
    derivedSeries (pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf (largeReeA1M K a))
      ((largeReeA1Y K a).subgroupOf (largeReeA1M K a))) 2 = ⊥ := by
  have hrange := largeReeA1Hom_range (K := K) (a := a) hK
  have hR : ∀ g, largeReeA1Hom K a g ∈ largeReeA1M K a := fun g => by
    rw [← hrange]
    exact ⟨g, rfl⟩
  let R' : SL2 K →* largeReeA1M K a := (largeReeA1Hom K a).codRestrict _ hR
  have hinj : Function.Injective R' := (injective_iff_map_eq_one R').2 fun g hg =>
    eq_one_of_largeReeA1Hom_eq_one a (congrArg Subtype.val hg)
  have hsurj : Function.Surjective R' := by
    rintro ⟨x, hx⟩
    rw [← hrange] at hx
    obtain ⟨g, rfl⟩ := hx
    exact ⟨g, rfl⟩
  have hX : sl2RootX R' =
      (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf (largeReeA1M K a) := by
    ext ⟨x, hx⟩
    rw [mem_sl2RootX, Subgroup.mem_subgroupOf, ← SetLike.mem_coe,
      coe_reeFixedOrbitUnipotent_zero hK]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_uSL a c).symm.trans (congrArg Subtype.val hc)⟩,
      fun ⟨c, hc⟩ => ⟨c, Subtype.ext ((largeReeA1Hom_uSL a c).trans hc)⟩⟩
  have hY : sl2RootY R' = (largeReeA1Y K a).subgroupOf (largeReeA1M K a) := by
    ext ⟨x, hx⟩
    rw [mem_sl2RootY, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, coe_largeReeA1Y hK]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_vSL a c).symm.trans (congrArg Subtype.val hc)⟩,
      fun ⟨c, hc⟩ => ⟨c, Subtype.ext ((largeReeA1Hom_vSL a c).trans hc)⟩⟩
  have hker : ∀ g : SL(2, K), R' g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := fun g hg =>
    ⟨1, one_pow 2, by rw [hinj (hg.trans (map_one R').symm)]; simp⟩
  refine ⟨coe_reeFixedOrbitUnipotent_zero hK, coe_largeReeA1Y hK,
    fun ρ' i hu hH hW => eq_largeReeRankOne hu hH hW,
    ⟨MulEquiv.ofBijective R' ⟨hinj, hsurj⟩, fun g => rfl, fun c => largeReeA1Hom_uSL a c,
      fun c => largeReeA1Hom_vSL a c⟩, ?_⟩
  rw [← hX, ← hY]
  exact exceptional_central_SL2_pair_stabilizer R' hsurj hker

end ReeTag

end CFSG.LieType.Ree
