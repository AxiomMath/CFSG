module

public import CFSG.LieType.Chevalley.GraphFixedSingletonsDerived

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem list_prod_map_mul_of_commute_of_ne {G ι : Type*} [Monoid G] {l : List ι} (hl : l.Nodup)
    (f g : ι → G) (h : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute (g x) (f y)) :
    (l.map fun x => f x * g x).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons]
    rw [ih hl.2 fun x hx y hy hxy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy]
    have hc : Commute (g a) (l.map f).prod := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      exact h a List.mem_cons_self b (List.mem_cons_of_mem _ hb) fun hab => hl.1 (hab ▸ hb)
    rw [mul_assoc, ← mul_assoc (g a), hc.eq, mul_assoc, mul_assoc]

theorem list_prod_inv_of_commute {G ι : Type*} [Group G] {l : List ι} (f : ι → G)
    (h : l.Pairwise fun x y => Commute (f x) (f y)) :
    ((l.map f).prod)⁻¹ = (l.map fun x => (f x)⁻¹).prod := by
  rw [List.prod_inv_reverse, List.map_map]
  refine (List.reverse_perm _).prod_eq' ?_
  rw [List.pairwise_reverse, List.pairwise_map]
  exact h.imp fun hxy => hxy.symm.inv_inv

section Commute

variable {t : TwistTag} (K : Type) [Field K]

theorem commute_weylElt_xUnit'
    {a : Fin t.foldedTag.rank} {l j : Fin t.tag.rank}
    (hl : l ∈ t.orbit a) (hj : j ∈ t.orbit a) (hlj : l ≠ j) (u : Kˣ) (c : K) :
    Commute (weylElt t.tag K l u) (xUnit t.tag K j c) := by
  rw [weylElt_eq_xUnit_mul]
  exact ((commute_xUnit_xUnit K hl hj _ _).mul_left
    (commute_xUnit_yUnit K hj hl (Ne.symm hlj) _ _).symm).mul_left
      (commute_xUnit_xUnit K hl hj _ _)

theorem commute_weylElt_yUnit'
    {a : Fin t.foldedTag.rank} {l j : Fin t.tag.rank}
    (hl : l ∈ t.orbit a) (hj : j ∈ t.orbit a) (hlj : l ≠ j) (u : Kˣ) (c : K) :
    Commute (weylElt t.tag K l u) (yUnit t.tag K j c) := by
  rw [weylElt_eq_xUnit_mul]
  exact ((commute_xUnit_yUnit K hl hj hlj _ _).mul_left
    (commute_yUnit_yUnit K hl hj hlj _ _)).mul_left (commute_xUnit_yUnit K hl hj hlj _ _)

theorem commute_weylElt_weylElt
    {a : Fin t.foldedTag.rank} {l j : Fin t.tag.rank}
    (hl : l ∈ t.orbit a) (hj : j ∈ t.orbit a) (hlj : l ≠ j) (u v : Kˣ) :
    Commute (weylElt t.tag K l u) (weylElt t.tag K j v) := by
  rw [weylElt_eq_xUnit_mul j v]
  exact ((commute_weylElt_xUnit' K hl hj hlj _ _).mul_right
    (commute_weylElt_yUnit' K hl hj hlj _ _)).mul_right (commute_weylElt_xUnit' K hl hj hlj _ _)

theorem list_prod_torusElt_conj_xUnit
    {a : Fin t.foldedTag.rank} (ω : List (Fin t.tag.rank))
    (hω : ω.Nodup) (hωa : ∀ i ∈ ω, i ∈ t.orbit a) {j : Fin t.tag.rank} (hj : j ∈ t.orbit a)
    (U : Fin t.tag.rank → Kˣ) (e : K) :
    (ω.map fun i => torusElt t.tag K i (U i)).prod * xUnit t.tag K j e *
        ((ω.map fun i => torusElt t.tag K i (U i)).prod)⁻¹ =
      xUnit t.tag K j ((if j ∈ ω then (U j : K) ^ 2 else 1) * e) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.nodup_cons] at hω
    have hi := hωa i List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    set P := (ω.map fun i => torusElt t.tag K i (U i)).prod
    have e1 : torusElt t.tag K i (U i) * P * xUnit t.tag K j e *
        (torusElt t.tag K i (U i) * P)⁻¹ =
        torusElt t.tag K i (U i) * (P * xUnit t.tag K j e * P⁻¹) *
          (torusElt t.tag K i (U i))⁻¹ := by
      group
    have hsum : ∀ l : Fin t.tag.rank, ∑ m, t.tag.cartan l m * (Pi.single j 1 : _ → ℤ) m =
        t.tag.cartan l j := fun l => by simp [Pi.single_apply]
    rw [e1, ih hω.2 fun l hl => hωa l (List.mem_cons_of_mem _ hl), ← pinnedX_single,
      root_torus_conjugation i (isRoot_single _ j), pinnedX_single, hsum]
    congr 1
    by_cases hij : i = j
    · subst hij
      rw [t.tag.cartan_self]
      simp [hω.1]
    · rw [t.cartan_eq_zero_of_mem_orbit hi hj hij, zpow_zero, Units.val_one, one_mul]
      simp only [List.mem_cons, Ne.symm hij, false_or]

end Commute

section Formulas

variable (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)

theorem injective_pow_orbitMin (a : Fin t.foldedTag.rank) :
    Function.Injective fun k : Fin (t.orbit a).card => (t.perm ^ (k : ℕ)) (t.orbitMin a) :=
  fun k l h => Fin.ext (t.injOn_pow_orbitMin a (Finset.mem_coe.2 (Finset.mem_range.2 k.2))
    (Finset.mem_coe.2 (Finset.mem_range.2 l.2)) h)

@[expose] def orbitYProd
    (a : Fin t.foldedTag.rank) (γ : Fin t.tag.rank → K) : ModGL t.tag K :=
  ((t.orbitWord a).map fun j => yUnit t.tag K j (γ j)).prod

theorem coe_orbitY_eq_orbitYProd
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) = orbitYProd t a (orbitParam t σ a c) := by
  rw [coe_orbitY, orbitYProd, t.orbitWord_eq_map_range, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => by
    rw [Function.comp_apply, orbitParam_pow t σ _ (List.mem_range.1 hk)]

@[expose] def orbitUnitParam (a : Fin t.foldedTag.rank) (u : Kˣ) : Fin t.tag.rank → Kˣ :=
  Function.extend (fun k : Fin (t.orbit a).card => (t.perm ^ (k : ℕ)) (t.orbitMin a))
    (fun k => Units.map (σ ^ (k : ℕ)).toMonoidHom u) 1

theorem orbitUnitParam_pow {a : Fin t.foldedTag.rank} (u : Kˣ) {k : ℕ}
    (hk : k < (t.orbit a).card) :
    orbitUnitParam t σ a u ((t.perm ^ k) (t.orbitMin a)) = Units.map (σ ^ k).toMonoidHom u :=
  (injective_pow_orbitMin t a).extend_apply
    (fun k : Fin (t.orbit a).card => Units.map (σ ^ (k : ℕ)).toMonoidHom u) 1 ⟨k, hk⟩

theorem coe_orbitUnitParam {a : Fin t.foldedTag.rank} (u : Kˣ) {j : Fin t.tag.rank}
    (hj : j ∈ t.orbit a) : (orbitUnitParam t σ a u j : K) = orbitParam t σ a (u : K) j := by
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitUnitParam_pow t σ u hk, orbitParam_pow t σ _ hk]
  rfl

@[expose] def orbitFieldUnit {a : Fin t.foldedTag.rank} (u : (orbitField t K σ a)ˣ) : Kˣ :=
  Units.map (orbitField t K σ a).subtype.toMonoidHom u

theorem coe_orbitFieldUnit {a : Fin t.foldedTag.rank} (u : (orbitField t K σ a)ˣ) :
    (orbitFieldUnit t σ u : K) = ((u : orbitField t K σ a) : K) :=
  rfl

theorem coe_orbitN_eq
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitN t K σ a u : ModGL t.tag K) = ((t.orbitWord a).map fun j =>
      weylElt t.tag K j (orbitUnitParam t σ a (orbitFieldUnit t σ u) j)).prod := by
  have hω := t.nodup_orbitWord a
  have hmem : ∀ j ∈ t.orbitWord a, j ∈ t.orbit a := fun j hj => (t.mem_orbitWord).1 hj
  set γ := orbitParam t σ a ((u : orbitField t K σ a) : K) with hγ
  set γ' := orbitParam t σ a (((-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) :
    orbitField t K σ a)) : K) with hγ'
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul, coe_orbitX_eq_orbitXProd,
    coe_orbitY_eq_orbitYProd, orbitXProd, orbitYProd,
    ← list_prod_map_mul_of_commute_of_ne hω (fun j => xUnit t.tag K j (γ j))
      (fun j => yUnit t.tag K j (γ' j))
      (fun x hx y hy hxy => (commute_xUnit_yUnit K (hmem y hy) (hmem x hx) (Ne.symm hxy) _ _).symm),
    ← list_prod_map_mul_of_commute_of_ne hω
      (fun j => xUnit t.tag K j (γ j) * yUnit t.tag K j (γ' j)) (fun j => xUnit t.tag K j (γ j))
      (fun x hx y hy hxy => (commute_xUnit_xUnit K (hmem x hx) (hmem y hy) _ _).mul_right
        (commute_xUnit_yUnit K (hmem x hx) (hmem y hy) hxy _ _))]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hU := coe_orbitUnitParam t σ (orbitFieldUnit t σ u) (hmem j hj)
  rw [coe_orbitFieldUnit] at hU
  rw [weylElt_eq_xUnit_mul, hU, Units.val_inv_eq_inv_val, hU]
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin (hmem j hj)
  congr 3
  rw [hγ', orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk, Subfield.coe_neg, map_neg,
    Units.val_inv_eq_inv_val, Subfield.coe_inv, map_inv₀]

theorem coe_orbitN_one
    (a : Fin t.foldedTag.rank) :
    (orbitN t K σ a 1 : ModGL t.tag K) =
      ((t.orbitWord a).map fun j => weylElt t.tag K j 1).prod := by
  rw [coe_orbitN_eq]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin ((t.mem_orbitWord).1 hj)
  rw [orbitUnitParam_pow t σ _ hk, show Units.map (σ ^ k).toMonoidHom
    (orbitFieldUnit t σ (1 : (orbitField t K σ a)ˣ)) = 1 by rw [orbitFieldUnit, map_one, map_one]]

theorem coe_orbitH_eq
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) = ((t.orbitWord a).map fun j =>
      torusElt t.tag K j (orbitUnitParam t σ a (orbitFieldUnit t σ u) j)).prod := by
  have hω := t.nodup_orbitWord a
  have hmem : ∀ j ∈ t.orbitWord a, j ∈ t.orbit a := fun j hj => (t.mem_orbitWord).1 hj
  set U := orbitUnitParam t σ a (orbitFieldUnit t σ u)
  rw [orbitH, Subgroup.coe_mul, Subgroup.coe_inv, coe_orbitN_eq, coe_orbitN_one,
    list_prod_inv_of_commute _ (hω.imp_of_mem fun hx hy hxy =>
      commute_weylElt_weylElt K (hmem _ hx) (hmem _ hy) hxy 1 1)]
  have hinv : ∀ j : Fin t.tag.rank, (weylElt t.tag K j 1)⁻¹ = weylElt t.tag K j (-1) :=
    fun j => weylElt_inv j 1
  simp only [hinv]
  rw [← list_prod_map_mul_of_commute_of_ne hω (fun j => weylElt t.tag K j (U j))
    (fun j => weylElt t.tag K j (-1))
    fun x hx y hy hxy => commute_weylElt_weylElt K (hmem x hx) (hmem y hy) hxy _ _]
  rfl

theorem orbitH_mul_orbitX_mul_inv
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ)
    (c : orbitField t K σ a) :
    orbitH t K σ a u * orbitX t K σ a c * (orbitH t K σ a u)⁻¹ =
      orbitX t K σ a ((u : orbitField t K σ a) ^ 2 * c) := by
  apply Subtype.ext
  have hω := t.nodup_orbitWord a
  have hmem : ∀ j ∈ t.orbitWord a, j ∈ t.orbit a := fun j hj => (t.mem_orbitWord).1 hj
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_orbitH_eq,
    coe_orbitX_eq_orbitXProd, coe_orbitX_eq_orbitXProd, orbitXProd, orbitXProd,
    ← MulAut.conj_apply, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [Function.comp_apply, MulAut.conj_apply,
    list_prod_torusElt_conj_xUnit K _ hω hmem (hmem j hj), ite_eq_left hj,
    coe_orbitUnitParam t σ _ (hmem j hj), coe_orbitFieldUnit]
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin (hmem j hj)
  rw [orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk,
    Subfield.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]

theorem coe_orbitH
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) = ((List.range (t.orbit a).card).map fun k =>
      torusElt t.tag K ((t.perm ^ k) (t.orbitMin a))
        (Units.map ((σ ^ k).comp (orbitField t K σ a).subtype).toMonoidHom u)).prod := by
  rw [coe_orbitH_eq, t.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  rw [Function.comp_apply, orbitUnitParam_pow t σ _ (List.mem_range.1 hk)]
  exact congrArg _ (Units.ext rfl)

end Formulas

section Perfect

variable (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)

theorem orbitX_zero
    (a : Fin t.foldedTag.rank) : orbitX t K σ a 0 = 1 :=
  (orbitXAdjHom t σ a).map_one

theorem orbitX_neg
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitX t K σ a (-c) = (orbitX t K σ a c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← orbitX_add, neg_add_cancel, orbitX_zero]

theorem canonicalRep_orbitReflection_eq_orbitN
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      (orbitN t K σ a 1 : ModGL t.tag K) := by
  rw [canonicalRep_orbitReflection, coe_orbitN_one]

theorem orbitX_mem_commutator
    {a : Fin t.foldedTag.rank} {u : (orbitField t K σ a)ˣ}
    (hu : (u : orbitField t K σ a) ^ 2 ≠ 1) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈
      ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ := by
  set b := c / ((u : orbitField t K σ a) ^ 2 - 1)
  have hb : (u : orbitField t K σ a) ^ 2 * b + -b = c := by
    have h1 : (u : orbitField t K σ a) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hu
    simp only [b]
    field_simp
    ring
  have hcomm : orbitH t K σ a u * orbitX t K σ a b * (orbitH t K σ a u)⁻¹ *
      (orbitX t K σ a b)⁻¹ = orbitX t K σ a c := by
    rw [orbitH_mul_orbitX_mul_inv, ← orbitX_neg, ← orbitX_add, hb]
  have hcomm' := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcomm'
  rw [← hcomm', ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (orbitH_mem_graphFixedRootGroup t σ a u)
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a b))

theorem orbitY_mem_commutator
    {a : Fin t.foldedTag.rank}
    (hx : ∀ c : orbitField t K σ a, (orbitX t K σ a c : ModGL t.tag K) ∈
      ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) ∈
      ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ := by
  rw [← canonicalRep_orbitReflection_conj_orbitX t σ a c,
    canonicalRep_orbitReflection_eq_orbitN t σ a]
  exact conj_mem_commutator_self (orbitN_mem_graphFixedRootGroup t σ a 1) (hx (-c))

theorem exists_unit_sq_ne_one {F : Type*} [Field F] (h : ∃ s : Finset F, 4 ≤ s.card) :
    ∃ u : Fˣ, (u : F) ^ 2 ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := h
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1, -1} : Finset F)) (t := s) (lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  refine ⟨Units.mk0 x hx.1, ?_⟩
  rw [Units.val_mk0]
  exact fun h => (sq_eq_one_iff.1 h).elim hx.2.1 hx.2.2

end Perfect

theorem fixed_orbit_rank_one_scalar_perfectness
    (t : TwistTag) (K : Type) [Field K]
    (σ : K →+* K) :
    (∀ a (u : (orbitField t K σ a)ˣ), (orbitH t K σ a u : ModGL t.tag K) =
      ((List.range (t.orbit a).card).map fun k => torusElt t.tag K ((t.perm ^ k) (t.orbitMin a))
        (Units.map ((σ ^ k).comp (orbitField t K σ a).subtype).toMonoidHom u)).prod) ∧
    (∀ a (u : (orbitField t K σ a)ˣ) (c : orbitField t K σ a),
      orbitH t K σ a u * orbitX t K σ a c * (orbitH t K σ a u)⁻¹ =
        orbitX t K σ a ((u : orbitField t K σ a) ^ 2 * c)) ∧
    ∀ a, (∃ s : Finset (orbitField t K σ a), 4 ≤ s.card) → ∀ c : orbitField t K σ a,
      (orbitX t K σ a c : ModGL t.tag K) ∈
          ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ ∧
        (orbitY t K σ a c : ModGL t.tag K) ∈
          ⁅graphFixedRootGroup t K σ, graphFixedRootGroup t K σ⁆ := by
  refine ⟨coe_orbitH t σ, orbitH_mul_orbitX_mul_inv t σ, fun a hL c => ?_⟩
  obtain ⟨u, hu⟩ := exists_unit_sq_ne_one hL
  have hx := orbitX_mem_commutator t σ hu
  exact ⟨hx c, orbitY_mem_commutator t σ hx c⟩

end CFSG.LieType.Chevalley
