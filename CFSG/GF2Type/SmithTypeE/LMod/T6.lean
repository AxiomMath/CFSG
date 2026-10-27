module

public import CFSG.GF2Type.SmithTypeE.LMod.Act
public import CFSG.GF2Type.SmithTypeE.LMod.Basic
public import CFSG.LargeExtraspecial.DW37Input

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6 Matrix
open scoped MatrixGroups

attribute [local irreducible] tvIdxTab tvTab tvImg tvList

section Points

@[expose] def T6 : Subgroup (Equiv.Perm (Fin 1953)) := Subgroup.closure (Set.range tvP)

theorem tvP_mem (k : Fin 1953) : tvP k ∈ T6 := Subgroup.subset_closure ⟨k, rfl⟩

theorem T6_eq_range : T6 = (actPerm : SL(6, ZMod 2) →* Equiv.Perm (Fin 1953)).range := by
  apply le_antisymm
  · rw [T6, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨tvSL k, rfl⟩
  · rintro _ ⟨A, rfl⟩
    have h : A ∈ Subgroup.closure (Set.range tvSL) := by
      rw [closure_range_tvSL]
      trivial
    induction h using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact tvP_mem k
    | one => rw [map_one]; exact T6.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact T6.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact T6.inv_mem hx

theorem actPerm_mem (A : SL(6, ZMod 2)) : actPerm A ∈ T6 := by
  rw [T6_eq_range]
  exact ⟨A, rfl⟩

theorem exists_actPerm_eq {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) :
    ∃ A : SL(6, ZMod 2), actPerm A = g := by
  rw [T6_eq_range] at hg
  exact hg

@[expose] noncomputable def slT6 : SL(6, ZMod 2) ≃* T6 :=
  MulEquiv.ofBijective (actPerm.codRestrict T6 actPerm_mem)
    ⟨fun A B h => actPerm_injective (congrArg Subtype.val h), fun g => by
      obtain ⟨A, hA⟩ := exists_actPerm_eq g.2
      exact ⟨A, Subtype.ext hA⟩⟩

@[expose] noncomputable def pslT6 : PSL(6, ZMod 2) ≃* T6 :=
  (CFSG.LargeExtraspecial.DW.slEquivPSL 6).symm.trans slT6

theorem mul_tvP_mul_inv {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) (p : Fin 1953) :
    g * tvP p * g⁻¹ = tvP (g p) := by
  obtain ⟨A, rfl⟩ := exists_actPerm_eq hg
  rw [tvP, ← map_inv, ← map_mul, ← map_mul, ← tvSL_actPerm]
  rfl

@[expose] def IsTvAut (g : Equiv.Perm (Fin 1953)) : Prop := ∀ p, g * tvP p * g⁻¹ = tvP (g p)

theorem isTvAut_of_mem {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) : IsTvAut g :=
  mul_tvP_mul_inv hg

theorem IsTvAut.mul {g h : Equiv.Perm (Fin 1953)} (hg : IsTvAut g) (hh : IsTvAut h) :
    IsTvAut (g * h) := by
  intro p
  have e : g * h * tvP p * (g * h)⁻¹ = g * (h * tvP p * h⁻¹) * g⁻¹ := by group
  rw [Equiv.Perm.mul_apply, e, hh p, hg (h p)]

theorem IsTvAut.inv {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g) : IsTvAut g⁻¹ := by
  intro p
  have h := hg (g⁻¹ p)
  have hai : g (g⁻¹ p) = p := Equiv.Perm.eq_inv_iff_eq.1 rfl
  rw [hai] at h
  rw [inv_inv, ← h]
  group

theorem IsTvAut.one : IsTvAut (1 : Equiv.Perm (Fin 1953)) := fun p => by simp

theorem isTvAut_of_apply {g : Equiv.Perm (Fin 1953)}
    (h : ∀ k a, g (tvP k a) = tvP (g k) (g a)) : IsTvAut g := by
  intro p
  ext b
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h]
  simp

theorem IsTvAut.apply_tvP {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g) (p q : Fin 1953) :
    g (tvP p q) = tvP (g p) (g q) := by
  have h2 := congrArg (fun σ : Equiv.Perm (Fin 1953) => σ (g q)) (hg p)
  simp only [Equiv.Perm.mul_apply] at h2
  simpa using h2

theorem IsTvAut.conj_mem {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g) {h : Equiv.Perm (Fin 1953)}
    (hh : h ∈ T6) : g * h * g⁻¹ ∈ T6 := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [hg k]
    exact tvP_mem _
  | one =>
    have e : g * 1 * g⁻¹ = 1 := by group
    rw [e]
    exact T6.one_mem
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact T6.mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact T6.inv_mem hx

theorem IsTvAut.mem_normalizer {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g) :
    g ∈ Subgroup.normalizer (T6 : Set (Equiv.Perm (Fin 1953))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hg.conj_mem hh, fun hh => ?_⟩
  have := hg.inv.conj_mem hh
  rwa [inv_inv, show g⁻¹ * (g * h * g⁻¹) * g = h by group] at this

theorem center_T6_eq_bot : Subgroup.center T6 = ⊥ := by
  have h : Subgroup.center (SL(6, ZMod 2)) = ⊥ :=
    CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot 6
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
  have hz' : slT6.symm z ∈ Subgroup.center SL(6, ZMod 2) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply slT6.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hz (slT6 A)
  rw [h, Subgroup.mem_bot] at hz'
  rw [← slT6.apply_symm_apply z, hz', map_one]

end Points

section Planes

theorem map_planeSet_tvP {k i : Nat} (hk : k < 1953) (hi : i < 1395) :
    (planeSet i).map (tvP ⟨k, hk⟩).toEmbedding = planeSet (planeImg k i) := by
  obtain ⟨hj, -, hpts⟩ := tw_parts hk hi
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    rw [mem_planeSet, Equiv.toEmbedding_apply, tvP_apply]
    exact (hpts a.val a.2 (mem_planeSet.mp ha)).2
  · rw [Finset.card_map, card_planeSet hi, card_planeSet hj]

@[expose] def PermPlanes (g : Equiv.Perm (Fin 1953)) : Prop :=
  ∀ i < 1395, ∃ j < 1395, (planeSet i).map g.toEmbedding = planeSet j

theorem PermPlanes.mul {g h : Equiv.Perm (Fin 1953)} (hg : PermPlanes g) (hh : PermPlanes h) :
    PermPlanes (g * h) := by
  intro i hi
  obtain ⟨j, hj, hij⟩ := hh i hi
  obtain ⟨l, hl, hjl⟩ := hg j hj
  refine ⟨l, hl, ?_⟩
  rw [← hjl, ← hij, Finset.map_map]
  rfl

theorem PermPlanes.inv {g : Equiv.Perm (Fin 1953)} (hg : PermPlanes g) : PermPlanes g⁻¹ := by
  choose f hf hfe using hg
  let F : Fin 1395 → Fin 1395 := fun i => ⟨f i.val i.2, hf i.val i.2⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hab' : f a.val a.2 = f b.val b.2 := congrArg Fin.val hab
    have e : (planeSet a.val).map g.toEmbedding = (planeSet b.val).map g.toEmbedding := by
      rw [hfe a.val a.2, hfe b.val b.2, hab']
    exact Fin.ext (planeSet_injective a.2 b.2 (Finset.map_injective _ e))
  intro i hi
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hF) ⟨i, hi⟩
  refine ⟨j.val, j.2, ?_⟩
  have e := hfe j.val j.2
  have hfj : f j.val j.2 = i := congrArg Fin.val hj
  rw [hfj] at e
  rw [← e, Finset.map_map]
  convert Finset.map_refl
  ext a
  simp

theorem permPlanes_tvP (k : Fin 1953) : PermPlanes (tvP k) := fun i hi =>
  ⟨planeImg k.val i, (tw_parts k.2 hi).1, map_planeSet_tvP k.2 hi⟩

theorem permPlanes_of_mem {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) : PermPlanes g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact permPlanes_tvP k
  | one => intro i hi; exact ⟨i, hi, by ext a; simp; rfl⟩
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem exists_planeAct (g : T6) (i : Fin 1395) :
    ∃ j : Fin 1395,
      (planeSet i.val).map (g : Equiv.Perm (Fin 1953)).toEmbedding = planeSet j.val := by
  obtain ⟨j, hj, e⟩ := permPlanes_of_mem g.2 i.val i.2
  exact ⟨⟨j, hj⟩, e⟩

@[expose] noncomputable def planeAct (g : T6) (i : Fin 1395) : Fin 1395 :=
  Classical.choose (exists_planeAct g i)

theorem map_planeSet_planeAct (g : T6) (i : Fin 1395) :
    (planeSet i.val).map (g : Equiv.Perm (Fin 1953)).toEmbedding =
      planeSet (planeAct g i).val :=
  Classical.choose_spec (exists_planeAct g i)

theorem planeAct_eq_iff (g : T6) (i j : Fin 1395) :
    planeAct g i = j ↔ (planeSet i.val).map (g : Equiv.Perm (Fin 1953)).toEmbedding =
      planeSet j.val := by
  rw [map_planeSet_planeAct]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (planeSet_injective (planeAct g i).2 j.2 h)⟩

noncomputable instance planeAction : MulAction T6 (Fin 1395) where
  smul := planeAct
  one_smul i := (planeAct_eq_iff 1 i i).mpr (by ext a; simp; rfl)
  mul_smul g h i := by
    show planeAct (g * h) i = planeAct g (planeAct h i)
    refine (planeAct_eq_iff (g * h) i _).mpr ?_
    rw [← map_planeSet_planeAct g, ← map_planeSet_planeAct h, Finset.map_map]
    rfl

theorem map_planeSet_smul (g : T6) (i : Fin 1395) :
    (planeSet i.val).map (g : Equiv.Perm (Fin 1953)).toEmbedding = planeSet (g • i).val :=
  map_planeSet_planeAct g i

theorem tvP_smul (k : Fin 1953) (i : Fin 1395) :
    (⟨tvP k, tvP_mem k⟩ : T6) • i = ⟨planeImg k.val i.val, (tw_parts k.2 i.2).1⟩ :=
  (planeAct_eq_iff _ i _).mpr (map_planeSet_tvP k.2 i.2)

theorem opp_smul (g : T6) (i j : Fin 1395) : Opp (g • i).val (g • j).val ↔ Opp i.val j.val := by
  rw [Opp, Opp, ← map_planeSet_smul, ← map_planeSet_smul, Finset.disjoint_map]

end Planes

end CFSG.GF2Type.SmithTypeE.LMod
