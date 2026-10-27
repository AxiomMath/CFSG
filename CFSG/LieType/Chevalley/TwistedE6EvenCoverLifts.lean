module

public import CFSG.LieType.Chevalley.TwistedE6EvenCoverForms
public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverLifts
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots

public noncomputable section

namespace CFSG.LieType.Chevalley.TwistedE6Cover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def partner (a : Fin TwistTag.E6.foldedTag.rank) : Fin TwistTag.E6.foldedTag.rank :=
  (![1, 0, 3, 2] : Fin 4 → Fin 4) a

@[expose] def orbitSingle (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1

@[expose] def edgeRoot (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  (TwistTag.E6.orbitWord (partner a)).foldr (reflect TwistTag.E6.tag) (orbitSingle a k)

@[expose] def EdgeShear (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) : Prop :=
  TwistTag.E6.tag.cartan ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
      ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin (partner a))) = -1 ∧
    TwistTag.E6.tag.cartan ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin (partner a)))
      ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) = -1 ∧
    edgeRoot a k = orbitSingle a k + orbitSingle (partner a) k

instance (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) : Decidable (EdgeShear a k) := by
  unfold EdgeShear
  infer_instance

@[expose] def EdgeComm (a : Fin TwistTag.E6.foldedTag.rank) (k k' : ℕ) : Prop :=
  (k ≠ k' → 0 ≤ iform (orbitSingle (partner a) k) (orbitSingle a k') ∧
      orbitSingle (partner a) k ≠ -orbitSingle a k' ∧
      0 ≤ iform (orbitSingle (partner a) k) (edgeRoot a k') ∧
      orbitSingle (partner a) k ≠ -edgeRoot a k') ∧
    0 ≤ iform (orbitSingle a k) (edgeRoot a k') ∧ orbitSingle a k ≠ -edgeRoot a k'

instance (a : Fin TwistTag.E6.foldedTag.rank) (k k' : ℕ) : Decidable (EdgeComm a k k') := by
  unfold EdgeComm
  infer_instance

@[expose] def EdgeData (a : Fin TwistTag.E6.foldedTag.rank) : Prop :=
  (TwistTag.E6.orbit (partner a)).card = (TwistTag.E6.orbit a).card ∧
    ∀ k < (TwistTag.E6.orbit a).card,
      EdgeShear a k ∧ ∀ k' < (TwistTag.E6.orbit a).card, EdgeComm a k k'

instance (a : Fin TwistTag.E6.foldedTag.rank) : Decidable (EdgeData a) := by
  unfold EdgeData
  infer_instance

theorem edgeData : ∀ a, EdgeData a := by
  decide

theorem orbitReflection_smul_orbitSingle
    (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) :
    TwistTag.E6.orbitReflection (partner a) • orbitSingle a k = edgeRoot a k :=
  TwistTag.E6.orbitReflection_smul _ _

theorem isRoot_orbitSingle (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) :
    IsRoot TwistTag.E6.tag (orbitSingle a k) :=
  isRoot_single _ _

theorem isRoot_edgeRoot
    (a : Fin TwistTag.E6.foldedTag.rank) (k : ℕ) :
    IsRoot TwistTag.E6.tag (edgeRoot a k) := by
  rw [← orbitReflection_smul_orbitSingle]
  exact IsRoot.smul (isRoot_orbitSingle a k) _

variable {K : Type} [Field K]

theorem simplyLaced_E6 : ∀ i, TwistTag.E6.tag.symmetrizer i i = 1 := fun i => by
  change (1 : Matrix (Fin 6) (Fin 6) ℤ) i i = 1
  exact Matrix.one_apply_eq i

theorem commute_pinnedX_of_iform
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ -β)
    (h0 : 0 ≤ iform α β) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) := by
  by_cases hab : α = β
  · subst hab
    change pinnedX _ K α c * pinnedX _ K α d = pinnedX _ K α d * pinnedX _ K α c
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
        TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
    exact (simply_laced_root_commutator_unit TwistTag.E6.tag hτ hα hβ hab hne).2
      (SimplyLacedCover.not_isRoot_add simplyLaced_E6 hα hβ h0) K _
      (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)

theorem reflect_single_of_cartan {i j : Fin TwistTag.E6.tag.rank}
    (hij : TwistTag.E6.tag.cartan i j = -1) :
    reflect TwistTag.E6.tag i (Pi.single j 1) = Pi.single j 1 + Pi.single i 1 := by
  funext l
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one, hij]
  ring

variable [CharP K 2]

theorem xUnit_shear
    {i j : Fin TwistTag.E6.tag.rank} (hij : TwistTag.E6.tag.cartan i j = -1)
    (hji : TwistTag.E6.tag.cartan j i = -1) (e : K) :
    xUnit TwistTag.E6.tag K j 1 * xUnit TwistTag.E6.tag K i e * (xUnit TwistTag.E6.tag K j 1)⁻¹ =
      pinnedX TwistTag.E6.tag K (Pi.single i 1 + Pi.single j 1) e *
        xUnit TwistTag.E6.tag K i e := by
  have hcomm := (a2_simple_root_commutatorElement K hij hji e 1).1
  rw [mul_one, ← pinnedX_single TwistTag.E6.tag K j e,
    CFSG.LieType.Ree.weylElt_conj_pinnedX_of_two_eq_zero CharTwo.two_eq_zero i
      (isRoot_single _ j) e, reflect_single_of_cartan hij, add_comm] at hcomm
  calc xUnit TwistTag.E6.tag K j 1 * xUnit TwistTag.E6.tag K i e * (xUnit TwistTag.E6.tag K j 1)⁻¹ =
      ⁅xUnit TwistTag.E6.tag K i e, xUnit TwistTag.E6.tag K j 1⁆⁻¹ *
        xUnit TwistTag.E6.tag K i e := by
        rw [commutatorElement_def]
        group
    _ = _ := by rw [hcomm, pinnedX_inv_charTwo]

theorem list_conj_shear {G ι : Type*} [Group G] {l : List ι} (hl : l.Nodup) (g h Z : ι → G)
    (hshear : ∀ k ∈ l, g k * h k * (g k)⁻¹ = Z k * h k)
    (hgh : ∀ k ∈ l, ∀ k' ∈ l, k ≠ k' → Commute (g k) (h k'))
    (hgZ : ∀ k ∈ l, ∀ k' ∈ l, k ≠ k' → Commute (g k) (Z k'))
    (hhZ : ∀ k ∈ l, ∀ k' ∈ l, Commute (h k) (Z k')) :
    (l.map g).prod * (l.map h).prod * ((l.map g).prod)⁻¹ = (l.map Z).prod * (l.map h).prod := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    have hk : k ∈ k :: l := List.mem_cons_self
    have hsub : ∀ x ∈ l, x ∈ k :: l := fun x hx => List.mem_cons_of_mem _ hx
    have hne : ∀ x ∈ l, k ≠ x := fun x hx h => hl.1 (h ▸ hx)
    have ih' := ih hl.2 (fun x hx => hshear x (hsub x hx))
      (fun x hx y hy => hgh x (hsub x hx) y (hsub y hy))
      (fun x hx y hy => hgZ x (hsub x hx) y (hsub y hy))
      (fun x hx y hy => hhZ x (hsub x hx) y (hsub y hy))
    simp only [List.map_cons, List.prod_cons]
    set Gp := (l.map g).prod
    set Hp := (l.map h).prod
    set Zp := (l.map Z).prod
    have h1 : Commute Gp (h k) := Commute.list_prod_left _ _ fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hgh y (hsub y hy) k hk (hne y hy).symm
    have h2 : Commute (g k) Zp := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hgZ k hk y (hsub y hy) (hne y hy)
    have h3 : Commute (g k) Hp := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hgh k hk y (hsub y hy) (hne y hy)
    have h4 : Commute (h k) Zp := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hhZ k hk y (hsub y hy)
    calc g k * Gp * (h k * Hp) * (g k * Gp)⁻¹
        = g k * (Gp * h k) * Hp * Gp⁻¹ * (g k)⁻¹ := by group
      _ = g k * h k * (Gp * Hp * Gp⁻¹) * (g k)⁻¹ := by rw [h1.eq]; group
      _ = g k * h k * (Zp * Hp) * (g k)⁻¹ := by rw [ih']
      _ = (g k * h k * (g k)⁻¹) * (g k * Zp * (g k)⁻¹) * (g k * Hp * (g k)⁻¹) := by group
      _ = Z k * h k * Zp * Hp := by rw [hshear k hk, h2.eq, h3.eq]; group
      _ = Z k * (h k * Zp) * Hp := by group
      _ = Z k * (Zp * h k) * Hp := by rw [h4.eq]
      _ = Z k * Zp * (h k * Hp) := by group

variable {σ : K →+* K}

omit [CharP K 2] in
theorem coe_orbitX_one
    (b : Fin TwistTag.E6.foldedTag.rank) :
    (orbitX TwistTag.E6 K σ b 1 : ModGL TwistTag.E6.tag K) =
      ((List.range (TwistTag.E6.orbit b).card).map fun k =>
        xUnit TwistTag.E6.tag K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin b)) 1).prod := by
  rw [coe_orbitX]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Subfield.coe_one, map_one]

theorem orbitX_shear
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a) :
    (orbitX TwistTag.E6 K σ (partner a) 1 : ModGL TwistTag.E6.tag K) *
        (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) *
        (orbitX TwistTag.E6 K σ (partner a) 1 : ModGL TwistTag.E6.tag K)⁻¹ =
      conjX σ (TwistTag.E6.orbitReflection (partner a)) a c *
        (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) := by
  obtain ⟨hcard, hdata⟩ := edgeData a
  rw [coe_orbitX_one, hcard, conjX, canonicalRep_conj_orbitX_charTwo CharTwo.two_eq_zero,
    coe_orbitX]
  refine list_conj_shear List.nodup_range
    (fun k => xUnit TwistTag.E6.tag K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin (partner a))) 1)
    (fun k => xUnit TwistTag.E6.tag K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
      ((σ ^ k) (c : K)))
    (fun k => pinnedX TwistTag.E6.tag K (TwistTag.E6.orbitReflection (partner a) •
      Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) ((σ ^ k) (c : K)))
    (fun k hk => ?_) (fun k hk k' hk' hkk' => ?_) (fun k hk k' hk' hkk' => ?_)
    (fun k hk k' hk' => ?_)
  · obtain ⟨⟨hij, hji, he⟩, -⟩ := hdata k (List.mem_range.1 hk)
    change _ = pinnedX _ K (TwistTag.E6.orbitReflection (partner a) • orbitSingle a k) _ * _
    rw [orbitReflection_smul_orbitSingle, he]
    exact xUnit_shear hij hji _
  · obtain ⟨-, h⟩ := hdata k (List.mem_range.1 hk)
    obtain ⟨h0, hne, -, -⟩ := (h k' (List.mem_range.1 hk')).1 hkk'
    rw [← pinnedX_single, ← pinnedX_single]
    exact commute_pinnedX_of_iform (isRoot_orbitSingle _ _) (isRoot_orbitSingle _ _) hne h0 _ _
  · obtain ⟨-, h⟩ := hdata k (List.mem_range.1 hk)
    obtain ⟨-, -, h0, hne⟩ := (h k' (List.mem_range.1 hk')).1 hkk'
    rw [← pinnedX_single]
    change Commute (pinnedX _ K (orbitSingle (partner a) k) 1)
      (pinnedX _ K (TwistTag.E6.orbitReflection (partner a) • orbitSingle a k') _)
    rw [orbitReflection_smul_orbitSingle]
    exact commute_pinnedX_of_iform (isRoot_orbitSingle _ _) (isRoot_edgeRoot _ _) hne h0 _ _
  · obtain ⟨-, h⟩ := hdata k (List.mem_range.1 hk)
    obtain ⟨-, h0, hne⟩ := h k' (List.mem_range.1 hk')
    rw [← pinnedX_single]
    change Commute (pinnedX _ K (orbitSingle a k) _)
      (pinnedX _ K (TwistTag.E6.orbitReflection (partner a) • orbitSingle a k') _)
    rw [orbitReflection_smul_orbitSingle]
    exact commute_pinnedX_of_iform (isRoot_orbitSingle _ _) (isRoot_edgeRoot _ _) hne h0 _ _

theorem commute_orbitX_conjX
    (a : Fin TwistTag.E6.foldedTag.rank)
    (c d : orbitField TwistTag.E6 K σ a) :
    Commute (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K)
      (conjX σ (TwistTag.E6.orbitReflection (partner a)) a d) := by
  obtain ⟨-, hdata⟩ := edgeData a
  rw [conjX, canonicalRep_conj_orbitX_charTwo CharTwo.two_eq_zero, coe_orbitX]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hy
  obtain ⟨-, h⟩ := hdata k (List.mem_range.1 hk)
  obtain ⟨-, h0, hne⟩ := h k' (List.mem_range.1 hk')
  rw [← pinnedX_single]
  change Commute (pinnedX _ K (orbitSingle a k) _)
    (pinnedX _ K (TwistTag.E6.orbitReflection (partner a) • orbitSingle a k') _)
  rw [orbitReflection_smul_orbitSingle]
  exact commute_pinnedX_of_iform (isRoot_orbitSingle _ _) (isRoot_edgeRoot _ _) hne h0 _ _

omit [CharP K 2] in
theorem conjX_one
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a) :
    conjX σ 1 a c = (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) := by
  rw [conjX, canonicalRep_one, one_mul, inv_one, mul_one]

omit [CharP K 2] in
theorem conjX_mem_graphFixedRootGroup
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ a) : conjX σ w a c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hn := canonicalRep_mem_graphFixedRootGroup (K := K) (σ := σ) hw
  exact mul_mem (mul_mem hn (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ a c))) (inv_mem hn)

omit [CharP K 2] in
theorem conjX_zero
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    conjX σ w a 0 = 1 := by
  rw [conjX, orbitX_zero TwistTag.E6 σ a, Subgroup.coe_one, mul_one, mul_inv_cancel]

theorem conjX_sq
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ a) : conjX σ w a c ^ 2 = 1 := by
  rw [sq, ← conjX_add, CharTwo.add_self_eq_zero, conjX_zero]

omit [CharP K 2] in
@[expose] def conjXC
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a) :
    graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨conjX σ w a c, conjX_mem_graphFixedRootGroup hw a c⟩

omit [CharP K 2] in
theorem conjXC_coe
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a) :
    (conjXC hw a c : ModGL TwistTag.E6.tag K) = conjX σ w a c :=
  rfl

omit [CharP K 2] in
theorem conjXC_add
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) (c c' : orbitField TwistTag.E6 K σ a) :
    conjXC hw a (c + c') = conjXC hw a c * conjXC hw a c' :=
  Subtype.ext (conjX_add w a c c')

variable
    [Finite K] {E : Type*} [Group E] {η : E →* graphFixedRootGroup TwistTag.E6 K σ}

omit [Finite K] [CharP K 2] in
theorem coe_map_conj (a b : E) :
    ((η (a * b * a⁻¹) : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
      (η a : ModGL TwistTag.E6.tag K) * (η b : ModGL TwistTag.E6.tag K) *
        (η a : ModGL TwistTag.E6.tag K)⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

variable (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
include hη hC

theorem lift_commute_conjX
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f)
    {w w' : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (hw' : w' ∈ relWeylTwist TwistTag.E6) {a a' : Fin TwistTag.E6.foldedTag.rank}
    (harith : ∀ i j : ℕ, i < f → j < f → ¬ ∀ l, (2 ^ f - 1 : ℤ) ∣
      2 ^ i * foldCoord (w • Pi.single (TwistTag.E6.orbitMin a) 1) l +
        2 ^ j * foldCoord (w' • Pi.single (TwistTag.E6.orbitMin a') 1) l)
    (hcomm : ∀ c d, Commute (conjX σ w a c) (conjX σ w' a' d)) (x y : E)
    (hx : ∃ c, (η x : ModGL TwistTag.E6.tag K) = conjX σ w a c)
    (hy : ∃ d, (η y : ModGL TwistTag.E6.tag K) = conjX σ w' a' d) :
    x * y = y * x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let P : Subgroup (ModGL TwistTag.E6.tag K) := rootSpan TwistTag.E6.tag K
    ((fun i => w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit a)) ⊓
      twistedFixedGroup TwistTag.E6 K σ
  let P' : Subgroup (ModGL TwistTag.E6.tag K) := rootSpan TwistTag.E6.tag K
    ((fun i => w' • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit a')) ⊓
      twistedFixedGroup TwistTag.E6 K σ
  have hP : ∀ g : graphFixedRootGroup TwistTag.E6 K σ,
      g ∈ P.subgroupOf _ ↔ ∃ c, g = conjXC hw a c := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := (orbitConjHom_bijective TwistTag.E6 σ a hw).2 ⟨g, hg⟩
      exact ⟨c.toAdd, Subtype.ext (congrArg Subtype.val hc).symm⟩
    · rintro ⟨c, rfl⟩
      exact canonicalRep_conj_orbitX_mem TwistTag.E6 σ a hw c
  have hP' : ∀ g : graphFixedRootGroup TwistTag.E6 K σ,
      g ∈ P'.subgroupOf _ ↔ ∃ d, g = conjXC hw' a' d := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := (orbitConjHom_bijective TwistTag.E6 σ a' hw').2 ⟨g, hg⟩
      exact ⟨c.toAdd, Subtype.ext (congrArg Subtype.val hc).symm⟩
    · rintro ⟨c, rfl⟩
      exact canonicalRep_conj_orbitX_mem TwistTag.E6 σ a' hw' c
  let τΓ : (Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) → graphFixedRootGroup TwistTag.E6 K σ :=
    fun t => ⟨fixedTorus σ t, fixedTorus_mem_graphFixedRootGroup t⟩
  have hτ : ∀ (t : Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) {v : WeylGroup TwistTag.E6.tag}
      (hv : v ∈ relWeylTwist TwistTag.E6) (b : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ b),
      τΓ t * conjXC hv b c * (τΓ t)⁻¹ = conjXC hv b (Subfield.inclusion (fixField_le_orbitField b)
          (foldChar σ (v • Pi.single (TwistTag.E6.orbitMin b) 1) t : fixField σ) * c) :=
    fun t v hv b c => Subtype.ext (fixedTorus_conj_orbitConj h2 hv b t c)
  have hx' : ∃ c, η x = conjXC hw a c := by
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, Subtype.ext hc⟩
  have hy' : ∃ d, η y = conjXC hw' a' d := by
    obtain ⟨d, hd⟩ := hy
    exact ⟨d, Subtype.ext hd⟩
  refine lift_commute_of_form_eq_zero η hη hC τΓ (P.subgroupOf _) (P'.subgroupOf _)
    (fun g hg g' hg' => ?_) (fun g hg => ?_) (fun b hb₁ hb₂ hbT g hg g' hg' => ?_) x y
    ((hP _).2 hx') ((hP' _).2 hy')
  · obtain ⟨c, rfl⟩ := (hP g).1 hg
    obtain ⟨d, rfl⟩ := (hP' g').1 hg'
    exact Subtype.ext (hcomm c d).eq
  · obtain ⟨c, rfl⟩ := (hP g).1 hg
    exact Subtype.ext (by rw [Subgroup.coe_pow, conjXC_coe, conjX_sq, Subgroup.coe_one])
  · obtain ⟨c, rfl⟩ := (hP g).1 hg
    obtain ⟨d, rfl⟩ := (hP' g').1 hg'
    have hF := form_conjX_eq_zero hf hk harith (fun c d => b (conjXC hw a c) (conjXC hw' a' d))
      (fun c₁ c₂ d => by
        rw [conjXC_add]
        exact hb₁ _ ((hP _).2 ⟨c₁, rfl⟩) _ ((hP _).2 ⟨c₂, rfl⟩) _ ((hP' _).2 ⟨d, rfl⟩))
      (fun c d₁ d₂ => by
        rw [conjXC_add]
        exact hb₂ _ ((hP _).2 ⟨c, rfl⟩) _ ((hP' _).2 ⟨d₁, rfl⟩) _ ((hP' _).2 ⟨d₂, rfl⟩))
      (fun t c d => by
        rw [← hτ t hw a c, ← hτ t hw' a' d]
        exact hbT t _ ((hP _).2 ⟨c, rfl⟩) _ ((hP' _).2 ⟨d, rfl⟩))
    exact hF c d

theorem lift_commute_edge
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f)
    (a : Fin TwistTag.E6.foldedTag.rank) (z z' : E)
    (hz : ∃ c, (η z : ModGL TwistTag.E6.tag K) =
      conjX σ (TwistTag.E6.orbitReflection (partner a)) a c)
    (hz' : ∃ c, (η z' : ModGL TwistTag.E6.tag K) =
      conjX σ (TwistTag.E6.orbitReflection (partner a)) a c) :
    z * z' = z' * z := by
  obtain ⟨c, hc⟩ := hz
  obtain ⟨c', hc'⟩ := hz'
  set r := TwistTag.E6.orbitReflection (partner a)
  have hr : r ∈ relWeylTwist TwistTag.E6 := TwistTag.E6.orbitReflection_mem _
  obtain ⟨-, hdata⟩ := edgeData a
  obtain ⟨⟨-, -, he⟩, -⟩ := hdata 0 (TwistTag.E6.card_orbit_pos a)
  have hsingle : orbitSingle a 0 = Pi.single (TwistTag.E6.orbitMin a) 1 := by
    rw [orbitSingle, pow_zero, Equiv.Perm.one_apply]
  have hβ₀ : r • (Pi.single (TwistTag.E6.orbitMin a) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      orbitSingle a 0 + orbitSingle (partner a) 0 := by
    rw [← hsingle, orbitReflection_smul_orbitSingle, he]
  have hheight : height (orbitSingle a 0 + orbitSingle (partner a) 0) = 2 := by
    have e : height (orbitSingle a 0 + orbitSingle (partner a) 0) =
        height (orbitSingle a 0) + height (orbitSingle (partner a) 0) := by
      simp only [height, Pi.add_apply, Finset.sum_add_distrib]
    rw [e, orbitSingle, orbitSingle, height_single, height_single]
    norm_num
  have harith : ∀ i j : ℕ, i < f → j < f → ¬ ∀ l, (2 ^ f - 1 : ℤ) ∣
      2 ^ i * foldCoord ((1 : WeylGroup TwistTag.E6.tag) • Pi.single (TwistTag.E6.orbitMin a) 1) l +
        2 ^ j * foldCoord (r • Pi.single (TwistTag.E6.orbitMin a) 1) l := by
    rw [one_smul, hβ₀]
    refine fold_pair_not_dvd hf (isRoot_single _ _) (by rw [height_single]; exact one_pos)
      (by rw [← hβ₀]; exact IsRoot.smul (isRoot_single _ _) r) (by rw [hheight]; norm_num)
      fun hmem => ?_
    have h1 := TwistTag.E6.height_of_mem_diagramOrbit hmem
    rw [hheight, height_single] at h1
    exact absurd h1 (by decide)
  have hlift : ∀ x y : E, (∃ d, (η x : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a d) →
      (∃ d, (η y : ModGL TwistTag.E6.tag K) = conjX σ r a d) → Commute x y := by
    intro x y hx hy
    obtain ⟨d, hd⟩ := hx
    exact lift_commute_conjX hη hC hf hk (one_mem _) hr harith
      (fun c d => by rw [conjX_one]; exact commute_orbitX_conjX a c d) x y
      ⟨d, by rw [conjX_one, hd]⟩ hy
  have hcen : ∀ g ∈ η.ker, ∀ h : E, Commute g h := fun g hg h =>
    ((Subgroup.mem_center_iff.1 (hC hg)) h).symm
  have hker : ∀ g : E, ((η g : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) = 1 →
      g ∈ η.ker := fun g hg => (MonoidHom.mem_ker).2 (Subtype.ext hg)
  have hXmem : ∀ (b : Fin TwistTag.E6.foldedTag.rank) (d : orbitField TwistTag.E6 K σ b),
      (orbitX TwistTag.E6 K σ b d : ModGL TwistTag.E6.tag K) ∈
        graphFixedRootGroup TwistTag.E6 K σ :=
    fun b d => graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
      (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ b d)
  obtain ⟨x, hx⟩ := hη ⟨orbitX TwistTag.E6 K σ a c, hXmem a c⟩
  obtain ⟨x', hx'⟩ := hη ⟨orbitX TwistTag.E6 K σ a c', hXmem a c'⟩
  obtain ⟨n, hn⟩ := hη ⟨orbitX TwistTag.E6 K σ (partner a) 1, hXmem (partner a) 1⟩
  have hxM : (η x : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a c := by rw [hx]
  have hx'M : (η x' : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a c' := by rw [hx']
  have hnM : (η n : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ (partner a) 1 := by rw [hn]
  set z₀ := n * x * n⁻¹ * x⁻¹ with hz₀
  set z₀' := n * x' * n⁻¹ * x'⁻¹ with hz₀'
  have hz₀M : (η z₀ : ModGL TwistTag.E6.tag K) = conjX σ r a c := by
    rw [hz₀, map_mul, Subgroup.coe_mul, coe_map_conj, hnM, hxM, map_inv, Subgroup.coe_inv, hxM,
      orbitX_shear, mul_inv_cancel_right]
  have hz₀'M : (η z₀' : ModGL TwistTag.E6.tag K) = conjX σ r a c' := by
    rw [hz₀', map_mul, Subgroup.coe_mul, coe_map_conj, hnM, hx'M, map_inv, Subgroup.coe_inv, hx'M,
      orbitX_shear, mul_inv_cancel_right]
  have hcommX : (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) *
      orbitX TwistTag.E6 K σ a c' = orbitX TwistTag.E6 K σ a c' * orbitX TwistTag.E6 K σ a c := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← orbitX_add, ← orbitX_add, add_comm]
  have hc₀ : ⁅x, x'⁆ ∈ η.ker := hker _ (by
    simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hxM,
      hx'M]
    rw [hcommX]
    group)
  have key : ⁅x, x'⁆ = ⁅x, x'⁆ * ⁅z₀, z₀'⁆ := by
    have e1 : n * ⁅x, x'⁆ * n⁻¹ = ⁅x, x'⁆ := by
      rw [(hcen _ hc₀ n).eq.symm, mul_inv_cancel_right]
    have e2 : n * ⁅x, x'⁆ * n⁻¹ = ⁅z₀ * x, z₀' * x'⁆ := by
      rw [hz₀, hz₀']
      simp only [commutatorElement_def]
      group
    calc ⁅x, x'⁆ = n * ⁅x, x'⁆ * n⁻¹ := e1.symm
      _ = ⁅z₀ * x, z₀' * x'⁆ := e2
      _ = ⁅x, x'⁆ * ⁅z₀, z₀'⁆ := commutator_shear (hlift x z₀' ⟨c, hxM⟩ ⟨c', hz₀'M⟩)
          (hlift x' z₀ ⟨c', hx'M⟩ ⟨c, hz₀M⟩) (hcen _ hc₀)
  have hz₀z₀' : Commute z₀ z₀' := by
    have h1 : ⁅z₀, z₀'⁆ = 1 := by
      have := key
      rwa [left_eq_mul] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hu : z₀⁻¹ * z ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hz₀M, hc, inv_mul_cancel])
  have hu' : z₀'⁻¹ * z' ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hz₀'M, hc', inv_mul_cancel])
  have h := commute_mul_central hz₀z₀' (hcen _ hu) (hcen _ hu')
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
  exact h.eq

theorem lift_commute_simple
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f)
    (a : Fin TwistTag.E6.foldedTag.rank) (y y' : E)
    (hy : ∃ c, (η y : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a c)
    (hy' : ∃ c, (η y' : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a c) :
    y * y' = y' * y := by
  obtain ⟨c, hc⟩ := hy
  obtain ⟨c', hc'⟩ := hy'
  set r := TwistTag.E6.orbitReflection (partner a)
  have hr : r ∈ relWeylTwist TwistTag.E6 := TwistTag.E6.orbitReflection_mem _
  obtain ⟨m, hm⟩ := hη ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K r,
    canonicalRep_mem_graphFixedRootGroup hr⟩
  have hmM : (η m : ModGL TwistTag.E6.tag K) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K r := by
    rw [hm]
  have hconj : ∀ (g : E) (d : orbitField TwistTag.E6 K σ a),
      (η g : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a d →
        ∃ e, (η (m * g * m⁻¹) : ModGL TwistTag.E6.tag K) = conjX σ r a e := fun g d hg =>
    ⟨d, by rw [coe_map_conj, hmM, hg, conjX]⟩
  have h := lift_commute_edge hη hC hf hk a (m * y * m⁻¹) (m * y' * m⁻¹) (hconj y c hc)
    (hconj y' c' hc')
  have h' := congrArg (fun g => m⁻¹ * g * m) h
  simp only [mul_assoc, inv_mul_cancel_left] at h'
  simpa [mul_assoc] using h'

theorem lift_commute_orbitGroup
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (y y' : E)
    (hy : (η y : ModGL TwistTag.E6.tag K) ∈ orbitGroup σ α)
    (hy' : (η y' : ModGL TwistTag.E6.tag K) ∈ orbitGroup σ α) :
    y * y' = y' * y := by
  obtain ⟨w, hw, a, hO⟩ := TwistTag.E6.exists_diagramOrbit_eq hα
  obtain ⟨c, hc⟩ := exists_conjX_eq hw hO hy
  obtain ⟨c', hc'⟩ := exists_conjX_eq hw hO hy'
  obtain ⟨m, hm⟩ := hη ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K w,
    canonicalRep_mem_graphFixedRootGroup hw⟩
  have hmM : (η m : ModGL TwistTag.E6.tag K) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w := by
    rw [hm]
  have hconj : ∀ (g : E) (d : orbitField TwistTag.E6 K σ a),
      conjX σ w a d = (η g : ModGL TwistTag.E6.tag K) →
        ∃ e, (η (m⁻¹ * g * m⁻¹⁻¹) : ModGL TwistTag.E6.tag K) = orbitX TwistTag.E6 K σ a e :=
    fun g d hg => ⟨d, by
      rw [coe_map_conj, map_inv, Subgroup.coe_inv, hmM, ← hg, conjX]
      group⟩
  have h := lift_commute_simple hη hC hf hk a (m⁻¹ * y * m⁻¹⁻¹) (m⁻¹ * y' * m⁻¹⁻¹)
    (hconj y c hc) (hconj y' c' hc')
  have h' := congrArg (fun g => m * g * m⁻¹) h
  simp only [inv_inv, mul_assoc, mul_inv_cancel_left] at h'
  simpa [mul_assoc] using h'

end CFSG.LieType.Chevalley.TwistedE6Cover
