module

public import CFSG.LieType.Chevalley.RootWeightFiltrationSpace
public import CFSG.LieType.Chevalley.BorelStructure

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley RootWeightSpace
open scoped RealInnerProductSpace Pointwise

variable {τ : Tag} {K : Type*} [Field K]

@[expose] def LabelRaises (wt : Label τ → ℝ) (ε : ℝ) (T : Module.End K (RootModule τ K)) :
    Prop :=
  ∀ a b : Label τ, T (Finsupp.single b 1) a ≠ 0 → wt b + ε ≤ wt a

theorem mul_sub_one_expand {R : Type*} [Ring R] (x y : R) :
    x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by
  noncomm_ring

private theorem commutator_sub_one_expand {R : Type*} [Ring R] (x y : R) :
    x * y - y * x = (x - 1) * (y - 1) - (y - 1) * (x - 1) := by
  noncomm_ring
private theorem conjugate_sub_expand {R : Type*} [Ring R] (x y z : R)
    (hyz : y * z = 1) : y * x * z - x = (y * x - x * y) * z := by
  rw [sub_mul, mul_assoc x y z, hyz, mul_one]

namespace LabelRaises

variable {wt : Label τ → ℝ} {ε ε' : ℝ} {T T' : Module.End K (RootModule τ K)}

theorem zero : LabelRaises wt ε (0 : Module.End K (RootModule τ K)) := fun a b h => by
  simp at h

theorem mono (h : LabelRaises wt ε T) (hε : ε' ≤ ε) : LabelRaises wt ε' T := fun a b hab => by
  have := h a b hab
  linarith

theorem add (h : LabelRaises wt ε T) (h' : LabelRaises wt ε T') : LabelRaises wt ε (T + T') := by
  intro a b hab
  rw [LinearMap.add_apply, Finsupp.add_apply] at hab
  by_cases h0 : T (Finsupp.single b 1) a = 0
  · rw [h0, zero_add] at hab
    exact h' a b hab
  · exact h a b h0

theorem neg (h : LabelRaises wt ε T) : LabelRaises wt ε (-T) := by
  intro a b hab
  apply h a b
  simpa only [LinearMap.neg_apply, Finsupp.neg_apply, neg_ne_zero] using hab

theorem sub (h : LabelRaises wt ε T) (h' : LabelRaises wt ε T') :
    LabelRaises wt ε (T - T') := by
  intro a b hab
  rw [LinearMap.sub_apply, Finsupp.sub_apply] at hab
  by_cases h0 : T (Finsupp.single b 1) a = 0
  · rw [h0, zero_sub, neg_ne_zero] at hab
    exact h' a b hab
  · exact h a b h0


theorem mul (h : LabelRaises wt ε T) (h' : LabelRaises wt ε' T') :
    LabelRaises wt (ε + ε') (T * T') := by
  intro a b hab
  rw [Module.End.mul_apply, ← Finsupp.sum_single (T' (Finsupp.single b 1)), Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  have h1 := h a c (right_ne_zero_of_mul hc')
  have h2 := h' c b (Finsupp.mem_support_iff.mp hc)
  linarith

theorem of_diagonal (h : ∀ b, ∃ r : K, T (Finsupp.single b 1) = r • Finsupp.single b 1) :
    LabelRaises wt 0 T := by
  intro a b hab
  obtain ⟨r, hr⟩ := h b
  rw [hr, Finsupp.smul_apply, smul_eq_mul] at hab
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 (right_ne_zero_of_mul hab)
  rw [add_zero]

theorem one : LabelRaises wt 0 (1 : Module.End K (RootModule τ K)) :=
  of_diagonal fun b => ⟨1, by rw [one_smul, Module.End.one_apply]⟩

theorem mul_sub_one {x y : Module.End K (RootModule τ K)} (hε : 0 ≤ ε)
    (hx : LabelRaises wt ε (x - 1)) (hy : LabelRaises wt ε (y - 1)) :
    LabelRaises wt ε (x * y - 1) := by
  have e : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := mul_sub_one_expand x y
  rw [e]
  exact (((hx.mul hy).mono (by linarith)).add hx).add hy

theorem of_sub_one {x : Module.End K (RootModule τ K)} (hx : LabelRaises wt 0 (x - 1)) :
    LabelRaises wt 0 x := by
  have e : x - 1 + 1 = x := sub_add_cancel x 1
  have := hx.add one
  rwa [e] at this

theorem mul_commutator {x y : Module.End K (RootModule τ K)}
    (hx : LabelRaises wt ε (x - 1)) (hy : LabelRaises wt ε' (y - 1)) :
    LabelRaises wt (ε + ε') (x * y - y * x) := by
  rw [commutator_sub_one_expand x y]
  exact (hx.mul hy).sub (by simpa only [add_comm] using hy.mul hx)

theorem conjugate_sub {x y z : Module.End K (RootModule τ K)}
    (hx : LabelRaises wt ε (x - 1)) (hy : LabelRaises wt ε' (y - 1))
    (hz : LabelRaises wt 0 z) (hyz : y * z = 1) :
    LabelRaises wt (ε' + ε) (y * x * z - x) := by
  rw [conjugate_sub_expand x y z hyz]
  simpa only [add_zero] using (hy.mul_commutator hx).mul hz

theorem apply_eq_zero_of_lt (h : LabelRaises wt ε T) (a b : Label τ)
    (hab : wt a < wt b + ε) : T (Finsupp.single b 1) a = 0 := by
  by_contra hne
  exact (not_le_of_gt hab) (h a b hne)

end LabelRaises

variable (τ K) in
@[expose] def labelRaisingSubgroup (wt : Label τ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    Subgroup (ModGL τ K) where
  carrier := {u | LabelRaises wt ε ((u : Module.End K (RootModule τ K)) - 1) ∧
    LabelRaises wt ε ((↑u⁻¹ : Module.End K (RootModule τ K)) - 1)}
  one_mem' := by
    have e : (1 : Module.End K (RootModule τ K)) - 1 = 0 :=
      sub_self (1 : Module.End K (RootModule τ K))
    simp only [Set.mem_ofPred_eq, inv_one, Units.val_one]
    rw [e]
    exact ⟨LabelRaises.zero, LabelRaises.zero⟩
  mul_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, mul_inv_rev] at hu hv ⊢
    exact ⟨hu.1.mul_sub_one hε hv.1, hv.2.mul_sub_one hε hu.2⟩
  inv_mem' {u} hu := by
    simp only [Set.mem_ofPred_eq, inv_inv] at hu ⊢
    exact ⟨hu.2, hu.1⟩

theorem mem_labelRaisingSubgroup {wt : Label τ → ℝ} {ε : ℝ} {hε : 0 ≤ ε} {u : ModGL τ K} :
    u ∈ labelRaisingSubgroup τ K wt ε hε ↔
      LabelRaises wt ε ((u : Module.End K (RootModule τ K)) - 1) ∧
        LabelRaises wt ε ((↑u⁻¹ : Module.End K (RootModule τ K)) - 1) :=
  Iff.rfl

@[expose] def latticeGrade
    (m : RootWeightSpace τ) (b : Label τ) : ℝ :=
  ⟪ofLattice b.latticeWeight, m⟫

theorem labelRaises_pinnedX_sub_one
    {m : RootWeightSpace τ} {ε : ℝ} (hε : 0 ≤ ε)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hm : ε ≤ ⟪ofLattice α, m⟫) (c : K) :
    LabelRaises (latticeGrade m) ε ((pinnedX τ K α c : Module.End K (RootModule τ K)) - 1) := by
  intro a b hab
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, sub_ne_zero] at hab
  obtain ⟨k, hk, hab'⟩ := pinnedX_weight_shift hα c a b hab
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e : ofLattice (k • α) = (k : ℝ) • ofLattice α := by
    rw [Nat.cast_smul_eq_nsmul ℝ]
    exact map_nsmul ofLatticeHom k α
  simp only [latticeGrade, hab', ofLattice_add, e, inner_add_left, real_inner_smul_left]
  nlinarith

theorem posUnipotent_le_labelRaisingSubgroup
    {m : RootWeightSpace τ} {ε : ℝ} (hε : 0 ≤ ε)
    (hm : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → 0 < height α → ε ≤ ⟪ofLattice α, m⟫) :
    posUnipotent τ K ≤ labelRaisingSubgroup τ K (latticeGrade m) ε hε := by
  refine iSup₂_le fun α hα => fun g hg => ?_
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 (inv_mem hg)
  refine ⟨labelRaises_pinnedX_sub_one hε hα.1 (hm α hα.1 hα.2) c, ?_⟩
  rw [← hc']
  exact labelRaises_pinnedX_sub_one hε hα.1 (hm α hα.1 hα.2) c'

theorem torusGroup_le_labelRaisingSubgroup
    (wt : Label τ → ℝ) :
    torusGroup τ K ≤ labelRaisingSubgroup τ K wt 0 le_rfl := by
  have key : ∀ g ∈ (diagonalGroup : Subgroup (ModGL τ K)),
      LabelRaises wt 0 ((g : Module.End K (RootModule τ K)) - 1) := fun g hg =>
    LabelRaises.of_diagonal fun b => by
      obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hg b
      refine ⟨(c : K) - 1, ?_⟩
      rw [LinearMap.sub_apply, hc, Module.End.one_apply, sub_smul, one_smul]
  intro g hg
  have hg' := torusGroup_le_diagonalGroup hg
  exact ⟨key g hg', key g⁻¹ (inv_mem hg')⟩

theorem borelGroup_le_labelRaisingSubgroup
    {m : RootWeightSpace τ}
    (hm : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → 0 < height α → 0 ≤ ⟪ofLattice α, m⟫) :
    borelGroup τ K ≤ labelRaisingSubgroup τ K (latticeGrade m) 0 le_rfl :=
  sup_le (torusGroup_le_labelRaisingSubgroup _) (posUnipotent_le_labelRaisingSubgroup le_rfl hm)

theorem map_supported_le_of_entries (T : Module.End K (RootModule τ K)) {S S' : Set (Label τ)}
    (h : ∀ a b, b ∈ S → T (Finsupp.single b 1) a ≠ 0 → a ∈ S') :
    (Finsupp.supported K K S).map T ≤ Finsupp.supported K K S' := by
  rw [Finsupp.supported_eq_span_single, Submodule.map_span_le]
  rintro _ ⟨b, hb, rfl⟩
  rw [Finsupp.mem_supported]
  intro a ha
  exact h a b hb (Finsupp.mem_support_iff.1 ha)

theorem mapsWeights_list_prod_weylElt
    (ω : List (Fin τ.rank)) :
    MapsWeights (((ω.map fun i => weylElt τ K i 1).prod : ModGL τ K) :
        Module.End K (RootModule τ K)) (((coxeterSystem τ).wordProd ω) • ·) ∧
      MapsWeights ((↑((ω.map fun i => weylElt τ K i 1).prod)⁻¹ :
        Module.End K (RootModule τ K))) (((coxeterSystem τ).wordProd ω)⁻¹ • ·) := by
  induction ω with
  | nil =>
    simp only [List.map_nil, List.prod_nil, inv_one, Units.val_one, CoxeterSystem.wordProd_nil]
    exact ⟨MapsWeights.one.congr fun μ => (one_smul _ μ).symm,
      MapsWeights.one.congr fun μ => (one_smul _ μ).symm⟩
  | cons i ω ih =>
    have hn := mapsWeights_weylElt (R := K) i 1
    have hn' : MapsWeights ((↑(weylElt τ K i 1)⁻¹ : Module.End K (RootModule τ K)))
        (reflect τ i) := by
      rw [weylElt_inv]
      exact mapsWeights_weylElt i (-1)
    simp only [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul,
      CoxeterSystem.wordProd_cons]
    refine ⟨(hn.mul ih.1).congr fun μ => ?_, (ih.2.mul hn').congr fun μ => ?_⟩
    · rw [Function.comp_apply, mul_smul, simple_smul]
    · rw [Function.comp_apply, mul_smul, CoxeterSystem.inv_simple, simple_smul]

theorem mapsWeights_canonicalRep
    (w : WeylGroup τ) :
    MapsWeights (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) (w • ·) ∧
      MapsWeights ((↑(canonicalRep (coxeterSystem τ) K w)⁻¹ : Module.End K (RootModule τ K)))
        (w⁻¹ • ·) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact mapsWeights_list_prod_weylElt ω

theorem mem_subgroup_mul_singleton_mul_iff {G : Type*} [Group G] {B : Subgroup G} {n x : G} :
    x ∈ (B : Set G) * {n} * (B : Set G) ↔ ∃ b ∈ B, ∃ b' ∈ B, b * n * b' = x := by
  simp only [Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

end CFSG.LieType.Chevalley
