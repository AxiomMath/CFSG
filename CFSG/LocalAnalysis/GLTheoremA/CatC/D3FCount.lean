module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FAlg
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Lang.D4Three.UnitLayers
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FCoord

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E27Lie

variable {K : Type} [Field K] [Finite K]


theorem d4_card_posRoots :
    {α : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 α ∧ 0 < height α}.ncard = 12 := by
  have h : {α : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 α ∧ 0 < height α} = ↑(d4RootsFrom 1) := by
    ext α
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_d4RootsFrom]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
  rw [h, Set.ncard_coe_finset]
  decide +kernel

@[expose] def layerImage (A : Subgroup ↥(adjointGroup Tag.D4 K)) (k : ℕ) :
    Set (UnitCoord Tag.D4 K k) :=
  {q | ∃ x : unitN Tag.D4 K k, (x : ↥(adjointGroup Tag.D4 K)) ∈ A ∧ unitPhi Tag.D4 K k x = q}

theorem unitPhi_eq_one_iff (k : ℕ) (x : unitN Tag.D4 K k) :
    unitPhi Tag.D4 K k x = 1 ↔ (x : ↥(adjointGroup Tag.D4 K)) ∈ unitN Tag.D4 K (k + 1) :=
  ⟨fun h => unitPhi_ker Tag.D4 x h, fun h => unitPhi_triv Tag.D4 x h⟩

theorem layerImage_fixed {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hfix : ∀ a ∈ A, α a = a) (k : ℕ) {q : UnitCoord Tag.D4 K k} (hq : q ∈ layerImage A k) :
    la.tau k q = q := by
  obtain ⟨x, hxA, rfl⟩ := hq
  have h := la.act k x
  have hx : α (x : ↥(adjointGroup Tag.D4 K)) = x := hfix _ hxA
  have e : (⟨α x, la.stable k x x.2⟩ : unitN Tag.D4 K k) = x := Subtype.ext hx
  rw [e] at h
  exact h.symm

theorem card_pow_le_of_sigma_ne_one {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1) (hσ : σ ≠ 1) (la : LayerAct Tag.D4 α σ)
    (A : Subgroup ↥(adjointGroup Tag.D4 K)) (hA0 : A ≤ unitN Tag.D4 K 0)
    (hfix : ∀ a ∈ A, α a = a) : Nat.card A ^ 3 ≤ Nat.card K ^ 12 := by
  classical
  have hlayer : ∀ k, Nat.card (layerImage A k) ^ 3 ≤
      Nat.card K ^ Nat.card (UnitRoots Tag.D4 k) := by
    intro k
    haveI : Fintype (UnitRoots Tag.D4 k) := Fintype.ofFinite _
    let τ : (UnitRoots Tag.D4 k → K) →+ (UnitRoots Tag.D4 k → K) :=
      monoTauAdd (la.r k) (la.f k) σ
    have hτ : ∀ (c : K) (a : UnitRoots Tag.D4 k → K), τ (c • a) = σ c • τ a := by
      intro c a
      ext j
      simp only [τ, monoTauAdd_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    have hinj : Nat.card (layerImage A k) ≤ Nat.card {a : UnitRoots Tag.D4 k → K // τ a = a} := by
      refine Nat.card_le_card_of_injective
        (fun q => ⟨Multiplicative.toAdd q.1, ?_⟩) ?_
      · have h := layerImage_fixed la hfix k q.2
        have h' := congrArg Multiplicative.toAdd h
        exact h'
      · intro a b h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Multiplicative.toAdd.injective h')
    calc Nat.card (layerImage A k) ^ 3 ≤ Nat.card {a : UnitRoots Tag.D4 k → K // τ a = a} ^ 3 :=
          Nat.pow_le_pow_left hinj 3
      _ ≤ Nat.card K ^ Fintype.card (UnitRoots Tag.D4 k) := card_fixed_pow_le σ hσ3 hσ τ hτ
      _ = Nat.card K ^ Nat.card (UnitRoots Tag.D4 k) := by
        rw [Nat.card_eq_fintype_card (α := UnitRoots Tag.D4 k)]
  set d := (maxHeight Tag.D4).toNat with hd
  have hprod := card_le_prod_of_filtration (unitN Tag.D4 K) (unitPhi Tag.D4 K) d
    (unitN_bot Tag.D4) (unitN_chain Tag.D4) (unitPhi_eq_one_iff) A hA0
    (fun k => Nat.card (layerImage A k)) (fun k _ => le_rfl)
  have hsum : ∑ k ∈ Finset.range d, Nat.card (UnitRoots Tag.D4 k) ≤ 12 := by
    have := sum_card_unitRoots_le (τ := Tag.D4) d
    rwa [d4_card_posRoots] at this
  have hqpos : 0 < Nat.card K := Nat.card_pos
  calc Nat.card A ^ 3 ≤ (∏ k ∈ Finset.range d, Nat.card (layerImage A k)) ^ 3 :=
        Nat.pow_le_pow_left hprod 3
    _ = ∏ k ∈ Finset.range d, Nat.card (layerImage A k) ^ 3 := (Finset.prod_pow _ _ _).symm
    _ ≤ ∏ k ∈ Finset.range d, Nat.card K ^ Nat.card (UnitRoots Tag.D4 k) :=
        Finset.prod_le_prod' fun k _ => hlayer k
    _ = Nat.card K ^ ∑ k ∈ Finset.range d, Nat.card (UnitRoots Tag.D4 k) :=
        Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ Nat.card K ^ 12 := Nat.pow_le_pow_right hqpos hsum

end CFSG.LocalAnalysis.GLTheoremA
