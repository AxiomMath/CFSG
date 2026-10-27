module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] noncomputable def conjAut {X : Type} [Group X] (K : Subgroup X) (g : X)
    (hg : g ∈ normalizer (K : Set X)) : MulAut ↥K := by
  refine
    { toFun := fun k =>
        ⟨g * (k : X) * g⁻¹, (Subgroup.mem_set_normalizer_iff.mp hg (k : X)).mp k.2⟩
      invFun := fun k =>
        ⟨g⁻¹ * (k : X) * g,
          (Subgroup.mem_set_normalizer_iff''.mp hg (k : X)).mp k.2⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro k
    apply Subtype.ext
    group
  · intro k
    apply Subtype.ext
    group
  · intro a b
    apply Subtype.ext
    show g * ((a : X) * (b : X)) * g⁻¹ =
      (g * (a : X) * g⁻¹) * (g * (b : X) * g⁻¹)
    group

theorem coe_conjAut {X : Type} [Group X] (K : Subgroup X) {g : X}
    (hg : g ∈ normalizer (K : Set X)) (k : ↥K) :
    ((conjAut K g hg k : ↥K) : X) = g * (k : X) * g⁻¹ := by
  rfl

theorem conjAut_mul_self {X : Type} [Group X] (K : Subgroup X) {g : X}
    (hg : g ∈ normalizer (K : Set X)) (hg2 : g * g = 1) :
    conjAut K g hg * conjAut K g hg = 1 := by
  apply MulEquiv.ext
  intro k
  apply Subtype.ext
  rw [MulAut.mul_apply, MulAut.one_apply, coe_conjAut, coe_conjAut]
  have hkey : g * (g * (k : X) * g⁻¹) * g⁻¹ = (g * g) * (k : X) * (g * g)⁻¹ := by
    simp only [mul_assoc, mul_inv_rev]
  rw [hkey, hg2]
  simp

theorem card_fixedSubgroup_conjAut {X : Type} [Group X] (K : Subgroup X) {g : X}
    (hg : g ∈ normalizer (K : Set X)) :
    Nat.card (fixedSubgroup (conjAut K g hg)) = Nat.card ↥(K ⊓ centralizer ({g} : Set X)) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨(x.1 : X), ?_⟩
      invFun := fun y => ⟨⟨(y.1 : X), y.2.1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨x.1.2, ?_⟩
    change (x.1 : X) ∈ Subgroup.centralizer ({g} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : conjAut K g hg x.1 = x.1 := x.2
    have hco : g * (x.1 : X) * g⁻¹ = (x.1 : X) := by
      rw [← coe_conjAut K hg x.1, hx]
    exact (mul_inv_eq_iff_eq_mul.mp hco).symm
  · show conjAut K g hg (⟨(y.1 : X), y.2.1⟩ : ↥K) = ⟨(y.1 : X), y.2.1⟩
    apply Subtype.ext
    rw [coe_conjAut]
    have hc : (y.1 : X) * g = g * (y.1 : X) := by
      have hy : (y.1 : X) ∈ Subgroup.centralizer ({g} : Set X) := y.2.2
      rwa [Subgroup.mem_centralizer_singleton_iff] at hy
    exact mul_inv_eq_iff_eq_mul.mpr hc.symm
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    rfl

theorem conjAut_eq_conj_iff {X : Type} [Group X] (K : Subgroup X) {g : X}
    (hg : g ∈ normalizer (K : Set X)) (k : ↥K) :
    conjAut K g hg = MulAut.conj k ↔ ∀ l ∈ K, g * l * g⁻¹ = (k : X) * l * (k : X)⁻¹ := by
  constructor
  · intro h l hl
    have hk : conjAut K g hg ⟨l, hl⟩ = MulAut.conj k ⟨l, hl⟩ := by rw [h]
    have hval := congrArg (fun x : ↥K => (x : X)) hk
    rw [coe_conjAut, MulAut.conj_apply] at hval
    simpa using hval
  · intro h
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [coe_conjAut, MulAut.conj_apply]
    simpa using h l l.2

end CFSG.EvenSporadicStandard.Co3Std.CentT
