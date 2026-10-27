module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs

public section

namespace CFSG.KC.PairCount

variable {G V : Type*} [Group G] [Add V] [Fintype V] [DecidableEq V]

open Classical in
noncomputable def orb (op : G → V → V) (v : V) : Finset V :=
  Finset.univ.filter fun x => ∃ g, op g v = x

omit [Group G] [Add V] [DecidableEq V] in
theorem mem_orb {op : G → V → V} {v x : V} : x ∈ orb op v ↔ ∃ g, op g v = x := by
  classical
  unfold orb
  simp

section

set_option linter.unusedSectionVars false

variable {op : G → V → V} (hmul : ∀ g h x, op (g * h) x = op g (op h x)) (hone : ∀ x, op 1 x = x)
  (hadd : ∀ g x y, op g (x + y) = op g x + op g y) (h2 : ∀ a b : V, a + b + a = b)
  (hinj : ∀ a : V, Function.Injective (a + ·))
include hmul hone

theorem op_orb {v x : V} (g : G) (hx : x ∈ orb op v) : op g x ∈ orb op v := by
  obtain ⟨h, rfl⟩ := mem_orb.1 hx
  exact mem_orb.2 ⟨g * h, hmul g h v⟩

theorem op_inv (g : G) (x : V) : op g⁻¹ (op g x) = x := by
  rw [← hmul, inv_mul_cancel, hone]

theorem op_inv' (g : G) (x : V) : op g (op g⁻¹ x) = x := by
  rw [← hmul, mul_inv_cancel, hone]

include hadd

theorem count_eq (v w : V) (g : G) :
    ((orb op v).filter fun a => op g w + a ∈ orb op v).card =
      ((orb op v).filter fun a => w + a ∈ orb op v).card := by
  classical
  refine Finset.card_nbij' (fun a => op g⁻¹ a) (fun a => op g a) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    refine ⟨op_orb hmul hone _ ha.1, ?_⟩
    have := op_orb hmul hone g⁻¹ ha.2
    rwa [hadd, op_inv hmul hone] at this
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    refine ⟨op_orb hmul hone _ ha.1, ?_⟩
    rw [← hadd]
    exact op_orb hmul hone g ha.2
  · intro a _
    exact op_inv' hmul hone g a
  · intro a _
    exact op_inv hmul hone g a

theorem fibre_eq (v w : V) (g : G) :
    ((orb op w).filter fun x => x + op g v ∈ orb op v).card =
      ((orb op w).filter fun x => x + v ∈ orb op v).card := by
  classical
  refine Finset.card_nbij' (fun x => op g⁻¹ x) (fun x => op g x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    refine ⟨op_orb hmul hone _ hx.1, ?_⟩
    have := op_orb hmul hone g⁻¹ hx.2
    rwa [hadd, op_inv hmul hone] at this
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    refine ⟨op_orb hmul hone _ hx.1, ?_⟩
    rw [← hadd]
    exact op_orb hmul hone g hx.2
  · intro x _
    exact op_inv' hmul hone g x
  · intro x _
    exact op_inv hmul hone g x

include h2 hinj

theorem card_mul_le (v u : V) (hu : u ∈ orb op v) (H : Finset V)
    (hH : ∀ h ∈ H, ∃ k, op k v = v ∧ op k u = h) :
    (orb op v).card * H.card ≤
      (orb op (v + u)).card * ((orb op v).filter fun a => v + u + a ∈ orb op v).card := by
  classical
  set O := orb op v
  set W := orb op (v + u)
  let Q := (O ×ˢ W).filter fun p => p.2 + p.1 ∈ O
  have hQ1 : Q.card = ∑ a ∈ O, (W.filter fun x => x + a ∈ O).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  have hQ2 : Q.card = ∑ x ∈ W, (O.filter fun a => x + a ∈ O).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
  have hc : ∀ x ∈ W, (O.filter fun a => x + a ∈ O).card =
      (O.filter fun a => v + u + a ∈ O).card := by
    intro x hx
    obtain ⟨g, rfl⟩ := mem_orb.1 hx
    exact count_eq hmul hone hadd v (v + u) g
  have hf : ∀ a ∈ O, H.card ≤ (W.filter fun x => x + a ∈ O).card := by
    intro a ha
    obtain ⟨g, rfl⟩ := mem_orb.1 ha
    rw [fibre_eq hmul hone hadd v (v + u) g]
    have hsub : H.image (fun h => v + h) ⊆ W.filter fun x => x + v ∈ O := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨k, hkv, rfl⟩ := hH h hh
      rw [Finset.mem_filter]
      refine ⟨mem_orb.2 ⟨k, by rw [hadd, hkv]⟩, ?_⟩
      rw [h2]
      exact op_orb hmul hone k hu
    have hcard : (H.image fun h => v + h).card = H.card :=
      Finset.card_image_of_injective _ (hinj v)
    rw [← hcard]
    exact Finset.card_le_card hsub
  have h1 : O.card * H.card ≤ Q.card := by
    rw [hQ1]
    have := Finset.card_nsmul_le_sum O (fun a => (W.filter fun x => x + a ∈ O).card) H.card hf
    simpa [smul_eq_mul] using this
  have h3 : Q.card = W.card * (O.filter fun a => v + u + a ∈ O).card := by
    rw [hQ2, Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
  omega

end

end CFSG.KC.PairCount

end
