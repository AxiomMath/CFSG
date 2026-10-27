module

public import CFSG.GH74.GLS.Stage4.HexCD4Gal
public import CFSG.GH74.GLS.Stage4.HexCD4Mu

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

theorem exists_p3 (D : HexData4 root F K) (Gl : GalData F K) (hθ : D.θ = Gl.θ)
    {β : K → G → F} (hβ : PairData D β) (hcard3 : Nat.card (root 3) = Nat.card K)
    (hND : ∀ u ∈ root 3, (∀ x ∈ root 1, ⁅x, u⁆ = 1) → u = 1) :
    ∃ p3 : K → G, (∀ a b, p3 (a + b) = p3 a * p3 b) ∧ (∀ a, p3 a ∈ root 3) ∧
      Function.Injective p3 ∧ (∀ u ∈ root 3, ∃ a, p3 a = u) ∧
      ∀ a s, β s (p3 a) = Gl.trF (a * s) := by
  classical
  have hfK := Gl.finiteK
  have hrep : ∀ u ∈ root 3, ∃ a : K, ∀ s, β s u = Gl.trF (a * s) := fun u hu =>
    Gl.dual_rep (fun s => β s u) (fun s s' => hβ.add_s s s' u hu)
      (fun c s => by rw [← hθ]; exact hβ.lin c s u hu)
  choose! m3 hm3 using hrep
  have hadd : ∀ u ∈ root 3, ∀ v ∈ root 3, m3 (u * v) = m3 u + m3 v := by
    intro u hu v hv
    apply Gl.eq_of_trF_eq
    intro s
    rw [← hm3 _ ((root 3).mul_mem hu hv), hβ.add_u s u hu v hv, hm3 u hu, hm3 v hv, add_mul,
      Gl.trF_add]
  have hinj : ∀ u ∈ root 3, ∀ u' ∈ root 3, m3 u = m3 u' → u = u' := by
    intro u hu u' hu' he
    have hv : u * u'⁻¹ ∈ root 3 := (root 3).mul_mem hu ((root 3).inv_mem hu')
    have h1 := hadd _ hv u' hu'
    rw [inv_mul_cancel_right] at h1
    have h0 : m3 (u * u'⁻¹) = 0 := by
      rw [he] at h1
      exact add_eq_right.1 h1.symm
    have hcomm : ∀ x ∈ root 1, ⁅x, u * u'⁻¹⁆ = 1 := by
      intro x hx
      obtain ⟨s, rfl⟩ := D.p1_surj x hx
      rw [hβ.r1 s _ hv, hm3 _ hv, h0, zero_mul, Gl.trF_zero,
        map_zero_of_add' D.p2_add]
    have := hND _ hv hcomm
    exact mul_inv_eq_one.1 this
  let f : ↥(root 3) → K := fun u => m3 u
  have hf : Function.Bijective f := by
    refine (Nat.bijective_iff_injective_and_card f).2 ⟨fun u u' h => ?_, hcard3⟩
    exact Subtype.ext (hinj _ u.2 _ u'.2 h)
  let eqv := Equiv.ofBijective f hf
  have key : ∀ a, m3 ((eqv.symm a : ↥(root 3)) : G) = a := fun a => eqv.apply_symm_apply a
  refine ⟨fun a => ((eqv.symm a : ↥(root 3)) : G), fun a b => ?_, fun a => (eqv.symm a).2, ?_, ?_,
    fun a s => ?_⟩
  · apply hinj _ (eqv.symm (a + b)).2 _ ((root 3).mul_mem (eqv.symm a).2 (eqv.symm b).2)
    rw [key, hadd _ (eqv.symm a).2 _ (eqv.symm b).2, key, key]
  · intro a b h
    have := congrArg m3 h
    rwa [key, key] at this
  · intro u hu
    refine ⟨m3 u, ?_⟩
    have : eqv.symm (eqv ⟨u, hu⟩) = ⟨u, hu⟩ := eqv.symm_apply_apply _
    exact congrArg Subtype.val this
  · rw [hm3 _ (eqv.symm a).2, key]

end CFSG.GH74.GLS.Stage4.Hex
