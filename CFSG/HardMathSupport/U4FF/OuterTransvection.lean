module

public import CFSG.HardMathSupport.U4FF.Outer
public import CFSG.HardMathSupport.U4FF.OuterModel
public import CFSG.HardMathSupport.U4FF.Disp

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin

variable {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)] {n : ℕ}
  {L A : Subgroup (MulAut S)}

theorem exists_small_involution (hL : IsU4Group n L) (hA : IsElemAbelian2 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) (hirr : IsIrrOn (L ⊔ A))
    {σ : MulAut S} (hσA : σ ∈ A) (hσL : σ ∉ L) :
    ∃ t ∈ L, t ≠ 1 ∧ t * t = 1 ∧ disp t ≤ 2 * disp σ := by
  classical
  have hS : ∀ s : S, s * s = 1 := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  haveI : CharP K 2 := h.charP
  have hC := sup_inf_centralizer_eq_bot hS hL hA hAN hirr
  set x : Subgroup.normalizer (L : Set (MulAut S)) := ⟨σ, hAN hσA⟩ with hx
  have hσ2 : σ * σ = 1 := by simpa [sq] using hA.2 σ hσA
  have hα2 : miyamotoAct h L η x * miyamotoAct h L η x = 1 := by
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext hσ2
    rw [this, map_one]
  have hα1 : miyamotoAct h L η x ≠ 1 := by
    intro he
    have hcent := (miyamotoAct_eq_one_iff h L η x).1 he
    have : σ ∈ (L ⊔ A) ⊓ Subgroup.centralizer (L : Set (MulAut S)) :=
      ⟨Subgroup.mem_sup_right hσA, hcent⟩
    rw [hC, Subgroup.mem_bot] at this
    exact hσL (this ▸ L.one_mem)
  have hord : orderOf (miyamotoAct h L η x) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hff : miyamotoFieldFactor h (miyamotoAct h L η x) ≠ 1 := fun he =>
    hσL (mem_of_fieldFactor_eq_one hS hL hA hAN hirr h η hσA he)
  obtain ⟨g, hgne, hgsq⟩ := exists_displaced_involution h hord hff
  set ĝ : L := η.symm g with hĝ
  have hrel : ((η.symm (miyamotoAct h L η x g) : L) : MulAut S) = σ * (ĝ : MulAut S) * σ⁻¹ :=
    coe_symm_miyamotoAct_apply h L η x g
  set τ : L := η.symm (miyamotoAct h L η x g * g⁻¹) with hτ
  have hτcoe : (τ : MulAut S) = σ * (ĝ : MulAut S) * σ⁻¹ * (ĝ : MulAut S)⁻¹ := by
    rw [hτ, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hrel]
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  refine ⟨(τ : MulAut S), τ.2, ?_, ?_, ?_⟩
  · intro h1
    have h2 : τ = 1 := Subtype.ext h1
    have h3 : miyamotoAct h L η x g * g⁻¹ = 1 := η.symm.injective (by rw [← hτ, h2, map_one])
    exact hgne (mul_inv_eq_one.mp h3)
  · have h2 : τ * τ = 1 := by
      rw [hτ, ← map_mul, hgsq, map_one]
    have := congrArg Subtype.val h2
    simpa using this
  · rw [hτcoe, hσinv]
    have e : σ * (ĝ : MulAut S) * σ * (ĝ : MulAut S)⁻¹ =
        σ * ((ĝ : MulAut S) * σ * (ĝ : MulAut S)⁻¹) := by group
    rw [e]
    calc disp (σ * ((ĝ : MulAut S) * σ * (ĝ : MulAut S)⁻¹))
        ≤ disp ((ĝ : MulAut S) * σ * (ĝ : MulAut S)⁻¹) + disp σ := disp_mul_le _ _
      _ = disp σ + disp σ := by rw [disp_conj]
      _ = 2 * disp σ := by ring

end CFSG.HardMathSupport.U4FF
