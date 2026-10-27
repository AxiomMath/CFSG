module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenFour
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyInn
public import CFSG.Sporadic.Bridge.LySurj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier
  CFSG.ComponentClassification.OuterAutomorphisms


theorem rowLy_holds : I301BRow .ly := by
  intro S _ _ hS B I K R0 R1 y _ hBe hBc hyB hy1 _ _ _ hR0y hR0 hR0c _ _ hKB hR1 hKB1 h01
  obtain ⟨i, hi, ⟨e₁⟩⟩ := hS
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  have eS : S ≃* NativeSporadic.Ly := e₁.trans (by exact b.symm)
  have e0 : S ≃* J := by exact eS.trans lyEquivJ
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun a : MulAut S => (a : S → S)) DFunLike.coe_injective
  have hOut : Nat.card (Outer S) ∣ 2 := (outer_order_divides_two ⟨eS⟩).1
  have hR0c' : Nat.card R0 = 32 := hR0c
  have hBe' : IsElemAbelian 3 B := hBe
  have hBc' : Nat.card B = 27 := hBc
  have hR0e : timmesfeldIsExtraspecial ↥R0 := hR0.resolve_right (by rw [hR0c']; norm_num)
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R0)).mp hR0e.2.2.2
  set z : MulAut S := ((c : ↥R0) : MulAut S) with hz
  have hzR0 : z ∈ R0 := (c : ↥R0).2
  have hzc : ∀ r ∈ R0, r * z = z * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨r, hr⟩)
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf c ∣ 2 := hR0e.2.2.2 ▸ orderOf_dvd_natCard c
    have h2 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf c = 2 := ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left h2
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, h3]
  have hcc : (c : ↥R0) ∈ commutator ↥R0 := by
    rw [hR0e.2.1, hR0e.2.2.1]
    exact c.2
  obtain ⟨θ, hθ, hθz⟩ := LyA11.exists_hom_central e0 hOut hcc hz2
  have hBN0 : B ≤ Subgroup.normalizer (R0 : Set (MulAut S)) := le_sup_right.trans hKB
  have hBN1 : B ≤ Subgroup.normalizer (R1 : Set (MulAut S)) := le_sup_right.trans hKB1
  have hN1c : 64 ≤ Nat.card (R1 ⊓ Subgroup.normalizer (R0 : Set (MulAut S)) : Subgroup _) := by
    have := LyA11.two_mul_card_le_normalizer_inf hR1 h01
    omega
  have hH : ∀ g ∈ Subgroup.normalizer (R0 : Set (MulAut S)), g ∈ autZ.comap θ := by
    intro g hg
    refine LyA11.mem_autZ_of_commute ?_
    have h := congrArg θ (comm_of_mem_normalizer hR0e hzR0 hzc hz1 hg)
    rwa [map_mul, map_mul, hθz] at h
  haveI := hBe'.1
  exact (LyA11.false_of_restriction (LyA11.autZPermOf θ) (LyA11.card_ker_autZPermOf_le hθ)
    (B := B) (N := R1 ⊓ Subgroup.normalizer (R0 : Set (MulAut S)))
    (fun g hg => hH g (hBN0 hg)) (fun g hg => hH g hg.2)
    (fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)) hBe'.2 hBc'
    (hR1.to_inf_left) hN1c
    (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hBN1 hg, Subgroup.le_normalizer (hBN0 hg)⟩)).elim

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
