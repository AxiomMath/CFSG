module

public import CFSG.GF2Type.Smith1979.W4InspDefs
public import CFSG.GF2Type.Smith1979.W4InspSymOrth
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LargeExtraspecial.S12InspFamSmall

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem perm_five_no_independent_triple : ∀ a : Equiv.Perm (Fin 5), a * a = 1 → a ≠ 1 →
    ∀ b : Equiv.Perm (Fin 5), b * b = 1 → b ≠ a → b ≠ 1 → a * b = b * a →
    ∀ c : Equiv.Perm (Fin 5), c * c = 1 → c ≠ 1 → c ≠ a → c ≠ b → c ≠ a * b →
      a * c = c * a → b * c = c * b → False := by
  decide +kernel

theorem card_le_four_of_isElemAbelian_perm_five (E : Subgroup (Equiv.Perm (Fin 5)))
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  have : Fintype E := Fintype.ofFinite E
  have hcard : 4 < Fintype.card E := by
    rw [Fintype.card_eq_nat_card]
    exact hlt
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset E)) (t := Finset.univ)
    (by rw [Finset.card_singleton, Finset.card_univ]; omega)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset E)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega))
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a, b, a * b} : Finset E)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_four (by rw [Finset.card_univ]; omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb hc
  have hcom : ∀ x y : E, (x : Equiv.Perm (Fin 5)) * y = y * x := fun x y => hE.comm x.2 y.2
  have hsq : ∀ x : E, (x : Equiv.Perm (Fin 5)) * x = 1 := fun x => hE.mul_self_eq_one x.2
  exact perm_five_no_independent_triple a (hsq a) (fun h => ha (Subtype.ext h)) b (hsq b)
    (fun h => hb.2 (Subtype.ext h)) (fun h => hb.1 (Subtype.ext h)) (hcom a b) c (hsq c)
    (fun h => hc.1 (Subtype.ext h)) (fun h => hc.2.1 (Subtype.ext h))
    (fun h => hc.2.2.1 (Subtype.ext h)) (fun h => hc.2.2.2 (Subtype.ext h)) (hcom a c) (hcom b c)

theorem card_outer_eq_one_of_perm {X : Type} [Group X] {m : ℕ} (hm : m = 3 ∨ m = 5)
    (φ : X ≃* Equiv.Perm (Fin m)) : Nat.card (Outer X) = 1 := by
  rw [Nat.card_congr (equivalence φ).toEquiv]
  refine S12Insp5.card_outer_eq_one_of_inner fun ψ => ?_
  rcases hm with rfl | rfl
  · obtain ⟨c, hc⟩ := CFSG.Quasithin.G11.G118.g118_perm_three_aut_inner ψ
    exact ⟨c, MulEquiv.ext fun x => (hc x).trans (MulAut.conj_apply c x).symm⟩
  · obtain ⟨c, hc⟩ := CFSG.Monster.B.TwoA.sym5_conj_surjective ψ
    exact ⟨c, hc.symm⟩

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

omit [IsSimpleGroup G] in
theorem false_of_sym3 (hc : Ctx S g t) (φ : S.Xbar12 g ≃* Equiv.Perm (Fin 3)) : False := by
  have hO := card_outer_eq_one_of_perm (Or.inl rfl) φ
  have h1 : Nat.card (S.Lbar g) ∣ Nat.card S.Mbar := card_dvd_of_le (S.Lbar_le_Mbar g)
  have h2 := Setting.card_Mbar_dvd_card_Xbar12_mul_card_outer hc.hS
  rw [hO, S12Insp5.card_eq_factorial_of_perm φ] at h2
  have h3 := S.card_Lbar_ge hc.haQ hc.hne
  rw [hc.hw] at h3
  have h4 := Nat.le_of_dvd (by norm_num) (h1.trans h2)
  norm_num at h3 h4
  omega

omit [IsSimpleGroup G] in
theorem false_of_sym5 (hc : Ctx S g t) (φ : S.Xbar12 g ≃* Equiv.Perm (Fin 5)) : False := by
  have hO := card_outer_eq_one_of_perm (Or.inr rfl) φ
  have h1 := Setting.card_Lbar_le_mul_card_outer (g := g) hc.hS
  have h2 := Setting.card_inf_Lbar_le_of_forall (S := S) (g := g) hc.haQ (r := 2)
    fun E hE => by
      have h := card_le_four_of_isElemAbelian_perm_five _ (hE.map φ.toMonoidHom)
      rwa [Subgroup.card_map_of_injective φ.injective] at h
  have h3 := S.card_Lbar_ge hc.haQ hc.hne
  rw [hc.hw] at h3
  rw [hO] at h1
  norm_num at h3
  omega

open CFSG.Open Matrix in
omit [IsSimpleGroup G] in
theorem false_of_orth2 (hc : Ctx S g t)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_perm_five_of_orth hnd hmin hmod
  exact false_of_sym5 hc φ

end CFSG.GF2Type.Smith1979.W4Insp
