module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcFacts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcA6FactAux1
public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open Equiv

private theorem exists_fixed_involution {B : Type*} [Group B] [Fintype B]
    (heven : 2 ∣ Fintype.card B) (f : MulAut B) (hf : f * f = 1) :
    ∃ x : B, x ≠ 1 ∧ f x = x ∧ x * x = 1 := by
  classical
  have hinv : (Equiv.inv B) ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hinv
  have hcard : Fintype.card {x : B // x * x = 1} = (Equiv.inv B).supportᶜ.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [Equiv.Perm.mem_support, inv_eq_iff_mul_eq_one]
  have hT : 2 ∣ Fintype.card {x : B // x * x = 1} := by
    rw [hcard]
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.trans ((Nat.modEq_zero_iff_dvd).2 heven))
  let g : Perm {x : B // x * x = 1} :=
    Equiv.subtypeEquiv f.toEquiv fun a => by
      change a * a = 1 ↔ f a * f a = 1
      rw [← map_mul]
      exact ⟨fun h => by rw [h, map_one], fun h => f.injective (h.trans (map_one f).symm)⟩
  have hg : g ^ 2 ^ 1 = 1 := by
    ext x
    have hx := DFunLike.congr_fun hf x.1
    simpa [pow_two, g] using hx
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hT hg
    (a := ⟨1, mul_one 1⟩) (Subtype.ext (map_one f))
  exact ⟨b.1, fun h => hb1 (Subtype.ext h), congrArg Subtype.val hb, b.2⟩

private theorem a6_aut_eq_one (f α : MulAut (alternatingGroup (Fin 6))) (hf : f * f = 1)
    (hα : α * α * α = 1) (hfix : ∀ x, f x = x → α x = x) : α = 1 := by
  have hα3 : α ^ 3 ^ 1 = 1 := by
    rw [pow_one, pow_succ, pow_two]
    exact hα
  obtain ⟨σ, hσ⟩ := CFSG.ClassicalInvolution.Q3.TC.Thin.exists_conjNormal_six α ⟨1, hα3⟩
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
    (by norm_num)
  by_contra hne
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hne (by rw [← hσ, map_one])
  have hσ3 : σ * σ * σ = 1 := by
    apply hinj
    rw [map_mul, map_mul, map_one, hσ]
    exact hα
  have hcard : 2 ∣ Fintype.card (alternatingGroup (Fin 6)) := by
    rw [card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨x, hx1, hfx, hxx⟩ := exists_fixed_involution hcard f hf
  have hαx := hfix x hfx
  rw [← hσ] at hαx
  have hcomm : σ * (x : Perm (Fin 6)) = x * σ := by
    have h := congrArg Subtype.val hαx
    rw [MulAut.conjNormal_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  exact a6_order_three_not_commute_involution σ hσ3 hσ1 x (congrArg Subtype.val hxx)
    (fun h => hx1 (Subtype.ext h)) (Perm.mem_alternatingGroup.mp x.2) hcomm

theorem a6AutFact : A6AutFact := by
  intro B _ _ ⟨e⟩ f α hff _ hα3 _ hfix
  have hcore := a6_aut_eq_one (MulAut.congr e f) (MulAut.congr e α)
    (by rw [← map_mul, hff, map_one]) (by rw [← map_mul, ← map_mul, hα3, map_one]) ?_
  · exact (MulAut.congr e).injective (hcore.trans (map_one _).symm)
  · intro x hx
    change e (f (e.symm x)) = x at hx
    have h1 : f (e.symm x) = e.symm x := e.injective (by rw [hx, MulEquiv.apply_symm_apply])
    change e (α (e.symm x)) = x
    rw [hfix _ h1, MulEquiv.apply_symm_apply]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
