module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FK

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem sec4F_T1_cases {P : Subgroup G} {x : G} (hx : x ∈ normalizer (P : Set G))
    (hx2 : x * x ∈ P) {g : G} (hg : g ∈ P ⊔ zpowers x) : g ∈ P ∨ ∃ p ∈ P, g = x * p := by
  have hxinv : ∀ q ∈ P, x⁻¹ * q * x ∈ P := by
    intro q hq
    exact (Subgroup.mem_set_normalizer_iff.mp hx (x⁻¹ * q * x)).mpr
      (by rwa [show x * (x⁻¹ * q * x) * x⁻¹ = q by group])
  let S' : Subgroup G :=
    { carrier := {g | g ∈ P ∨ ∃ p ∈ P, g = x * p}
      mul_mem' := by
        rintro a b (ha | ⟨p, hp, rfl⟩) (hb | ⟨q, hq, rfl⟩)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr ⟨x⁻¹ * a * x * q, mul_mem (hxinv a ha) hq, by group⟩
        · exact Or.inr ⟨p * b, mul_mem hp hb, by group⟩
        · exact Or.inl (by
            rw [show (x * p) * (x * q) = (x * x) * (x⁻¹ * p * x * q) by group]
            exact mul_mem hx2 (mul_mem (hxinv p hp) hq))
      one_mem' := Or.inl P.one_mem
      inv_mem' := by
        rintro a (ha | ⟨p, hp, rfl⟩)
        · exact Or.inl (inv_mem ha)
        · exact Or.inr ⟨(x⁻¹ * p⁻¹ * x) * (x * x)⁻¹,
            mul_mem (hxinv p⁻¹ (inv_mem hp)) (inv_mem hx2), by group⟩ }
  have hle : P ⊔ zpowers x ≤ S' :=
    sup_le (fun q hq => Or.inl hq)
      (Subgroup.zpowers_le.mpr (Or.inr ⟨1, P.one_mem, by group⟩))
  exact hle hg

theorem Sec4FSetup.T1_conj_mem (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hyT : y ∈ P ⊔ zpowers x) : y ∈ P := by
  rcases sec4F_T1_cases hT.xP hT.x2 hyT with hyP | ⟨p, hp, hyp⟩
  · exact hyP
  · exact (h.K hT hp (by
      rcases hy with ⟨k, hk⟩
      exact ⟨k, by rw [← hyp]; exact hk⟩)).elim

theorem Sec4FSetup.conjA_le_P (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {g : G}
    (hg : CFSG.conjugate A g ≤ P ⊔ zpowers x) : CFSG.conjugate A g ≤ P := by
  have hA' : CFSG.conjugate A g =
      Subgroup.closure (Set.range (fun c : Option (Fin 7) => g⁻¹ * sec4MPt t φ c * g)) := by
    have hfun : (fun x : Option (Fin 7) =>
          (MulAut.conj g⁻¹).toMonoidHom (sec4MPt t φ x)) =
        (fun c : Option (Fin 7) => g⁻¹ * sec4MPt t φ c * g) := by
      funext c
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [h.A_eq_closure, CFSG.conjugate, MonoidHom.map_closure, ← Set.range_comp', hfun]
  rw [hA']
  refine (Subgroup.closure_le P).mpr ?_
  rintro e ⟨c, rfl⟩
  change g⁻¹ * sec4MPt t φ c * g ∈ P
  refine h.T1_conj_mem hT ?_ ?_
  · obtain ⟨k, hk⟩ := (conj_iff_mem_conjClassIn_top (t := t)).mpr (h.pt_mem_conj c)
    exact ⟨k * g, by rw [hk]; group⟩
  · exact hg (by rw [hA']; exact Subgroup.subset_closure ⟨c, rfl⟩)

end CFSG.OddStandard.SmallF3.Omega
