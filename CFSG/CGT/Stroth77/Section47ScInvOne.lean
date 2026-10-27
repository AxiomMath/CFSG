module

public import CFSG.CGT.Stroth77.Section47ScInv

public section

namespace CFSG.CGT.Stroth77

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}

theorem t200_mul_self_ne_c₁_of_eq_one (dD : StrothWeakTypeData D (.t200 m)) (hm : m = 1)
    {y : G} (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    y * y ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  subst hm
  obtain ⟨v, l, rfl⟩ := t200_mem_CSc₁ dD le_rfl hy
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [dD.nf_mul_self, dD.t200_c_pow, Bool.and_false, dD.d8_fff, mul_one]
  intro h
  have h0 := congrFun (dD.ofTorus_inj h) 0
  have hk := t200_one_le_k (m := 1) le_rfl 0
  have h2 : ((x 0 + x 0 : ℤ) : ZMod (2 ^ (StrothTypeIndex.t200 1).k 0)) = ((1 : ℤ) : ZMod _) := by
    cases l <;> simpa [SigmaFourAction.d8Act, Stroth34T200.t200_φu, om200_apply] using h0
  have he := (Stroth42Core.even_intCast_iff hk (x 0 + x 0)).2 ⟨x 0, rfl⟩
  rw [h2, Stroth42Core.even_intCast_iff hk] at he
  exact absurd he (by decide)

end Stroth47Core

variable {G : Type} [Group G] [Finite G]

theorem stroth_4_7_inv_conj_notMem_of_one_le :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧ ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      g⁻¹ * e * g ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  intro G _ _ F D m hm dD h hN hnc e he hS hrel g hg hmem
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have he_sq : e * e = (dD.c : G) ^ 2 ^ (m - 1) := by
      rcases hrel with hrel | hrel <;> exact hrel.e_sq
    have heC : e ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} :=
      Subgroup.mem_centralizer_singleton_iff.2 (by rw [← he_sq, mul_assoc])
    have hgc := Subgroup.mem_centralizer_singleton_iff.1 hg
    refine Stroth47Core.t200_mul_self_ne_c₁_of_eq_one dD (by omega)
      (Subgroup.mem_inf.2 ⟨hmem, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
        heC) hg⟩) ?_
    calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
      _ = g⁻¹ * (g * (dD.c : G) ^ 2 ^ (m - 1)) := by rw [he_sq, mul_assoc, ← hgc]
      _ = (dD.c : G) ^ 2 ^ (m - 1) := by group
  · exact stroth_4_7_inv_conj_notMem F hm2 dD h hN hnc e he hS hrel g hg hmem

end CFSG.CGT.Stroth77
