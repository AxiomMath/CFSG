module

public import CFSG.Certificates.Kernel.QTwoD6.Glue2

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K CFSG.StandardType.QTwoLin

@[expose] noncomputable def permG : Subgroup (V7 ≃ₗ[ZMod 3] V7) where
  carrier := {g | ∃ σ : Equiv.Perm (Fin 6), ∃ ε : (ZMod 3)ˣ,
    g e0 = (ε : ZMod 3) • e0 ∧ ∀ j, g (ub j.succ) = ub (σ j).succ}
  one_mem' := ⟨1, 1, by simp, fun j => by simp⟩
  mul_mem' := by
    rintro a b ⟨σ, ε, ha0, ha⟩ ⟨τ, δ, hb0, hb⟩
    refine ⟨σ * τ, δ * ε, ?_, fun j => ?_⟩
    · rw [LinearEquiv.mul_apply, hb0, map_smul, ha0, smul_smul, Units.val_mul]
    · rw [LinearEquiv.mul_apply, hb, ha]
      rfl
  inv_mem' := by
    rintro a ⟨σ, ε, ha0, ha⟩
    refine ⟨σ⁻¹, ε⁻¹, ?_, fun j => ?_⟩
    · apply a.injective
      change a (a.symm e0) = a (((ε⁻¹ : (ZMod 3)ˣ) : ZMod 3) • e0)
      rw [LinearEquiv.apply_symm_apply, map_smul, ha0, smul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    · apply a.injective
      change a (a.symm (ub j.succ)) = a (ub (σ⁻¹ j).succ)
      rw [LinearEquiv.apply_symm_apply, ha]
      simp

theorem permG_ext {g h : V7 ≃ₗ[ZMod 3] V7} {σ : Equiv.Perm (Fin 6)} {ε : (ZMod 3)ˣ}
    (hg0 : g e0 = (ε : ZMod 3) • e0) (hg : ∀ j, g (ub j.succ) = ub (σ j).succ)
    (hh0 : h e0 = (ε : ZMod 3) • e0) (hh : ∀ j, h (ub j.succ) = ub (σ j).succ) : g = h := by
  apply LinearEquiv.ext
  intro v
  have hub : ∀ j : Fin 7, g (ub j) = h (ub j) := by
    intro j
    induction j using Fin.cases with
    | zero => rw [ub_zero, hg0, hh0]
    | succ j => rw [hg, hh]
  rw [eq_sum_us_ub v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, hub]

theorem permG_finite_card : Finite permG ∧ Nat.card permG ≤ 1440 := by
  classical
  have hmem : ∀ g : permG, ∃ p : Equiv.Perm (Fin 6) × (ZMod 3)ˣ,
      (g : V7 ≃ₗ[ZMod 3] V7) e0 = (p.2 : ZMod 3) • e0 ∧
        ∀ j, (g : V7 ≃ₗ[ZMod 3] V7) (ub j.succ) = ub (p.1 j).succ := by
    rintro ⟨g, σ, ε, h0, h⟩
    exact ⟨(σ, ε), h0, h⟩
  let f : permG → Equiv.Perm (Fin 6) × (ZMod 3)ˣ := fun g => Classical.choose (hmem g)
  have hf : Function.Injective f := by
    intro g h hgh
    have hg := Classical.choose_spec (hmem g)
    have hh := Classical.choose_spec (hmem h)
    change f g = f h at hgh
    apply Subtype.ext
    refine permG_ext hg.1 hg.2 ?_ ?_
    · rw [hh.1]
      change (((f h).2 : (ZMod 3)ˣ) : ZMod 3) • e0 = (((f g).2 : (ZMod 3)ˣ) : ZMod 3) • e0
      rw [hgh]
    · intro j
      rw [hh.2 j]
      change ub ((f h).1 j).succ = ub ((f g).1 j).succ
      rw [hgh]
  have hfin : Finite permG := Finite.of_injective f hf
  refine ⟨hfin, ?_⟩
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Equiv.Perm (Fin 6) × (ZMod 3)ˣ) = 1440 := by
    have hu : Fintype.card (ZMod 3)ˣ = 2 := by decide +kernel
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin, hu]
    decide
  omega

theorem exists_refl_not_permG {Aℓ : Subgroup (V7 ≃ₗ[ZMod 3] V7)}
    (hgen : Aℓ = Subgroup.closure {g | g ∈ Aℓ ∧ IsReflLin g}) (hcard : 1440 < Nat.card Aℓ) :
    ∃ g ∈ Aℓ, IsReflLin g ∧ g ∉ permG := by
  by_contra h
  push Not at h
  have hle : Aℓ ≤ permG := by
    rw [hgen, Subgroup.closure_le]
    intro g hg
    exact h g hg.1 hg.2
  obtain ⟨hfin, hcd⟩ := permG_finite_card
  have := Subgroup.card_le_of_le hle
  omega

@[expose] def jPerm (j : Fin 6) : Equiv.Perm (Fin 6) :=
  ![Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 2 3, Equiv.swap 3 4, 1, Equiv.swap 4 5] j

theorem sAct_ub : ∀ j : Fin 6, j ≠ 4 → ∀ k : Fin 6, sAct j (ub k.succ) = ub (jPerm j k).succ := by
  decide +kernel

theorem sAct_e0 : ∀ j : Fin 6, sAct j e0 = e0 := by
  decide +kernel

theorem simpleD6_perm {j : Fin 6} (hj : j ≠ 4) :
    simpleD6 j e0 = e0 ∧ ∀ k, simpleD6 j (ub k.succ) = ub (jPerm j k).succ :=
  ⟨by rw [simpleD6_apply_eq, sAct_e0], fun k => by rw [simpleD6_apply_eq, sAct_ub j hj]⟩

theorem J6_le_permG : J6 ≤ permG := by
  rw [J6, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨h0, h⟩ := simpleD6_perm hj
  exact ⟨jPerm j, 1, by rw [h0, Units.val_one, one_smul], h⟩

@[expose] def cIdx (i : Fin 5) : Fin 6 := ![0, 1, 2, 3, 5] i

theorem cIdx_ne (i : Fin 5) : cIdx i ≠ 4 := by
  revert i
  decide

theorem jPerm_cIdx : ∀ i : Fin 5, jPerm (cIdx i) = Equiv.swap i.castSucc i.succ := by
  decide

theorem exists_J6_perm (σ : Equiv.Perm (Fin 6)) :
    ∃ g ∈ J6, g e0 = e0 ∧ ∀ k, g (ub k.succ) = ub (σ k).succ := by
  let M : Submonoid (Equiv.Perm (Fin 6)) :=
    { carrier := {σ | ∃ g ∈ J6, g e0 = e0 ∧ ∀ k, g (ub k.succ) = ub (σ k).succ}
      one_mem' := ⟨1, J6.one_mem, rfl, fun k => rfl⟩
      mul_mem' := by
        rintro σ τ ⟨g, hg, hg0, hgk⟩ ⟨h, hh, hh0, hhk⟩
        refine ⟨g * h, J6.mul_mem hg hh, ?_, fun k => ?_⟩
        · rw [LinearEquiv.mul_apply, hh0, hg0]
        · rw [LinearEquiv.mul_apply, hhk, hgk]
          rfl }
  have hgen : Set.range (fun i : Fin 5 => Equiv.swap i.castSucc i.succ) ⊆ M := by
    rintro _ ⟨i, rfl⟩
    have hmem : simpleD6 (cIdx i) ∈ J6 := Subgroup.subset_closure ⟨cIdx i, cIdx_ne i, rfl⟩
    obtain ⟨h0, h⟩ := simpleD6_perm (cIdx_ne i)
    refine ⟨simpleD6 (cIdx i), hmem, h0, fun k => ?_⟩
    rw [h, jPerm_cIdx]
  have htop := Equiv.Perm.mclosure_swap_castSucc_succ 5
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => Equiv.swap i.castSucc i.succ) := by
    rw [htop]
    exact Submonoid.mem_top σ
  exact (Submonoid.closure_le.mpr hgen) hσ

theorem decV_16128 : decV 16128 = wb := by
  decide +kernel

theorem decV_16129 : decV 16129 = e0 + wb := by
  decide +kernel

theorem decV_127 : decV 127 = e0 + (2 : ZMod 3) • wb := by
  decide +kernel

theorem eq_smul_decV_line {ℓ : V7} (hℓD : ℓ ∈ Dplane) (hℓ0 : ℓ ∉ Submodule.span (ZMod 3) {e0}) :
    ∃ y ∈ [16128, 16129, 127], ∃ μ : ZMod 3, μ ≠ 0 ∧ ℓ = μ • decV y := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hℓD
  have hb : b ≠ 0 := by
    rintro rfl
    apply hℓ0
    rw [zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hcase : ∀ a b : ZMod 3, b ≠ 0 → a = 0 ∨ a = b ∨ a = 2 * b := by decide
  have h4 : ∀ b : ZMod 3, 2 * b * 2 = b := by decide
  rcases hcase a b hb with rfl | rfl | rfl
  · exact ⟨16128, by simp, b, hb, by rw [decV_16128, zero_smul, zero_add]⟩
  · exact ⟨16129, by simp, a, hb, by rw [decV_16129, smul_add]⟩
  · refine ⟨127, by simp, 2 * b, mul_ne_zero (by decide) hb, ?_⟩
    rw [decV_127, smul_add, smul_smul, h4]

end CFSG.StandardType.QTwoD6.K

end
