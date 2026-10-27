module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.QuasithinUnique

open Module

namespace SteinbergBQ.DeletedModule

variable {m : ℕ}

@[expose] def pairVec (i j : Fin m) : Fin m → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem pairVec_apply (i j p : Fin m) :
    pairVec i j p = (if p = i then 1 else 0) + (if p = j then 1 else 0) := by
  simp [pairVec, Pi.single_apply]

theorem sum_pairVec (i j : Fin m) : ∑ p, pairVec i j p = 0 := by
  simp only [pairVec_apply, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  decide

theorem pairVec_self (i : Fin m) : pairVec i i = 0 := by
  funext p
  rw [pairVec_apply, Pi.zero_apply]
  split_ifs <;> decide

theorem pairVec_apply_left {i j : Fin m} (hij : i ≠ j) : pairVec i j i = 1 := by
  rw [pairVec_apply, ite_eq_left rfl, ite_eq_right hij, add_zero]

theorem pairVec_ne_zero {i j : Fin m} (hij : i ≠ j) : pairVec i j ≠ 0 := by
  intro h
  have h1 := pairVec_apply_left hij
  rw [h, Pi.zero_apply] at h1
  exact absurd h1 (by decide)

variable {Δ : Submodule (ZMod 2) (Fin m → ZMod 2)}

theorem pairVec_mem (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (i j : Fin m) : pairVec i j ∈ Δ :=
  (hΔ _).2 (sum_pairVec i j)

theorem eq_sum_pairVec (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (i₀ : Fin m) (x : Δ) :
    x = ∑ i, (x : Fin m → ZMod 2) i • (⟨pairVec i i₀, pairVec_mem hΔ i i₀⟩ : Δ) := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext p
  simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pairVec_apply,
    mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have h1 := (hΔ x).1 x.2
  have h2 : (∑ i, if p = i₀ then (x : Fin m → ZMod 2) i else 0) = 0 := by
    split_ifs
    · exact h1
    · simp
  rw [h2, add_zero]

theorem eq_of_forall_pairVec (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (hm : 0 < m)
    {f g : Δ →ₗ[ZMod 2] Δ}
    (hfg : ∀ i j, f ⟨pairVec i j, pairVec_mem hΔ i j⟩ = g ⟨pairVec i j, pairVec_mem hΔ i j⟩) :
    f = g := by
  ext1 x
  rw [eq_sum_pairVec hΔ ⟨0, hm⟩ x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, hfg]

variable {ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) Δ}

theorem rho_pairVec
    (hρ : ∀ σ (x : Δ) i, (((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x :
      Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i))
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    ((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ)
      ⟨pairVec i j, pairVec_mem hΔ i j⟩ = ⟨pairVec (σ i) (σ j), pairVec_mem hΔ _ _⟩ := by
  apply Subtype.ext
  funext p
  rw [hρ]
  simp only [pairVec_apply, Equiv.Perm.inv_eq_iff_eq]

theorem rho_swap_sub
    (hρ : ∀ σ (x : Δ) i, (((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x :
      Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i))
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) {a b : Fin m} (hab : a ≠ b) (x : Δ) :
    ((ρ (Equiv.swap a b) : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x - x =
      ((x : Fin m → ZMod 2) a + (x : Fin m → ZMod 2) b) •
        (⟨pairVec a b, pairVec_mem hΔ a b⟩ : Δ) := by
  apply Subtype.ext
  funext p
  have hcoe : ((⟨pairVec a b, pairVec_mem hΔ a b⟩ : Δ) : Fin m → ZMod 2) = pairVec a b := rfl
  rw [Submodule.coe_sub, Pi.sub_apply, hρ, Equiv.swap_inv, Submodule.coe_smul, Pi.smul_apply,
    hcoe, pairVec_apply, smul_eq_mul, CharTwo.sub_eq_add]
  by_cases hpa : p = a
  · subst hpa
    rw [Equiv.swap_apply_left, ite_eq_left rfl, ite_eq_right hab, add_zero, mul_one, add_comm]
  · by_cases hpb : p = b
    · subst hpb
      rw [Equiv.swap_apply_right, ite_eq_right hpa, ite_eq_left rfl, zero_add, mul_one]
    · rw [Equiv.swap_apply_of_ne_of_ne hpa hpb, ite_eq_right hpa, ite_eq_right hpb, add_zero,
        mul_zero, CharTwo.add_self_eq_zero]

theorem fixes_pairVec_of_commute
    (hρ : ∀ σ (x : Δ) i, (((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x :
      Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i))
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (hm : 3 ≤ m) {h : LinearMap.GeneralLinearGroup (ZMod 2) Δ}
    (hc : ∀ σ, h * ρ σ = ρ σ * h) (a b : Fin m) :
    (h : Δ →ₗ[ZMod 2] Δ) ⟨pairVec a b, pairVec_mem hΔ a b⟩ =
      ⟨pairVec a b, pairVec_mem hΔ a b⟩ := by
  classical
  by_cases hab : a = b
  · subst hab
    have h0 : (⟨pairVec a a, pairVec_mem hΔ a a⟩ : Δ) = 0 := Subtype.ext (pairVec_self a)
    rw [h0, map_zero]
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin m, c ≠ a ∧ c ≠ b := by
    by_contra h1
    push Not at h1
    have h2 : (Finset.univ : Finset (Fin m)) ⊆ {a, b} := fun c _ => by
      by_cases hca : c = a
      · simp [hca]
      · simp [h1 c hca]
    have h3 := Finset.card_le_card h2
    rw [Finset.card_univ, Fintype.card_fin] at h3
    have h4 := Finset.card_le_two (a := a) (b := b)
    omega
  set τ := Equiv.swap a b
  set x : Δ := ⟨pairVec a c, pairVec_mem hΔ a c⟩
  have hx : ((ρ τ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x - x =
      ⟨pairVec a b, pairVec_mem hΔ a b⟩ := by
    rw [rho_swap_sub hρ hΔ hab]
    have h1 : (x : Fin m → ZMod 2) a = 1 := pairVec_apply_left (Ne.symm hca)
    have h2 : (x : Fin m → ZMod 2) b = 0 := by
      change pairVec a c b = 0
      rw [pairVec_apply, ite_eq_right (Ne.symm hab), ite_eq_right (Ne.symm hcb), add_zero]
    rw [h1, h2, add_zero, one_smul]
  have hcomm := congrArg (fun k : LinearMap.GeneralLinearGroup (ZMod 2) Δ =>
    (k : Δ →ₗ[ZMod 2] Δ) x) (hc τ)
  simp only [Units.val_mul, Module.End.mul_apply] at hcomm
  set y : Δ := (h : Δ →ₗ[ZMod 2] Δ) x with hy
  have h3 : (h : Δ →ₗ[ZMod 2] Δ) ⟨pairVec a b, pairVec_mem hΔ a b⟩ =
      ((y : Fin m → ZMod 2) a + (y : Fin m → ZMod 2) b) •
        (⟨pairVec a b, pairVec_mem hΔ a b⟩ : Δ) := by
    conv_lhs => rw [← hx]
    rw [map_sub, hcomm, rho_swap_sub hρ hΔ hab]
  have hkey : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hkey ((y : Fin m → ZMod 2) a + (y : Fin m → ZMod 2) b) with h4 | h4
  · exfalso
    rw [h4, zero_smul] at h3
    have h5 : (⟨pairVec a b, pairVec_mem hΔ a b⟩ : Δ) = 0 := by
      have h6 := congrArg (((h⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) :
        Δ →ₗ[ZMod 2] Δ)) h3
      rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply, map_zero] at h6
    exact pairVec_ne_zero hab (congrArg Subtype.val h5)
  · rw [h3, h4, one_smul]

theorem eq_one_of_commute
    (hρ : ∀ σ (x : Δ) i, (((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x :
      Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i))
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (hm : 3 ≤ m) {h : LinearMap.GeneralLinearGroup (ZMod 2) Δ}
    (hc : ∀ σ, h * ρ σ = ρ σ * h) : h = 1 := by
  apply Units.ext
  rw [Units.val_one]
  exact eq_of_forall_pairVec hΔ (by omega) fun i j => by
    rw [fixes_pairVec_of_commute hρ hΔ hm hc i j, Module.End.one_apply]

theorem rho_injective
    (hρ : ∀ σ (x : Δ) i, (((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x :
      Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i))
    (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (hm : 3 ≤ m) : Function.Injective ρ := by
  classical
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hpair : ∀ i j : Fin m, i ≠ j → σ i = i ∨ σ i = j := by
    intro i j hij
    have h1 := rho_pairVec hρ hΔ σ i j
    rw [hσ, Units.val_one, Module.End.one_apply] at h1
    have h2 := congrFun (congrArg Subtype.val h1) (σ i)
    change pairVec i j (σ i) = pairVec (σ i) (σ j) (σ i) at h2
    rw [pairVec_apply_left (σ.injective.ne hij), pairVec_apply] at h2
    by_contra h3
    push Not at h3
    rw [ite_eq_right h3.1, ite_eq_right h3.2, add_zero] at h2
    exact absurd h2 (by decide)
  ext i
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin m, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    have h1 : 2 ≤ ((Finset.univ : Finset (Fin m)).erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 h1
    exact ⟨j, k, (Finset.ne_of_mem_erase hj).symm, (Finset.ne_of_mem_erase hk).symm, hjk⟩
  rcases hpair i j hij with h1 | h1
  · rw [h1, Equiv.Perm.one_apply]
  · rcases hpair i k hik with h2 | h2
    · rw [h2, Equiv.Perm.one_apply]
    · exact absurd (h1.symm.trans h2) hjk

theorem finrank_delta (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0) (hm : 0 < m) :
    finrank (ZMod 2) Δ = m - 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => ∑ i, x i
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum] }
  have hker : LinearMap.ker f = Δ := by
    ext x
    rw [LinearMap.mem_ker, hΔ]
    rfl
  have hrange : LinearMap.range f = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨c • Pi.single ⟨0, hm⟩ 1, ?_⟩
    change ∑ i, (c • Pi.single (⟨0, hm⟩ : Fin m) (1 : ZMod 2)) i = c
    simp [Pi.single_apply]
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) f
  rw [hrange, hker, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  omega

end SteinbergBQ.DeletedModule

open SteinbergBQ.DeletedModule CFSG.GroupTheory.AutAlternating

theorem odd_deleted_symmetric_actor_is_self_normalizing {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    {Δ : Submodule (ZMod 2) (Fin m → ZMod 2)} (hΔ : ∀ x, x ∈ Δ ↔ ∑ i, x i = 0)
    (ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) Δ)
    (hρ : ∀ σ (x : Δ) i, (((ρ σ : LinearMap.GeneralLinearGroup (ZMod 2) Δ) : Δ →ₗ[ZMod 2] Δ) x :
      Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i)) :
    Function.Injective ρ ∧
      Subgroup.normalizer (ρ.range : Set (LinearMap.GeneralLinearGroup (ZMod 2) Δ)) = ρ.range ∧
      Subgroup.centralizer (ρ.range : Set (LinearMap.GeneralLinearGroup (ZMod 2) Δ)) = ⊥ ∧
      ∀ K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) Δ), ρ.range ≤ K →
        (ρ.range.subgroupOf K).Normal → K = ρ.range := by
  classical
  have hinj := rho_injective hρ hΔ hm
  have hcent : Subgroup.centralizer (ρ.range : Set (LinearMap.GeneralLinearGroup (ZMod 2) Δ)) =
      ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    exact eq_one_of_commute hρ hΔ hm fun σ =>
      (Subgroup.mem_centralizer_iff.1 hh (ρ σ) ⟨σ, rfl⟩).symm
  have hnorm : Subgroup.normalizer (ρ.range : Set (LinearMap.GeneralLinearGroup (ZMod 2) Δ)) =
      ρ.range := by
    refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
    by_cases h3 : m = 3
    ·
      subst h3
      have hdim : finrank (ZMod 2) Δ = 2 := finrank_delta hΔ (by norm_num)
      have hcard : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) Δ) = 6 := by
        let bas := Module.finBasisOfFinrankEq (ZMod 2) Δ hdim
        rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' bas).toEquiv,
          Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
        norm_num
      have hS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) Δ) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      obtain ⟨σ, rfl⟩ := ((Nat.bijective_iff_injective_and_card ρ).2
        ⟨hinj, by rw [hcard, hS]⟩).2 g
      exact ⟨σ, rfl⟩
    have h5 : 5 ≤ m := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    have h6 : m ≠ 6 := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    have hgσ : ∀ σ : Equiv.Perm (Fin m), ∃ σ', ρ σ' = g * ρ σ * g⁻¹ := fun σ =>
      (Subgroup.mem_normalizer_iff.1 hg (ρ σ)).1 ⟨σ, rfl⟩
    choose ψf hψf using hgσ
    have hψmul : ∀ σ τ, ψf (σ * τ) = ψf σ * ψf τ := fun σ τ => hinj (by
      rw [map_mul, hψf, hψf, hψf, map_mul]
      group)
    let ψhom : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m) :=
      { toFun := ψf
        map_one' := hinj (by rw [hψf, map_one]; group)
        map_mul' := hψmul }
    have hψinj : Function.Injective ψhom := fun σ τ hστ => hinj (by
      have h1 := congrArg ρ hστ
      change ρ (ψf σ) = ρ (ψf τ) at h1
      rw [hψf, hψf] at h1
      exact mul_right_cancel (mul_left_cancel h1))
    let ψ : Equiv.Perm (Fin m) ≃* Equiv.Perm (Fin m) :=
      MulEquiv.ofBijective ψhom (Finite.injective_iff_bijective.1 hψinj)
    have hψ : ∀ σ, ρ (ψ σ) = g * ρ σ * g⁻¹ := hψf
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hA : (alternatingGroup (Fin m)).map (ψ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m)) =
        alternatingGroup (Fin m) := by
      apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
      rw [Subgroup.index_map_equiv, alternatingGroup.index_eq_two]
    let φ : MulAut (alternatingGroup (Fin m)) :=
      (ψ.subgroupMap (alternatingGroup (Fin m))).trans (MulEquiv.subgroupCongr hA)
    have hφ : ∀ a : alternatingGroup (Fin m),
        ((φ a : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = ψ a := fun _ => rfl
    obtain ⟨π, hπ⟩ := (aut_alternatingGroup_bijective_conj m h5 h6).2 φ
    have hπA : ∀ a ∈ alternatingGroup (Fin m), π * a * π⁻¹ = ψ a := by
      intro a ha
      have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin m)) =>
        ((f ⟨a, ha⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m))) hπ
      simp only [MulAut.conjNormal_apply] at h1
      rw [h1, hφ]
    have hπS : ∀ σ, ψ σ = π * σ * π⁻¹ := by
      intro σ
      have h1 : MulAut.conjNormal (H := alternatingGroup (Fin m)) (π⁻¹ * ψ σ * π) =
          MulAut.conjNormal σ := by
        refine MulEquiv.ext fun a => Subtype.ext ?_
        simp only [MulAut.conjNormal_apply]
        have hσa : σ * (a : Equiv.Perm (Fin m)) * σ⁻¹ ∈ alternatingGroup (Fin m) :=
          (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ a.2 σ
        have h2 := hπA _ hσa
        rw [map_mul, map_mul, map_inv, ← hπA a a.2] at h2
        calc π⁻¹ * ψ σ * π * (a : Equiv.Perm (Fin m)) * (π⁻¹ * ψ σ * π)⁻¹ =
            π⁻¹ * (ψ σ * (π * (a : Equiv.Perm (Fin m)) * π⁻¹) * (ψ σ)⁻¹) * π := by group
          _ = π⁻¹ * (π * (σ * (a : Equiv.Perm (Fin m)) * σ⁻¹) * π⁻¹) * π := by rw [← h2]
          _ = σ * (a : Equiv.Perm (Fin m)) * σ⁻¹ := by group
      have h4 := conjNormal_injective_alternatingGroup m (by omega) h1
      calc ψ σ = π * (π⁻¹ * ψ σ * π) * π⁻¹ := by group
        _ = π * σ * π⁻¹ := by rw [h4]
    have hcomm : ∀ σ, (ρ π)⁻¹ * g * ρ σ = ρ σ * ((ρ π)⁻¹ * g) := by
      intro σ
      have h1 := hψ σ
      rw [hπS, map_mul, map_mul, map_inv] at h1
      calc (ρ π)⁻¹ * g * ρ σ = (ρ π)⁻¹ * (g * ρ σ * g⁻¹) * g := by group
        _ = (ρ π)⁻¹ * (ρ π * ρ σ * (ρ π)⁻¹) * g := by rw [h1]
        _ = ρ σ * ((ρ π)⁻¹ * g) := by group
    exact ⟨π, inv_mul_eq_one.1 (eq_one_of_commute hρ hΔ hm hcomm)⟩
  refine ⟨hinj, hnorm, hcent, fun K hK hKn => le_antisymm ?_ hK⟩
  rw [← hnorm]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK).1 hKn

end CFSG.QuasithinUnique
