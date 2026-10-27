module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverF
public import CFSG.ClassicalInvolution.Q3.TL4AECoverJ

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr

theorem exists_alt_map {k : ℕ} (hk : 3 ≤ k) (p₀ p : Fin k) :
    ∃ σ ∈ alternatingGroup (Fin k), σ p₀ = p := by
  by_cases hp : p = p₀
  · exact ⟨1, Subgroup.one_mem _, by rw [hp]; rfl⟩
  obtain ⟨q, hq₀, hqp⟩ : ∃ q : Fin k, q ≠ p₀ ∧ q ≠ p := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin k)) ⊆ {p₀, p} := fun q _ => by
      by_cases hq : q = p₀
      · simp [hq]
      · simp [h q hq]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_insert_le p₀ ({p} : Finset (Fin k))
    rw [Finset.card_singleton] at h2
    omega
  refine ⟨Equiv.swap p₀ q * Equiv.swap p₀ p, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hq₀),
      Equiv.Perm.sign_swap (Ne.symm hp)]
    rfl
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hp (Ne.symm hqp)]

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ}

omit [Finite G] in
theorem exists_lift_ePt (I : AEIdent P k) (hodd : Odd k) (p : Fin k) :
    ∃ u : ↥(pSpan P), I.φ u = ePt k p := by
  have h : ePt k p ∈ I.φ.range := by
    rw [I.range_eq]
    exact ePt_mem_aeModel hodd p
  exact h

omit [Finite G] in
theorem mem_ker_of_map_eq_ePt (I : AEIdent P k) {u : ↥(pSpan P)} {p : Fin k}
    (hu : I.φ u = ePt k p) : u ∈ (permHom I).ker := by
  rw [mem_ker_permHom, hu]
  rfl

omit [Finite G] in
theorem map_conj_ePt (I : AEIdent P k) (x : ↥(pSpan P)) {u : ↥(pSpan P)} {p : Fin k}
    (hu : I.φ u = ePt k p) :
    I.φ (x * u * x⁻¹) = ePt k ((permHom I x : Equiv.Perm (Fin k)) p) := by
  rw [map_mul, map_mul, map_inv, hu, conj_ePt, coe_permHom]

omit [Finite G] in
theorem comm_of_pow_three_fix (I : AEIdent P k) (hker : IsPGroup 2 ↥I.φ.ker) {p₀ : Fin k}
    {u₀ : ↥(pSpan P)} (hu₀ : I.φ u₀ = ePt k p₀) {y : ↥(pSpan P)} {a : ℕ} (hy : y ^ 3 ^ a = 1)
    (hy0 : (permHom I y : Equiv.Perm (Fin k)) p₀ = p₀) : y * u₀ = u₀ * y := by
  refine I.comm_of_pow_three hker hy ?_
  have h := map_conj_ePt I y hu₀
  rw [hy0, ← hu₀, map_mul, map_mul, map_inv] at h
  calc I.φ y * I.φ u₀ = I.φ y * I.φ u₀ * (I.φ y)⁻¹ * I.φ y := by group
    _ = I.φ u₀ * I.φ y := by rw [h]

theorem conj_eq_of_fix (I : AEIdent P k) (hker : IsPGroup 2 ↥I.φ.ker)
    (hUab : ∀ a ∈ (permHom I).ker, ∀ b ∈ (permHom I).ker, a * b = b * a) {p₀ : Fin k}
    {u₀ : ↥(pSpan P)} (hu₀ : I.φ u₀ = ePt k p₀) {x : ↥(pSpan P)}
    (hx : (permHom I x : Equiv.Perm (Fin k)) p₀ = p₀) : x * u₀ * x⁻¹ = u₀ := by
  have hu₀U : u₀ ∈ (permHom I).ker := mem_ker_of_map_eq_ePt I hu₀
  set C := Subgroup.centralizer ({u₀} : Set ↥(pSpan P)) with hCdef
  have hUC : (permHom I).ker ≤ C := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hUab u hu u₀ hu₀U)
  have hTA : Subgroup.closure {τ : Equiv.Perm (Fin k) | τ.IsThreeCycle ∧ τ p₀ = p₀} ≤
      alternatingGroup (Fin k) :=
    (Subgroup.closure_le _).mpr fun τ hτ => hτ.1.mem_alternatingGroup
  have key : ∀ σ ∈ Subgroup.closure {τ : Equiv.Perm (Fin k) | τ.IsThreeCycle ∧ τ p₀ = p₀},
      ∀ x : ↥(pSpan P), (permHom I x : Equiv.Perm (Fin k)) = σ → x ∈ C := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem τ hτ =>
      intro x hxτ
      have hτA : τ ∈ alternatingGroup (Fin k) := hτ.1.mem_alternatingGroup
      have hr : mkQ k (ofPerm τ) ∈ I.φ.range := by
        rw [I.range_eq]
        exact mem_aeModel_ofPerm hτA
      have h3 : mkQ k (ofPerm τ) ^ 3 = 1 := by
        rw [← map_pow, ofPerm_pow, ← hτ.1.orderOf, pow_orderOf_eq_one, ofPerm_one, map_one]
      obtain ⟨y, hyφ, a, hya⟩ := I.exists_lift_pow_three hr h3
      have hyτ : (permHom I y : Equiv.Perm (Fin k)) = τ := by
        rw [coe_permHom, hyφ]
        rfl
      have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_of_pow_three_fix I hker hu₀ hya (by rw [hyτ]; exact hτ.2))
      have hyx : y⁻¹ * x ∈ (permHom I).ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyτ, hxτ, inv_mul_cancel]
        rfl
      have e : x = y * (y⁻¹ * x) := by group
      rw [e]
      exact C.mul_mem hyC (hUC hyx)
    | one =>
      intro x hx1
      exact hUC (by rw [MonoidHom.mem_ker]; exact Subtype.ext hx1)
    | mul σ₁ σ₂ h₁ _ ih₁ ih₂ =>
      intro x hx12
      obtain ⟨x₁, hx₁⟩ := permHom_surjective I ⟨σ₁, hTA h₁⟩
      have hx₁' : (permHom I x₁ : Equiv.Perm (Fin k)) = σ₁ := congrArg Subtype.val hx₁
      have hx₂ : (permHom I (x₁⁻¹ * x) : Equiv.Perm (Fin k)) = σ₂ := by
        rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hx₁', hx12, inv_mul_cancel_left]
      have e : x = x₁ * (x₁⁻¹ * x) := by group
      rw [e]
      exact C.mul_mem (ih₁ x₁ hx₁') (ih₂ _ hx₂)
    | inv σ _ ih =>
      intro x hxinv
      have h1 : (permHom I x⁻¹ : Equiv.Perm (Fin k)) = σ := by
        rw [map_inv, Subgroup.coe_inv, hxinv, inv_inv]
      have h2 := C.inv_mem (ih x⁻¹ h1)
      rwa [inv_inv] at h2
  have hxC := key _ (mem_closure_threeCycle_fix p₀ (permHom I x).2 hx) x rfl
  rw [Subgroup.mem_centralizer_singleton_iff] at hxC
  rw [hxC, mul_inv_cancel_right]

omit [Finite G] in
theorem exists_map_point (I : AEIdent P k) (hk : 3 ≤ k) (p₀ p : Fin k) :
    ∃ x : ↥(pSpan P), (permHom I x : Equiv.Perm (Fin k)) p₀ = p := by
  obtain ⟨σ, hσ, hσp⟩ := exists_alt_map hk p₀ p
  obtain ⟨x, hx⟩ := permHom_surjective I ⟨σ, hσ⟩
  exact ⟨x, by rw [hx]; exact hσp⟩

@[expose] noncomputable def pointLift (I : AEIdent P k) (hk : 3 ≤ k) (p₀ : Fin k)
    (u₀ : ↥(pSpan P)) (p : Fin k) : ↥(pSpan P) :=
  (exists_map_point I hk p₀ p).choose * u₀ * (exists_map_point I hk p₀ p).choose⁻¹

theorem pointLift_spec (I : AEIdent P k) (hk : 3 ≤ k) (hker : IsPGroup 2 ↥I.φ.ker)
    (hUab : ∀ a ∈ (permHom I).ker, ∀ b ∈ (permHom I).ker, a * b = b * a) {p₀ : Fin k}
    {u₀ : ↥(pSpan P)} (hu₀ : I.φ u₀ = ePt k p₀) {p : Fin k} {x : ↥(pSpan P)}
    (hx : (permHom I x : Equiv.Perm (Fin k)) p₀ = p) :
    x * u₀ * x⁻¹ = pointLift I hk p₀ u₀ p := by
  set x' := (exists_map_point I hk p₀ p).choose with hx'
  have hx'p : (permHom I x' : Equiv.Perm (Fin k)) p₀ = p := (exists_map_point I hk p₀ p).choose_spec
  have hfix : (permHom I (x'⁻¹ * x) : Equiv.Perm (Fin k)) p₀ = p₀ := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hx,
      Equiv.Perm.inv_eq_iff_eq, hx'p]
  have h := conj_eq_of_fix I hker hUab hu₀ hfix
  show x * u₀ * x⁻¹ = x' * u₀ * x'⁻¹
  calc x * u₀ * x⁻¹ = x' * ((x'⁻¹ * x) * u₀ * (x'⁻¹ * x)⁻¹) * x'⁻¹ := by group
    _ = x' * u₀ * x'⁻¹ := by rw [h]

theorem conj_pointLift (I : AEIdent P k) (hk : 3 ≤ k) (hker : IsPGroup 2 ↥I.φ.ker)
    (hUab : ∀ a ∈ (permHom I).ker, ∀ b ∈ (permHom I).ker, a * b = b * a) {p₀ : Fin k}
    {u₀ : ↥(pSpan P)} (hu₀ : I.φ u₀ = ePt k p₀) (x : ↥(pSpan P)) (p : Fin k) :
    x * pointLift I hk p₀ u₀ p * x⁻¹ =
      pointLift I hk p₀ u₀ ((permHom I x : Equiv.Perm (Fin k)) p) := by
  set x' := (exists_map_point I hk p₀ p).choose with hx'
  have hx'p : (permHom I x' : Equiv.Perm (Fin k)) p₀ = p := (exists_map_point I hk p₀ p).choose_spec
  have hxx' : (permHom I (x * x') : Equiv.Perm (Fin k)) p₀ =
      (permHom I x : Equiv.Perm (Fin k)) p := by
    rw [map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, hx'p]
  rw [← pointLift_spec I hk hker hUab hu₀ hxx']
  show x * (x' * u₀ * x'⁻¹) * x⁻¹ = x * x' * u₀ * (x * x')⁻¹
  group

omit [Finite G] in
theorem map_pointLift (I : AEIdent P k) (hk : 3 ≤ k) {p₀ : Fin k} {u₀ : ↥(pSpan P)}
    (hu₀ : I.φ u₀ = ePt k p₀) (p : Fin k) : I.φ (pointLift I hk p₀ u₀ p) = ePt k p := by
  rw [pointLift, map_conj_ePt I _ hu₀, (exists_map_point I hk p₀ p).choose_spec]

omit [Finite G] in
theorem pointLift_mem_ker (I : AEIdent P k) (hk : 3 ≤ k) {p₀ : Fin k} {u₀ : ↥(pSpan P)}
    (hu₀ : I.φ u₀ = ePt k p₀) (p : Fin k) : pointLift I hk p₀ u₀ p ∈ (permHom I).ker :=
  mem_ker_of_map_eq_ePt I (map_pointLift I hk hu₀ p)

end CFSG.ClassicalInvolution.Q3.TL4.AECov
