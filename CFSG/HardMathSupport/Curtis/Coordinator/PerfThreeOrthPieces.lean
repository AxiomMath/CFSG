module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Quasithin.SteinbergBSBinaryCubeBound

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Module

section Pieces

variable {K : Type*} [Field K]

theorem eq_zero_or_one_of_card_two [Finite K] (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_contra! h
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  exact h.2 ((hy c h.1).trans (hy 1 one_ne_zero).symm)

theorem two_eq_zero_of_card_two [Finite K] (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have := card_nsmul_eq_zero (G := K) (x := 1)
  rw [Nat.card_eq_fintype_card] at hK
  rw [hK] at this
  simpa using this

variable {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def restrictHom (E : Subgroup (V ≃ₗ[K] V)) (U : Submodule K V)
    (hU : ∀ g ∈ E, U.map (g : V ≃ₗ[K] V).toLinearMap = U) : E →* (U ≃ₗ[K] U) where
  toFun g := LinearEquiv.ofSubmodules (g : V ≃ₗ[K] V) U U (hU g g.2)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

@[expose] noncomputable def quotientHom {M : Type*} [AddCommGroup M] [Module K M] {E : Type*}
    [Group E] (ρ : E →* (M ≃ₗ[K] M)) (A : Submodule K M)
    (hA : ∀ g, A.map (ρ g).toLinearMap = A) : E →* ((M ⧸ A) ≃ₗ[K] (M ⧸ A)) where
  toFun g := Submodule.Quotient.equiv A A (ρ g) (hA g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ m => simp [Submodule.Quotient.equiv]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ m => simp [Submodule.Quotient.equiv]

theorem quotientHom_mk {M : Type*} [AddCommGroup M] [Module K M] {E : Type*}
    [Group E] (ρ : E →* (M ≃ₗ[K] M)) (A : Submodule K M)
    (hA : ∀ g, A.map (ρ g).toLinearMap = A) (g : E) (m : M) :
    quotientHom ρ A hA g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ g m) := by
  simp [quotientHom, Submodule.Quotient.equiv]

theorem commutator_le_ker_of_finrank_le_five [Finite K] (hK : Nat.card K = 2) {E : Type*} [Group E]
    [Finite E] (hE : IsPGroup 3 E) {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (ρ : E →* (M ≃ₗ[K] M)) (hM : finrank K M ≤ 5) : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ ≤ ρ.ker := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  set R := ρ.range with hR
  have hR3 : IsPGroup 3 R := IsPGroup.of_surjective hE ρ.rangeRestrict ρ.rangeRestrict_surjective
  have : Finite R := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR3
  have hdvd : Nat.card R ∣ Nat.card (M ≃ₗ[K] M) := Subgroup.card_subgroup_dvd_card R
  rw [CFSG.Quasithin.SteinbergBS.card_linearEquiv_eq_card_GL, Matrix.card_GL_field, hq] at hdvd
  have hn2 : n ≤ 2 := by
    by_contra hn3
    push Not at hn3
    have h27 : 27 ∣ Nat.card R := by
      rw [hn]
      have : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 hn3
      simpa using this
    exact CFSG.Quasithin.SteinbergBS.not_dvd_card_GL_two (d := finrank K M) (by omega)
      (h27.trans hdvd)
  have hcomm : ∀ a b : R, a * b = b * a := by
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
    · intro a b
      have h1 : Nat.card R = 1 := by simpa using hn
      have := (Nat.card_eq_one_iff_unique.mp h1).1
      exact Subsingleton.elim _ _
    · intro a b
      have h1 : Nat.card R = 3 := by simpa using hn
      have := isCyclic_of_prime_card h1
      exact (IsCyclic.commGroup (α := R)).mul_comm a b
    · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := R) hn
      exact fun a b => this.is_comm.comm a b
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact congrArg Subtype.val (hcomm ⟨ρ g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
    ⟨ρ h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩)

theorem commutator_apply_sub_mem [Finite K] (hK : Nat.card K = 2) [FiniteDimensional K V]
    {E : Subgroup (V ≃ₗ[K] V)} [Finite E] (hE : IsPGroup 3 E) {A B : Submodule K V} (hAB : A ≤ B)
    (hA : ∀ g ∈ E, A.map (g : V ≃ₗ[K] V).toLinearMap = A)
    (hB : ∀ g ∈ E, B.map (g : V ≃ₗ[K] V).toLinearMap = B)
    (hdim : finrank K B ≤ finrank K A + 5) {c : E}
    (hc : c ∈ ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆) :
    ∀ b ∈ B, (c : V ≃ₗ[K] V) b - b ∈ A := by
  set ρB := restrictHom E B hB with hρB
  set A' : Submodule K B := A.comap B.subtype with hA'
  have hAmem : ∀ (g : E) (a : V), a ∈ A → (g : V ≃ₗ[K] V) a ∈ A := fun g a ha => by
    have : (g : V ≃ₗ[K] V) a ∈ A.map (g : V ≃ₗ[K] V).toLinearMap := ⟨a, ha, rfl⟩
    rwa [hA g g.2] at this
  have hA'g : ∀ g : E, A'.map (ρB g).toLinearMap = A' := by
    intro g
    apply le_antisymm
    · rintro _ ⟨a', ha', rfl⟩
      exact hAmem g _ ha'
    · intro x hx
      refine ⟨ρB g⁻¹ x, ?_, ?_⟩
      · exact hAmem g⁻¹ _ hx
      · change ρB g (ρB g⁻¹ x) = x
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  set ρ' := quotientHom ρB A' hA'g with hρ'
  have hfin : finrank K (B ⧸ A') ≤ 5 := by
    have h1 := Submodule.finrank_quotient_add_finrank A'
    have h2 : finrank K A' = finrank K A :=
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hAB)
    omega
  have hker := commutator_le_ker_of_finrank_le_five hK hE ρ' hfin hc
  intro b hb
  have h1 : ρ' c = 1 := MonoidHom.mem_ker.mp hker
  have h2 := congrArg (fun f => f (Submodule.Quotient.mk (⟨b, hb⟩ : B))) h1
  simp only [hρ', quotientHom_mk] at h2
  have h3 := (Submodule.Quotient.eq A').mp h2
  exact h3

theorem eq_one_of_chain [Finite K] (hK : Nat.card K = 2) {c : V ≃ₗ[K] V} {k : ℕ}
    (hc : c ^ 3 ^ k = 1) {U₁ U₂ : Submodule K V} (h2 : ∀ v, c v - v ∈ U₂)
    (h1 : ∀ u ∈ U₂, c u - u ∈ U₁) (h0 : ∀ u ∈ U₁, c u = u) : c = 1 := by
  have h2K := two_eq_zero_of_card_two hK
  have hadd : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2K, zero_smul]
  set m : V →ₗ[K] V := (c : V →ₗ[K] V) - LinearMap.id with hm
  have hmv : ∀ v, m v = c v - v := fun v => rfl
  have hcm : ∀ v, c v = v + m v := fun v => by rw [hmv]; abel
  have hm3 : ∀ v, m (m (m v)) = 0 := by
    intro v
    have hv2 : m v ∈ U₂ := h2 v
    have hv1 : m (m v) ∈ U₁ := h1 _ hv2
    have := h0 _ hv1
    rw [hmv (m (m v)), this, sub_self]
  have hc2 : ∀ v, c (c v) = v + m (m v) := fun v => by
    rw [hcm v, map_add, hcm (m v), hcm v]
    have := hadd (m v)
    calc v + m v + (m v + m (m v)) = v + (m v + m v) + m (m v) := by abel
      _ = v + m (m v) := by rw [this, add_zero]
  have hc4 : c ^ 4 = 1 := by
    apply LinearEquiv.ext
    intro v
    have e1 : (c ^ 4) v = c (c (c (c v))) := by simp [pow_succ, LinearEquiv.mul_apply]
    rw [e1, hc2 (c (c v)), hc2 v]
    simp only [map_add, hm3 v, add_zero]
    rw [add_assoc, hadd, add_zero]
    rfl
  have hg : c ^ (Nat.gcd 4 (3 ^ k)) = 1 := pow_gcd_eq_one.mpr ⟨hc4, hc⟩
  have hcop : Nat.gcd 4 (3 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rwa [hcop, pow_one] at hg

end Pieces

end CFSG.HardMathSupport.Curtis.Coordinator
