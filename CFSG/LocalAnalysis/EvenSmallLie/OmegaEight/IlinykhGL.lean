module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27OrdersArith

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Matrix

theorem card_GL_seven_two :
    Nat.card (GL (Fin 7) (ZMod 2)) = 2 ^ 21 * 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 7]
  simp [ZMod.card, Fin.prod_univ_succ]

theorem card_GL_eight_two :
    Nat.card (GL (Fin 8) (ZMod 2)) = 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
  CFSG.OddStandard.Seitz77.card_GL8_two

@[expose] def addPerms (M : Type*) [AddCommGroup M] : Subgroup (Equiv.Perm M) where
  carrier := {σ | ∀ x y, σ (x + y) = σ x + σ y}
  mul_mem' {σ τ} hσ hτ x y := by
    change σ (τ (x + y)) = σ (τ x) + σ (τ y)
    rw [hτ x y, hσ]
  one_mem' x y := rfl
  inv_mem' {σ} hσ x y := by
    change σ.symm (x + y) = σ.symm x + σ.symm y
    apply σ.injective
    rw [hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem mem_addPerms {M : Type*} [AddCommGroup M] {σ : Equiv.Perm M} :
    σ ∈ addPerms M ↔ ∀ x y, σ (x + y) = σ x + σ y := Iff.rfl

@[expose] def addPermsEquiv (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] :
    addPerms M ≃ (M ≃ₗ[ZMod 2] M) where
  toFun σ :=
    { toLinearMap := AddMonoidHom.toZModLinearMap 2
        { toFun := σ.1, map_zero' := by
            have h := σ.2 0 0
            rw [add_zero] at h
            exact (add_eq_left.mp h.symm), map_add' := σ.2 }
      invFun := σ.1.symm
      left_inv := σ.1.symm_apply_apply
      right_inv := σ.1.apply_symm_apply }
  invFun e := ⟨e.toEquiv, fun x y => e.map_add x y⟩
  left_inv σ := rfl
  right_inv e := rfl

theorem card_addPerms_eq_card_linearEquiv (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] :
    Nat.card (addPerms M) = Nat.card (M ≃ₗ[ZMod 2] M) :=
  Nat.card_congr (addPermsEquiv M)

theorem card_addPerms_pi (n : ℕ) :
    Nat.card (addPerms (Fin n → ZMod 2)) = Nat.card (GL (Fin n) (ZMod 2)) := by
  rw [card_addPerms_eq_card_linearEquiv]
  exact Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).toEquiv.symm)

theorem card_addPerms_congr {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (e : M ≃+ M') :
    Nat.card (addPerms M) = Nat.card (addPerms M') := by
  refine Nat.card_congr
    { toFun := fun σ => ⟨e.toEquiv.symm.trans (σ.1.trans e.toEquiv), fun x y => ?_⟩
      invFun := fun σ => ⟨e.toEquiv.trans (σ.1.trans e.toEquiv.symm), fun x y => ?_⟩
      left_inv := fun σ => ?_
      right_inv := fun σ => ?_ }
  · simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
      AddEquiv.coe_toEquiv, map_add, σ.2 _ _]
  · simp only [Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
      AddEquiv.coe_toEquiv, map_add, σ.2 _ _]
  · ext x
    simp
  · ext x
    simp

theorem card_orbit_dvd_card_addPerms {N M : Type*} [Group N] [AddCommGroup M] [Finite M]
    [MulAction N M] (hadd : ∀ (n : N) (x y : M), n • (x + y) = n • x + n • y) (m : M) :
    Nat.card (MulAction.orbit N m) ∣ Nat.card (addPerms M) := by
  set φ := MulAction.toPermHom N M
  have hle : φ.range ≤ addPerms M := by
    rintro _ ⟨n, rfl⟩ x y
    exact hadd n x y
  have horb : MulAction.orbit N m = MulAction.orbit φ.range m := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨⟨φ n, n, rfl⟩, rfl⟩
    · rintro ⟨⟨_, n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
  rw [horb]
  calc Nat.card (MulAction.orbit φ.range m)
      = (MulAction.stabilizer φ.range m).index := by
        rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
    _ ∣ Nat.card φ.range := Subgroup.index_dvd_card _
    _ ∣ Nat.card (addPerms M) := Subgroup.card_dvd_of_le hle

theorem card_stabilizer_lt_of_prime_degree {K Ω : Type*} [Group K] [Finite K] [MulAction K Ω]
    [Finite Ω] (hfaith : ∀ k : K, (∀ x : Ω, k • x = x) → k = 1)
    (htrans : ∀ x y : Ω, ∃ k : K, k • x = y) {p : ℕ} (hp : p.Prime) (hΩ : Nat.card Ω = p)
    (ω : Ω) (hcop : ¬ p ∣ Nat.card (MulAction.stabilizer K ω))
    (hsyl : ∀ d, d ∣ Nat.card (MulAction.stabilizer K ω) → d % p = 1 → d = 1) :
    Nat.card (MulAction.stabilizer K ω) < p := by
  have := Fact.mk hp
  set S := MulAction.stabilizer K ω
  set m := Nat.card S
  have horb : MulAction.orbit K ω = Set.univ :=
    Set.eq_univ_of_forall fun x => htrans ω x
  have hindex : S.index = p := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, hΩ]
  have hK : Nat.card K = p * m := by
    rw [← S.index_mul_card, hindex]
  have hm0 : m ≠ 0 := Nat.card_pos.ne'
  obtain ⟨Q⟩ : Nonempty (Sylow p K) := inferInstance
  have hQ : Nat.card Q = p := by
    rw [Sylow.card_eq_multiplicity, hK, Nat.factorization_mul hp.ne_zero hm0,
      Finsupp.add_apply, hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hcop,
      add_zero, pow_one]
  have hQindex : (Q : Subgroup K).index = m := by
    have h := (Q : Subgroup K).index_mul_card
    rw [hQ, hK, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hn1 : Nat.card (Sylow p K) = 1 := by
    refine hsyl _ (hQindex ▸ Sylow.card_dvd_index Q) ?_
    have h := card_sylow_modEq_one p K
    rw [Nat.ModEq, Nat.one_mod_eq_one.mpr hp.ne_one] at h
    exact h
  have : Subsingleton (Sylow p K) := (Nat.card_eq_one_iff_unique.mp hn1).1
  have hQn : (Q : Subgroup K).Normal := Sylow.normal_of_subsingleton Q
  have : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ]
    exact hp.one_lt
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  have hgen : ∀ g ∈ (Q : Subgroup K), g ∈ Subgroup.zpowers (q : K) := by
    have hord : orderOf (q : K) = p := by
      have hdvd : orderOf (q : K) ∣ p := by
        have h := Subgroup.orderOf_dvd_natCard (Q : Subgroup K) q.2
        rwa [hQ] at h
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h)) hq
      · exact h
    have hle : Subgroup.zpowers (q : K) ≤ Q := (Subgroup.zpowers_le).2 q.2
    have heq : Subgroup.zpowers (q : K) = Q :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hQ])
    intro g hg
    rwa [heq]
  have hQtrans : ∀ x : Ω, ∃ g ∈ (Q : Subgroup K), g • ω = x := by
    by_contra! hnot
    obtain ⟨x₀, hx₀⟩ := hnot
    have hfix : ∀ g ∈ (Q : Subgroup K), g • ω = ω := by
      intro g hg
      by_contra hne
      have hsub : MulAction.orbit Q ω = Set.univ := by
        apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
        · rw [Set.ncard_univ, hΩ]
          have hpos : (MulAction.orbit Q ω).ncard ≠ 1 := by
            intro h1
            obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
            have h1 : ω ∈ MulAction.orbit Q ω := MulAction.mem_orbit_self ω
            have h2 : g • ω ∈ MulAction.orbit Q ω := ⟨⟨g, hg⟩, rfl⟩
            rw [ha] at h1 h2
            exact hne (h2.trans h1.symm)
          have hdvd : (MulAction.orbit Q ω).ncard ∣ p := by
            have h := Subgroup.index_dvd_card (MulAction.stabilizer Q ω)
            rw [hQ] at h
            rwa [← MulAction.index_stabilizer]
          rcases (Nat.dvd_prime hp).mp hdvd with h | h
          · exact absurd h hpos
          · exact h.ge
      have hx : x₀ ∈ MulAction.orbit Q ω := hsub ▸ Set.mem_univ x₀
      obtain ⟨⟨g', hg'⟩, hg'x⟩ := hx
      exact hx₀ g' hg' hg'x
    have htriv : ∀ g ∈ (Q : Subgroup K), ∀ x : Ω, g • x = x := by
      intro g hg x
      obtain ⟨k, rfl⟩ := htrans ω x
      have h := hfix (k⁻¹ * g * k) (by simpa using hQn.conj_mem g hg k⁻¹)
      calc g • k • ω = k • (k⁻¹ * g * k) • ω := by rw [smul_smul, smul_smul]; group
        _ = k • ω := by rw [h]
    exact hq (Subtype.ext (hfaith q (htriv q q.2)))
  have hconj : ∀ h : S, (h : K) * q * (h : K)⁻¹ ∈ (Q : Subgroup K) :=
    fun h => hQn.conj_mem q q.2 h
  have hinj : Function.Injective
      (fun h : S => (⟨(h : K) * q * (h : K)⁻¹, hconj h⟩ : Q)) := by
    intro h₁ h₂ heq
    simp only [Subtype.mk.injEq] at heq
    set c := (h₂ : K)⁻¹ * h₁
    have hcq : c * q = q * c := by
      have : (h₂ : K)⁻¹ * ((h₁ : K) * q * (h₁ : K)⁻¹) * (h₁ : K) =
          (h₂ : K)⁻¹ * ((h₂ : K) * q * (h₂ : K)⁻¹) * (h₁ : K) := by rw [heq]
      simp only [c]
      calc (h₂ : K)⁻¹ * h₁ * q = (h₂ : K)⁻¹ * ((h₁ : K) * q * (h₁ : K)⁻¹) * (h₁ : K) := by group
        _ = (h₂ : K)⁻¹ * ((h₂ : K) * q * (h₂ : K)⁻¹) * (h₁ : K) := this
        _ = q * ((h₂ : K)⁻¹ * h₁) := by group
    have hcω : c • ω = ω := by
      simp only [c, mul_smul]
      rw [h₁.2, ← h₂.2, inv_smul_smul, h₂.2]
    have hcg : ∀ g ∈ Subgroup.zpowers (q : K), c * g = g * c := by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_right hcq k))
    have hc1 : c = 1 := by
      apply hfaith
      intro x
      obtain ⟨g, hg, rfl⟩ := hQtrans x
      rw [smul_smul, hcg g (hgen g hg), mul_smul, hcω]
    have : (h₁ : K) = h₂ := by
      have h := congrArg ((h₂ : K) * ·) hc1
      simpa [c] using h
    exact Subtype.ext this
  have hle : m ≤ p := hQ ▸ Nat.card_le_card_of_injective _ hinj
  rcases hle.lt_or_eq with h | h
  · exact h
  · exact absurd (h ▸ dvd_refl p) hcop

end CFSG.EvenSmallLie.OmegaEight
