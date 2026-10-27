module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (ringAut_card_and_cyclic cyclic_involutions_eq)

theorem two_endo (k₀ : Type*) [Field k₀] [CharP k₀ 2] {W : Type*}
    [AddCommGroup W] [Module k₀ W] : (2 : Module.End k₀ W) = 0 := by
  have h : algebraMap k₀ (Module.End k₀ W) 2 = 2 := map_ofNat _ 2
  rw [← h, CharTwo.two_eq_zero, map_zero]

theorem two_of_hom {k₀ : Type*} [Field k₀] [CharP k₀ 2] {W : Type*}
    [AddCommGroup W] [Module k₀ W] [Nontrivial W] {K : Type*} [Field K]
    (ε : K →+* Module.End k₀ W) : (2 : K) = 0 := by
  apply ε.injective
  rw [map_ofNat, two_endo k₀, map_zero]

section Involution

variable {k₀ : Type*} [Field k₀] [CharP k₀ 2] {W : Type*} [AddCommGroup W] [Module k₀ W]
  [Nontrivial W] {K : Type*} [Field K] (ε : K →+* Module.End k₀ W)

structure InvData (a₀ : (Module.End k₀ W)ˣ) (τ : K ≃+* K) : Prop where
  sq : a₀ * a₀ = 1
  conj : ∀ x, ε (τ x) = a₀.val * ε x * (a₀⁻¹).val

variable {ε}

omit [CharP k₀ 2] [Nontrivial W] in
theorem InvData.inv_eq {a₀ : (Module.End k₀ W)ˣ} {τ : K ≃+* K} (h : InvData ε a₀ τ) :
    a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right h.sq

omit [CharP k₀ 2] [Nontrivial W] in
theorem InvData.comm {a₀ : (Module.End k₀ W)ˣ} {τ : K ≃+* K} (h : InvData ε a₀ τ) (x : K) :
    a₀.val * ε x = ε (τ x) * a₀.val := by
  rw [h.conj x, h.inv_eq]
  have : a₀.val * a₀.val = 1 := by rw [← Units.val_mul, h.sq, Units.val_one]
  calc a₀.val * ε x = a₀.val * ε x * (a₀.val * a₀.val) := by rw [this, mul_one]
    _ = a₀.val * ε x * a₀.val * a₀.val := by rw [mul_assoc (a₀.val * ε x)]
    _ = _ := by rw [mul_assoc, mul_assoc]

omit [CharP k₀ 2] in
theorem InvData.tau_tau {a₀ : (Module.End k₀ W)ˣ} {τ : K ≃+* K} (h : InvData ε a₀ τ) (x : K) :
    τ (τ x) = x := by
  apply ε.injective
  rw [h.conj, h.conj, h.inv_eq]
  have : a₀.val * a₀.val = 1 := by rw [← Units.val_mul, h.sq, Units.val_one]
  calc a₀.val * (a₀.val * ε x * a₀.val) * a₀.val
      = (a₀.val * a₀.val) * ε x * (a₀.val * a₀.val) := by simp only [mul_assoc]
    _ = ε x := by rw [this]; simp

omit [Nontrivial W] in
theorem conj_mul_aux' {R : Type*} [Ring R] (a a' : R) (h : a' * a = 1) (u v : R) :
    (a * u * a') * (a * v * a') = a * (u * v) * a' := by
  calc (a * u * a') * (a * v * a') = a * u * (a' * a) * v * a' := by simp only [mul_assoc]
    _ = a * (u * v) * a' := by rw [h]; simp only [mul_one, mul_assoc]

omit [CharP k₀ 2] in
theorem exists_conjAut [Finite K] (a : (Module.End k₀ W)ˣ)
    (ha : ∀ x : K, ∃ y : K, ε y = a.val * ε x * (a⁻¹).val) :
    ∃ τ : K ≃+* K, ∀ x, ε (τ x) = a.val * ε x * (a⁻¹).val := by
  choose f hf using ha
  have hinv : (a⁻¹).val * a.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let g : K →+* K :=
    { toFun := f
      map_one' := by
        apply ε.injective
        rw [hf, map_one, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      map_mul' := fun u v => by
        apply ε.injective
        rw [hf, map_mul, map_mul, hf, hf, conj_mul_aux' _ _ hinv]
      map_zero' := by
        apply ε.injective
        rw [hf, map_zero]
        simp
      map_add' := fun u v => by
        apply ε.injective
        rw [hf, map_add, map_add, hf, hf]
        simp only [mul_add, add_mul] }
  exact ⟨RingEquiv.ofBijective g (Finite.injective_iff_bijective.mp g.injective), hf⟩

theorem neg_eq_self_W (k₀ : Type*) [Field k₀] [CharP k₀ 2] {W : Type*} [AddCommGroup W]
    [Module k₀ W] (w : W) : -w = w :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_charTwo k₀ w)

end Involution

section Collapse

variable {k₀ : Type*} [Field k₀] [CharP k₀ 2] {W : Type*} [AddCommGroup W] [Module k₀ W]
  [Nontrivial W] [Finite W] {K : Type*} [Field K] [Finite K] (ε : K →+* Module.End k₀ W)

theorem semilinear_collapse
    (A : Subgroup (Module.End k₀ W)ˣ)
    (hA2 : ∀ a ∈ A, a * a = 1)
    (hnorm : ∀ a ∈ A, ∀ x : K, ∃ y : K, ε y = a.val * ε x * (a⁻¹).val)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w})
    (hbad : ∃ a ∈ A, ∃ x : K, a.val * ε x ≠ ε x * a.val) :
    Nat.card A = 2 ∧ Nat.card K = 4 ∧ Nat.card W = 4 ∧
      (letI : Module K W := Module.compHom W ε; Module.finrank K W = 1) := by
  classical
  have h2K : (2 : K) = 0 := two_of_hom ε
  have hKchar : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2K
  obtain ⟨a₀, ha₀A, x₀, hx₀⟩ := hbad
  obtain ⟨τ, hτ⟩ := exists_conjAut (ε := ε) a₀ (hnorm a₀ ha₀A)
  have hdata : InvData ε a₀ τ := ⟨hA2 a₀ ha₀A, hτ⟩
  have h1 : a₀.val * a₀.val = 1 := by rw [← Units.val_mul, hdata.sq, Units.val_one]
  have hτne : τ x₀ ≠ x₀ := by
    intro h
    apply hx₀
    rw [hdata.comm x₀, h]
  obtain ⟨μ, lam, hμ0, hτμ, hlam, hεμ⟩ : ∃ μ lam : K, μ ≠ 0 ∧ τ μ = μ ∧ τ lam + lam = 1 ∧
      ε μ = ε (τ x₀) + ε x₀ := by
    have hμ0 : τ x₀ + x₀ ≠ 0 := fun h => hτne (CharTwo.add_eq_zero.mp h)
    have hτμ : τ (τ x₀ + x₀) = τ x₀ + x₀ := by
      rw [map_add, hdata.tau_tau, add_comm]
    refine ⟨τ x₀ + x₀, x₀ * (τ x₀ + x₀)⁻¹, hμ0, hτμ, ?_, map_add ε _ _⟩
    have h3 : τ (x₀ * (τ x₀ + x₀)⁻¹) = τ x₀ * (τ x₀ + x₀)⁻¹ := by
      rw [map_mul, map_inv₀, hτμ]
    rw [h3, ← add_mul]
    exact mul_inv_cancel₀ hμ0
  have hR : ∀ u : W, a₀.val u = u → ∃ w, a₀.val w - w = u := by
    intro u hu
    refine ⟨ε lam u, ?_⟩
    have h1' : a₀.val (ε lam u) = ε (τ lam) u := by
      have := congrArg (fun f : Module.End k₀ W => f u) (hdata.comm lam)
      simp only [Module.End.mul_apply] at this
      rw [this, hu]
    rw [h1']
    have h2' : ε (τ lam) u + ε lam u = u := by
      have := congrArg (fun x : K => ε x u) hlam
      simp only [map_add, LinearMap.add_apply, map_one, Module.End.one_apply] at this
      exact this
    rw [sub_eq_add_neg, neg_eq_self_W k₀]
    exact h2'
  have hfix : ∀ b ∈ A, ∀ u : W, a₀.val u = u → b.val u = u := by
    intro b hb u hu
    obtain ⟨w, hw⟩ := hR u hu
    rw [← hw]
    exact hquad a₀ ha₀A b hb w
  have hlin : ∀ b ∈ A, (∀ x : K, b.val * ε x = ε x * b.val) → b = 1 := by
    intro b hb hbl
    apply Units.ext
    rw [Units.val_one]
    apply LinearMap.ext
    intro v
    show b.val v = v
    have hw₁ : a₀.val (a₀.val v + v) = a₀.val v + v := by
      rw [map_add, ← Module.End.mul_apply, h1, Module.End.one_apply, add_comm]
    have hu₁ : a₀.val (ε (τ x₀) v + ε x₀ (a₀.val v)) = ε (τ x₀) v + ε x₀ (a₀.val v) := by
      have hc1 : a₀.val (ε (τ x₀) v) = ε x₀ (a₀.val v) := by
        have := congrArg (fun f : Module.End k₀ W => f v) (hdata.comm (τ x₀))
        simp only [Module.End.mul_apply] at this
        rw [this, hdata.tau_tau]
      have hc2 : a₀.val (ε x₀ (a₀.val v)) = ε (τ x₀) v := by
        have := congrArg (fun f : Module.End k₀ W => f (a₀.val v)) (hdata.comm x₀)
        simp only [Module.End.mul_apply] at this
        have h3 : a₀.val (a₀.val v) = v := by
          rw [← Module.End.mul_apply, h1, Module.End.one_apply]
        rw [this, h3]
      rw [map_add, hc1, hc2, add_comm]
    have hz : ε x₀ (a₀.val v) + ε x₀ (a₀.val v) = 0 := add_self_eq_zero_of_charTwo k₀ _
    have hkey : ε μ v = (ε (τ x₀) v + ε x₀ (a₀.val v)) + ε x₀ (a₀.val v + v) := by
      rw [hεμ, LinearMap.add_apply, map_add, add_assoc, ← add_assoc (ε x₀ (a₀.val v)), hz,
        zero_add]
    have hb1 : b.val (ε μ v) = ε μ v := by
      rw [hkey, map_add, hfix b hb _ hu₁]
      have := congrArg (fun f : Module.End k₀ W => f (a₀.val v + v)) (hbl x₀)
      simp only [Module.End.mul_apply] at this
      rw [this, hfix b hb _ hw₁]
    have hb2 : b.val (ε μ v) = ε μ (b.val v) := by
      have := congrArg (fun f : Module.End k₀ W => f v) (hbl μ)
      simpa only [Module.End.mul_apply] using this
    have hb3 : ε μ (b.val v) = ε μ v := hb2 ▸ hb1
    have hinv : ε μ⁻¹ * ε μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ0, map_one]
    calc b.val v = (ε μ⁻¹ * ε μ) (b.val v) := by rw [hinv, Module.End.one_apply]
      _ = ε μ⁻¹ (ε μ (b.val v)) := rfl
      _ = ε μ⁻¹ (ε μ v) := by rw [hb3]
      _ = (ε μ⁻¹ * ε μ) v := rfl
      _ = v := by rw [hinv, Module.End.one_apply]
  obtain ⟨n, hK2⟩ : ∃ n : ℕ, Nat.card K = 2 ^ n := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
  have hcyc : IsCyclic (RingAut K) := (ringAut_card_and_cyclic hK2).2
  have hτne' : τ ≠ 1 := fun h => hτne (by rw [h]; rfl)
  have hτ2 : τ * τ = 1 := by
    ext x
    exact hdata.tau_tau x
  have hA : ∀ b ∈ A, b = 1 ∨ b = a₀ := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    right
    obtain ⟨σ, hσ⟩ := exists_conjAut (ε := ε) b (hnorm b hb)
    have hbdata : InvData ε b σ := ⟨hA2 b hb, hσ⟩
    have hσne : σ ≠ 1 := by
      intro h
      apply hb1
      apply hlin b hb
      intro x
      rw [hbdata.comm x, h]
      rfl
    have hσ2 : σ * σ = 1 := by
      ext x
      exact hbdata.tau_tau x
    have hordσ : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσne
    have hordτ : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτne'
    have hστ : σ = τ := cyclic_involutions_eq σ τ hordσ hordτ
    have hba : b * a₀ = 1 := by
      apply hlin (b * a₀) (A.mul_mem hb ha₀A)
      intro x
      calc (b * a₀).val * ε x = b.val * (a₀.val * ε x) := by rw [Units.val_mul, mul_assoc]
        _ = b.val * (ε (τ x) * a₀.val) := by rw [hdata.comm x]
        _ = (b.val * ε (τ x)) * a₀.val := by rw [mul_assoc]
        _ = (ε (σ (τ x)) * b.val) * a₀.val := by rw [hbdata.comm]
        _ = ε x * (b * a₀).val := by rw [hστ, hdata.tau_tau, mul_assoc, Units.val_mul]
    rw [eq_inv_of_mul_eq_one_left hba, hdata.inv_eq]
  have ha₀ne : a₀ ≠ 1 := by
    intro h
    apply hx₀
    rw [h]
    simp
  have hAcard : Nat.card A = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, A.one_mem⟩, ⟨a₀, ha₀A⟩, fun h => ha₀ne (congrArg Subtype.val h).symm, ?_⟩
    ext ⟨b, hb⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases hA b hb with rfl | rfl
    · left; rfl
    · right; rfl
  let f : W →+ W := (a₀.val - 1 : Module.End k₀ W).toAddMonoidHom
  have hker : ∀ w, w ∈ f.ker ↔ a₀.val w = w := by
    intro w
    simp [f, AddMonoidHom.mem_ker, sub_eq_zero]
  have hrange_le : f.range ≤ f.ker := by
    rintro _ ⟨w, rfl⟩
    rw [hker]
    show a₀.val ((a₀.val - 1) w) = (a₀.val - 1) w
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← Module.End.mul_apply, h1, Module.End.one_apply, ← neg_sub, neg_eq_self_W k₀]
  have hker_le : f.ker ≤ f.range := by
    intro u hu
    obtain ⟨w, hw⟩ := hR u ((hker u).mp hu)
    exact ⟨w, by simpa [f] using hw⟩
  have hrk : f.range = f.ker := le_antisymm hrange_le hker_le
  have hW : Nat.card W = Nat.card f.ker * Nat.card f.ker := by
    have := AddSubgroup.card_ker_mul_card_range f
    rw [hrk] at this
    exact this.symm
  have hfixset : Nat.card {w : W // ∀ a ∈ A, a.val w = w} = Nat.card f.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rw [hker]
    constructor
    · intro h
      exact h a₀ ha₀A
    · intro h a ha
      rcases hA a ha with rfl | rfl
      · simp
      · exact h
  have hker_pos : 0 < Nat.card f.ker := Nat.card_pos
  have h2 : Nat.card f.ker ≤ 2 := by
    have := hoff
    rw [hAcard, hfixset, hW] at this
    exact Nat.le_of_mul_le_mul_right (by linarith) hker_pos
  have h2' : 2 ≤ Nat.card f.ker := by
    by_contra hcon
    have h1' : Nat.card f.ker = 1 := by omega
    have h3 : Nat.card W = 1 := by rw [hW, h1']
    have h4 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial W)
    omega
  have hker2 : Nat.card f.ker = 2 := le_antisymm h2 h2'
  have hW4 : Nat.card W = 4 := by rw [hW, hker2]
  let _ : Module K W := Module.compHom W ε
  have hfin : Module.Finite K W := Module.Finite.of_finite
  have hcardW : Nat.card W = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
  have hrank : 0 < Module.finrank K W := Module.finrank_pos
  have hK3 : 3 ≤ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    have hne0 : x₀ ≠ 0 := fun h => hτne (by rw [h, map_zero])
    have hne1 : x₀ ≠ 1 := fun h => hτne (by rw [h, map_one])
    have hsub : ({0, 1, x₀} : Finset K).card = 3 :=
      Finset.card_eq_three.mpr ⟨0, 1, x₀, zero_ne_one, hne0.symm, hne1.symm, rfl⟩
    calc 3 = ({0, 1, x₀} : Finset K).card := hsub.symm
      _ ≤ Fintype.card K := Finset.card_le_univ _
      _ = Nat.card K := (Nat.card_eq_fintype_card).symm
  have hKdvd : Nat.card K ∣ 2 ^ 2 := by
    have : Nat.card K ∣ Nat.card K ^ Module.finrank K W := dvd_pow_self _ hrank.ne'
    rw [← hcardW, hW4] at this
    exact this
  obtain ⟨i, hi, hiK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hKdvd
  have hK4 : Nat.card K = 4 := by
    interval_cases i
    · omega
    · omega
    · rw [hiK]; norm_num
  have hdim : Module.finrank K W = 1 := by
    have h : 4 ^ Module.finrank K W = 4 ^ 1 := by
      have h' := hcardW
      rw [hW4, hK4] at h'
      rw [← h']
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h
  exact ⟨hAcard, hK4, hW4, hdim⟩

end Collapse

section Linearization

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

@[expose] def repOfSubgroup (L : Subgroup (Module.End k W)ˣ) : Representation k ↥L W :=
  (Units.coeHom (Module.End k W)).comp L.subtype

theorem repOfSubgroup_apply (L : Subgroup (Module.End k W)ˣ) (g : ↥L) (w : W) :
    repOfSubgroup L g w = g.1.val w := rfl

@[expose] def epsHom {G : Type*} [Monoid G] (ρ : Representation k G W) :
    EndRing ρ →+* Module.End k W where
  toFun ψ := ψ.restrictScalars k
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem epsHom_apply {G : Type*} [Monoid G] (ρ : Representation k G W) (ψ : EndRing ρ) (w : W) :
    epsHom ρ ψ w = ψ w := rfl

theorem epsHom_injective {G : Type*} [Monoid G] (ρ : Representation k G W) :
    Function.Injective (epsHom ρ) := fun _ _ h =>
  LinearMap.ext fun w => congrFun (congrArg DFunLike.coe h) w

theorem epsHom_commutes {G : Type*} [Monoid G] (ρ : Representation k G W) (ψ : EndRing ρ) (g : G)
    (w : W) : epsHom ρ ψ (ρ g w) = ρ g (epsHom ρ ψ w) :=
  (mem_endRing_iff ρ (epsHom ρ ψ)).mp ⟨ψ, rfl⟩ g w

theorem normalizes_endRing {L : Subgroup (Module.End k W)ˣ} (a : (Module.End k W)ˣ)
    (hnorm : ∀ g ∈ L, a⁻¹ * g * a ∈ L) (δ : EndRing (repOfSubgroup L)) :
    ∃ y : EndRing (repOfSubgroup L),
      epsHom _ y = a.val * epsHom _ δ * (a⁻¹).val := by
  have hz : ∀ (g : ↥L) (v : W),
      (a.val * epsHom _ δ * (a⁻¹).val) (repOfSubgroup L g v) =
        repOfSubgroup L g ((a.val * epsHom _ δ * (a⁻¹).val) v) := by
    intro g v
    have hg' : a⁻¹ * g.1 * a ∈ L := hnorm g.1 g.2
    have e1 : a⁻¹ * g.1 = (a⁻¹ * g.1 * a) * a⁻¹ := by group
    have e2 : a * (a⁻¹ * g.1 * a) = g.1 * a := by group
    have h1 : a⁻¹.val (g.1.val v) = (a⁻¹ * g.1 * a).val (a⁻¹.val v) := by
      exact congrArg (fun u : (Module.End k W)ˣ => u.val v) e1
    have h2 : epsHom _ δ ((a⁻¹ * g.1 * a).val (a⁻¹.val v)) =
        (a⁻¹ * g.1 * a).val (epsHom _ δ (a⁻¹.val v)) :=
      epsHom_commutes (repOfSubgroup L) δ ⟨_, hg'⟩ _
    have h3 : a.val ((a⁻¹ * g.1 * a).val (epsHom _ δ (a⁻¹.val v))) =
        g.1.val (a.val (epsHom _ δ (a⁻¹.val v))) := by
      exact congrArg (fun u : (Module.End k W)ˣ => u.val (epsHom _ δ (a⁻¹.val v))) e2
    simp only [Module.End.mul_apply, repOfSubgroup_apply]
    rw [h1, h2, h3]
  obtain ⟨y, hy⟩ := (mem_endRing_iff (repOfSubgroup L)
    (a.val * epsHom _ δ * (a⁻¹).val)).mpr hz
  exact ⟨y, LinearMap.ext fun w => congrFun hy w⟩

theorem two_le_finrank_of_perfect [Finite W] [Nontrivial W] (L : Subgroup (Module.End k W)ˣ)
    [Fact (repOfSubgroup L).IsIrreducible] (hLperf : Group.IsPerfect L) (hLnt : L ≠ ⊥) :
    2 ≤ Module.finrank (EndRing (repOfSubgroup L)) W := by
  classical
  have hfin : Module.Finite (EndRing (repOfSubgroup L)) W := Module.Finite.of_finite
  by_contra hlt
  push Not at hlt
  have hpos : 0 < Module.finrank (EndRing (repOfSubgroup L)) W := Module.finrank_pos
  have h1 : Module.finrank (EndRing (repOfSubgroup L)) W = 1 := by omega
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hspan : ∀ w : W, ∃ c : EndRing (repOfSubgroup L), c • v = w :=
    (finrank_eq_one_iff_of_nonzero' v hv).mp h1
  have hscalar : ∀ g : ↥L, ∃ c : EndRing (repOfSubgroup L), ∀ w, g.1.val w = c • w := by
    intro g
    obtain ⟨c, hc⟩ := hspan (g.1.val v)
    refine ⟨c, fun w => ?_⟩
    obtain ⟨d, rfl⟩ := hspan w
    have h2 : d • g.1.val v = g.1.val (d • v) := epsHom_commutes (repOfSubgroup L) d g v
    rw [← h2, ← hc, ← mul_smul, ← mul_smul, mul_comm]
  have hcomm : ∀ g h : ↥L, g * h = h * g := by
    intro g h
    obtain ⟨cg, hcg⟩ := hscalar g
    obtain ⟨ch, hch⟩ := hscalar h
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    show g.1.val (h.1.val w) = h.1.val (g.1.val w)
    have e1 : g.1.val (ch • w) = ch • g.1.val w := (epsHom_commutes (repOfSubgroup L) ch g w).symm
    have e2 : h.1.val (cg • w) = cg • h.1.val w := (epsHom_commutes (repOfSubgroup L) cg h w).symm
    rw [hch w, hcg w, e1, hcg w, e2, hch w, ← mul_smul, ← mul_smul, mul_comm]
  have hmc : IsMulCommutative ↥L := ⟨⟨hcomm⟩⟩
  have hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLnt
  have hperf : Group.IsPerfect ↥L := hLperf
  exact Group.IsPerfect.not_isMulCommutative ↥L hmc

theorem repOfSubgroup_isIrreducible_of_le {H K : Subgroup (Module.End k W)ˣ} (hHK : H ≤ K)
    (h : (repOfSubgroup H).IsIrreducible) : (repOfSubgroup K).IsIrreducible := by
  rw [isIrreducible_iff] at h ⊢
  exact ⟨h.1, fun U hU => h.2 U fun g u hu => hU ⟨g.1, hHK g.2⟩ u hu⟩

theorem repD_repOfSubgroup_injective (L : Subgroup (Module.End k W)ˣ) :
    Function.Injective (repD (repOfSubgroup L)) := fun _ _ hgh =>
  Subtype.ext (Units.ext (LinearMap.ext fun w =>
    congrArg (fun φ : Module.End (EndRing (repOfSubgroup L)) W => φ w) hgh))

set_option synthInstance.maxHeartbeats 400000 in
theorem quadratic_offender_endomorphism_field_linearization
    [Finite k] [CharP k 2] [Finite W] [Nontrivial W]
    (L A : Subgroup (Module.End k W)ˣ) [Fact (repOfSubgroup L).IsIrreducible]
    (hLperf : Group.IsPerfect L) (hLnt : L ≠ ⊥)
    (hAnorm : ∀ a ∈ A, ∀ g ∈ L, a * g * a⁻¹ ∈ L)
    (hA2 : ∀ a ∈ A, a * a = 1) (_hAnt : A ≠ ⊥)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w}) :
    (∀ a ∈ A, ∀ δ : EndRing (repOfSubgroup L), a.val * epsHom _ δ = epsHom _ δ * a.val) ∧
      2 ≤ Module.finrank (EndRing (repOfSubgroup L)) W ∧
      (∀ f : Module.End k W, (∀ g ∈ L ⊔ A, f * g.val = g.val * f) ↔
        ∃ δ : EndRing (repOfSubgroup L), f = epsHom _ δ) ∧
      (∀ {m : ℕ} (b : Module.Basis (Fin m) (EndRing (repOfSubgroup L)) W) {E : Type} [Field E]
        (ι : EndRing (repOfSubgroup L) →+* E), (matRepE b ι).IsIrreducible) ∧
      Function.Injective (repD (repOfSubgroup L)) ∧
      Function.Injective (repD (repOfSubgroup (L ⊔ A))) ∧
      (∃ _ : Fact (repOfSubgroup (L ⊔ A)).IsIrreducible,
        ∀ {m : ℕ} (b : Module.Basis (Fin m) (EndRing (repOfSubgroup (L ⊔ A))) W) {E : Type}
          [Field E] (ι : EndRing (repOfSubgroup (L ⊔ A)) →+* E), (matRepE b ι).IsIrreducible) ∧
      (∃ CA : Submodule (EndRing (repOfSubgroup L)) W, (∀ w, w ∈ CA ↔ ∀ a ∈ A, a.val w = w) ∧
        Nat.card (EndRing (repOfSubgroup L)) ^
          (Module.finrank (EndRing (repOfSubgroup L)) W -
            Module.finrank (EndRing (repOfSubgroup L)) CA) ≤ Nat.card A) ∧
      Nat.card W ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, a.val w = w} := by
  classical
  have hfin : Finite (EndRing (repOfSubgroup L)) := finite_endRing _
  have hchar : CharP (EndRing (repOfSubgroup L)) 2 :=
    charP_of_injective_algebraMap (algebraMap k (EndRing (repOfSubgroup L))).injective 2
  have hnormD : ∀ a ∈ A, ∀ δ : EndRing (repOfSubgroup L), ∃ y : EndRing (repOfSubgroup L),
      epsHom _ y = a.val * epsHom _ δ * (a⁻¹).val := by
    intro a ha δ
    refine normalizes_endRing a (fun g hg => ?_) δ
    have := hAnorm a⁻¹ (A.inv_mem ha) g hg
    simpa using this
  have hdim2 : 2 ≤ Module.finrank (EndRing (repOfSubgroup L)) W :=
    two_le_finrank_of_perfect L hLperf hLnt
  have hlin : ∀ a ∈ A, ∀ δ : EndRing (repOfSubgroup L),
      a.val * epsHom _ δ = epsHom _ δ * a.val := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, δ, hδ⟩ := hcon
    obtain ⟨-, hD4, hW4, -⟩ := semilinear_collapse (epsHom (repOfSubgroup L)) A hA2 hnormD hquad
      hoff ⟨a, ha, δ, hδ⟩
    have hfinW : Module.Finite (EndRing (repOfSubgroup L)) W := Module.Finite.of_finite
    have h1 := natCard_eq_pow_finrank (ρ := repOfSubgroup L)
    rw [hW4, hD4] at h1
    have h2 : 4 ^ Module.finrank (EndRing (repOfSubgroup L)) W ≤ 4 ^ 1 := by
      rw [← h1]; norm_num
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 4)).mp h2
    omega
  refine ⟨hlin, hdim2, ?_, ?_, repD_repOfSubgroup_injective L, repD_repOfSubgroup_injective (L ⊔ A),
    ?_, ?_, ?_⟩
  ·
    intro f
    constructor
    · intro hf
      refine (mem_endRing_iff (repOfSubgroup L) f).mpr (fun g v => ?_) |>.elim fun δ hδ => ⟨δ, ?_⟩
      · have := congrArg (fun φ : Module.End k W => φ v) (hf g.1 (Subgroup.mem_sup_left g.2))
        exact this
      · exact LinearMap.ext fun w => (congrFun hδ w).symm
    · rintro ⟨δ, rfl⟩ g hg
      let C : Subgroup (Module.End k W)ˣ :=
        { carrier := {g | epsHom _ δ * g.val = g.val * epsHom _ δ}
          mul_mem' := fun {x y} hx hy => by
            show epsHom _ δ * (x * y).val = (x * y).val * epsHom _ δ
            rw [Units.val_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
          one_mem' := by simp
          inv_mem' := fun {x} hx => by
            show epsHom _ δ * (x⁻¹).val = (x⁻¹).val * epsHom _ δ
            have hx' : epsHom _ δ * x.val = x.val * epsHom _ δ := hx
            have hXY : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
            have hYX : (x⁻¹).val * x.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
            symm
            calc (x⁻¹).val * epsHom _ δ = (x⁻¹).val * epsHom _ δ * (x.val * (x⁻¹).val) := by
                  rw [hXY, mul_one]
              _ = (x⁻¹).val * (epsHom _ δ * x.val) * (x⁻¹).val := by simp only [mul_assoc]
              _ = (x⁻¹).val * (x.val * epsHom _ δ) * (x⁻¹).val := by rw [hx']
              _ = ((x⁻¹).val * x.val) * (epsHom _ δ * (x⁻¹).val) := by simp only [mul_assoc]
              _ = epsHom _ δ * (x⁻¹).val := by rw [hYX, one_mul] }
      have hLC : L ≤ C := fun g hg => by
        apply LinearMap.ext
        intro v
        exact (epsHom_commutes (repOfSubgroup L) δ ⟨g, hg⟩ v)
      have hAC : A ≤ C := fun a ha => (hlin a ha δ).symm
      exact sup_le hLC hAC hg
  · intro m b E _ ι
    exact matRepE_isIrreducible b ι
  · have hG : (repOfSubgroup (L ⊔ A)).IsIrreducible :=
      repOfSubgroup_isIrreducible_of_le le_sup_left Fact.out
    have : Fact (repOfSubgroup (L ⊔ A)).IsIrreducible := ⟨hG⟩
    refine ⟨this, ?_⟩
    intro m b E _ ι
    exact matRepE_isIrreducible b ι
  ·
    let CA : Submodule (EndRing (repOfSubgroup L)) W :=
      { carrier := {w | ∀ a ∈ A, a.val w = w}
        add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
        zero_mem' := fun a _ => map_zero _
        smul_mem' := fun c w hw a ha => by
          have := congrArg (fun φ : Module.End k W => φ w) (hlin a ha c)
          show a.val (epsHom _ c w) = epsHom _ c w
          rw [show a.val (epsHom _ c w) = (a.val * epsHom _ c) w from rfl, this]
          show epsHom _ c (a.val w) = epsHom _ c w
          rw [hw a ha] }
    refine ⟨CA, fun w => Iff.rfl, ?_⟩
    have hfinW : Module.Finite (EndRing (repOfSubgroup L)) W := Module.Finite.of_finite
    have h1 := natCard_eq_pow_finrank (ρ := repOfSubgroup L)
    have h2 : Nat.card ↥CA = Nat.card (EndRing (repOfSubgroup L)) ^
        Module.finrank (EndRing (repOfSubgroup L)) CA := Module.natCard_eq_pow_finrank
    have h3 : Nat.card {w : W // ∀ a ∈ A, a.val w = w} = Nat.card ↥CA :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => Iff.rfl)
    have hle : Module.finrank (EndRing (repOfSubgroup L)) CA ≤
        Module.finrank (EndRing (repOfSubgroup L)) W := Submodule.finrank_le CA
    rw [h3, h2, h1] at hoff
    have hsplit : Nat.card (EndRing (repOfSubgroup L)) ^
        Module.finrank (EndRing (repOfSubgroup L)) W =
        Nat.card (EndRing (repOfSubgroup L)) ^
          (Module.finrank (EndRing (repOfSubgroup L)) W -
            Module.finrank (EndRing (repOfSubgroup L)) CA) *
        Nat.card (EndRing (repOfSubgroup L)) ^ Module.finrank (EndRing (repOfSubgroup L)) CA := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hsplit] at hoff
    exact Nat.le_of_mul_le_mul_right hoff (pow_pos Nat.card_pos _)
  · calc Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w} := hoff
      _ ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, a.val w = w} :=
        Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)

end Linearization

end CFSG.QuasithinUnique.Setup.SL2Modules
