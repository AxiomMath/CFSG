module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Martineau
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_notMem_span_finset [FiniteDimensional (ZMod 2) V] (s : Finset V)
    (hs : s.card < finrank (ZMod 2) V) : ∃ v : V, v ∉ span (ZMod 2) (s : Set V) := by
  by_contra hcon
  push Not at hcon
  have htop : span (ZMod 2) (s : Set V) = ⊤ := Submodule.eq_top_iff'.2 hcon
  have h : finrank (ZMod 2) (span (ZMod 2) (s : Set V)) ≤ s.card :=
    finrank_span_finset_le_card s
  rw [htop, finrank_top] at h
  omega

@[expose] def TransvNormalised (M : V →ₗ[ZMod 2] V) (a : V) : Prop :=
  ∀ (f : Dual (ZMod 2) V) (w : V), f w = 0 → f a = 0 → ∃ c : ZMod 2, ∀ u : V,
    M u + f (M u) • w = M (u + f u • w) + c • (u + f u • w)

variable {M : V →ₗ[ZMod 2] V} {a : V}

theorem TransvNormalised.exists_eigen [FiniteDimensional (ZMod 2) V]
    (hdim : 4 ≤ finrank (ZMod 2) V) (hM : TransvNormalised M a) (w : V) :
    ∃ r : ZMod 2, M w = r • w := by
  classical
  obtain ⟨u₁, hu₁⟩ := exists_notMem_span_finset ({a, w} : Finset V)
    (by have := Finset.card_le_two (a := a) (b := w); omega)
  obtain ⟨v₀, hv₀⟩ := exists_notMem_span_finset ({a, w, u₁} : Finset V)
    (by have := Finset.card_le_three (a := a) (b := w) (c := u₁); omega)
  obtain ⟨f, hf1, hf0⟩ := exists_dual_one_of_notMem hv₀
  have hfa : f a = 0 := hf0 a (subset_span (by simp))
  have hfw : f w = 0 := hf0 w (subset_span (by simp))
  have hfu : f u₁ = 0 := hf0 u₁ (subset_span (by simp))
  obtain ⟨c, hc⟩ := hM f w hfw hfa
  have hc0 : c = 0 := by
    by_contra hne
    have h1 := hc u₁
    rw [hfu, zero_smul, add_zero, zmod_two_eq_one_of_ne_zero hne, one_smul] at h1
    have h2 : f (M u₁) • w = u₁ := add_left_cancel h1
    apply hu₁
    rw [← h2]
    exact Submodule.smul_mem _ _ (subset_span (by simp))
  have h1 := hc v₀
  rw [hf1, one_smul, hc0, zero_smul, add_zero, map_add] at h1
  refine ⟨f (M v₀), ?_⟩
  exact (add_left_cancel h1).symm

theorem exists_smul_of_forall_eigen (ha : a ≠ 0) (h : ∀ w : V, ∃ r : ZMod 2, M w = r • w) :
    ∃ c : ZMod 2, ∀ v : V, M v = c • v := by
  obtain ⟨c, hc⟩ := h a
  refine ⟨c, fun v => ?_⟩
  by_cases hv : v ∈ span (ZMod 2) {a}
  · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, hc, smul_comm]
  · obtain ⟨μ, hμ⟩ := h v
    obtain ⟨ν, hν⟩ := h (a + v)
    have h1 : c • a + μ • v = ν • a + ν • v := by
      rw [← hc, ← hμ, ← map_add, hν, smul_add]
    have h2 : (c - ν) • a + (μ - ν) • v = 0 := by
      rw [sub_smul, sub_smul]
      calc c • a - ν • a + (μ • v - ν • v) = (c • a + μ • v) - (ν • a + ν • v) := by abel
        _ = 0 := by rw [h1, sub_self]
    obtain ⟨h3, h4⟩ := coeff_eq_zero_of_indep ha hv h2
    rw [hμ, show μ = c by rw [sub_eq_zero.1 h4, sub_eq_zero.1 h3]]

theorem TransvNormalised.exists_smul [FiniteDimensional (ZMod 2) V]
    (hdim : 4 ≤ finrank (ZMod 2) V) (ha : a ≠ 0) (hM : TransvNormalised M a) :
    ∃ c : ZMod 2, ∀ v : V, M v = c • v :=
  exists_smul_of_forall_eigen ha (hM.exists_eigen hdim)

theorem endo_eq_pow_of_aut_stabilizer {H : Type*} [CommGroup H] (hsq : ∀ x : H, x ^ 2 = 1)
    (hcard : Nat.card H = 16) (D : H →* H) {a : H} (ha : a ≠ 1)
    (hnorm : ∀ τ : H ≃* H, τ a = a → ∃ e : ℕ, ∀ x, τ (D x) = D (τ x) * τ x ^ e) :
    ∃ e : ℕ, ∀ x, D x = x ^ e := by
  classical
  have h2 : ∀ x : Additive H, 2 • x = 0 := fun x => by
    apply Additive.toMul.injective
    simpa using hsq (Additive.toMul x)
  let _ : Module (ZMod 2) (Additive H) := AddCommGroup.zmodModule h2
  have : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have : FiniteDimensional (ZMod 2) (Additive H) := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (Additive H) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive H)
    rw [Nat.card_congr (Additive.toMul : Additive H ≃ H), hcard, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  let M : Additive H →ₗ[ZMod 2] Additive H :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive D)
  have hM : TransvNormalised M (Additive.ofMul a) := by
    intro f w hw hfa
    let t : Additive H ≃ₗ[ZMod 2] Additive H := LinearEquiv.transvection hw
    let τ : H ≃* H := MulEquiv.toAdditive.symm t.toAddEquiv
    have hτa : τ a = a := by
      apply Additive.ofMul.injective
      show t (Additive.ofMul a) = Additive.ofMul a
      rw [LinearEquiv.transvection.apply, hfa, zero_smul, add_zero]
    obtain ⟨e, he⟩ := hnorm τ hτa
    refine ⟨(e : ZMod 2), fun u => ?_⟩
    show t (M u) = M (t u) + (e : ZMod 2) • t u
    rw [Nat.cast_smul_eq_nsmul]
    exact Additive.toMul.injective (he (Additive.toMul u))
  obtain ⟨c, hc⟩ := hM.exists_smul (by omega) (fun h => ha (Additive.ofMul.injective h))
  refine ⟨c.val, fun x => ?_⟩
  apply Additive.ofMul.injective
  show M (Additive.ofMul x) = c.val • Additive.ofMul x
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  exact hc _

theorem exists_pow_of_conj {G : Type*} [Group G] {A K : Subgroup G}
    (surj : ∀ f : G → G, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
      (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n ∈ K, ∀ a ∈ A, n * a * n⁻¹ = f a)
    (D : G → G) (hD1 : ∀ a ∈ A, D a ∈ A) {a₀ : G} (ha₀ : a₀ ∈ A)
    (hstab : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * a₀ * n⁻¹ = a₀ →
      ∃ e : ℕ, ∀ a ∈ A, n * D (n⁻¹ * a * n) * n⁻¹ = D a * a ^ e)
    (φ : G → G) (hφ1 : ∀ a ∈ A, φ a ∈ A) (hφ2 : ∀ a ∈ A, ∀ b ∈ A, φ (a * b) = φ a * φ b)
    (hφ3 : ∀ a ∈ A, ∀ b ∈ A, φ a = φ b → a = b) (hφa : φ a₀ = a₀) :
    ∃ e : ℕ, ∀ y ∈ A, φ (D y) = D (φ y) * φ y ^ e := by
  obtain ⟨n, hnK, hn⟩ := surj φ hφ1 hφ2 hφ3
  obtain ⟨e, he⟩ := hstab n hnK (fun a ha => by rw [hn a ha]; exact hφ1 a ha)
    (by rw [hn a₀ ha₀, hφa])
  refine ⟨e, fun y hy => ?_⟩
  have h1 := he (φ y) (hφ1 y hy)
  have h2 : n⁻¹ * φ y * n = y := by rw [← hn y hy]; group
  rw [h2, hn (D y) (hD1 y hy)] at h1
  exact h1

theorem endo_eq_pow_of_stabilizer {G : Type*} [Group G] {A K : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x ^ 2 = 1)
    (hcard : Nat.card A = 16)
    (surj : ∀ f : G → G, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
      (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n ∈ K, ∀ a ∈ A, n * a * n⁻¹ = f a)
    (D : G → G) (hD1 : ∀ a ∈ A, D a ∈ A) (hD2 : ∀ a ∈ A, ∀ b ∈ A, D (a * b) = D a * D b)
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1)
    (hstab : ∀ n ∈ K, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → n * a₀ * n⁻¹ = a₀ →
      ∃ e : ℕ, ∀ a ∈ A, n * D (n⁻¹ * a * n) * n⁻¹ = D a * a ^ e) :
    ∃ e : ℕ, ∀ a ∈ A, D a = a ^ e := by
  classical
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hcomm _ x.2 _ y.2) }
  let D' : ↥A →* ↥A :=
    MonoidHom.mk' (fun x => ⟨D x, hD1 x x.2⟩) (fun x y => Subtype.ext (hD2 x x.2 y y.2))
  have hnorm : ∀ τ : ↥A ≃* ↥A, τ ⟨a₀, ha₀⟩ = ⟨a₀, ha₀⟩ →
      ∃ e : ℕ, ∀ x, τ (D' x) = D' (τ x) * τ x ^ e := by
    intro τ hτ
    let φ : G → G := fun x => if h : x ∈ A then ((τ ⟨x, h⟩ : ↥A) : G) else 1
    have hφ1 : ∀ a ∈ A, φ a ∈ A := fun a ha => by
      simp only [φ, dite_eq_left ha]
      exact (τ ⟨a, ha⟩).2
    have hφ2 : ∀ a ∈ A, ∀ b ∈ A, φ (a * b) = φ a * φ b := fun a ha b hb => by
      simp only [φ, dite_eq_left ha, dite_eq_left hb, dite_eq_left (A.mul_mem ha hb)]
      exact congrArg Subtype.val (τ.map_mul ⟨a, ha⟩ ⟨b, hb⟩)
    have hφ3 : ∀ a ∈ A, ∀ b ∈ A, φ a = φ b → a = b := fun a ha b hb h => by
      simp only [φ, dite_eq_left ha, dite_eq_left hb] at h
      exact congrArg Subtype.val (τ.injective (Subtype.ext h))
    have hφa : φ a₀ = a₀ := by
      simp only [φ, dite_eq_left ha₀]
      exact congrArg Subtype.val hτ
    obtain ⟨e, he⟩ := exists_pow_of_conj surj D hD1 ha₀ hstab φ hφ1 hφ2 hφ3 hφa
    refine ⟨e, fun x => Subtype.ext ?_⟩
    have h := he x x.2
    simp only [φ, dite_eq_left x.2, dite_eq_left (hD1 x x.2)] at h
    exact h
  obtain ⟨e, he⟩ := endo_eq_pow_of_aut_stabilizer (H := ↥A) (fun x => Subtype.ext (hsq x x.2))
    hcard D' (a := ⟨a₀, ha₀⟩) (fun h => ha₀1 (congrArg Subtype.val h)) hnorm
  exact ⟨e, fun a ha => congrArg Subtype.val (he ⟨a, ha⟩)⟩

end CFSG.EvenSporadicStandard.ThStd
