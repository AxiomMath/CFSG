module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGIrr
public import CFSG.Permutation.UnitaryThreeRecognition.HeisLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.UnitaryThreeRecognition.Heisenberg

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V} {lam : ZMod 3}

private lemma fg_card_cases {q d : ℕ} (h : q ^ d = 3 ^ 6) (h4 : 4 ∣ q - 1) : q = 9 ∨ q = 729 := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at h
  have hq : q ∣ 3 ^ 6 := by
    rw [← h]
    exact dvd_pow_self q hd
  obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hq
  have hmd : m * d = 6 := by
    rw [← pow_mul] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  interval_cases m
  · omega
  · norm_num at h4
  · left
    norm_num
  · norm_num at h4
  · omega
  · omega
  · right
    norm_num

private lemma fg_rho_indep (hsq : ∀ v, ρ (ρ v) = -v) {v₀ : V} (hv₀ : v₀ ≠ 0) {a b : ZMod 3}
    (h : a • v₀ + b • ρ v₀ = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hv₀, rfl⟩
  · exfalso
    have h2 : b • ρ v₀ = -(a • v₀) := eq_neg_of_add_eq_zero_right h
    have h1 : ρ v₀ = (-(b⁻¹ * a)) • v₀ := by
      calc ρ v₀ = (b⁻¹ * b) • ρ v₀ := by rw [inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • (b • ρ v₀) := by rw [mul_smul]
        _ = b⁻¹ • (-(a • v₀)) := by rw [h2]
        _ = (-(b⁻¹ * a)) • v₀ := by rw [smul_neg, smul_smul, neg_smul]
    have h3 : ((-(b⁻¹ * a)) * (-(b⁻¹ * a)) + 1) • v₀ = 0 := by
      have h4 := hsq v₀
      rw [h1, map_smul, h1, smul_smul] at h4
      rw [add_smul, h4, one_smul, neg_add_cancel]
    have h5 : ∀ k : ZMod 3, k * k + 1 ≠ 0 := by decide
    exact h5 _ ((smul_eq_zero.mp h3).resolve_right hv₀)

theorem fg_commutant_rho (hB : B.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hρ : FGCplx B ρ lam) {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hH : FGCplxGroup B ρ H)
    [IsSimpleGroup ↥H] (hcard : ¬ Nat.card ↥H ∣ 11232) (hnab : ∃ a b : ↥H, a * b ≠ b * a)
    (c : V →ₗ[ZMod 3] V) (hc : ∀ g ∈ H, ∀ v, c (g v) = g (c v)) :
    ∃ α β : ZMod 3, ∀ v, c v = α • v + β • ρ v := by
  haveI hV : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  let R : Set (Module.End (ZMod 3) V) := {f | ∃ g ∈ H, (g : V →ₗ[ZMod 3] V) = f}
  have hirr : IsIrred R := fun U hU =>
    fg_irreducible hB hdim hρ hH hcard U (fun g hg w hw => hU _ ⟨g, hg, rfl⟩ w hw)
  have hRmem : ∀ f : Module.End (ZMod 3) V, (∀ g ∈ H, ∀ v, f (g v) = g (f v)) →
      f ∈ Subalgebra.centralizer (ZMod 3) R := by
    intro f hf
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    ext v
    exact (hf g hg v).symm
  have hρmem : ρ ∈ Subalgebra.centralizer (ZMod 3) R :=
    hRmem ρ (fun g hg v => (hH.comm g hg v).symm)
  have hcmem : c ∈ Subalgebra.centralizer (ZMod 3) R := hRmem c hc
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  letI : Fintype V := Fintype.ofFinite V
  let F := SchurField R hirr hV
  letI : Fintype F := Fintype.ofFinite F
  let ι : F →+* Module.End (ZMod 3) V := SchurField.toEnd hirr hV
  have hι : Function.Injective ι := SchurField.toEnd_injective hirr hV
  let ρ' : F := SchurField.mk hirr hV ρ (by
    rintro _ ⟨g, hg, rfl⟩
    ext v
    exact hH.comm g hg v)
  have hιρ : ι ρ' = ρ := rfl
  have hρ2 : ρ' * ρ' = -1 := by
    apply hι
    rw [map_mul, map_neg, map_one, hιρ]
    ext v
    simp [Module.End.mul_apply, hρ.sq]
  have hne1 : (-1 : F) ≠ 1 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 := congrArg (fun f : F => (ι f) v) h
    simp only [map_neg, map_one, LinearMap.neg_apply, Module.End.one_apply] at h1
    have h2 : (2 : ZMod 3) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      exact neg_add_cancel v
    exact hv ((smul_eq_zero.mp h2).resolve_left (by decide))
  have h4 : 4 ∣ Nat.card F - 1 := by
    let u : Fˣ := Units.mkOfMulEqOne ρ' (-ρ') (by rw [mul_neg, hρ2, neg_neg])
    have hu2 : ¬ u ^ 2 ^ 1 = 1 := by
      intro h
      apply hne1
      have h' := congrArg (fun z : Fˣ => (z : F)) h
      simp only [pow_one, Units.val_pow_eq_pow_val, Units.val_one] at h'
      rw [pow_two] at h'
      change ρ' * ρ' = 1 at h'
      rw [← hρ2]
      exact h'
    have hu4 : u ^ 2 ^ (1 + 1) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      have h2 : ρ' ^ 2 = -1 := by rw [pow_two, hρ2]
      change ρ' ^ (2 ^ (1 + 1)) = 1
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2]
      simp
    have hord : orderOf u = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) hu2 hu4
      simpa using h
    have hdvd := orderOf_dvd_natCard u
    rwa [hord, Nat.card_units] at hdvd
  have hcardV : Fintype.card V = 3 ^ 6 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := V), ZMod.card, hdim]
  have hq : Nat.card F ^ Module.finrank F V = 3 ^ 6 := by
    have h1 : Fintype.card V = Fintype.card F ^ Module.finrank F V :=
      Module.card_eq_pow_finrank (K := F) (V := V)
    rw [Nat.card_eq_fintype_card, ← h1, hcardV]
  rcases fg_card_cases hq h4 with h9 | h729
  ·
    let Cm : Subalgebra (ZMod 3) (Module.End (ZMod 3) V) := Subalgebra.centralizer (ZMod 3) R
    haveI : Finite ↥Cm := inferInstanceAs (Finite F)
    have hCm : Nat.card ↥Cm = 9 := h9
    let φ : ZMod 3 × ZMod 3 → ↥Cm := fun p =>
      p.1 • (1 : ↥Cm) + p.2 • (⟨ρ, hρmem⟩ : ↥Cm)
    have hφval : ∀ p v, ((φ p : ↥Cm) : Module.End (ZMod 3) V) v = p.1 • v + p.2 • ρ v := by
      intro p v
      simp [φ]
    have hφinj : Function.Injective φ := by
      intro p p' h
      obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
      have h0 := congrArg (fun z : ↥Cm => ((z : Module.End (ZMod 3) V)) v₀) h
      simp only [hφval] at h0
      have h1 : (p.1 - p'.1) • v₀ + (p.2 - p'.2) • ρ v₀ = 0 := by
        have h' : p.1 • v₀ + p.2 • ρ v₀ - (p'.1 • v₀ + p'.2 • ρ v₀) = 0 := sub_eq_zero.mpr h0
        rw [← h']
        module
      obtain ⟨h2, h3⟩ := fg_rho_indep hρ.sq hv₀ h1
      exact Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3)
    have hbij : Function.Bijective φ :=
      (Nat.bijective_iff_injective_and_card φ).mpr
        ⟨hφinj, by rw [Nat.card_prod, Nat.card_zmod, hCm]⟩
    obtain ⟨⟨α, β⟩, hαβ⟩ := hbij.2 ⟨c, hcmem⟩
    refine ⟨α, β, fun v => ?_⟩
    have h0 := congrArg (fun z : ↥Cm => ((z : Module.End (ZMod 3) V)) v) hαβ
    simp only [hφval] at h0
    exact h0.symm
  ·
    exfalso
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    have hbijF : Function.Bijective (fun a : F => ι a v₀) := by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨smul_left_injective F hv₀, ?_⟩
      rw [h729, Nat.card_eq_fintype_card (α := V), hcardV]
      norm_num
    have hcommF : ∀ g ∈ H, ∀ (a : F) (w : V), g (ι a w) = ι a (g w) := by
      intro g hg a w
      have hmem := SchurField.toEnd_mem hirr hV a
      rw [Subalgebra.mem_centralizer_iff] at hmem
      have h1 := hmem (g : Module.End (ZMod 3) V) ⟨g, hg, rfl⟩
      have h2 := congrArg (fun f : Module.End (ZMod 3) V => f w) h1
      exact h2
    have hscal : ∀ g ∈ H, ∃ a : F, ∀ w, g w = ι a w := by
      intro g hg
      obtain ⟨a, ha⟩ := hbijF.2 (g v₀)
      refine ⟨a, fun w => ?_⟩
      obtain ⟨b, rfl⟩ := hbijF.2 w
      have ha' : ι a v₀ = g v₀ := ha
      calc g (ι b v₀) = ι b (g v₀) := hcommF g hg b v₀
        _ = ι b (ι a v₀) := by rw [ha']
        _ = ι (b * a) v₀ := by rw [map_mul]; rfl
        _ = ι (a * b) v₀ := by rw [mul_comm]
        _ = ι a (ι b v₀) := by rw [map_mul]; rfl
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    obtain ⟨ax, hax⟩ := hscal x x.2
    obtain ⟨ay, hay⟩ := hscal y y.2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change (x : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) w) =
      (y : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) w)
    rw [hay w, hcommF x x.2, hax w, hcommF y y.2, hay w]
    have e1 : ι ay (ι ax w) = ι (ay * ax) w := by rw [map_mul]; rfl
    have e2 : ι ax (ι ay w) = ι (ax * ay) w := by rw [map_mul]; rfl
    rw [e1, e2, mul_comm]

end CFSG.OddStandard.SmallF3.Omega
