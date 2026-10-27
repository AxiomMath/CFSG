module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCModel
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCPar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharPar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups

section Induced

variable {K₀ H : Type*} [Group K₀] [Group H]

noncomputable def inducedAut (φ : K₀ →* H) (hs : Function.Surjective φ) (θ : MulAut K₀)
    (hθ : φ.ker.map θ.toMonoidHom = φ.ker) : MulAut H :=
  ((QuotientGroup.quotientKerEquivOfSurjective φ hs).symm.trans
    (QuotientGroup.congr φ.ker φ.ker θ hθ)).trans (QuotientGroup.quotientKerEquivOfSurjective φ hs)

theorem inducedAut_apply (φ : K₀ →* H) (hs : Function.Surjective φ) (θ : MulAut K₀)
    (hθ : φ.ker.map θ.toMonoidHom = φ.ker) (k : K₀) :
    inducedAut φ hs θ hθ (φ k) = φ (θ k) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective φ hs).symm (φ k) =
      (QuotientGroup.mk k : K₀ ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [inducedAut, MulEquiv.trans_apply, h1]
  rfl

theorem inducedAut_pow_apply (φ : K₀ →* H) (hs : Function.Surjective φ) (θ : MulAut K₀)
    (hθ : φ.ker.map θ.toMonoidHom = φ.ker) (m : ℕ) (k : K₀) :
    (inducedAut φ hs θ hθ ^ m) (φ k) = φ ((θ ^ m) k) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, inducedAut_apply, ih, pow_succ, MulAut.mul_apply]

theorem orderOf_inducedAut_dvd (φ : K₀ →* H) (hs : Function.Surjective φ) (θ : MulAut K₀)
    (hθ : φ.ker.map θ.toMonoidHom = φ.ker) : orderOf (inducedAut φ hs θ hθ) ∣ orderOf θ := by
  refine orderOf_dvd_of_pow_eq_one ?_
  ext h
  obtain ⟨k, rfl⟩ := hs h
  rw [inducedAut_pow_apply, pow_orderOf_eq_one]
  rfl

end Induced

section KL1

variable {K₀ : Type} [Group K₀] {F : Type} [Field F] [Finite F]

theorem trivial_on_quotient_std (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (φ : K₀ →* projectiveSL 3 F) (hs : Function.Surjective φ)
    {W₀ : Submodule F (Fin 3 → F)} (hW₀ : W₀ = vPlus F ∨ W₀ = vMinus F)
    {P₀ : Subgroup K₀} (hP : P₀.map φ = projStabilizer W₀)
    {X₀ : Subgroup K₀} (hXP : P₀ ≤ normalizer (X₀ : Set K₀)) (hXp : IsPGroup p ↥X₀)
    (hXne : X₀.map φ ≠ ⊥)
    (θ : MulAut K₀) (hθX : ∀ x ∈ X₀, θ x = x) (hθker : φ.ker.map θ.toMonoidHom = φ.ker)
    (hord : Nat.Coprime (orderOf θ) p) : ∀ k : K₀, φ (θ k) = φ k := by
  have hCen : ∀ g ∈ CenD F, proj 3 F g ∈ normalizer ((X₀.map φ : Subgroup _) : Set _) := by
    intro g hg
    have hg' : proj 3 F g ∈ projStabilizer W₀ := by
      refine Subgroup.mem_map_of_mem _ ?_
      rcases hW₀ with rfl | rfl
      · exact CenD_le_stabilizer_vPlus h2 hg
      · exact CenD_le_stabilizer_vMinus h2 hg
    rw [← hP] at hg'
    obtain ⟨k, hk, hkg⟩ := hg'
    rw [← hkg]
    exact le_normalizer_map φ ⟨k, hXP hk, rfl⟩
  have hclass := classify_p_subgroup h2 p (X₀.map φ) (hXp.map φ) hXne hCen
  set α := inducedAut φ hs θ hθker with hα
  have hαord : Nat.Coprime (orderOf α) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_inducedAut_dvd φ hs θ hθker) hord
  have hαfix : ∀ y ∈ X₀.map φ, α y = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hα, inducedAut_apply, hθX x hx]
  have hα1 : α = 1 := by
    rcases hclass with h | h
    · refine aut_eq_one_of_fix_radP p α (fun a b => hαfix _ ?_) hαord
      rw [h]
      exact Subgroup.mem_map_of_mem _ (mem_radP.mpr ⟨a, b, rfl⟩)
    · refine aut_eq_one_of_fix_radM p α (fun a b => hαfix _ ?_) hαord
      rw [h]
      exact Subgroup.mem_map_of_mem _ (mem_radM.mpr ⟨a, b, rfl⟩)
  intro k
  rw [← inducedAut_apply φ hs θ hθker k, ← hα, hα1]
  rfl

theorem trivial_on_quotient [Finite K₀] (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (φ : K₀ →* projectiveSL 3 F) (hs : Function.Surjective φ) (hker : φ.ker ≤ center K₀)
    {P₀ : Subgroup K₀} (hPar : ParData K₀ p P₀)
    {X₀ : Subgroup K₀} (hXP : P₀ ≤ normalizer (X₀ : Set K₀)) (hXp : IsPGroup p ↥X₀)
    (hXne : X₀.map φ ≠ ⊥)
    (θ : MulAut K₀) (hθX : ∀ x ∈ X₀, θ x = x) (hθker : φ.ker.map θ.toMonoidHom = φ.ker)
    (hord : Nat.Coprime (orderOf θ) p) : ∀ k : K₀, φ (θ k) = φ k := by
  obtain ⟨h, hh⟩ := exists_conj_std p (map_mem_maximalParabolics hs hker hPar)
  set c : MulAut (projectiveSL 3 F) := MulAut.conj h with hc
  set φ₁ : K₀ →* projectiveSL 3 F := c.toMonoidHom.comp φ with hφ₁
  have hs₁ : Function.Surjective φ₁ := c.surjective.comp hs
  have hker₁ : φ₁.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact map_eq_one_iff c.toMonoidHom c.injective
  obtain ⟨W₀, hW₀, hP₁⟩ : ∃ W₀ : Submodule F (Fin 3 → F), (W₀ = vPlus F ∨ W₀ = vMinus F) ∧
      P₀.map φ₁ = projStabilizer W₀ := by
    rcases hh with hh | hh
    · exact ⟨vPlus F, Or.inl rfl, by rw [hφ₁, ← Subgroup.map_map]; exact hh⟩
    · exact ⟨vMinus F, Or.inr rfl, by rw [hφ₁, ← Subgroup.map_map]; exact hh⟩
  have hXne₁ : X₀.map φ₁ ≠ ⊥ := by
    intro h'
    apply hXne
    refine Subgroup.map_injective (f := c.toMonoidHom) c.injective ?_
    rw [Subgroup.map_bot, ← h', hφ₁, Subgroup.map_map]
  have := trivial_on_quotient_std p h2 φ₁ hs₁ hW₀ hP₁ hXP hXp hXne₁ θ hθX
    (by rw [hker₁]; exact hθker) hord
  intro k
  exact c.injective (this k)

end KL1

section KL2

variable {K₀ : Type} [Group K₀]

theorem eq_one_of_central (p : ℕ) (θ : MulAut K₀) (hθ : ∀ k, θ k * k⁻¹ ∈ Subgroup.center K₀)
    (hgen : ∀ k : K₀, k ∈ Subgroup.closure {x : K₀ | ∃ a : ℕ, x ^ p ^ a = 1})
    (hZ : ∀ z ∈ Subgroup.center K₀, (∃ a : ℕ, z ^ p ^ a = 1) → θ z = z)
    (hord : Nat.Coprime (orderOf θ) p) : θ = 1 := by
  let β : K₀ →* K₀ := MonoidHom.mk' (fun k => θ k * k⁻¹) (by
    intro a b
    have hc : Commute a⁻¹ (θ b * b⁻¹) :=
      Commute.inv_left (Subgroup.mem_center_iff.mp (hθ b) a : Commute a (θ b * b⁻¹))
    calc θ (a * b) * (a * b)⁻¹ = θ a * ((θ b * b⁻¹) * a⁻¹) := by
          simp only [map_mul, mul_inv_rev, mul_assoc]
      _ = θ a * (a⁻¹ * (θ b * b⁻¹)) := by rw [hc.eq.symm]
      _ = (θ a * a⁻¹) * (θ b * b⁻¹) := by rw [mul_assoc])
  have hβ : ∀ k, β k = θ k * k⁻¹ := fun _ => rfl
  have hβZ : ∀ k, β k ∈ Subgroup.center K₀ := fun k => hθ k
  have hβp : ∀ k, ∃ a : ℕ, (β k) ^ p ^ a = 1 := by
    intro k
    refine Subgroup.closure_induction (p := fun x _ => ∃ a : ℕ, (β x) ^ p ^ a = 1) ?_ ?_ ?_ ?_ (hgen k)
    · rintro x ⟨a, ha⟩
      exact ⟨a, by rw [← map_pow, ha, map_one]⟩
    · exact ⟨0, by simp⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have hc : Commute (β x) (β y) := (Subgroup.mem_center_iff.mp (hβZ y) (β x))
      rw [map_mul, hc.mul_pow, pow_add, pow_mul, ha, one_pow, one_mul, mul_comm (p ^ a) (p ^ b),
        pow_mul, hb, one_pow]
    · rintro x - ⟨a, ha⟩
      exact ⟨a, by rw [map_inv, inv_pow, ha, inv_one]⟩
  have hfixβ : ∀ k, θ (β k) = β k := fun k => hZ _ (hβZ k) (hβp k)
  have hit : ∀ (j : ℕ) (k : K₀), (θ ^ j) k = (β k) ^ j * k := by
    intro j k
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfixβ, pow_succ, mul_assoc,
        show θ k = β k * k by rw [hβ]; group]
  ext k
  rw [MulAut.one_apply]
  have h1 := hit (orderOf θ) k
  rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
  have h2 : (β k) ^ orderOf θ = 1 := by
    have : (β k) ^ orderOf θ * k = 1 * k := by rw [← h1, one_mul]
    exact mul_right_cancel this
  obtain ⟨a, ha⟩ := hβp k
  have hcop : Nat.Coprime (orderOf θ) (p ^ a) := Nat.Coprime.pow_right a hord
  have h3 : orderOf (β k) ∣ orderOf θ := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (β k) ∣ p ^ a := orderOf_dvd_of_pow_eq_one ha
  have h5 : orderOf (β k) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 hcop) h4
  have h6 : β k = 1 := orderOf_eq_one_iff.mp h5
  rw [hβ] at h6
  exact mul_inv_eq_one.mp h6

end KL2

end CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
