module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerNC
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerToral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

section Realized

variable {K : Type*} [Field K] {G : Type*} [Group G]

@[expose] def realized (E : Subgroup (MulAut G)) (ρ : SpecialLinearGroup (Fin 3) K →* G) :
    Subgroup (MulAut (SpecialLinearGroup (Fin 3) K)) where
  carrier := {a | ∃ ε ∈ E, ∀ s, ρ (a s) = ε (ρ s)}
  one_mem' := ⟨1, E.one_mem, fun s => rfl⟩
  mul_mem' := by
    rintro a b ⟨ε, hε, ha⟩ ⟨ε', hε', hb⟩
    refine ⟨ε * ε', E.mul_mem hε hε', fun s => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, ha, hb]
  inv_mem' := by
    rintro a ⟨ε, hε, ha⟩
    refine ⟨ε⁻¹, E.inv_mem hε, fun s => ?_⟩
    have h := ha (a⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    show ρ (a⁻¹ s) = ε⁻¹ (ρ s)
    rw [h]
    simp

theorem zpow_apply_eq_of_apply_eq {σ : MulAut G} {x : G} (h : σ x = x) {ε : MulAut G}
    (hε : ε ∈ Subgroup.zpowers σ) : ε x = x := by
  have hσ : σ ∈ MulAction.stabilizer (MulAut G) x := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut G) x := Subgroup.zpowers_le.2 hσ
  have := hle hε
  rwa [MulAction.mem_stabilizer_iff] at this

theorem pow_apply_of_act {ρ : SpecialLinearGroup (Fin 3) K →* G} {ε : MulAut G}
    {γ : GL (Fin 3) K} (h : ∀ s, ε (ρ s) = ρ (conjSL γ s)) (n : ℕ)
    (s : SpecialLinearGroup (Fin 3) K) : (ε ^ n) (ρ s) = ρ ((conjSL γ ^ n) s) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, h, ih]

theorem exists_smul_one_of_conjSL_eq_one {g : GL (Fin 3) K} (h : conjSL g = 1) :
    ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 3) K,
      Commute t.toMatrix (g : Matrix (Fin 3) (Fin 3) K) := by
    intro t
    have h2 : conjSL g t.toSpecialLinearGroup = t.toSpecialLinearGroup := by rw [h]; rfl
    exact (conjSL_apply_eq_self_iff.1 h2).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  refine ⟨c, ?_⟩
  rw [← hc]
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem exists_pow_three_smul_one {ρ : SpecialLinearGroup (Fin 3) K →* G}
    (hρ : Function.Injective ρ) {ε : MulAut G} (hε3 : ε ^ 3 = 1) {γ : GL (Fin 3) K}
    (hγ : ∀ s, ε (ρ s) = ρ (conjSL γ s)) :
    ∃ α : K, (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := by
  have h1 : conjSL (γ ^ 3) = 1 := by
    refine MulEquiv.ext fun s => hρ ?_
    rw [map_pow, ← pow_apply_of_act hγ 3 s, hε3]
    rfl
  obtain ⟨c, hc⟩ := exists_smul_one_of_conjSL_eq_one h1
  exact ⟨c, by rw [← hc, Units.val_pow_eq_pow_val]⟩

end Realized

section Acts

variable {K : Type*} [Field K] [Finite K] {G : Type*} [Group G]

theorem le_seitzHyperGamma_of_acts (h3 : 3 ∣ Nat.card K - 1) (h4 : Nat.card K ≠ 4)
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    {ρ : SpecialLinearGroup (Fin 3) K →* G} (hρ : Function.Injective ρ)
    {σ : MulAut G} (hσ : σ ∈ E) (hσ1 : σ ≠ 1) (hσρ : ∀ s, σ (ρ s) = ρ s)
    (hact : ∀ ε ∈ E, ∃ γ : GL (Fin 3) K, ∀ s, ε (ρ s) = ρ (conjSL γ s)) :
    ρ.range ≤ seitzHyperGamma 3 E := by
  classical
  have hq : 4 < Nat.card K := four_lt_card_of_three_dvd h3 h4
  by_cases hker : ∃ ε ∈ E, ε ∉ Subgroup.zpowers σ ∧ ∀ s, ε (ρ s) = ρ s
  · obtain ⟨ε, hε, hεσ, hfix⟩ := hker
    rintro _ ⟨s, rfl⟩
    exact mem_seitzHyperGamma_of_fixed hE hcard hσ hε hσ1 hεσ (hσρ s) (hfix s)
  push Not at hker
  obtain ⟨ε₁, hε₁, hε₁σ⟩ := exists_notMem_zpowers hE hcard hσ
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_notMem_closure_pair hE hcard hσ hε₁
  obtain ⟨γ₁, hγ₁⟩ := hact ε₁ hε₁
  obtain ⟨γ₂, hγ₂⟩ := hact ε₂ hε₂
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσ
  have hε₁3 : ε₁ ^ 3 = 1 := hE.2 ε₁ hε₁
  have hε₂3 : ε₂ ^ 3 = 1 := hE.2 ε₂ hε₂
  have hcomm : ε₁ * ε₂ = ε₂ * ε₁ :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨ε₁, hε₁⟩ : E) ⟨ε₂, hε₂⟩)
  have hR₁ : conjSL γ₁ ∈ realized E ρ := ⟨ε₁, hε₁, fun s => (hγ₁ s).symm⟩
  have hR₂ : conjSL γ₂ ∈ realized E ρ := ⟨ε₂, hε₂, fun s => (hγ₂ s).symm⟩
  have hγ₁3 := exists_pow_three_smul_one hρ hε₁3 hγ₁
  have hγ₂3 := exists_pow_three_smul_one hρ hε₂3 hγ₂
  have hconj : conjSL (γ₁ * γ₂) = conjSL (γ₂ * γ₁) := by
    refine MulEquiv.ext fun s => hρ ?_
    have e1 : ∀ s, ρ (conjSL (γ₁ * γ₂) s) = (ε₁ * ε₂) (ρ s) := by
      intro s
      rw [map_mul, MulAut.mul_apply, MulAut.mul_apply, ← hγ₁ ((conjSL γ₂) s), ← hγ₂ s]
    have e2 : ∀ s, ρ (conjSL (γ₂ * γ₁) s) = (ε₂ * ε₁) (ρ s) := by
      intro s
      rw [map_mul, MulAut.mul_apply, MulAut.mul_apply, ← hγ₂ ((conjSL γ₁) s), ← hγ₁ s]
    rw [e1, e2, hcomm]
  obtain ⟨c, hc⟩ : ∃ c : K, ((γ₁ * γ₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • ((γ₂ * γ₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : conjSL ((γ₁ * γ₂) * (γ₂ * γ₁)⁻¹) = 1 := by
      rw [map_mul, hconj, map_inv, mul_inv_cancel]
    obtain ⟨c, hc⟩ := exists_smul_one_of_conjSL_eq_one h1
    refine ⟨c, ?_⟩
    have e : ((γ₁ * γ₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((γ₁ * γ₂) * (γ₂ * γ₁)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((γ₂ * γ₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul]
      congr 1
      group
    rw [e, hc, smul_mul_assoc, one_mul]
  have hc3 : c ^ 3 = 1 := by
    have hdet := congrArg Matrix.det hc
    rw [Matrix.det_smul, Fintype.card_fin] at hdet
    have hD : Matrix.det ((γ₂ * γ₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (γ₂ * γ₁))).ne_zero
    have hsw : Matrix.det ((γ₁ * γ₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.det ((γ₂ * γ₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      simp only [Units.val_mul, Matrix.det_mul]
      exact mul_comm _ _
    rw [hsw] at hdet
    have : c ^ 3 * Matrix.det ((γ₂ * γ₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 * Matrix.det ((γ₂ * γ₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [one_mul]
      exact hdet.symm
    exact mul_right_cancel₀ hD this
  have hPG : PlaneGen (realized E ρ) := by
    by_cases hc1 : c = 1
    · subst hc1
      have hxy : γ₁ * γ₂ = γ₂ * γ₁ := Units.ext (by rw [hc, one_smul])
      refine planeGen_of_toralPair h3 hxy hγ₁3 hγ₂3 ?_ hR₁ hR₂
      intro a b hab h1
      apply hab
      have hfix : ∀ s, (ε₁ ^ a * ε₂ ^ b) (ρ s) = ρ s := by
        intro s
        rw [MulAut.mul_apply, pow_apply_of_act hγ₂ b s, pow_apply_of_act hγ₁ a]
        have := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin 3) K) => φ s) h1
        simp only [MulAut.mul_apply, MulAut.one_apply] at this
        rw [this]
      have hmem : ε₁ ^ a * ε₂ ^ b ∈ E := E.mul_mem (E.pow_mem hε₁ a) (E.pow_mem hε₂ b)
      have hin : ε₁ ^ a * ε₂ ^ b ∈ Subgroup.zpowers σ := by
        by_contra hn
        obtain ⟨s, hs⟩ := hker _ hmem hn
        exact hs (hfix s)
      exact pow_mul_pow_mem_zpowers hε₁σ hε₂c hσ3 hε₁3 hε₂3 hin
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hprim : IsPrimitiveRoot c 3 := by
        have := orderOf_eq_prime hc3 hc1
        rw [← this]
        exact IsPrimitiveRoot.orderOf c
      exact planeGen_of_heisPair hprim hq hc hγ₁3 hγ₂3 hR₁ hR₂
  have hcl : planeClosure (realized E ρ) ≤ (seitzHyperGamma 3 E).comap ρ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro k ⟨a, ⟨ε, hε, ha⟩, ha1, hak⟩
    have hεσ : ε ∉ Subgroup.zpowers σ := by
      intro hmem
      apply ha1
      refine MulEquiv.ext fun s => hρ ?_
      rw [ha s, zpow_apply_eq_of_apply_eq (hσρ s) hmem]
      rfl
    show ρ k ∈ seitzHyperGamma 3 E
    exact mem_seitzHyperGamma_of_fixed hE hcard hσ hε hσ1 hεσ (hσρ k) (by rw [← ha k, hak])
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ planeClosure (realized E ρ) := by
    rw [hPG]
    exact Subgroup.mem_top s
  exact hcl hs

end Acts

section Perm

variable {K : Type*} [Field K] [Finite K] {G : Type*} [Group G]

theorem le_seitzHyperGamma_of_perm (h3 : 3 ∣ Nat.card K - 1)
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    {ρ : SpecialLinearGroup (Fin 3) K →* G} {B C : Subgroup G}
    {σ τ f : MulAut G} (hσ : σ ∈ E) (hτ : τ ∈ E) (hf : f ∈ E) (hσ1 : σ ≠ 1)
    (hτσ : τ ∉ Subgroup.zpowers σ) (hfσ : f ∉ Subgroup.zpowers σ)
    (hσρ : ∀ s, σ (ρ s) = ρ s) (hσB : ∀ x ∈ B, σ x = x) (hσC : ∀ x ∈ C, σ x = x)
    (hcomB : ∀ s, ∀ y ∈ B, ρ s * y = y * ρ s) (hcomC : ∀ s, ∀ y ∈ C, ρ s * y = y * ρ s)
    (hτρ : ∀ s, τ (ρ s) ∈ B) (hτB : ∀ y ∈ B, τ y ∈ C)
    {γ : GL (Fin 3) K} (hfρ : ∀ s, f (ρ s) = ρ (conjSL γ s))
    (hγ : ∃ α : K, (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ρ.range ≤ seitzHyperGamma 3 E := by
  have hτ3 : ∀ z, τ (τ (τ z)) = z := by
    intro z
    have := congrArg (fun φ : MulAut G => φ z) (hE.2 τ hτ)
    simpa [pow_succ, MulAut.mul_apply] using this
  have hQ : ∀ q x : SpecialLinearGroup (Fin 3) K,
      (γ : Matrix (Fin 3) (Fin 3) K) * q = q * γ →
        x * q * x⁻¹ ∈ (seitzHyperGamma 3 E).comap ρ := by
    intro q x hq
    have hρq : ρ q ∈ seitzHyperGamma 3 E := by
      refine mem_seitzHyperGamma_of_fixed hE hcard hσ hf hσ1 hfσ (hσρ q) ?_
      rw [hfρ q, conjSL_apply_eq_self_iff.2 hq]
    have hz₂B : τ (ρ x) ∈ B := hτρ x
    have hz₃C : τ (τ (ρ x)) ∈ C := hτB _ hz₂B
    have hc₂ : Commute (ρ x) (τ (ρ x)) := hcomB x _ hz₂B
    have hc₃ : Commute (ρ x) (τ (τ (ρ x))) := hcomC x _ hz₃C
    have hy : ρ x * τ (ρ x) * τ (τ (ρ x)) ∈ seitzHyperGamma 3 E := by
      refine mem_seitzHyperGamma_of_fixed hE hcard hσ hτ hσ1 hτσ ?_ ?_
      · rw [map_mul, map_mul, hσρ x, hσB _ hz₂B, hσC _ hz₃C]
      · rw [map_mul, map_mul, hτ3 (ρ x)]
        calc τ (ρ x) * τ (τ (ρ x)) * ρ x = (τ (ρ x) * τ (τ (ρ x))) * ρ x := rfl
          _ = ρ x * (τ (ρ x) * τ (τ (ρ x))) := (hc₂.mul_right hc₃).eq.symm
          _ = ρ x * τ (ρ x) * τ (τ (ρ x)) := (mul_assoc _ _ _).symm
    have hw : Commute (τ (ρ x) * τ (τ (ρ x))) (ρ q) :=
      Commute.mul_left (hcomB q _ hz₂B).symm (hcomC q _ hz₃C).symm
    have hconj : ρ x * τ (ρ x) * τ (τ (ρ x)) * ρ q * (ρ x * τ (ρ x) * τ (τ (ρ x)))⁻¹ =
        ρ (x * q * x⁻¹) := by
      calc ρ x * τ (ρ x) * τ (τ (ρ x)) * ρ q * (ρ x * τ (ρ x) * τ (τ (ρ x)))⁻¹
          = ρ x * ((τ (ρ x) * τ (τ (ρ x))) * ρ q * (τ (ρ x) * τ (τ (ρ x)))⁻¹) * (ρ x)⁻¹ := by
            group
        _ = ρ x * ρ q * (ρ x)⁻¹ := by rw [hw.mul_inv_cancel]
        _ = ρ (x * q * x⁻¹) := by simp [map_mul, map_inv]
    show ρ (x * q * x⁻¹) ∈ seitzHyperGamma 3 E
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hρq) (Subgroup.inv_mem _ hy)
  have htop := eq_top_of_forall_commute_conj_mem h3 hγ hQ
  rintro _ ⟨s, rfl⟩
  have : s ∈ (seitzHyperGamma 3 E).comap ρ := by
    rw [htop]
    exact Subgroup.mem_top s
  exact this

end Perm

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
