module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityResidual
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityStd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)

section Model

variable {n : ℕ} (K : Type) [Field K] [Finite K]

@[expose] def TransvectionIntrinsic (hn : 3 ≤ n) : Prop :=
  ∀ α β : MulAut (projectiveSL n K), α ^ 2 = 1 → linearFieldPart K hn α ≠ 1 → β ^ 2 = 1 →
    β ≠ 1 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : projectiveSL n K →* Γ),
      Function.Injective φ₁ → Function.Injective φ₂ →
        (perfectCore (autFixSubgroup α)).map φ₁ = (perfectCore (autFixSubgroup β)).map φ₂ →
          ∀ y ∈ perfectCore (autFixSubgroup α), IsInvolutionClass 1 y →
            ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y

variable {K}

theorem exists_twisted_transvection_of_linearFieldPart_ne_one {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (α : MulAut (projectiveSL n K)) (hα : α ^ 2 = 1)
    (hfc : linearFieldPart K (Nat.le_of_succ_le hn) α ≠ 1) :
    ∃ m : projectiveSL n K, (α m)⁻¹ * m ∈ perfectCore (autFixSubgroup α) ∧
      IsInvolutionClass 1 ((α m)⁻¹ * m) := by
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  obtain ⟨σ, A, ε, hε, rfl⟩ := ProjectivePlane.exists_standard_form K n hn3 α
  have hσ : σ ≠ 1 := by rwa [linearFieldPart_eq hn3 hε] at hfc
  have hfus : PerfectTwistedFusionIn (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε)
      (IsInvolutionClass 1) := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rw [pow_zero, mul_one] at hα ⊢
      exact perfectTwistedFusionIn_conjAut_mul_fieldAut hf hK hn3 A σ hσ hα
    · rw [pow_one] at hα ⊢
      exact perfectTwistedFusionIn_conjAut_mul_fieldAut_mul_dualAut hf hK hn3 (by omega) A σ hσ hα
  obtain ⟨m, y, -, hmy, hy, P, hP, hyP, hPα⟩ := hfus
  refine ⟨m, ?_, ?_⟩
  · rw [hmy]
    exact le_perfectCore_of_perfect (fun p hp => hPα p hp) hP hyP
  · rw [hmy]
    exact hy

variable (n K) in
@[expose] def TransvectionIntrinsicStd : Prop :=
  ∀ (σ : K ≃+* K) (ε : ℕ), σ ≠ 1 → ε ≤ 1 → (fieldAut n K σ * dualAut n K ^ ε) ^ 2 = 1 →
    ∀ β : MulAut (projectiveSL n K), β ^ 2 = 1 → β ≠ 1 →
      ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : projectiveSL n K →* Γ),
        Function.Injective φ₁ → Function.Injective φ₂ →
          (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K ^ ε))).map φ₁ =
            (perfectCore (autFixSubgroup β)).map φ₂ →
          ∀ y ∈ perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K ^ ε)),
            IsInvolutionClass 1 y →
              ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y

theorem transvectionIntrinsic_of_std {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (h : TransvectionIntrinsicStd n K) : TransvectionIntrinsic K hn := by
  intro α β hα2 hfc hβ2 hβ1 Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX y hy hyt
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  obtain ⟨σ, A, ε, hε, rfl⟩ := ProjectivePlane.exists_standard_form K n hn α
  have hσ : σ ≠ 1 := by rwa [linearFieldPart_eq hn hε] at hfc
  obtain ⟨H, hH⟩ : ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ * dualAut n K ^ ε =
      conjAut n K H * (fieldAut n K σ * dualAut n K ^ ε) * (conjAut n K H)⁻¹ := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · simp only [pow_zero, mul_one] at hα2 ⊢
      exact (even_linear_field_involution_descent hf hK hn A σ hσ hα2).2.2
    · simp only [pow_one] at hα2 ⊢
      exact (UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A σ hσ
        hα2).2.2
  set α' := conjAut n K A * fieldAut n K σ * dualAut n K ^ ε with hα'
  set α₀ := fieldAut n K σ * dualAut n K ^ ε with hα₀
  set ψ := conjAut n K H with hψ
  have hα₀2 : α₀ ^ 2 = 1 := by
    have e1 : α₀ = ψ⁻¹ * α' * ψ := by rw [hH]; group
    calc α₀ ^ 2 = ψ⁻¹ * α' ^ 2 * ψ := by rw [e1, sq, sq]; group
      _ = 1 := by rw [hα2]; group
  have hcore : perfectCore (autFixSubgroup α') =
      (perfectCore (autFixSubgroup α₀)).map ψ.toMonoidHom := by
    rw [hH, perfectCore_autFixSubgroup_conj]
  have hy₀ : ψ⁻¹ y ∈ perfectCore (autFixSubgroup α₀) := by
    rw [hcore] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    simpa using hy₀
  obtain ⟨z, hz, hzy⟩ := h σ ε hσ hε hα₀2 β hβ2 hβ1 Γ (φ₁.comp ψ.toMonoidHom) φ₂
    (hφ₁.comp ψ.injective) hφ₂ (by rw [← Subgroup.map_map, ← hcore]; exact hX) (ψ⁻¹ y) hy₀
    (hyt.conjAut_inv H)
  refine ⟨z, hz, ?_⟩
  rw [hzy]
  simp

end Model

section Recenter

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_transvection_of_fieldComponent_ne_one (hset : SeitzSetting G L)
    {n f : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTP : TransvectionIntrinsic K (Nat.le_of_succ_le hn)) :
    ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      ∀ hg : g⁻¹ * t * g ∈ normalizer (L : Set G),
        fieldComponent (Nat.le_of_succ_le hn) e ⟨g⁻¹ * t * g, hg⟩ ≠ 1 →
          ∃ (h : G) (z : L), IsInvolutionClass 1 (e z) ∧ h⁻¹ * t * h = t * (z : G) := by
  intro g hgC hgN hfc
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  have hOut := isSolvable_outer_of_mulEquiv hn3 e
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hgtC : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := conj_inv_mem_centralizer_self_iff.2 hgC
  have hgtN : g * t * g⁻¹ ∈ normalizer (L : Set G) := hCN hgtC
  have hfcα : linearFieldPart K hn3 (normalizerAut e ⟨g⁻¹ * t * g, hgN⟩) ≠ 1 := by
    rwa [fieldComponent_apply] at hfc
  set t' := g⁻¹ * t * g with ht'
  set L' := CFSG.conjugate L g with hL'
  set Λ := perfectCore (L ⊓ centralizer ({t'} : Set G)) with hΛ
  have hsym : Λ = perfectCore (L' ⊓ centralizer ({t} : Set G)) :=
    perfectCore_inf_centralizer_conj_eq hset.standardSetting hOut htC ht g
  have hΛL : Λ ≤ L := (perfectCore_le _).trans inf_le_left
  have hΛL' : Λ ≤ L' := by
    rw [hsym]
    exact (perfectCore_le _).trans inf_le_left
  have htN' : t ∈ normalizer (L' : Set G) :=
    centralizer_conj_le_normalizer_conjugate hCN g
      (mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hgC).symm)
  set e' := conjChart e g with he'
  set φ₁ : projectiveSL n K →* G := L.subtype.comp e.symm.toMonoidHom with hφ₁
  set φ₂ : projectiveSL n K →* G := L'.subtype.comp e'.symm.toMonoidHom with hφ₂
  have hinj₁ : Function.Injective φ₁ := L.subtype_injective.comp e.symm.injective
  have hinj₂ : Function.Injective φ₂ := L'.subtype_injective.comp e'.symm.injective
  have hφe₁ : φ₁.comp e.toMonoidHom = L.subtype := by
    ext x
    simp [hφ₁]
  have hφe₂ : φ₂.comp e'.toMonoidHom = L'.subtype := by
    ext x
    simp [hφ₂]
  set α := normalizerAut e ⟨t', hgN⟩ with hα
  set β := normalizerAut e' ⟨t, htN'⟩ with hβ
  have hX₁ : (perfectCore (autFixSubgroup α)).map φ₁ = Λ := by
    rw [hα, ← map_perfectCore_inf_centralizer_eq e hgN, Subgroup.map_map, hφe₁,
      subgroupOf_map_subtype, inf_of_le_left hΛL]
  have hX₂ : (perfectCore (autFixSubgroup β)).map φ₂ = Λ := by
    rw [hβ, ← map_perfectCore_inf_centralizer_eq e' htN', ← hsym, Subgroup.map_map, hφe₂,
      subgroupOf_map_subtype, inf_of_le_left hΛL']
  have hα2 : α ^ 2 = 1 := normalizerAut_sq_eq_one e hgN (conj_mul_conj_eq_one ht g)
  have hβ2 : β ^ 2 = 1 := normalizerAut_sq_eq_one e' htN' ht2
  have hβ1 : β ≠ 1 := by
    rw [hβ, normalizerAut_conjChart e g htN' hgtN]
    refine normalizerAut_ne_one e hgtN fun hC => hfc ?_
    have hmem : g * t * g⁻¹ ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hC, hgtC⟩
    rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
    · exfalso
      have h0 : t = 1 := by
        have e1 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
        rw [e1, h1]
        group
      rw [h0, orderOf_one] at ht
      exact absurd ht (by decide)
    · have htt : t' = t := by
        rw [ht']
        calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h1]
          _ = t := by group
      have h2 : t' ∈ centralizer (L : Set G) := htt ▸ htC
      exact fieldComponent_eq_one_of_mem_centralizer hn3 e h2
  obtain ⟨m, hmΛ, hmy⟩ := exists_twisted_transvection_of_linearFieldPart_ne_one hK hn α hα2 hfcα
  obtain ⟨z, hz, hzy⟩ :=
    hTP α β hα2 hfcα hβ2 hβ1 G φ₁ φ₂ hinj₁ hinj₂ (hX₁.trans hX₂.symm) _ hmΛ hmy
  have hαm : φ₁ (α m) = t' * φ₁ m * t'⁻¹ := by
    have h := coe_symm_normalizerAut_apply e ⟨t', hgN⟩ (e.symm m)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  set y := φ₁ ((α m)⁻¹ * m) with hy
  have ht't' : t' * t' = 1 := conj_mul_conj_eq_one ht g
  have hxy : (φ₁ m)⁻¹ * t' * φ₁ m = t' * y := by
    have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht't'
    rw [hy, map_mul, map_inv, hαm]
    calc (φ₁ m)⁻¹ * t' * φ₁ m = (t' * t') * ((φ₁ m)⁻¹ * t'⁻¹ * φ₁ m) := by
          rw [ht't', one_mul, hti]
      _ = t' * ((t' * φ₁ m * t'⁻¹)⁻¹ * φ₁ m) := by group
  have hyL' : y ∈ L' := by
    rw [← hzy]
    exact (e'.symm z).2
  have hgyL : g * y * g⁻¹ ∈ L := mem_conjugate_iff_mul_mul_inv_mem.1 hyL'
  refine ⟨g * φ₁ m * g⁻¹, ⟨g * y * g⁻¹, hgyL⟩, ?_, ?_⟩
  · have hzy' : ((e'.symm z : L') : G) = y := hzy
    have h1 : (⟨g * y * g⁻¹, hgyL⟩ : L) = conjugateToSelf L g (e'.symm z) :=
      Subtype.ext (by rw [coe_conjugateToSelf, hzy'])
    rw [h1, ← conjChart_apply, ← he', MulEquiv.apply_symm_apply]
    exact hz
  · calc (g * φ₁ m * g⁻¹)⁻¹ * t * (g * φ₁ m * g⁻¹) =
          g * ((φ₁ m)⁻¹ * t' * φ₁ m) * g⁻¹ := by rw [ht']; group
      _ = g * (t' * y) * g⁻¹ := by rw [hxy]
      _ = t * (g * y * g⁻¹) := by rw [ht']; group

theorem exists_conj_eq_mul_transvection_of_rigid (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : InnerGraphFieldRigid K (Nat.le_of_succ_le hn))
    (hTP : TransvectionIntrinsic K (Nat.le_of_succ_le hn)) :
    ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  have := charP_two_of_card_eq_two_pow hK
  exact exists_conj_eq_mul_transvection_of_innerGraphFieldRigid hset hn hK e
    (fun U β hβ => mem_range_conj_of_fix_sylow_of_mulEquiv (p := 2) (Nat.le_of_succ_le hn) e U β hβ)
    (fun U {_} hz1 hz => isInvolutionClass_one_of_commute_sylow_of_mulEquiv (by omega) e U hz1 hz)
    ht hKt hFR (exists_conj_eq_mul_transvection_of_fieldComponent_ne_one hset hn hK e ht hKt hTP)

theorem exists_conj_eq_mul_transvection_of_rigid_std (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : InnerGraphFieldRigid K (Nat.le_of_succ_le hn)) (hTP : TransvectionIntrinsicStd n K) :
    ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G) :=
  exists_conj_eq_mul_transvection_of_rigid hset hn hK e ht hKt hFR
    (transvectionIntrinsic_of_std hK (Nat.le_of_succ_le hn) hTP)

end Recenter

end CFSG.SeitzReduction.LinearPilot
