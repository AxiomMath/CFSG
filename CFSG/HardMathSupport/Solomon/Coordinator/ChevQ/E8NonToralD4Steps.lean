module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Frame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Pos
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralFixedUnipotent
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCubeFrame
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.AlgebraicGroups CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

set_option linter.unusedSectionVars false


theorem exists_posStable_frame {K : Type} [Field K] [Finite K]
    {P : Subgroup (adjointGroup .E8 K)} {D : LangPlaneData .E8 K P} {z : adjointGroup .E8 K}
    (F : CubeFrame D z) (hD4 : E8D4OrthOrbit F.a F.ω) :
    ∃ (g₁ t₁ m₁ : ModGL .E8 (AlgebraicClosure K)) (ω₁ x₁ : WeylGroup .E8),
      g₁ ∈ adjointGroup .E8 (AlgebraicClosure K) ∧
      g₁ * (t₁ * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) ω₁) * g₁⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL .E8 K) ∧
      Units.map (entrywiseHom D.Fr) g₁ =
        g₁ * (m₁ * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) x₁) ∧
      t₁ ∈ torusGroup .E8 (AlgebraicClosure K) ∧
      m₁ ∈ familyGroup (K := AlgebraicClosure K) F.a ∧
      (fun α => x₁ • α) '' familyKernel F.a = familyKernel F.a ∧ KernelPosStable F.a x₁ ∧
      ω₁ ^ 3 = 1 ∧ ω₁ ∈ familyStabilizer F.a ∧ KernelPosStable F.a ω₁ ∧
      E8D4OrthOrbit F.a ω₁ ∧
      ∀ q ∈ P, ∀ u ∈ familyGroup (K := AlgebraicClosure K) F.a, Commute u
        (g₁⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (q : ModGL .E8 K) * g₁) := by
  set L := AlgebraicClosure K with hL
  have hωS : F.ω ∈ familyStabilizer F.a := F.ω_stab
  have hωK := image_familyKernel hωS
  obtain ⟨ρ, hρ, hpos⟩ := exists_kernelWeyl_conj_posStable F.a
    (fun γ hγ => smul_mem_of_image_eq hωK hγ) F.ω_pow
    (orbitSum_ne_zero_of_e8D4OrthOrbit F.ω_pow hD4)
  have hρS := mem_familyStabilizer_of_mem_closure hρ
  have hρK := image_familyKernel hρS
  have hx' : (fun α => (ρ * F.x * ρ⁻¹) • α) '' familyKernel F.a = familyKernel F.a :=
    image_smul_mul_eq (image_smul_mul_eq hρK F.x_stab) (image_smul_inv_eq hρK)
  obtain ⟨ρ₁, hρ₁, hpos₁⟩ := exists_kernelWeyl_mul_posStable F.a hx'
  have hρ₁K := image_familyKernel (mem_familyStabilizer_of_mem_closure hρ₁)
  obtain ⟨t₁, ht₁, ht₁eq⟩ := exists_conj_torus_mul_canonicalRep
    (rootDiagUnit_mem_torusGroup F.b) ρ F.ω
  obtain ⟨m₁, hm₁, hm₁eq⟩ := exists_reframe_mul_canonicalRep (x := F.x) F.a D.Fr F.m_mem hρ hρ₁
  have hnρM : canonicalRep (coxeterSystem Tag.E8) L ρ ∈ familyGroup (K := L) F.a :=
    canonicalRep_closure_mem_familyGroup F.a hρ
  have hnρG : canonicalRep (coxeterSystem Tag.E8) L ρ ∈ adjointGroup Tag.E8 L :=
    (Subgroup.mem_inf.1 (familyGroup_le_familyCentralizer F.a hnρM)).1
  set nρ := canonicalRep (coxeterSystem Tag.E8) L ρ with hnρ
  refine ⟨F.g * nρ⁻¹, t₁, m₁, ρ * F.ω * ρ⁻¹, ρ₁ * (ρ * F.x * ρ⁻¹),
    mul_mem F.g_mem (inv_mem hnρG), ?_, ?_, ht₁, hm₁, image_smul_mul_eq hρ₁K hx', hpos₁, ?_,
    mul_mem_familyStabilizer (mul_mem_familyStabilizer hρS hωS) (familyStabilizer_inv hρS), hpos,
    e8D4OrthOrbit_conj hρS hD4, ?_⟩
  · rw [← ht₁eq, ← F.conj_z, monomialElt]
    group
  · rw [map_mul, map_inv, F.frame, ← hm₁eq]
    group
  · rw [conj_pow, F.ω_pow, mul_one, mul_inv_cancel]
  · intro q hq u hu
    have hu' : nρ⁻¹ * u * nρ ∈ familyGroup (K := L) F.a :=
      mul_mem (mul_mem (inv_mem hnρM) hu) hnρM
    have hc := (F.commute_plane hu' q hq).map (MulAut.conj nρ)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
    have e1 : nρ * (nρ⁻¹ * u * nρ) * nρ⁻¹ = u := by group
    have e2 : (F.g * nρ⁻¹)⁻¹ * baseChangeGL (algebraMap K L) (q : ModGL Tag.E8 K) * (F.g * nρ⁻¹) =
        nρ * (F.g⁻¹ * baseChangeGL (algebraMap K L) (q : ModGL Tag.E8 K) * F.g) * nρ⁻¹ := by
      group
    rw [e2]
    rwa [e1] at hc

theorem conj_frob_eq_of_frame {G : Type*} [Group G] (Φ : G →* G) {g z₁ ν c : G}
    (hz : g * z₁ * g⁻¹ = c) (hν : Φ g = g * ν) (hc : Φ c = c) : ν * Φ z₁ * ν⁻¹ = z₁ := by
  have e : z₁ = g⁻¹ * c * g := by
    rw [← hz]
    group
  have hΦ : Φ z₁ = ν⁻¹ * z₁ * ν := by
    rw [e, map_mul, map_mul, map_inv, hν, hc]
    group
  rw [hΦ]
  group

section Monomial

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem exists_frob_conj_monomial (p : ℕ) [Fact p.Prime] [CharP L p] (e : ℕ)
    {t₁ m₁ : ModGL τ L} {ω₁ x₁ : WeylGroup τ} (ht₁ : t₁ ∈ torusGroup τ L)
    (hfix : frobTwistGL τ L p e (m₁ * canonicalRep (coxeterSystem τ) L x₁)
      (t₁ * canonicalRep (coxeterSystem τ) L ω₁) = t₁ * canonicalRep (coxeterSystem τ) L ω₁) :
    ∃ t₂ ∈ torusGroup τ L,
      m₁ * (t₂ * canonicalRep (coxeterSystem τ) L (x₁ * ω₁ * x₁⁻¹)) * m₁⁻¹ =
        t₁ * canonicalRep (coxeterSystem τ) L ω₁ ∧
      canonicalRep (coxeterSystem τ) L x₁ *
          entrywiseFrobGL τ L p e (t₁ * canonicalRep (coxeterSystem τ) L ω₁) *
          (canonicalRep (coxeterSystem τ) L x₁)⁻¹ =
        t₂ * canonicalRep (coxeterSystem τ) L (x₁ * ω₁ * x₁⁻¹) := by
  have hΦ : entrywiseFrobGL τ L p e (t₁ * canonicalRep (coxeterSystem τ) L ω₁) =
      entrywiseFrobGL τ L p e t₁ * canonicalRep (coxeterSystem τ) L ω₁ := by
    rw [map_mul]
    exact congrArg _ (W2.E8Lift.units_map_entrywiseHom_canonicalRep _ ω₁)
  obtain ⟨t₂, ht₂, h⟩ := exists_conj_torus_mul_canonicalRep
    (units_map_entrywiseHom_mem_torusGroup (iterateFrobenius L p e) ht₁) x₁ ω₁
  refine ⟨t₂, ht₂, ?_, by rw [hΦ]; exact h⟩
  rw [frobTwistGL_apply] at hfix
  have e' : ∀ A B C : ModGL τ L, A * (B * C * B⁻¹) * A⁻¹ = A * B * C * (A * B)⁻¹ :=
    fun _ _ _ => by group
  rw [← h, ← hΦ, e']
  exact hfix

theorem exists_monomial_twist (p : ℕ) [Fact p.Prime] [CharP L p] (e : ℕ) {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {m₁ y t t₁ t₂ : ModGL τ L} {w ω₁ x₁ : WeylGroup τ}
    (hwS : w ∈ familyStabilizer a)
    (hx₁ : (fun α => x₁ • α) '' familyKernel a = familyKernel a)
    (ht : t ∈ torusGroup τ L) (ht₁ : t₁ ∈ torusGroup τ L)
    (hm : m₁ = y * (t * canonicalRep (coxeterSystem τ) L w))
    (hc : t * canonicalRep (coxeterSystem τ) L w *
        (t₂ * canonicalRep (coxeterSystem τ) L (x₁ * ω₁ * x₁⁻¹)) *
          (t * canonicalRep (coxeterSystem τ) L w)⁻¹ = t₁ * canonicalRep (coxeterSystem τ) L ω₁)
    (ha : canonicalRep (coxeterSystem τ) L x₁ *
          entrywiseFrobGL τ L p e (t₁ * canonicalRep (coxeterSystem τ) L ω₁) *
          (canonicalRep (coxeterSystem τ) L x₁)⁻¹ =
        t₂ * canonicalRep (coxeterSystem τ) L (x₁ * ω₁ * x₁⁻¹)) :
    ∃ t' ∈ torusGroup τ L,
      m₁ * canonicalRep (coxeterSystem τ) L x₁ =
        y * (t' * canonicalRep (coxeterSystem τ) L (w * x₁)) ∧
      frobTwistGL τ L p e (t' * canonicalRep (coxeterSystem τ) L (w * x₁))
          (t₁ * canonicalRep (coxeterSystem τ) L ω₁) =
        t₁ * canonicalRep (coxeterSystem τ) L ω₁ ∧
      w * x₁ * ω₁ = ω₁ * (w * x₁) ∧
      ∀ γ ∈ familyKernel a, (w * x₁) • γ ∈ familyKernel a := by
  obtain ⟨t', ht', h'⟩ := E6ThreeInner.exists_torus_mul_canonicalRep_mul ht
    (one_mem (torusGroup τ L)) w x₁
  rw [one_mul] at h'
  have hfix : frobTwistGL τ L p e (t' * canonicalRep (coxeterSystem τ) L (w * x₁))
      (t₁ * canonicalRep (coxeterSystem τ) L ω₁) = t₁ * canonicalRep (coxeterSystem τ) L ω₁ := by
    have e' : ∀ A B C : ModGL τ L, A * B * C * (A * B)⁻¹ = A * (B * C * B⁻¹) * A⁻¹ :=
      fun _ _ _ => by group
    rw [frobTwistGL_apply, ← h', e', ha, hc]
  refine ⟨t', ht', ?_, hfix, ?_, fun γ hγ =>
    smul_mem_of_image_eq (image_smul_mul_eq (image_familyKernel hwS) hx₁) hγ⟩
  · rw [hm, ← h']
    group
  · rw [frobTwistGL_apply] at hfix
    exact commute_of_conj_entrywise_eq (iterateFrobenius L p e) ht' ht₁ hfix

end Monomial

theorem normalizesRGroup_of_twisted_curve {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K) [Fact (ringChar K).Prime]
    [CharP (AlgebraicClosure K) (ringChar K)] {e : ℕ} (he : 1 ≤ e)
    (hcard : Nat.card K = ringChar K ^ e)
    {E₀ P : Subgroup (adjointGroup τ K)} {z : adjointGroup τ K} (hz3 : z ^ 3 = 1)
    (hE : E₀ ≤ P ⊔ Subgroup.zpowers z) (hPz : ∀ q ∈ P, Commute z q)
    {ι : Type} (a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ)
    {g z₁ y n' n₀ : ModGL τ (AlgebraicClosure K)} (hg : g ∈ adjointGroup τ (AlgebraicClosure K))
    (hz₁ : g * z₁ * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K))
    (hν : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e g = g * (y * n'))
    (hP : ∀ q ∈ P, ∀ u ∈ familyGroup (K := AlgebraicClosure K) a, Commute u
      (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (q : ModGL τ K) * g))
    (hS : ∀ h ∈ familyGroup (K := AlgebraicClosure K) a ⊓ Subgroup.centralizer {z₁},
      frobTwistGL τ (AlgebraicClosure K) (ringChar K) e (y * n') h ∈
        familyGroup (K := AlgebraicClosure K) a ⊓ Subgroup.centralizer {z₁})
    (hy : y ∈ closedIdentityComponent
      (familyGroup (K := AlgebraicClosure K) a ⊓ Subgroup.centralizer {z₁}))
    (hn₀ : n₀ ∈ closedIdentityComponent
      (familyGroup (K := AlgebraicClosure K) a ⊓ Subgroup.centralizer {z₁}))
    (X : AlgebraicClosure K → ModGL τ (AlgebraicClosure K))
    (hXY : ∀ c, X c ∈ closedIdentityComponent
      (familyGroup (K := AlgebraicClosure K) a ⊓ Subgroup.centralizer {z₁}))
    (hX1 : ∀ c, c ≠ 0 → X c ≠ 1) (hXp : ∀ c, X c ^ ringChar K = 1)
    (μ : (AlgebraicClosure K)ˣ)
    (hX : ∀ c, n₀ * frobTwistGL τ (AlgebraicClosure K) (ringChar K) e n' (X c) * n₀⁻¹ =
      X ((μ : AlgebraicClosure K) * iterateFrobenius (AlgebraicClosure K) (ringChar K) e c)) :
    NormalizesRGroup (ringChar K) E₀ := by
  set L := AlgebraicClosure K with hL
  have hYle := closedIdentityComponent_le
    (familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁})
  obtain ⟨ζ, hζY, hζ⟩ := exists_inv_mul_frobTwistGL_familyGroup_inf_centralizer (ringChar K) a
    {z₁} he (y * n') hS (n₀ * y⁻¹) (mul_mem hn₀ (inv_mem hy))
  have hq : 2 ≤ Nat.card K := by
    rw [hcard]
    exact (Fact.out : (ringChar K).Prime).two_le.trans (Nat.le_self_pow (by omega) _)
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_mul_pow_eq μ hq
  have hFr : ∀ c : L, iterateFrobenius L (ringChar K) e c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hcard]
  have hXt : n₀ * (n' * entrywiseFrobGL τ L (ringChar K) e (X t) * n'⁻¹) * n₀⁻¹ = X t := by
    have h := hX t
    rw [hFr, ht, frobTwistGL_apply] at h
    exact h
  have hζ' : ζ⁻¹ * (y * n' * entrywiseFrobGL τ L (ringChar K) e ζ * (y * n')⁻¹) = n₀ * y⁻¹ := by
    rw [frobTwistGL_apply] at hζ
    exact hζ
  have hfixed := twisted_conj_fixed (entrywiseFrobGL τ L (ringChar K) e) hζ' hXt
  have hu₁MC : ζ * X t * ζ⁻¹ ∈ familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁} :=
    mul_mem (mul_mem (hYle hζY) (hYle (hXY t))) (inv_mem (hYle hζY))
  obtain ⟨hu₁M, hu₁C⟩ := Subgroup.mem_inf.1 hu₁MC
  have hu₁G : ζ * X t * ζ⁻¹ ∈ adjointGroup τ L :=
    (Subgroup.mem_inf.1 (familyGroup_le_familyCentralizer a hu₁M)).1
  have hu₁1 : ζ * X t * ζ⁻¹ ≠ 1 := by
    intro h
    apply hX1 t ht0
    calc X t = ζ⁻¹ * (ζ * X t * ζ⁻¹) * ζ := by group
      _ = 1 := by rw [h]; group
  have hu₁r : (ζ * X t * ζ⁻¹) ^ ringChar K = 1 := by
    rw [conj_pow, hXp, mul_one, mul_inv_cancel]
  exact normalizesRGroup_of_fixed_unipotent hτ hK3 (iterateFrobenius L (ringChar K) e) hFr hg
    hz3 hE hPz hz₁ hν hu₁G hu₁1 hu₁r hfixed (Subgroup.mem_centralizer_singleton_iff.1 hu₁C)
    (fun q hq => hP q hq _ hu₁M)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
