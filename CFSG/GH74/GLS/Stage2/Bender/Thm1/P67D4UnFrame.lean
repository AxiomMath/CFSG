module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnField
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnDefs
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition

public noncomputable section


namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD

section Pure

variable (p : ℕ) [Fact p.Prime] {L : Type} [Field L] [CharP L p]

theorem iterateFrobenius_pow_four (f : ℕ) :
    iterateFrobenius L p f ^ 4 = iterateFrobenius L p (4 * f) := by
  rw [iterateFrobenius_eq_pow, iterateFrobenius_eq_pow, ← pow_mul, mul_comm]

end Pure

section Four

variable (p : ℕ) [Fact p.Prime] {L : Type} [Field L] [CharP L p]

theorem twistHom_four (f : ℕ) (g : ModGL TwistTag.D4.tag L) :
    twistHom TwistTag.D4 L (iterateFrobenius L p (4 * f)) g =
      (twistHom TwistTag.D4 L (iterateFrobenius L p f))^[4] g := by
  rw [twistHom_iterate, iterateFrobenius_pow_four, twistHom_apply]
  have hP : diagramMap TwistTag.D4 L ^ 4 = diagramMap TwistTag.D4 L := by
    have h3 := diagramMap_pow_order TwistTag.D4 L
    change diagramMap TwistTag.D4 L ^ 3 = 1 at h3
    rw [pow_succ, h3, one_mul]
  rw [hP]

theorem twistHom_trialityOpposition (Fr : L →+* L) :
    twistHom TwistTag.D4 L Fr (trialityOpposition L) = trialityOpposition L := by
  rw [twistHom_apply, units_map_entrywiseHom_trialityOpposition,
    diagramMap_comm_trialityOpposition, mul_inv_cancel_right]

end Four


section Psi

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {L : Type} [Field L] [CharP L p] [Algebra K L]

omit [Finite K] in
theorem un_psi_four [IsAlgClosure K L] (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    twistHom TwistTag.D4 L (iterateFrobenius L p (4 * f)) (d4MinusPsi σ L g₀ y) =
      d4MinusPsi σ L g₀ y := by
  have hmem := (d4MinusPsi_mem_range_iff (K := K) (σ := σ) hp hf hK hσ
    (iterateFrobenius L p f) (fun c => rfl) hg₀C hg₀ (d4MinusPsi σ L g₀ y)).1 ⟨y, rfl⟩
  set x := d4MinusPsi σ L g₀ y with hx
  set F := twistHom TwistTag.D4 L (iterateFrobenius L p f) with hF
  set z := trialityOpposition L with hz
  have hFz : F z = z := twistHom_trialityOpposition _
  have hzz : z * z = 1 := by
    have := trialityOpposition_sq (K := L)
    rwa [pow_two] at this
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have h1 : F x = z * x * z := by
    have := hmem.2
    rw [hz1] at this
    calc F x = z * (z * F x * z) * z := by
          rw [← mul_assoc, ← mul_assoc, hzz, one_mul, mul_assoc, hzz, mul_one]
      _ = z * x * z := by rw [this]
  have h2 : F (F x) = x := by
    rw [h1, map_mul, map_mul, hFz, h1]
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz]; group
  rw [twistHom_four]
  have h4 : (⇑F)^[4] x = x := by
    have : (⇑F)^[4] x = F (F (F (F x))) := rfl
    rw [this, h2, h2]
  exact h4

end Psi

section Nine

variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p]

theorem un_frob_nine (x : ModGL TwistTag.D4.tag L)
    (hx : twistHom TwistTag.D4 L (iterateFrobenius L p (4 * f)) x = x) :
    Units.map (entrywiseHom (iterateFrobenius L p (9 * f))) x =
      twistHom TwistTag.D4 L (iterateFrobenius L p f) x := by
  set P := diagramMap TwistTag.D4 L with hPdef
  have hP3 : P ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hPPP : P * (P * P) = 1 := by
    have : P * (P * P) = P ^ 3 := by rw [pow_three', mul_assoc]
    rw [this, hP3]
  have hinv : P⁻¹ = P * P := inv_eq_of_mul_eq_one_right hPPP
  have hinv2 : P⁻¹ * P⁻¹ = P := by
    calc P⁻¹ * P⁻¹ = P * (P * (P * P)) := by rw [hinv]; group
      _ = P := by rw [hPPP, mul_one]
  have hPE : ∀ k : ℕ, Units.map (entrywiseHom (iterateFrobenius L p k)) P = P := fun k =>
    units_map_entrywiseHom_diagramMap _
  have hcomp : ∀ a b : ℕ, ∀ g : ModGL TwistTag.D4.tag L,
      Units.map (entrywiseHom (iterateFrobenius L p a))
        (Units.map (entrywiseHom (iterateFrobenius L p b)) g) =
      Units.map (entrywiseHom (iterateFrobenius L p (a + b))) g := fun a b g => by
    rw [units_map_entrywiseHom_comp, iterateFrobenius_add]
  have h4 : Units.map (entrywiseHom (iterateFrobenius L p (4 * f))) x = P⁻¹ * x * P := by
    rw [twistHom_apply] at hx
    calc Units.map (entrywiseHom (iterateFrobenius L p (4 * f))) x
        = P⁻¹ * (P * Units.map (entrywiseHom (iterateFrobenius L p (4 * f))) x * P⁻¹) * P := by
          group
      _ = P⁻¹ * x * P := by rw [hx]
  have h8 : Units.map (entrywiseHom (iterateFrobenius L p (8 * f))) x = P * x * P⁻¹ := by
    have e8 : 8 * f = 4 * f + 4 * f := by ring
    rw [e8, ← hcomp, h4, map_mul, map_mul, map_inv, hPE, h4]
    calc P⁻¹ * (P⁻¹ * x * P) * P = (P⁻¹ * P⁻¹) * x * (P * P) := by group
      _ = P * x * P⁻¹ := by rw [hinv2, ← hinv]
  have e9 : 9 * f = f + 8 * f := by ring
  rw [e9, ← hcomp, h8, map_mul, map_mul, map_inv, hPE, twistHom_apply]

end Nine

section Tau

variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p] {K₄ : Type} [Field K₄]
  [Algebra K₄ L]

theorem un_triEmb_fieldActor_nine [Finite K₄] {σ₄ ε : K₄ ≃+* K₄}
    (hσ₄ : ∀ c, σ₄ c = c ^ p ^ (4 * f)) (hε : ∀ c, ε c = c ^ p ^ (9 * f))
    (y : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom) :
    triEmb K₄ σ₄ L (fieldActor (t := TwistTag.D4) σ₄ ε y) =
      twistHom TwistTag.D4 L (iterateFrobenius L p f) (triEmb K₄ σ₄ L y) := by
  have hcomm9 : (algebraMap K₄ L).comp ε.toRingHom =
      (iterateFrobenius L p (9 * f)).comp (algebraMap K₄ L) :=
    RingHom.ext fun c => by simp [hε, iterateFrobenius_def, map_pow]
  have hcomm4 : (algebraMap K₄ L).comp σ₄.toRingHom =
      (iterateFrobenius L p (4 * f)).comp (algebraMap K₄ L) :=
    RingHom.ext fun c => by simp [hσ₄, iterateFrobenius_def, map_pow]
  have h1 : triEmb K₄ σ₄ L (fieldActor (t := TwistTag.D4) σ₄ ε y) =
      Units.map (entrywiseHom (iterateFrobenius L p (9 * f))) (triEmb K₄ σ₄ L y) := by
    rw [triEmb_apply, triEmb_apply, coe_fieldActor, units_map_entrywiseHom_eq_baseChangeGL,
      units_map_entrywiseHom_eq_baseChangeGL, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomm9]
  rw [h1]
  exact un_frob_nine _ (triEmb_fixed _ hcomm4 y)

end Tau

section TauEmb

variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p] {K₄ : Type} [Field K₄]
  [Finite K₄] [Algebra K₄ L]

theorem un_triEmb_tau {σ₄ ε : K₄ ≃+* K₄}
    (hσ₄ : ∀ c, σ₄ c = c ^ p ^ (4 * f)) (hε : ∀ c, ε c = c ^ p ^ (9 * f))
    (y : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom) :
    triEmb K₄ σ₄ L (unTau σ₄ ε y) =
      trialityOpposition L *
        twistHom TwistTag.D4 L (iterateFrobenius L p f) (triEmb K₄ σ₄ L y) *
          (trialityOpposition L)⁻¹ := by
  have hz : triEmb K₄ σ₄ L (unZ K₄ σ₄.toRingHom) = trialityOpposition L := by
    rw [triEmb_apply, coe_unZ, baseChangeGL_trialityOpposition]
  rw [unTau_apply, map_mul, map_mul, map_inv, hz, un_triEmb_fieldActor_nine hσ₄ hε]

end TauEmb

section Transport

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L : Type}
  [Field L] [CharP L p] [Algebra K L] {K₄ : Type} [Field K₄] [Finite K₄] [Algebra K₄ L]
  {σ₄ ε : K₄ ≃+* K₄}

omit [Finite K] [Finite K₄] in
theorem un_exists_psi4 [IsAlgClosure K L] [IsAlgClosure K₄ L] (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hK₄ : Nat.card K₄ = (p ^ (4 * f)) ^ 3) (hσ₄ : ∀ c, σ₄ c = c ^ p ^ (4 * f))
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L) :
    ∃ ψ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom,
      Function.Injective ψ₄ ∧ ∀ y, triEmb K₄ σ₄ L (ψ₄ y) = d4MinusPsi σ L g₀ y := by
  have hrange : ∀ y, d4MinusPsi σ L g₀ y ∈ (triEmb K₄ σ₄ L).range := by
    intro y
    rw [triEmb_range hp (by omega : 1 ≤ 4 * f) hK₄ hσ₄ (iterateFrobenius L p (4 * f))
      (fun c => rfl)]
    exact Subgroup.mem_inf.2 ⟨d4MinusPsi_mem_adjointGroup hg₀C y,
      un_psi_four hp hf hK hσ hg₀C hg₀ y⟩
  let e := MonoidHom.ofInjective (triEmb_injective (K := K₄) (σ := σ₄) (L := L))
  refine ⟨(e.symm : (triEmb K₄ σ₄ L).range →* _).comp
    ((d4MinusPsi σ L g₀).codRestrict _ hrange), ?_, fun y => ?_⟩
  · intro a b hab
    have h1 := e.symm.injective hab
    have h2 : d4MinusPsi σ L g₀ a = d4MinusPsi σ L g₀ b := congrArg Subtype.val h1
    exact d4MinusPsi_injective g₀ h2
  · have h1 := e.apply_symm_apply ⟨d4MinusPsi σ L g₀ y, hrange y⟩
    exact congrArg Subtype.val h1

end Transport

section TransportII

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L : Type}
  [Field L] [CharP L p] [Algebra K L] {K₄ : Type} [Field K₄] [Finite K₄] [Algebra K₄ L]
  {σ₄ ε : K₄ ≃+* K₄}

omit [Finite K] in
theorem un_tau_fixed_iff [IsAlgClosure K L] (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hσ₄ : ∀ c, σ₄ c = c ^ p ^ (4 * f)) (hε : ∀ c, ε c = c ^ p ^ (9 * f))
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L)
    {ψ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom}
    (hψ₄ : ∀ y, triEmb K₄ σ₄ L (ψ₄ y) = d4MinusPsi σ L g₀ y)
    (y₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom) :
    unTau σ₄ ε y₄ = y₄ ↔ y₄ ∈ Set.range ψ₄ := by
  have hmem := fun x => d4MinusPsi_mem_range_iff (K := K) (σ := σ) hp hf hK hσ
    (iterateFrobenius L p f) (fun c => rfl) hg₀C hg₀ x
  constructor
  · intro h
    have h1 := un_triEmb_tau (L := L) (f := f) hσ₄ hε y₄
    rw [h] at h1
    have hx : triEmb K₄ σ₄ L y₄ ∈ (d4MinusPsi σ L g₀).range :=
      (hmem _).2 ⟨triEmb_mem_adjointGroup y₄, h1.symm⟩
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, triEmb_injective (K := K₄) (σ := σ₄) (L := L) ?_⟩
    rw [hψ₄, hy]
  · rintro ⟨y, rfl⟩
    refine triEmb_injective (K := K₄) (σ := σ₄) (L := L) ?_
    rw [un_triEmb_tau hσ₄ hε, hψ₄]
    exact ((hmem _).1 ⟨y, rfl⟩).2

end TransportII

section TransportIII

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L : Type}
  [Field L] [CharP L p] [Algebra K L] {K₄ : Type} [Field K₄] [Finite K₄] [Algebra K₄ L]
  {σ₄ : K₄ ≃+* K₄}

theorem un_psi4_phi (hσ : ∀ c, σ c = c ^ (p ^ f)) (hσ₄ : ∀ c, σ₄ c = c ^ p ^ (4 * f))
    {g₀ : ModGL TwistTag.D4.tag L}
    (hP : diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L)
    {ψ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom}
    (hψ₄ : ∀ y, triEmb K₄ σ₄ L (ψ₄ y) = d4MinusPsi σ L g₀ y)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : triEmb K₄ σ₄ L s₄ = d4MinusPsi σ L g₀ s)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ψ₄ ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y) =
      (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (ψ₄ y) := by
  have hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L p f).comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, iterateFrobenius_def, map_pow]
  have hcomm4 : (algebraMap K₄ L).comp σ₄.toRingHom =
      (iterateFrobenius L p (4 * f)).comp (algebraMap K₄ L) :=
    RingHom.ext fun c => by simp [hσ₄, iterateFrobenius_def, map_pow]
  refine triEmb_injective (K := K₄) (σ := σ₄) (L := L) ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hψ₄, hs₄,
    triEmb_fieldActor (iterateFrobenius L p (4 * f)) hcomm4]
  rw [d4MinusPsi_fieldActor (iterateFrobenius L p f) hcomm hP]

end TransportIII

section Diag

variable {L : Type} [Field L] {K₄ : Type} [Field K₄] [Algebra K₄ L]

theorem un_diag_matrix [Finite K₄] (σ₄ : K₄ ≃+* K₄) (b₄ : K₄ˣ) (b : Lˣ)
    (hb : (b : L) = algebraMap K₄ L b₄) (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : triEmb K₄ σ₄ L s₄ = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b₄, 1] := by
  refine baseChangeGL_injective (algebraMap K₄ L) ?_
  rw [← triEmb_apply (σ := σ₄), hs₄]
  refine Eq.trans ?_ (baseChangeGL_rootDiagUnit (algebraMap K₄ L) (τ := TwistTag.D4.tag)
    ![1, 1, b₄, 1]).symm
  congr 1
  funext i
  fin_cases i
  · simp
  · simp
  · exact Units.ext hb
  · simp

end Diag

section Frame

theorem pow_twelve_mod_three {p f : ℕ} (hq : (p ^ f) % 3 = 2) : (p ^ (12 * f)) % 3 = 1 := by
  have : p ^ (12 * f) = (p ^ f) ^ 12 := by rw [← pow_mul, mul_comm]
  rw [this, Nat.pow_mod, hq]

theorem un_frame {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hs : D4MinusToral p f hp K σ s) :
    ∃ (K₄ : Type) (_ : Field K₄) (_ : Finite K₄) (_ : CharP K₄ p)
      (_ : Nat.card K₄ = ((p ^ f) ^ 4) ^ 3) (σ₄ ε : K₄ ≃+* K₄) (_ : ∀ c, σ₄ c = c ^ ((p ^ f) ^ 4))
      (_ : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) (b : K₄ˣ) (_ : b ^ 3 = 1) (_ : b ≠ 1)
      (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
      (_ : (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1])
      (ψ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom),
      Function.Injective ψ₄ ∧
      (∀ y, ψ₄ ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y) =
        (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (ψ₄ y)) ∧
      (∀ y₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom,
        unTau σ₄ ε y₄ = y₄ ↔ y₄ ∈ Set.range ψ₄) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, hKL, hAC, hCh, g₀, b, hframe, hb3, hb1, hsb⟩ := hs
  obtain ⟨hg₀C, hP, hFg₀⟩ := hframe
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have h12 : 1 ≤ 12 * f := by omega
  have hKp : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨K₄, hF₄, hfin, hAlg₄, hAC₄, hCh₄, hK₄', hrange⟩ :=
    exists_subfield_isAlgClosure p L (K := K) (m := 3 * f) (n := 12 * f) h12 hKp ⟨4, by ring⟩
  have hK₄ : Nat.card K₄ = (p ^ (4 * f)) ^ 3 := by
    rw [hK₄', ← pow_mul]
    ring_nf
  let σ₄ : K₄ ≃+* K₄ := iterateFrobeniusEquiv K₄ p (4 * f)
  let ε : K₄ ≃+* K₄ := iterateFrobeniusEquiv K₄ p (9 * f)
  have hσ₄ : ∀ c, σ₄ c = c ^ p ^ (4 * f) := fun c => rfl
  have hε : ∀ c, ε c = c ^ p ^ (9 * f) := fun c => rfl
  have hbN : ((b : Lˣ) : L) ^ p ^ (12 * f) = (b : L) := by
    have h3 : (b : Lˣ) ^ 3 = 1 := hb3
    have hN := pow_twelve_mod_three hq
    obtain ⟨k, hk⟩ : ∃ k, p ^ (12 * f) = 3 * k + 1 := ⟨p ^ (12 * f) / 3, by omega⟩
    have : (b : Lˣ) ^ p ^ (12 * f) = b := by
      rw [hk, pow_succ, pow_mul, h3, one_pow, one_mul]
    exact congrArg (fun u : Lˣ => (u : L)) this
  obtain ⟨c, hc⟩ := hrange _ hbN
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact b.ne_zero hc.symm
  let b₄ : K₄ˣ := Units.mk0 c hc0
  have hb₄ : ((b : Lˣ) : L) = algebraMap K₄ L (b₄ : K₄) := hc.symm
  obtain ⟨ψ₄, hinj, hψ₄⟩ := un_exists_psi4 (K := K) (σ := σ) (K₄ := K₄)
    (σ₄ := σ₄) hp hf hK hσ hK₄ hσ₄ hg₀C hFg₀
  have hψs : triEmb K₄ σ₄ L (ψ₄ s) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] := by
    rw [hψ₄, d4MinusPsi_apply, hsb]
    group
  have hexp : ∀ n : ℕ, (p ^ f) ^ n = p ^ (n * f) := fun n => by rw [← pow_mul, mul_comm]
  refine ⟨K₄, hF₄, hfin, hCh₄, ?_, σ₄, ε, ?_, ?_, b₄, ?_, ?_, ψ₄ s,
    un_diag_matrix σ₄ b₄ b hb₄ (ψ₄ s) hψs, ψ₄, hinj, ?_, ?_⟩
  · rw [hK₄, hexp 4, mul_comm]
  · intro c; rw [hσ₄, hexp 4, mul_comm]
  · intro c; rw [hε, hexp 9, mul_comm]
  · have h3 : ((b₄ ^ 3 : K₄ˣ) : K₄) = 1 := by
      apply (algebraMap K₄ L).injective
      simpa [← hb₄] using congrArg (fun u : Lˣ => (u : L)) hb3
    exact Units.ext h3
  · intro h1
    apply hb1
    refine Units.ext ?_
    have := congrArg (fun u : K₄ˣ => algebraMap K₄ L (u : K₄)) h1
    simpa [← hb₄] using this
  · intro y
    exact un_psi4_phi hσ hσ₄ hP hψ₄ s (ψ₄ s) (hψ₄ s) y
  · intro y₄
    exact un_tau_fixed_iff hp hf hK hσ hσ₄ hε hg₀C hFg₀ hψ₄ y₄

end Frame

end CFSG.GH74.GLS.Stage2.Bender.Thm1
