module

public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaConst
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Balance.BootstrapDelta

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (IsElemAbelian signalizerFunctorEk)
open scoped commutatorElement

section Statement

variable {K X : Type*} [Group K] [Group X]

@[expose] def ToralAction (ψ : K →* X) (F : Subgroup X) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F, ∃ x ∈ P, ∀ y : K, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)

theorem ToralAction.mono {ψ : K →* X} {F F' : Subgroup X} (h : ToralAction ψ F) (hle : F' ≤ F) :
    ToralAction ψ F' := by
  obtain ⟨P, hP, hact⟩ := h
  exact ⟨P, hP, fun f hf => hact f (hle hf)⟩

@[expose] def StrongConclusion (L F : Subgroup X) : Prop :=
  (∀ d ∈ deltaCore F, ∀ x ∈ L, d * x = x * d) ∧
    ∀ f ∈ F, f ≠ 1 → ∀ d ∈ involutionOddCore f, ∀ g ∈ F, ∀ x ∈ L,
      d * g * x * (d * g)⁻¹ = g * d * x * (g * d)⁻¹

end Statement

@[expose] def StrongLocalTwoBalanceToralOn (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralAction ψ F → StrongConclusion ψ.range F

theorem StrongLocalTwoBalanceToralOn.mono {t : StatedLieTag} {Q Q' : ℕ → ℕ → ℕ → Prop}
    (h : StrongLocalTwoBalanceToralOn t Q) (hQ : ∀ n p e, Q' n p e → Q n p e) :
    StrongLocalTwoBalanceToralOn t Q' := fun n p e hp hq => h n p e hp (hQ n p e hq)

@[expose] def StrongLocalTwoBalanceToralAt (t : StatedLieTag) : Prop :=
  StrongLocalTwoBalanceToralOn t fun _ _ _ => True

@[expose] def StrongLocalTwoBalanceToral : Prop :=
  ∀ t : StatedLieTag, StrongLocalTwoBalanceToralAt t

theorem strongLocalTwoBalanceToral_of_tags
    (h : ∀ t : StatedLieTag, IsFundTag t → StrongLocalTwoBalanceToralAt t) :
    StrongLocalTwoBalanceToral := fun t =>
  fun n p e hp hq hfund => h t hfund n p e hp hq hfund

section Aux

variable {K : Type*} [Group K]

theorem aux_central_commutator (c₁ c₂ g₁ g₂ : K) (h1 : ∀ x, x * c₁ = c₁ * x)
    (h2 : ∀ x, x * c₂ = c₂ * x) :
    (c₁ * g₁) * (c₂ * g₂) * (c₁ * g₁)⁻¹ * (c₂ * g₂)⁻¹ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
  have f1 : c₁ * g₁ * c₂ * g₂ = c₁ * c₂ * (g₁ * g₂) := by
    rw [mul_assoc c₁ g₁ c₂, h2 g₁]; group
  have f2 : c₂ * g₂ * c₁ * g₁ = c₁ * c₂ * (g₂ * g₁) := by
    rw [mul_assoc c₂ g₂ c₁, h1 g₂, ← mul_assoc c₂ c₁, h1 c₂]; group
  have hu : ∀ x, (c₁ * c₂) * x * (c₁ * c₂)⁻¹ = x := fun x => by
    have : x * (c₁ * c₂) = (c₁ * c₂) * x := by
      rw [← mul_assoc, h1 x, mul_assoc, h2 x, mul_assoc]
    rw [← this, mul_inv_cancel_right]
  calc (c₁ * g₁) * (c₂ * g₂) * (c₁ * g₁)⁻¹ * (c₂ * g₂)⁻¹
      = (c₁ * g₁ * c₂ * g₂) * (c₂ * g₂ * c₁ * g₁)⁻¹ := by group
    _ = (c₁ * c₂ * (g₁ * g₂)) * (c₁ * c₂ * (g₂ * g₁))⁻¹ := by rw [f1, f2]
    _ = (c₁ * c₂) * ((g₁ * g₂) * (g₂ * g₁)⁻¹) * (c₁ * c₂)⁻¹ := by group
    _ = (g₁ * g₂) * (g₂ * g₁)⁻¹ := hu _
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by group

theorem commute_of_perfect_of_commutator_mem_center {r : K} {R : Subgroup K} (hR : R ≤ ⁅R, R⁆)
    (h : ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center K) : ∀ s ∈ R, r * s = s * r := by
  have hC : ⁅R, R⁆ ≤ Subgroup.centralizer ({r} : Set K) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    obtain ⟨c₁, hc₁⟩ : ∃ c, c = r * g₁ * r⁻¹ * g₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c, c = r * g₂ * r⁻¹ * g₂⁻¹ := ⟨_, rfl⟩
    have h1 : ∀ x, x * c₁ = c₁ * x := hc₁ ▸ Subgroup.mem_center_iff.mp (h g₁ hg₁)
    have h2 : ∀ x, x * c₂ = c₂ * x := hc₂ ▸ Subgroup.mem_center_iff.mp (h g₂ hg₂)
    have e1 : r * g₁ * r⁻¹ = c₁ * g₁ := by rw [hc₁]; simp
    have e2 : r * g₂ * r⁻¹ = c₂ * g₂ := by rw [hc₂]; simp
    have e3 : r * g₁⁻¹ * r⁻¹ = (c₁ * g₁)⁻¹ := by rw [← e1]; group
    have e4 : r * g₂⁻¹ * r⁻¹ = (c₂ * g₂)⁻¹ := by rw [← e2]; group
    have key : r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r⁻¹ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
      calc r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r⁻¹
          = (r * g₁ * r⁻¹) * (r * g₂ * r⁻¹) * (r * g₁⁻¹ * r⁻¹) * (r * g₂⁻¹ * r⁻¹) := by group
        _ = (c₁ * g₁) * (c₂ * g₂) * (c₁ * g₁)⁻¹ * (c₂ * g₂)⁻¹ := by rw [e1, e2, e3, e4]
        _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := aux_central_commutator _ _ _ _ h1 h2
    have h3 : r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r := by
      have := congrArg (· * r) key
      simpa [mul_assoc] using this
    exact h3.symm
  intro s hs
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC (hR hs))).symm

end Aux

section Frame

theorem exists_commuting_generators_of_frameGroup (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {X : Type} [Group X]
    (ψ : (modelUniv t n p e hp).K →* X) (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K)
    (𝓜 : Set (Subgroup X))
    (h𝓜 : ∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, M = R.map ψ)
    (hcomm : ∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x)
    {F : Subgroup X}
    (hact : ∀ f ∈ F, ∃ x ∈ frameGroup 𝓜, ∀ y ∈ ψ.range, f * y * f⁻¹ = x * y * x⁻¹) :
    ∃ S : Set (modelUniv t n p e hp).K, (∀ r ∈ S, ∀ r' ∈ S, r * r' = r' * r) ∧
      (∀ r ∈ S, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, r ∈ R ∧
        ∀ s ∈ R, r * s = s * r) ∧
      ∀ f ∈ F, ∃ x ∈ Subgroup.closure S, ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  have hperf := CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p e hp2 hfund hadm
    (by omega)
  let 𝓡 : Set (modelUniv t n p e hp).K := {r | ∃ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t
    (modelUniv t n p e hp).D, M = R.map ψ ∧ r ∈ R ∧ ∀ s ∈ M, s * ψ r = ψ r * s}
  have hcommR : ∀ r ∈ 𝓡, ∀ (M' : Subgroup X) (R' : Subgroup (modelUniv t n p e hp).K),
      M' ∈ 𝓜 → R' ∈ fundamentalSubgroups t (modelUniv t n p e hp).D → M' = R'.map ψ →
        ∀ s ∈ R', r * s = s * r := by
    rintro r ⟨M, hM, R, hR, rfl, hr, hrc⟩ M' R' hM' hR' hMR'
    have hs : ∀ s ∈ R', ψ r * ψ s = ψ s * ψ r := by
      intro s hs
      have hψs : ψ s ∈ M' := hMR' ▸ ⟨s, hs, rfl⟩
      have hψr : ψ r ∈ R.map ψ := ⟨r, hr, rfl⟩
      by_cases hMM : R.map ψ = M'
      · rw [← hMM] at hψs
        exact (hrc _ hψs).symm
      · exact hcomm _ hM M' hM' hMM _ hψr _ hψs
    refine commute_of_perfect_of_commutator_mem_center (hperf R' hR') ?_
    intro s hsR
    refine hker ?_
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hs s hsR]
    group
  have hlift_comm : ∀ r ∈ 𝓡, ∀ r' ∈ 𝓡, r * r' = r' * r := by
    intro r hr r' hr'
    obtain ⟨M', hM', R', hR', hMR', hr'R', -⟩ := hr'
    exact hcommR r hr M' R' hM' hR' hMR' r' hr'R'
  have hlift : ∀ x ∈ frameGroup 𝓜, ∃ x' ∈ Subgroup.closure 𝓡, ψ x' = x := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ x' ∈ Subgroup.closure 𝓡, ψ x' = x) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨M, hM, hzM, -, -, hzc⟩
      obtain ⟨R, hR, rfl⟩ := h𝓜 M hM
      obtain ⟨r, hr, hrz⟩ := hzM
      refine ⟨r, Subgroup.subset_closure ⟨R.map ψ, hM, R, hR, rfl, hr, ?_⟩, hrz⟩
      rw [hrz]
      exact hzc
    · exact ⟨1, Subgroup.one_mem _, map_one ψ⟩
    · rintro a b - - ⟨a', ha', rfl⟩ ⟨b', hb', rfl⟩
      exact ⟨a' * b', Subgroup.mul_mem _ ha' hb', map_mul ψ a' b'⟩
    · rintro a - ⟨a', ha', rfl⟩
      exact ⟨a'⁻¹, Subgroup.inv_mem _ ha', map_inv ψ a'⟩
  refine ⟨𝓡, hlift_comm, ?_, fun f hf => ?_⟩
  · intro r hrmem
    obtain ⟨M, hM, R, hR, hMR, hr, -⟩ := id hrmem
    exact ⟨R, hR, hr, hcommR r hrmem M R hM hR hMR⟩
  · obtain ⟨x, hx, hxy⟩ := hact f hf
    obtain ⟨x', hx'P, rfl⟩ := hlift x hx
    refine ⟨x', hx'P, fun y => ?_⟩
    have := hxy (ψ y) ⟨y, rfl⟩
    rw [this, map_mul, map_mul, map_inv]

theorem toralAction_of_frameGroup (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {X : Type} [Group X]
    (ψ : (modelUniv t n p e hp).K →* X) (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K)
    (𝓜 : Set (Subgroup X))
    (h𝓜 : ∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, M = R.map ψ)
    (hcomm : ∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x)
    {F : Subgroup X}
    (hact : ∀ f ∈ F, ∃ x ∈ frameGroup 𝓜, ∀ y ∈ ψ.range, f * y * f⁻¹ = x * y * x⁻¹) :
    ToralAction ψ F := by
  obtain ⟨S, hS, -, hlift⟩ := exists_commuting_generators_of_frameGroup t n p e hp hfund hadm hp2
    h5 ψ hker 𝓜 h𝓜 hcomm hact
  have hpair : S.Pairwise Commute := fun r hr r' hr' _ => hS r hr r' hr'
  have := Subgroup.isMulCommutative_closure hpair
  refine ⟨Subgroup.closure S, fun x hx y hy => ?_, hlift⟩
  exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)

theorem exists_involutory_lifts_of_frameGroup (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {X : Type} [Group X]
    (ψ : (modelUniv t n p e hp).K →* X) (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K)
    (𝓜 : Set (Subgroup X))
    (h𝓜 : ∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, M = R.map ψ)
    (hcomm : ∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x)
    (hsq : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, ∀ r ∈ R,
      (∀ s ∈ R, r * s = s * r) → r * r = 1)
    {F : Subgroup X}
    (hact : ∀ f ∈ F, ∃ x ∈ frameGroup 𝓜, ∀ y ∈ ψ.range, f * y * f⁻¹ = x * y * x⁻¹) :
    ∃ P : Subgroup (modelUniv t n p e hp).K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      (∀ x ∈ P, x * x = 1) ∧
      ∀ f ∈ F, ∃ x ∈ P, ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹) := by
  obtain ⟨S, hS, hSR, hlift⟩ := exists_commuting_generators_of_frameGroup t n p e hp hfund hadm
    hp2 h5 ψ hker 𝓜 h𝓜 hcomm hact
  have hpair : S.Pairwise Commute := fun r hr r' hr' _ => hS r hr r' hr'
  have hc := Subgroup.isMulCommutative_closure hpair
  have hPc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hc.is_comm.comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
  refine ⟨Subgroup.closure S, hPc, ?_, hlift⟩
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x * x = 1) ?_ ?_ ?_ ?_ hx
  · intro r hr
    obtain ⟨R, hR, hrR, hrc⟩ := hSR r hr
    exact hsq R hR r hrR hrc
  · exact mul_one 1
  · intro a b ha hb hha hhb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hPc b hb a ha]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hha, hhb, mul_one]
  · intro a ha hha
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [hha, inv_one]

end Frame

@[expose] def StrongLocalTwoBalanceFrameOn (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ 𝓜 : Set (Subgroup X),
        (∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, M = R.map ψ) →
        (∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x) →
        ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
          (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
          (∀ f ∈ F, ∃ x ∈ frameGroup 𝓜, ∀ y ∈ ψ.range, f * y * f⁻¹ = x * y * x⁻¹) →
            StrongConclusion ψ.range F

@[expose] def StrongLocalTwoBalanceFrameAt (t : StatedLieTag) : Prop :=
  StrongLocalTwoBalanceFrameOn t fun _ _ _ => True

theorem strongLocalTwoBalanceFrameOn_of_toral {t : StatedLieTag} {Q : ℕ → ℕ → ℕ → Prop}
    (h : StrongLocalTwoBalanceToralOn t Q) : StrongLocalTwoBalanceFrameOn t Q := by
  intro n p e hp hq hfund hadm hp2 h5 X _ _ ψ hker hnorm 𝓜 h𝓜 hcomm F hcard hF2 hfaith hact
  exact h n p e hp hq hfund hadm hp2 h5 X ψ hker hnorm F hcard hF2 hfaith
    (toralAction_of_frameGroup t n p e hp hfund hadm hp2 h5 ψ hker 𝓜 h𝓜 hcomm hact)

section ModelLevel

variable {X : Type} [Group X] [Finite X]

theorem odd_orderOf_of_mem_involutionOddCore {f d : X} (hd : d ∈ involutionOddCore f) :
    Odd (orderOf d) :=
  (odd_card_oddCoreIn (Subgroup.centralizer ({f} : Set X))).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hd)

theorem deltaCore_eq_bot_of_commutes {L F : Subgroup X}
    (hC : ∀ x : X, (∀ y ∈ L, x * y = y * x) → Odd (orderOf x) → x = 1)
    (hF : ∃ f ∈ F, f ≠ 1) (h : ∀ d ∈ deltaCore F, ∀ x ∈ L, d * x = x * d) :
    deltaCore F = ⊥ := by
  obtain ⟨f, hf, hf1⟩ := hF
  refine (Subgroup.eq_bot_iff_forall _).2 fun d hd => hC d (h d hd) ?_
  exact odd_orderOf_of_mem_involutionOddCore (deltaCore_le_involutionOddCore hf hf1 hd)

theorem stronglyBalanced_of_strongConclusion {L A : Subgroup X} (hA : IsElemAbelian 2 A)
    (hC : ∀ x : X, (∀ y ∈ L, x * y = y * x) → Odd (orderOf x) → x = 1)
    (h : ∀ F ∈ signalizerFunctorEk 2 2 A, StrongConclusion L F) :
    StronglyBalanced A ∧ ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hΔ : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := fun F hF =>
    deltaCore_eq_bot_of_commutes hC (exists_ne_one_of_card_eq_two_pow (by norm_num) hF.2)
      (h F hF).1
  refine ⟨fun a ha ha1 d hd => ?_, hΔ⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hg1 : g = 1
  · simp [hg1]
  by_cases hga : g = a
  · subst hga
    exact (Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer g hd)).symm
  have hcard : Nat.card (Subgroup.closure ({a, g} : Set X)) = 4 :=
    card_closure_pair_eq_four (hA2 a ha) (hA2 g hg) ha1 hg1 (Ne.symm hga) (hcomm a ha g hg)
  have hFA : Subgroup.closure ({a, g} : Set X) ≤ A := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [ha, hg]
  have hF : Subgroup.closure ({a, g} : Set X) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hcard]; norm_num⟩
  have haF : a ∈ Subgroup.closure ({a, g} : Set X) := Subgroup.subset_closure (by simp)
  have hgF : g ∈ Subgroup.closure ({a, g} : Set X) := Subgroup.subset_closure (by simp)
  have e := (h _ hF).2 a haF ha1 d hd g hgF
  have hcx : ∀ x ∈ L, ((g * d)⁻¹ * (d * g)) * x = x * ((g * d)⁻¹ * (d * g)) := by
    intro x hx
    have hx' : ((g * d)⁻¹ * (d * g)) * x * ((g * d)⁻¹ * (d * g))⁻¹ = x := by
      calc ((g * d)⁻¹ * (d * g)) * x * ((g * d)⁻¹ * (d * g))⁻¹
          = (g * d)⁻¹ * (d * g * x * (d * g)⁻¹) * (g * d) := by group
        _ = (g * d)⁻¹ * (g * d * x * (g * d)⁻¹) * (g * d) := by rw [e x hx]
        _ = x := by group
    exact mul_inv_eq_iff_eq_mul.mp hx'
  have hga' : g⁻¹ ∈ Subgroup.centralizer ({a} : Set X) :=
    Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm g hg a ha))
  have hmem : (g * d)⁻¹ * (d * g) ∈ involutionOddCore a := by
    have h1 : g⁻¹ * d * g⁻¹⁻¹ ∈ involutionOddCore a := conj_mem_oddCoreIn hga' hd
    have h2 : (g * d)⁻¹ * (d * g) = d⁻¹ * (g⁻¹ * d * g⁻¹⁻¹) := by group
    rw [h2]
    exact (involutionOddCore a).mul_mem ((involutionOddCore a).inv_mem hd) h1
  have h1 := hC _ hcx (odd_orderOf_of_mem_involutionOddCore hmem)
  have h2 : d * g = g * d := by
    have := congrArg (g * d * ·) h1
    simpa [mul_assoc] using this
  exact h2.symm

theorem rankThreeBalance_of_strongConclusion {L A : Subgroup X} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8)
    (hC : ∀ x : X, (∀ y ∈ L, x * y = y * x) → Odd (orderOf x) → x = 1)
    (h : ∀ F ∈ signalizerFunctorEk 2 2 A, StrongConclusion L F) : RankThreeBalance A := by
  obtain ⟨hSB, hΔ⟩ := stronglyBalanced_of_strongConclusion hA hC h
  refine ⟨hA, hcard, ?_, ?_⟩
  · intro a ha ha1 b hb hb1
    have : ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (inf_le_left.trans (hSB a ha ha1))
    rw [this]
    exact bot_le
  · intro F hF a ha ha1
    rw [hΔ F hF]
    exact inf_le_left.trans bot_le

end ModelLevel

end CFSG.ClassicalInvolution.Balance.StrongBalance
