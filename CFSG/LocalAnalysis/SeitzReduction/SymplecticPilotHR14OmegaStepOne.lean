module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaO2Even
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueReduce
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace two_mul_finrank_commSpace_le mem_omegaGroup
  exists_map_ne_zero)

section Omega

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem involutionO2_omega_of_odd [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {N : ℕ} (hN : Odd N)
    (hdim : finrank K V = 2 * N) :
    InvolutionO2 ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  intro s hss
  have hev : Even (finrank K (omegaInvSpace (s : V ≃ₗ[K] V))) :=
    (mem_omegaGroup.1 (omega_le_omegaGroup hQ s.2)).2
  have hle : 2 * finrank K (omegaInvSpace (s : V ≃ₗ[K] V)) ≤ finrank K V :=
    two_mul_finrank_commSpace_le (congrArg Subtype.val hss)
  refine mem_closure_odd_centralizer_of_mem_omega hK hQ s hss ?_
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    rw [hdim] at h
    have hlN : finrank K (omegaInvSpace (s : V ≃ₗ[K] V)) = N := by omega
    rw [hlN] at hev
    exact Nat.not_even_iff_odd.2 hN hev

end Omega

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def statedOmegaEquivOmega (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

theorem omegaInv_statedScalars_subgroupOf_eq_bot [CharP K 2] (hQ : ⇑Q = Q₀)
    (hne : ∃ v, Q₀ v ≠ 0) : (StatedScalars ι K).subgroupOf (StatedOmega Q₀) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_subgroupOf, mem_statedScalars_iff, mem_scalars] at hA
  obtain ⟨c, hc⟩ := hA
  have hAO : toLinEquiv ι K (A : GL ι K) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have h1 : (A : GL ι K) ∈ (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap (toLinEquiv ι K).toMonoidHom :=
      statedOmega_eq_comap hQ ▸ A.2
    exact omega_le_orthogonalGroup (Subgroup.mem_comap.1 h1)
  obtain ⟨v, hv⟩ := hne
  have h2 := map_of_mem hAO v
  rw [hc, map_smul_eq_sq, hQ] at h2
  have hc1 : c ^ 2 = 1 := by
    have e : (c ^ 2 - 1) * Q₀ v = 0 := by linear_combination h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hv)
  have hc' : c = 1 := by
    have e : (c - 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hc1 + (1 - c) * h2'
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply (toLinEquiv ι K).injective
  refine LinearEquiv.ext fun w => ?_
  rw [hc, hc', one_smul, Subgroup.coe_one, map_one]
  rfl

@[expose] noncomputable def statedProjOmegaEquiv [CharP K 2] (hQ : ⇑Q = Q₀)
    (hne : ∃ v, Q₀ v ≠ 0) : StatedProj (StatedOmega Q₀) ≃* StatedOmega Q₀ :=
  (QuotientGroup.quotientMulEquivOfEq
    (omegaInv_statedScalars_subgroupOf_eq_bot hQ hne)).trans QuotientGroup.quotientBot

theorem involutionO2_statedProj_of_odd [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hQ : ⇑Q = Q₀) (hnd : (polarBilin Q).Nondegenerate) [Nontrivial (ι → K)] {N : ℕ}
    (hN : Odd N) (hdim : Fintype.card ι = 2 * N) :
    InvolutionO2 (StatedProj (StatedOmega Q₀)) := by
  have hne : ∃ v, Q₀ v ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_map_ne_zero hnd
    exact ⟨a, by rwa [← hQ]⟩
  have h := involutionO2_omega_of_odd hK hnd hN (by rw [Module.finrank_fintype_fun_eq_card, hdim])
  exact h.of_mulEquiv ((statedProjOmegaEquiv hQ hne).trans (statedOmegaEquivOmega hQ)).symm

end Matrix

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem involutionO2_statedProj_plus (hK : 4 ≤ Nat.card K) {N : ℕ} (hN : Odd N) :
    InvolutionO2 (StatedProj (StatedOmega (StatedQuadPlus N K))) := by
  have hN0 : 0 < N := hN.pos
  have : Nontrivial (Fin N ⊕ Fin N → K) := by
    have : Nonempty (Fin N ⊕ Fin N) := ⟨Sum.inl ⟨0, hN0⟩⟩
    infer_instance
  exact involutionO2_statedProj_of_odd hK (CFSG.LieType.Universal.Spin.coe_quadPlus N K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus N K) hN
    (by rw [Fintype.card_sum, Fintype.card_fin]; ring)

theorem involutionO2_statedProj_minus (hK : 4 ≤ Nat.card K) {N : ℕ} (hN : Odd N) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    InvolutionO2 (StatedProj (StatedOmega (StatedQuadMinus N K b c))) := by
  have hN0 : 0 < N := hN.pos
  have : Nontrivial (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2 → K) := by
    have : Nonempty (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    infer_instance
  exact involutionO2_statedProj_of_odd hK (CFSG.LieType.Universal.Spin.coe_quadMinus N K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite N K hirr) hN
    (by rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; omega)

end Models

section LieModel

theorem charP_two_and_four_le_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) : CharP K 2 ∧ 4 ≤ Nat.card K := by
  have := Fintype.ofFinite K
  refine ⟨charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card]), ?_⟩
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem involutionO2_of_lieModel_POmega {G : Type} [Group G] {τ : StatedLieTag}
    (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) {N f : ℕ} (hN : Odd N) (hf : 2 ≤ f)
    (hG : CFSG.Blueprint.LieModel G τ N 2 f) : InvolutionO2 G := by
  obtain ⟨-, hcl⟩ | ⟨hN0, -⟩ | ⟨hN0, -⟩ | ⟨hN0, -⟩ := hG
  · rcases hτ with rfl | rfl
    · obtain ⟨-, K, _, _, hcard, ⟨φ⟩⟩ := hcl
      obtain ⟨hc, hK4⟩ := charP_two_and_four_le_of_card hcard hf
      exact (involutionO2_statedProj_plus hK4 hN).of_mulEquiv φ.symm
    · obtain ⟨-, K, _, _, hcard, b, c, hirr, ⟨φ⟩⟩ := hcl
      obtain ⟨hc, hK4⟩ := charP_two_and_four_le_of_card hcard hf
      exact (involutionO2_statedProj_minus hK4 hN hirr).of_mulEquiv φ.symm
  all_goals exact absurd hN0 hN.pos.ne'

end LieModel

section Step1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem not_mem_range_conj_of_even (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hnev : Even n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
      (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range := by
  have hO2 : InvolutionO2 (spGlobal e) := by
    rcases hκ with rfl | rfl
    · have hty := hglob.1
      simp only [Sp2mKindType] at hty
      exact involutionO2_of_lieModel_POmega (Or.inl rfl) (Even.add_one hnev) hf hty
    · have hty := hglob.1
      simp only [Sp2mKindType] at hty
      exact involutionO2_of_lieModel_POmega (Or.inr rfl) (Even.add_one hnev) hf hty
  exact not_mem_range_conj_of_conj_mem_normalizer hset hn hKc hf e ht hKt hκ hglob hO2 g hg

@[expose] def SpOmegaStepOneOddInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Odd n →
    Nat.card K = 2 ^ f → 2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
        (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
          (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range

theorem spOmegaStepOneInput_of_odd {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (h : SpOmegaStepOneOddInput κ) : SpOmegaStepOneInput κ := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob g hg
  rcases Nat.even_or_odd n with hev | hodd
  · exact not_mem_range_conj_of_even hset (by omega) hev hKc hf e ht hKt hκ hglob g hg
  · exact h G L hset n f K hn hodd hKc hf e t ht hKt hroot hglob g hg

end Step1

end CFSG.SeitzReduction.SymplecticPilot
