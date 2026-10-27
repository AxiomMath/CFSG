module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowO2
public import CFSG.Blueprint.SourceQuadraticClassification
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOne
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions (exists_map_ne_zero)

theorem exists_mulEquiv_omega_of_lieModel_two {G : Type} [Group G] {τ : StatedLieTag}
    (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) {N : ℕ} (hG : LieModel G τ N 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V),
      Nat.card F = 2 ∧ (polarBilin Q).Nondegenerate ∧ finrank F V = 2 * N ∧
        (τ = .POmegaMinus → ∀ T : Submodule F V, (∀ x ∈ T, Q x = 0) →
          2 * finrank F T + 2 ≤ finrank F V) ∧
        Nonempty (G ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  obtain ⟨-, hcl⟩ | ⟨hN0, hτ'⟩ | ⟨hN0, hτ'⟩ | ⟨hN0, hτ'⟩ := hG
  · rcases hτ with rfl | rfl
    · obtain ⟨⟨-, -, hN4⟩, F, _, _, hcard, ⟨φ⟩⟩ := hcl
      have hc : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hcard
      have : Nontrivial (Fin N ⊕ Fin N → F) := by
        have : Nonempty (Fin N ⊕ Fin N) := ⟨Sum.inl ⟨0, by omega⟩⟩
        infer_instance
      have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus N F
      have hQ := CFSG.LieType.Universal.Spin.coe_quadPlus N F
      have hne : ∃ v, StatedQuadPlus N F v ≠ 0 := by
        obtain ⟨a, ha⟩ := exists_map_ne_zero hnd
        exact ⟨a, by rwa [← hQ]⟩
      refine ⟨F, inferInstance, inferInstance, hc, _, inferInstance, inferInstance, inferInstance,
        CFSG.LieType.Universal.Spin.quadPlus N F, by rw [hcard, pow_one], hnd, ?_,
        (fun h => by cases h),
        ⟨φ.trans ((statedProjOmegaEquiv hQ hne).trans (statedOmegaEquivOmega hQ))⟩⟩
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    · obtain ⟨⟨-, -, hN4⟩, F, _, _, hcard, b, c, hirr, ⟨φ⟩⟩ := hcl
      have hc : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hcard
      have : Nontrivial (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2 → F) := by
        have : Nonempty (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
        infer_instance
      have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite N F hirr
      have hQ := CFSG.LieType.Universal.Spin.coe_quadMinus N F b c
      have hne : ∃ v, StatedQuadMinus N F b c v ≠ 0 := by
        obtain ⟨a, ha⟩ := exists_map_ne_zero hnd
        exact ⟨a, by rwa [← hQ]⟩
      have hdim : finrank F (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2 → F) = 2 * N := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]
        omega
      refine ⟨F, inferInstance, inferInstance, hc, _, inferInstance, inferInstance, inferInstance,
        CFSG.LieType.Universal.Spin.quadMinus N F b c, by rw [hcard, pow_one], hnd, hdim,
        fun _ T hT => ?_,
        ⟨φ.trans ((statedProjOmegaEquiv hQ hne).trans (statedOmegaEquivOmega hQ))⟩⟩
      have h1 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (StatedQuadMinus N F b c) (W := T)
        fun x hx => by rw [← hQ]; exact hT x hx
      rw [CFSG.Blueprint.EvenSource.sourceWittIndex_statedQuadMinus N F (by omega) hirr] at h1
      rw [hdim]
      omega
  all_goals rcases hτ with rfl | rfl <;> simp_all [CFSG.Blueprint.chevalleyExceptionalTags,
    CFSG.Blueprint.reeTitsTags]

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem nsGlobal_inf_centralizer_eq_bot_and_odd_two (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : NsRowGlobal e t (q2GlobalKind κ)) :
    nsGlobal e ⊓ centralizer (nsGlobal e : Set G) = ⊥ ∧
      Odd (Nat.card (centralizer (nsGlobal e : Set G))) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hn e
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, -⟩ := hact htN
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      LieModel (nsGlobal e) τ (n + 1 + 1) 2 1 := by
    rcases hκ with rfl | rfl
    · exact ⟨_, Or.inr rfl, hty⟩
    · exact ⟨_, Or.inl rfl, hty⟩
  have hS : IsSimpleGroup (nsGlobal e) := LinearPilot.isSimpleGroup_of_lieModel_POmega hτ hτm
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hLm : LieModel L .PSp (n + 1) 2 1 := lieModel_of_mulEquiv_statedSp e hK1 (by omega) (by
    intro h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega)
  have hna : ∃ a b : nsGlobal e, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup (nsGlobal e) := { (inferInstance : Group (nsGlobal e)) with mul_comm := hc }
    have hp : (Nat.card (nsGlobal e)).Prime := IsSimpleGroup.prime_card
    have h8 : 2 ^ 8 ∣ Nat.card (nsGlobal e) :=
      (two_pow_eight_dvd_card_of_lieModel_PSp hLm).trans (Subgroup.card_dvd_of_le hLS)
    rcases (Nat.dvd_prime hp).1 h8 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp
  have hZ : center (nsGlobal e) = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).2
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro y ⟨hy, hyc⟩
    have hyZ : (⟨y, hy⟩ : nsGlobal e) ∈ center (nsGlobal e) := by
      rw [mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_iff.1 hyc z z.2)
    rw [hZ, mem_bot] at hyZ
    exact (mem_bot).2 (congrArg Subtype.val hyZ)
  · have htZ : t ∉ centralizer (nsGlobal e : Set G) := by
      intro htZ
      apply hout
      refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
      rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
    exact EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ

omit [Finite K] [CharP K 2] in
theorem conj_mem_nsGlobal_of_mem_range_two (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : NsRowGlobal e t (q2GlobalKind κ)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
    (hin : (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∈
      (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range) :
    g⁻¹ * t * g ∈ nsGlobal e := by
  obtain ⟨m, hm⟩ := hin
  obtain ⟨hZ, hodd⟩ := nsGlobal_inf_centralizer_eq_bot_and_odd_two hK hn e ht hKt hκ hglob
  have hact : ∀ x ∈ nsGlobal e,
      (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ = (m : G) * x * (m : G)⁻¹ := by
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hm ⟨x, hx⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    rw [← h1]
    rfl
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hww : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  have hwm := eq_of_forall_conj_eq_conj_of_odd hZ hodd hww m.2 hact
  exact hwm ▸ m.2

omit [Finite G] in
theorem mul_self_map_conj_eq_one {M : Subgroup G} {X : Type*} [Group X] (φ : M ≃* X) {t : G}
    (ht : orderOf t = 2) {g : G} (hw : g⁻¹ * t * g ∈ M) : φ ⟨_, hw⟩ * φ ⟨_, hw⟩ = 1 := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  rw [← map_mul, ← map_one φ]
  congr 1
  apply Subtype.ext
  show (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1
  calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [htt]; group

end Global

@[expose] def OmegaTwoHighTypeAO2Input : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V), Nat.card F = 2 →
    (polarBilin Q).Nondegenerate → 10 ≤ finrank F V →
    ∀ s : V ≃ₗ[F] V, s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ → s * s = 1 → OmegaTwoHighTypeA Q s →
      ¬ (2 * finrank F (omegaInvSpace s) = finrank F V ∧ finrank F (omegaInvSpace s) % 4 = 2) →
        s ∈ omegaO2Cent Q s

@[expose] def SpTwoOmegaLagrangianATwoInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
        [FiniteDimensional F V] (Q : QuadraticForm F V)
        (φ : nsGlobal e ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆),
        Nat.card F = 2 → (polarBilin Q).Nondegenerate → finrank F V = 2 * (n + 1 + 1) →
        ∀ (g : G) (hw : g⁻¹ * t * g ∈ nsGlobal e),
          ¬ ((∀ w ∈ omegaInvSpace (φ ⟨g⁻¹ * t * g, hw⟩ : V ≃ₗ[F] V), Q w = 0) ∧
            2 * finrank F (omegaInvSpace (φ ⟨g⁻¹ * t * g, hw⟩ : V ≃ₗ[F] V)) = finrank F V ∧
            finrank F (omegaInvSpace (φ ⟨g⁻¹ * t * g, hw⟩ : V ≃ₗ[F] V)) % 4 = 2)

end CFSG.SeitzReduction.SymplecticPilot
