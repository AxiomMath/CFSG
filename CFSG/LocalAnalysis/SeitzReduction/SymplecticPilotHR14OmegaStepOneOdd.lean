module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOne

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Subgroup
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace two_mul_finrank_commSpace_le mem_omegaGroup
  exists_map_ne_zero)

section Transport

theorem mem_closure_odd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {x : X}
    (h : φ x ∈ closure {y : Y | y ∈ centralizer ({φ x} : Set Y) ∧ Odd (orderOf y)}) :
    x ∈ closure {z : X | z ∈ centralizer ({x} : Set X) ∧ Odd (orderOf z)} := by
  have hle : closure {y : Y | y ∈ centralizer ({φ x} : Set Y) ∧ Odd (orderOf y)} ≤
      (closure {z : X | z ∈ centralizer ({x} : Set X) ∧ Odd (orderOf z)}).comap
        φ.symm.toMonoidHom := by
    rw [closure_le]
    rintro y ⟨hyc, hyo⟩
    rw [SetLike.mem_coe, mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff] at hyc ⊢
      have := congrArg φ.symm hyc
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
      exact this
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hyo
  have h2 := hle h
  rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h2
  exact h2

variable {G : Type*} [Group G]

theorem mem_closure_odd_inf_of_mem_closure {M : Subgroup G} {s : G} (hs : s ∈ M)
    (h : (⟨s, hs⟩ : M) ∈
      closure {x : M | x ∈ centralizer ({⟨s, hs⟩} : Set M) ∧ Odd (orderOf x)}) :
    s ∈ closure {x : G | x ∈ M ⊓ centralizer ({s} : Set G) ∧ Odd (orderOf x)} := by
  have hle : closure {x : M | x ∈ centralizer ({(⟨s, hs⟩ : M)} : Set M) ∧ Odd (orderOf x)} ≤
      (closure {x : G | x ∈ M ⊓ centralizer ({s} : Set G) ∧ Odd (orderOf x)}).comap
        M.subtype := by
    rw [closure_le]
    rintro x ⟨hxc, hxo⟩
    rw [SetLike.mem_coe, mem_comap]
    apply Subgroup.subset_closure
    refine ⟨⟨x.2, ?_⟩, ?_⟩
    · show (x : G) ∈ centralizer ({s} : Set G)
      rw [mem_centralizer_singleton_iff] at hxc ⊢
      exact congrArg Subtype.val hxc
    · rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact hxo
  exact hle h

end Transport

theorem exists_mulEquiv_omega_of_lieModel {G : Type} [Group G] {τ : StatedLieTag}
    (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) {N f : ℕ} (hf : 2 ≤ f)
    (hG : CFSG.Blueprint.LieModel G τ N 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V),
      Nat.card F = 2 ^ f ∧ 4 ≤ Nat.card F ∧ (polarBilin Q).Nondegenerate ∧
        finrank F V = 2 * N ∧
        Nonempty (G ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  obtain ⟨-, hcl⟩ | ⟨hN0, hτ'⟩ | ⟨hN0, hτ'⟩ | ⟨hN0, hτ'⟩ := hG
  · rcases hτ with rfl | rfl
    · obtain ⟨⟨-, -, hN4⟩, F, _, _, hcard, ⟨φ⟩⟩ := hcl
      obtain ⟨hc, hF4⟩ := charP_two_and_four_le_of_card hcard hf
      have : Nontrivial (Fin N ⊕ Fin N → F) := by
        have : Nonempty (Fin N ⊕ Fin N) := ⟨Sum.inl ⟨0, by omega⟩⟩
        infer_instance
      have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus N F
      have hQ := CFSG.LieType.Universal.Spin.coe_quadPlus N F
      have hne : ∃ v, StatedQuadPlus N F v ≠ 0 := by
        obtain ⟨a, ha⟩ := exists_map_ne_zero hnd
        exact ⟨a, by rwa [← hQ]⟩
      refine ⟨F, inferInstance, inferInstance, hc, _, inferInstance, inferInstance, inferInstance,
        CFSG.LieType.Universal.Spin.quadPlus N F, hcard, hF4, hnd, ?_,
        ⟨φ.trans ((statedProjOmegaEquiv hQ hne).trans (statedOmegaEquivOmega hQ))⟩⟩
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    · obtain ⟨⟨-, -, hN4⟩, F, _, _, hcard, b, c, hirr, ⟨φ⟩⟩ := hcl
      obtain ⟨hc, hF4⟩ := charP_two_and_four_le_of_card hcard hf
      have : Nontrivial (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2 → F) := by
        have : Nonempty (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
        infer_instance
      have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite N F hirr
      have hQ := CFSG.LieType.Universal.Spin.coe_quadMinus N F b c
      have hne : ∃ v, StatedQuadMinus N F b c v ≠ 0 := by
        obtain ⟨a, ha⟩ := exists_map_ne_zero hnd
        exact ⟨a, by rwa [← hQ]⟩
      refine ⟨F, inferInstance, inferInstance, hc, _, inferInstance, inferInstance, inferInstance,
        CFSG.LieType.Universal.Spin.quadMinus N F b c, hcard, hF4, hnd, ?_,
        ⟨φ.trans ((statedProjOmegaEquiv hQ hne).trans (statedOmegaEquivOmega hQ))⟩⟩
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega
  all_goals rcases hτ with rfl | rfl <;> simp_all [CFSG.Blueprint.chevalleyExceptionalTags,
    CFSG.Blueprint.reeTitsTags]

section LemmaO2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_mem_omegaO2Cent (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    (φ : M ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {g : G} (hw : g⁻¹ * t * g ∈ M)
    (h : ((φ ⟨_, hw⟩ : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) : V ≃ₗ[F] V) ∈
      omegaO2Cent Q (φ ⟨_, hw⟩ : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆)) : False := by
  have h1 := mem_closure_odd_centralizer_omega (φ ⟨_, hw⟩).2 h
  have h2 := mem_closure_odd_of_mulEquiv φ h1
  have h3 := mem_closure_odd_inf_of_mem_closure hw h2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  exact conj_not_mem_closure_odd_inf ht hKt hCN hset.center_eq_bot
    (isCyclic_outer_of_mulEquiv_statedSp hn e) g h3

omit [Finite K] [CharP K 2] in
theorem conj_mem_spGlobal_of_mem_range {n f : ℕ} (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    (hin : (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∈
      (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range) :
    g⁻¹ * t * g ∈ spGlobal e := by
  obtain ⟨m, hm⟩ := hin
  obtain ⟨hZ, hodd⟩ := spGlobal_inf_centralizer_eq_bot_and_odd hn hKc hf e ht hKt hκ hglob
  have hact : ∀ x ∈ spGlobal e,
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

end LemmaO2

@[expose] def SpOmegaLagrangianInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Odd n →
    Nat.card K = 2 ^ f → 2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
        [FiniteDimensional F V] (Q : QuadraticForm F V)
        (φ : spGlobal e ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆),
        4 ≤ Nat.card F → (polarBilin Q).Nondegenerate → finrank F V = 2 * (n + 1) →
        ∀ (g : G) (hw : g⁻¹ * t * g ∈ spGlobal e),
          2 * finrank F (omegaInvSpace ((φ ⟨g⁻¹ * t * g, hw⟩ :
            ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
              V ≃ₗ[F] V)) ≠ finrank F V

theorem spOmegaStepOneOddInput_of_lagrangian {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : SpOmegaLagrangianInput κ) :
    SpOmegaStepOneOddInput κ := by
  intro G _ _ L hset n f K _ _ _ hn hodd hKc hf e t ht hKt hroot hglob g hg hin
  have hwG := conj_mem_spGlobal_of_mem_range (by omega) hKc hf e ht hKt hκ hglob hg hin
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      CFSG.Blueprint.LieModel (spGlobal e) τ (n + 1) 2 f := by
    have hty := hglob.1
    rcases hκ with rfl | rfl
    · simp only [Sp2mKindType] at hty
      exact ⟨_, Or.inl rfl, hty⟩
    · simp only [Sp2mKindType] at hty
      exact ⟨_, Or.inr rfl, hty⟩
  obtain ⟨F, _, _, _, V, _, _, _, Q, -, hF4, hnd, hdim, ⟨φ⟩⟩ :=
    exists_mulEquiv_omega_of_lieModel hτ hf hτm
  set s := φ ⟨_, hwG⟩ with hs
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hss : s * s = 1 := by
    rw [hs, ← map_mul, ← map_one φ]
    congr 1
    apply Subtype.ext
    show (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  have hle : 2 * finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) ≤ finrank F V :=
    two_mul_finrank_commSpace_le (congrArg Subtype.val hss)
  have hne := h G L hset n f K hn hodd hKc hf e t ht hKt hroot hglob F V Q φ hF4 hnd hdim g hwG
  have hl : 2 * finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) < finrank F V :=
    lt_of_le_of_ne hle hne
  exact false_of_mem_omegaO2Cent hset (by omega) e ht hKt φ hwG
    (mem_omegaO2Cent_of_mem_omega hF4 hnd s.2 (congrArg Subtype.val hss) hl)

theorem spOmegaStepOneInput_of_lagrangian {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : SpOmegaLagrangianInput κ) :
    SpOmegaStepOneInput κ :=
  spOmegaStepOneInput_of_odd hκ (spOmegaStepOneOddInput_of_lagrangian hκ h)

@[expose] def OmegaLagrangianCO2Input : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V), 4 ≤ Nat.card F →
    (polarBilin Q).Nondegenerate → 8 ≤ finrank F V →
    ∀ s : V ≃ₗ[F] V, s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ → s * s = 1 →
      2 * finrank F (omegaInvSpace s) = finrank F V → (∃ w ∈ omegaInvSpace s, Q w ≠ 0) →
        s ∈ omegaO2Cent Q s

@[expose] def OmegaLagrangianAO2Input : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V), 4 ≤ Nat.card F →
    (polarBilin Q).Nondegenerate → ∀ N : ℕ, 0 < N → 4 ∣ N → finrank F V = 2 * N →
    ∀ s : V ≃ₗ[F] V, s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ → s * s = 1 →
      finrank F (omegaInvSpace s) = N → (∀ w ∈ omegaInvSpace s, Q w = 0) →
        s ∈ omegaO2Cent Q s

@[expose] def SpOmegaLagrangianATwoInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → (n + 1) % 4 = 2 →
    Nat.card K = 2 ^ f → 2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
        [FiniteDimensional F V] (Q : QuadraticForm F V)
        (φ : spGlobal e ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆),
        4 ≤ Nat.card F → (polarBilin Q).Nondegenerate → finrank F V = 2 * (n + 1) →
        ∀ (g : G) (hw : g⁻¹ * t * g ∈ spGlobal e),
          ¬ (2 * finrank F (omegaInvSpace ((φ ⟨g⁻¹ * t * g, hw⟩ :
            ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
              V ≃ₗ[F] V)) = finrank F V ∧
            ∀ w ∈ omegaInvSpace ((φ ⟨g⁻¹ * t * g, hw⟩ :
              ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
                V ≃ₗ[F] V), Q w = 0)

theorem spOmegaLagrangianInput_of_inputs {κ : Sp2mKind} (hC : OmegaLagrangianCO2Input)
    (hA : OmegaLagrangianAO2Input) (hA2 : SpOmegaLagrangianATwoInput κ) :
    SpOmegaLagrangianInput κ := by
  intro G _ _ L hset n f K _ _ _ hn hodd hKc hf e t ht hKt hroot hglob F _ _ _ V _ _ _ Q φ hF4
    hnd hdim g hw hlag
  set s := φ ⟨_, hw⟩ with hs
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hss : (s : V ≃ₗ[F] V) * s = 1 := by
    have e1 : s * s = 1 := by
      rw [hs, ← map_mul, ← map_one φ]
      congr 1
      apply Subtype.ext
      show (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt]; group
    exact congrArg Subtype.val e1
  by_cases hQW : ∀ w ∈ omegaInvSpace (s : V ≃ₗ[F] V), Q w = 0
  · rcases Nat.even_or_odd (n + 1) with ⟨j, hj⟩ | hodd'
    · rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact false_of_mem_omegaO2Cent hset (by omega) e ht hKt φ hw
          (hA F V Q hF4 hnd (n + 1) (by omega) ⟨i, by omega⟩ hdim s s.2 hss (by omega) hQW)
      · exact hA2 G L hset n f K hn (by omega) hKc hf e t ht hKt hroot hglob F V Q φ hF4 hnd hdim
          g hw ⟨hlag, hQW⟩
    · obtain ⟨j, hj⟩ := hodd
      obtain ⟨i, hi⟩ := hodd'
      omega
  · push Not at hQW
    exact false_of_mem_omegaO2Cent hset (by omega) e ht hKt φ hw
      (hC F V Q hF4 hnd (by omega) s s.2 hss hlag hQW)

theorem spOmegaStepOneInput_of_inputs {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (hC : OmegaLagrangianCO2Input) (hA : OmegaLagrangianAO2Input)
    (hA2 : SpOmegaLagrangianATwoInput κ) : SpOmegaStepOneInput κ :=
  spOmegaStepOneInput_of_lagrangian hκ (spOmegaLagrangianInput_of_inputs hC hA hA2)

end CFSG.SeitzReduction.SymplecticPilot
