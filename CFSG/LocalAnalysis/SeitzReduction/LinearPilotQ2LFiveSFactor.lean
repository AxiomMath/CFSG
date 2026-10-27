module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHRoot

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore oddCoreLift)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swap_factor_of_swap
    (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hswap : LinearTwoSwapKindAt e t a b X₀ htX) :
    ∃ A : Subgroup G,
      centralizerPerfectCore (modelToG e X₀) = A ⊔ A.map (MulAut.conj t).toMonoidHom ∧
      A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      (∀ x ∈ A, ∀ y ∈ A.map (MulAut.conj t).toMonoidHom, x * y = y * x) ∧
      Nat.card A = Nat.card (Matrix.SpecialLinearGroup (Fin (n - 2)) K) ∧
      modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ)) ≤
        centralizerPerfectCore (modelToG e X₀) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  set X : Subgroup G := modelToG e X₀ with hXdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  set D : Subgroup G := modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) with hDdef
  have hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype :=
    rfl
  obtain ⟨Kc, hKc, hDKK, hne, hcomm, hZ, hiso⟩ := hswap
  obtain ⟨-, -, hcent, hinf, hsup, -, -, ⟨φK⟩⟩ := neighbourCore_swap_linear_two hset hK e hn
    htC ht hab hX₀ hX₀c hX htX hDe hKc hDKK hne hcomm hiso
  obtain ⟨-, -, ⟨eDb⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e hn htC hab hX₀ hX₀c hX hDe
  obtain ⟨-, hDX, hDq, -⟩ := neighbour_hyps_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX htX hDe
  set H : Subgroup G := centralizer (X : Set G) with hH
  set A : Subgroup H := oddCoreLift Kc with hA
  set AG : Subgroup G := A.map H.subtype with hAG
  have hEX : centralizerPerfectCore X = AG ⊔ AG.map (MulAut.conj t).toMonoidHom := by
    rw [centralizerPerfectCore_eq_map_perfectCore_top, ← hsup, Subgroup.map_sup,
      map_subtype_map_conj_eq_map_conj_coe]
  have hAGt : AG.map (MulAut.conj t).toMonoidHom =
      (A.map (MulAut.conj (⟨t, htX⟩ : H)).toMonoidHom).map H.subtype :=
    (map_subtype_map_conj_eq_map_conj_coe A ⟨t, htX⟩).symm
  have hAs : AG.map (MulAut.conj t).toMonoidHom ≤ centralizer (AG : Set G) := by
    rw [hAGt]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((mem_centralizer_iff.1 (hcent hy)) x hx)
  have hcommG : ∀ x ∈ AG, ∀ y ∈ AG.map (MulAut.conj t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (hAs hy)) x hx
  have hinfG : AG ⊓ AG.map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hAGt, hAG, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hinf, Subgroup.map_bot]
  obtain ⟨ψ⟩ := hiso
  set eA : AG ≃* Kc := (A.equivMapOfInjective H.subtype H.subtype_injective).symm.trans φK
    with heA
  have hAGc : Nat.card AG = Nat.card (Matrix.SpecialLinearGroup (Fin (n - 2)) K) := by
    rw [Nat.card_congr ((eA.trans ψ).trans eDb).toEquiv]
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp hDq.1
  have hDE : D ≤ centralizerPerfectCore X := CFSG.Quasithin.le_perfectCore_of_perfect hDX hDperf
  exact ⟨AG, hEX, hinfG, hcommG, hAGc, hDE⟩

theorem exists_swap_factor_of_swap_five
    (hset : SeitzSetting G L)
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 5} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hswap : LinearTwoSwapKindAt e t a b X₀ htX) :
    ∃ A : Subgroup G,
      centralizerPerfectCore (modelToG e X₀) = A ⊔ A.map (MulAut.conj t).toMonoidHom ∧
      A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      (∀ x ∈ A, ∀ y ∈ A.map (MulAut.conj t).toMonoidHom, x * y = y * x) ∧
      ¬ 16 ∣ Nat.card A ∧
      modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)) ≤
        centralizerPerfectCore (modelToG e X₀) := by
  obtain ⟨A, h1, h2, h3, h4, h5⟩ :=
    exists_swap_factor_of_swap hset hK e le_rfl htC ht hab hX₀ hX₀c htX hswap
  refine ⟨A, h1, h2, h3, ?_, h5⟩
  rw [h4, show (5 - 2 : ℕ) = 3 from rfl, card_specialLinearGroup_fin_three_eq hK]
  decide

end CFSG.SeitzReduction.LinearPilot
