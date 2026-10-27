module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8Kinds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore oddCoreLift)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open scoped commutatorElement

section Model

variable {n : ℕ} {K : Type} [Field K]

theorem eq_of_proj_eq_of_card_two (hK : Nat.card K = 2) {A B : SpecialLinearGroup (Fin n) K}
    (h : LinearFlag.proj n K A = LinearFlag.proj n K B) : A = B := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h1 : LinearFlag.proj n K (A * B⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 (LinearFlag.proj_eq_one_iff.1 h1)
  have hU : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hU).1
  have hc1 : c = 1 := Subsingleton.elim c 1
  have h2 : A * B⁻¹ = 1 := by
    apply Subtype.ext
    rw [hc, hc1, Units.val_one, map_one]
    rfl
  exact mul_inv_eq_one.mp h2

theorem mem_blockSpecialLinear_sdiff {S T : Finset (Fin n)} {A : SpecialLinearGroup (Fin n) K}
    (hS : A ∈ blockSpecialLinear S) (hT : A ∈ blockSpecialLinear Tᶜ) :
    A ∈ blockSpecialLinear (S \ T) := by
  have h := (blockSpecialLinear_inf (F := K) S Tᶜ).le (mem_inf.2 ⟨hS, hT⟩)
  rwa [← Finset.sdiff_eq_inter_compl] at h

theorem commutator_mem_blockSL_sdiff_of_card_two (hK : Nat.card K = 2) {S : Finset (Fin n)}
    {c d : Fin n} (hcd : c ≠ d) {x₁ x₂ : LinearFlag.projectiveSL n K}
    (hx₁ : x₁ ∈ blockSL S ⊓ centralizer ({order3Elt K hcd} : Set (LinearFlag.projectiveSL n K)))
    (hx₂ : x₂ ∈ blockSL S ⊓ centralizer ({order3Elt K hcd} : Set (LinearFlag.projectiveSL n K))) :
    ⁅x₁, x₂⁆ ∈ blockSL (K := K) (S \ {c, d}) := by
  set y := SpecialLinearGroup.transvection hcd (1 : K) *
    SpecialLinearGroup.transvection (Ne.symm hcd) 1 with hy
  set Q : Subgroup (SpecialLinearGroup (Fin n) K) := centralizer ({y} : Set _) with hQ
  have hQp : ∀ A ∈ Q, Order3Pattern c d (A : Matrix (Fin n) (Fin n) K) := fun A hA =>
    order3Pattern_of_commute hcd (mem_centralizer_singleton_iff.1 hA)
  have hlift : ∀ x ∈ blockSL S ⊓ centralizer ({order3Elt K hcd} : Set _),
      ∃ A ∈ blockSpecialLinear S, A ∈ Q ∧ LinearFlag.proj n K A = x := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_blockSL.1 (mem_inf.1 hx).1
    refine ⟨A, hA, mem_centralizer_singleton_iff.2 ?_, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
    have hy' : LinearFlag.proj n K y = order3Elt K hcd := rfl
    apply eq_of_proj_eq_of_card_two hK
    rw [map_mul (LinearFlag.proj n K) A y, map_mul (LinearFlag.proj n K) y A, hy']
    exact h1
  obtain ⟨A₁, hA₁S, hA₁Q, rfl⟩ := hlift x₁ hx₁
  obtain ⟨A₂, hA₂S, hA₂Q, rfl⟩ := hlift x₂ hx₂
  rw [← map_commutatorElement]
  refine proj_mem_blockSL (mem_blockSpecialLinear_sdiff ?_ ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hA₁S hA₂S) (inv_mem hA₁S)) (inv_mem hA₂S)
  · exact commutator_mem_blockSpecialLinear_compl_of_order3 hcd hQp hA₁Q hA₂Q

theorem perfectCore_blockSL_inf_centralizer_of_card_two [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 3 ≤ n) {S : Finset (Fin n)} {c d : Fin n} (hcd : c ≠ d)
    (hS : 3 ≤ (S \ {c, d}).card) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 c d) (hX₀c : Nat.card X₀ = 3) :
    perfectCore (blockSL S ⊓ centralizer (X₀ : Set (LinearFlag.projectiveSL n K))) =
      blockSL (K := K) (S \ {c, d}) := by
  set H := blockSL S ⊓ centralizer (X₀ : Set (LinearFlag.projectiveSL n K)) with hH
  have hy : order3Elt K hcd ∈ X₀ := order3Elt_mem_of_card_eq_three hK hn hcd hX₀ hX₀c
  have hHy : H ≤ blockSL S ⊓ centralizer ({order3Elt K hcd} : Set _) :=
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.2 hy))
  have hperf := commutator_blockSL_eq_of_three_le (K := K) hS
  apply le_antisymm
  · have hcomm : ⁅H, H⁆ ≤ blockSL (K := K) (S \ {c, d}) :=
      (commutator_le.2 fun x₁ hx₁ x₂ hx₂ =>
        commutator_mem_blockSL_sdiff_of_card_two hK hcd (hHy hx₁) (hHy hx₂))
    calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ :=
          (CFSG.Quasithin.perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := commutator_mono (CFSG.Quasithin.perfectCore_le H)
          (CFSG.Quasithin.perfectCore_le H)
      _ ≤ _ := hcomm
  · refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (blockSL_mono Finset.sdiff_subset)
      ?_) hperf
    refine le_trans (blockSL_mono fun x hx => ?_) (blockSL_compl_le_centralizer hX₀)
    rw [Finset.mem_compl]
    exact (Finset.mem_sdiff.1 hx).2

end Model

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem modelToG_inf_centralizer (e : L ≃* LinearFlag.projectiveSL n K)
    (A B : Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG e A ⊓ centralizer (modelToG e B : Set G) =
      modelToG e (A ⊓ centralizer (B : Set (LinearFlag.projectiveSL n K))) := by
  apply le_antisymm
  · rintro g ⟨hgA, hgB⟩
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hgA
    refine (mem_modelToG e).2 ⟨x, mem_inf.2 ⟨hx, mem_centralizer_iff.2 fun y hy => ?_⟩, rfl⟩
    have h1 := mem_centralizer_iff.1 hgB _ (symm_mem_modelToG e hy)
    have h2 : e.symm (y * x) = e.symm (x * y) := by
      apply Subtype.ext
      rw [map_mul, map_mul, L.coe_mul, L.coe_mul]
      exact h1
    exact e.symm.injective h2
  · exact le_inf (modelToG_mono e inf_le_left) (modelToG_le_centralizer e inf_le_right)

theorem perfectCore_modelToG [Finite G] [Finite K] (e : L ≃* LinearFlag.projectiveSL n K)
    (A : Subgroup (LinearFlag.projectiveSL n K)) :
    perfectCore (modelToG e A) = modelToG e (perfectCore A) := by
  rw [modelToG, modelToG, ← CFSG.Quasithin.map_perfectCore, ← CFSG.Quasithin.map_perfectCore]

theorem perfectCore_modelToG_blockSL_inf_centralizer [Finite G] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K)
    {S : Finset (Fin n)} {c d : Fin n} (hcd : c ≠ d) (hS : 3 ≤ (S \ {c, d}).card)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 c d)
    (hX₀c : Nat.card X₀ = 3) :
    perfectCore (modelToG e (blockSL (K := K) S) ⊓ centralizer (modelToG e X₀ : Set G)) =
      modelToG e (blockSL (K := K) (S \ {c, d})) := by
  rw [modelToG_inf_centralizer, perfectCore_modelToG,
    perfectCore_blockSL_inf_centralizer_of_card_two hK hn hcd hS hX₀ hX₀c]

end Transport

section Param

theorem natCard_eq_of_mulEquiv_of_implicit {A B : Type*} {_ : Mul A} {_ : Mul B} (e : A ≃* B) :
    Nat.card A = Nat.card B :=
  Nat.card_congr e.toEquiv

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_linear_two
    (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    {Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hiso : Nonempty (Kc ≃* ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))))) :
    ∃ P : SwapParam t (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))),
      Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore (modelToG e X₀) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨-, -, hcH', hdH', hsH', -, -, ⟨eK⟩⟩ := neighbourCore_swap_linear_two hset hK e hn htC
    ht hab hX₀ hX₀c rfl htX rfl hKc hDKK hne hcomm hiso
  obtain ⟨ψ⟩ := hiso
  have h1 := natCard_eq_of_mulEquiv_of_implicit eK
  have h2 := natCard_eq_of_mulEquiv_of_implicit ψ
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : Finite K := finite_of_card_eq_two_pow hK1
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK1
  have hcH : (oddCoreLift Kc).map (MulAut.conj
        (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))).toMonoidHom ≤
      centralizer (oddCoreLift Kc : Set (centralizer (modelToG e X₀ : Set G))) := hcH'
  have hdH : oddCoreLift Kc ⊓ (oddCoreLift Kc).map (MulAut.conj
      (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))).toMonoidHom = ⊥ := hdH'
  have hsH : oddCoreLift Kc ⊔ (oddCoreLift Kc).map (MulAut.conj
      (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))).toMonoidHom =
      perfectCore (⊤ : Subgroup (centralizer (modelToG e X₀ : Set G))) := hsH'
  have hKct : ((oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype).map
        (MulAut.conj t).toMonoidHom =
      ((oddCoreLift Kc).map (MulAut.conj
        (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))).toMonoidHom).map
          (centralizer (modelToG e X₀ : Set G)).subtype :=
    (F4Pilot.map_subtype_map_conj (oddCoreLift Kc) ⟨t, htX⟩).symm
  have hc1 : ((oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype).map
        (MulAut.conj t).toMonoidHom ≤
      centralizer (((oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype :
        Subgroup G) : Set G) := by
    rw [hKct]
    exact F4Pilot.map_le_centralizer_map _ hcH
  have hd1 : (oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype ⊓
      ((oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype).map
        (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ (centralizer _).subtype_injective, hdH,
      Subgroup.map_bot]
  have he1 : (oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype ⊔
      ((oddCoreLift Kc).map (centralizer (modelToG e X₀ : Set G)).subtype).map
        (MulAut.conj t).toMonoidHom = centralizerPerfectCore (modelToG e X₀) := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  obtain ⟨-, -, -, -, -, hDC, hDq, ⟨φD⟩, -, -⟩ :=
    neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c rfl rfl
  have hDH : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) ≤
      centralizer (modelToG e X₀ : Set G) := hDC.trans inf_le_left
  have hDt : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) ≤
      centralizer ({t} : Set G) := hDC.trans inf_le_right
  have hDE : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) ≤
      centralizerPerfectCore (modelToG e X₀) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDH (isPerfect_iff.mp ⟨hDq.1⟩)
  have hrange := F4Pilot.range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := F4Pilot.swapDiagHom_injective hc1 hd1
  obtain ⟨-, -, ⟨eDb⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e hn htC hab hX₀ hX₀c rfl rfl
  have h3 := Nat.card_congr (MulEquiv.toEquiv eDb)
  have h4 := Nat.card_congr (MulEquiv.toEquiv φD)
  have hcard : Nat.card (centralizerPerfectCore (modelToG e X₀) ⊓ centralizer ({t} : Set G) :
      Subgroup G) ≤ Nat.card (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))) := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective (centralizer _).subtype_injective]
    exact (h1.trans (h2.trans (h3.trans h4.symm))).le
  have hfix := (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm
  exact E8Pilot.exists_swapParam_of_decomposition htt hc1 hd1 he1 hfix

end Param

end CFSG.SeitzReduction.LinearPilot
