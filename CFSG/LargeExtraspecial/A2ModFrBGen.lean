module

public import CFSG.LargeExtraspecial.A2ModFrBRoots
public import CFSG.LieType.Universal.Spin.Twisted.Generation

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def planeTwo : Fin 2 → K := ![0, 1]

@[expose] noncomputable def extra (p : Fin 2 → K) : spinGroup (quadMinus n K b c) :=
  twShortRoot n hirr (iB hn) true (.ofAdd p) * lr n b c (iA_ne_iB hn) true false *
    (twShortRoot n hirr (iB hn) true (.ofAdd p))⁻¹

noncomputable abbrev xδ : spinGroup (quadMinus n K b c) :=
  lr n b c (iC_ne_iA hn) true true

theorem extra_mul_xδ (h2 : (2 : K) = 0) (p : Fin 2 → K) :
    extra hn hirr p * xδ (b := b) (c := c) hn =
      (twShortRoot n hirr (iB hn) true (.ofAdd p) * lr n b c (iC_ne_iB hn) true true) *
        lr n b c (iA_ne_iB hn) true false *
        (twShortRoot n hirr (iB hn) true (.ofAdd p) * lr n b c (iC_ne_iB hn) true true)⁻¹ := by
  rw [extra]
  set tw := twShortRoot n hirr (iB hn) true (.ofAdd p)
  set ℓ := lr n b c (iA_ne_iB hn) true false
  set g := lr n b c (iC_ne_iB hn) true true
  have hδtw : Commute (xδ (b := b) (c := c) hn) tw :=
    commute_longRoot_twShortRoot_of_ne n hirr (iC_ne_iA hn) (iC_ne_iB hn).symm
      (iA_ne_iB hn).symm true true true 1 p
  have hℓδ : Commute ℓ (xδ (b := b) (c := c) hn) := by
    rw [xδ, lr_swap h2]
    exact HypFrame.commute_longRoot_longRoot_left _ _ _ _ _ _ _ _
  have hcomm := commutator_lr (b := b) (c := c) (iC_ne_iB hn) (iA_ne_iB hn).symm
    (iC_ne_iA hn) true true true
  rw [Bool.not_true, lr_swap h2 (iA_ne_iB hn).symm false true] at hcomm
  have e : g * ℓ * g⁻¹ = xδ hn * ℓ := by
    rw [mul_mul_inv_eq_commutatorElement_mul, hcomm]
  calc tw * ℓ * tw⁻¹ * xδ hn = tw * ℓ * (tw⁻¹ * xδ hn) := by group
    _ = tw * ℓ * (xδ hn * tw⁻¹) := by rw [hδtw.inv_right.eq]
    _ = tw * (ℓ * xδ hn) * tw⁻¹ := by group
    _ = tw * (xδ hn * ℓ) * tw⁻¹ := by rw [hℓδ.eq]
    _ = tw * (g * ℓ * g⁻¹) * tw⁻¹ := by rw [e]
    _ = tw * g * ℓ * (tw * g)⁻¹ := by group

theorem xδ_mem [Finite K] (hK : Nat.card K = 2) :
    xδ (b := b) (c := c) hn ∈ (leviZ n b c hn hirr hK).range ⊔ Subgroup.zpowers (nodeA b c hn) := by
  have h2 := two_eq_zero_of_card hK
  have hcomm := commutator_lr (b := b) (c := c) (iC_ne_iB hn) (iA_ne_iB hn).symm
    (iC_ne_iA hn) true false true
  rw [Bool.not_false, lr_swap h2 (iA_ne_iB hn).symm true true] at hcomm
  rw [xδ, ← hcomm, commutatorElement_def]
  have h1 : lr n b c (iC_ne_iB hn) true false ∈
      (leviZ n b c hn hirr hK).range ⊔ Subgroup.zpowers (nodeA b c hn) :=
    Subgroup.mem_sup_left ⟨_, leviZ_elemTv_eq_lr n hn hirr hK (iC_ne_iB hn)⟩
  have h3 : nodeA b c hn ∈ (leviZ n b c hn hirr hK).range ⊔ Subgroup.zpowers (nodeA b c hn) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact mul_mem (mul_mem (mul_mem h1 h3) (inv_mem h1)) (inv_mem h3)

section Generation

variable [Finite K] (hK : Nat.card K = 2)

noncomputable abbrev genB : Subgroup (spinGroup (quadMinus n K b c)) :=
  (leviZ n b c hn hirr hK).range ⊔ Subgroup.zpowers (nodeA b c hn) ⊔
    Subgroup.zpowers (nodeB b c hn) ⊔ Subgroup.zpowers (extra hn hirr planeOne) ⊔
    Subgroup.zpowers (extra hn hirr planeTwo)

include hK

omit [Finite K] in
theorem eq_zero_or_eq_one (x : K) : x = 0 ∨ x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact eq_zero_or_eq_one_of_card_two hK x

theorem lr_true_false_mem {i j : Fin (n - 1)} (hij : i ≠ j) :
    lr n b c hij true false ∈ genB hn hirr hK := by
  refine Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left ⟨elemTv i j, leviZ_elemTv_eq_lr n hn hirr hK hij⟩)))

theorem nodeA_mem : nodeA b c hn ∈ genB hn hirr hK :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))))

theorem nodeB_mem : nodeB b c hn ∈ genB hn hirr hK :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

theorem extra_planeOne_mem : extra hn hirr planeOne ∈ genB hn hirr hK :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem extra_planeTwo_mem : extra hn hirr planeTwo ∈ genB hn hirr hK :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem lr_mem {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    lr n b c hij s t ∈ genB hn hirr hK := by
  have h2 := two_eq_zero_of_card hK
  have hFT : ∀ {i j : Fin (n - 1)} (hij : i ≠ j), lr n b c hij false true ∈ genB hn hirr hK :=
    fun hij => by rw [lr_swap h2]; exact lr_true_false_mem hn hirr hK hij.symm
  have hTB : ∀ {i : Fin (n - 1)} (hi : i ≠ iB hn), lr n b c hi true true ∈ genB hn hirr hK := by
    intro i hi
    by_cases hiA : i = iA hn
    · subst hiA
      exact nodeA_mem hn hirr hK
    rw [← commutator_lr (b := b) (c := c) hiA (iA_ne_iB hn) hi true false true,
      commutatorElement_def]
    have h1 := lr_true_false_mem hn hirr hK hiA
    have h3 := nodeA_mem hn hirr hK
    exact mul_mem (mul_mem (mul_mem h1 h3) (inv_mem h1)) (inv_mem h3)
  have hFB : ∀ {i : Fin (n - 1)} (hi : i ≠ iB hn), lr n b c hi false false ∈ genB hn hirr hK := by
    intro i hi
    by_cases hiA : i = iA hn
    · subst hiA
      exact nodeB_mem hn hirr hK
    rw [← commutator_lr (b := b) (c := c) hiA (iA_ne_iB hn) hi false true false,
      commutatorElement_def]
    have h1 := hFT hiA
    have h3 := nodeB_mem hn hirr hK
    exact mul_mem (mul_mem (mul_mem h1 h3) (inv_mem h1)) (inv_mem h3)
  have hSS : ∀ (u : Bool) {i j : Fin (n - 1)} (hij : i ≠ j),
      lr n b c hij u u ∈ genB hn hirr hK := by
    intro u i j hij
    have hB : ∀ {i : Fin (n - 1)} (hi : i ≠ iB hn), lr n b c hi u u ∈ genB hn hirr hK := by
      intro i hi
      cases u
      · exact hFB hi
      · exact hTB hi
    by_cases hjB : j = iB hn
    · subst hjB
      exact hB hij
    by_cases hiB : i = iB hn
    · subst hiB
      rw [lr_swap h2]
      exact hB hij.symm
    have hmid : lr n b c (Ne.symm hjB) u u ∈ genB hn hirr hK := by
      rw [lr_swap h2]
      exact hB hjB
    have h1 : lr n b c hiB u (!u) ∈ genB hn hirr hK := by
      cases u
      · exact hFT hiB
      · exact lr_true_false_mem hn hirr hK hiB
    rw [← commutator_lr (b := b) (c := c) hiB (Ne.symm hjB) hij u (!u) u, Bool.not_not,
      commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1 hmid) (inv_mem h1)) (inv_mem hmid)
  cases s <;> cases t
  · exact hSS false hij
  · exact hFT hij
  · exact lr_true_false_mem hn hirr hK hij
  · exact hSS true hij

theorem longRoot_mem {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (x : K) :
    (minusFrame n b c).longRoot hij s t (.ofAdd x) ∈ genB hn hirr hK := by
  rcases eq_zero_or_eq_one hK x with rfl | rfl
  · rw [ofAdd_zero, map_one]
    exact one_mem _
  · exact lr_mem hn hirr hK hij s t

theorem twShortRoot_iA_mem_of_extra_mem {q : Fin 2 → K} (hq : extra hn hirr q ∈ genB hn hirr hK) :
    twShortRoot n hirr (iA hn) true (.ofAdd q) ∈ genB hn hirr hK := by
  have h2 := two_eq_zero_of_card hK
  have hc := commutator_longRoot_twShortRoot n hirr (iA_ne_iB hn) true false (1 : K) q
  rw [Bool.not_false, one_smul, one_mul] at hc
  have hℓ : ⁅lr n b c (iA_ne_iB hn) true false, twShortRoot n hirr (iB hn) true (.ofAdd q)⁆ =
      lr n b c (iA_ne_iB hn) true false * extra hn hirr q := by
    rw [commutatorElement_def, extra, lr_inv h2]
    group
  have hmem : ⁅lr n b c (iA_ne_iB hn) true false, twShortRoot n hirr (iB hn) true (.ofAdd q)⁆ ∈
      genB hn hirr hK := by
    rw [hℓ]
    exact mul_mem (lr_true_false_mem hn hirr hK _) hq
  rw [lr, hc] at hmem
  have := mul_mem hmem (inv_mem (longRoot_mem hn hirr hK (iA_ne_iB hn) true true
    (planeNorm b c q)))
  rwa [mul_inv_cancel_right] at this

theorem twShortRoot_iA_mem (p : Fin 2 → K) :
    twShortRoot n hirr (iA hn) true (.ofAdd p) ∈ genB hn hirr hK := by
  have h1 := twShortRoot_iA_mem_of_extra_mem hn hirr hK (extra_planeOne_mem hn hirr hK)
  have h2 := twShortRoot_iA_mem_of_extra_mem hn hirr hK (extra_planeTwo_mem hn hirr hK)
  have hp : p = p 0 • planeOne + p 1 • planeTwo := by
    funext i
    fin_cases i <;> simp [planeOne, planeTwo]
  rw [hp, ofAdd_add, map_mul]
  have key : ∀ (x : K) {q : Fin 2 → K},
      twShortRoot n hirr (iA hn) true (.ofAdd q) ∈ genB hn hirr hK →
      twShortRoot n hirr (iA hn) true (.ofAdd (x • q)) ∈ genB hn hirr hK := by
    intro x q hq
    rcases eq_zero_or_eq_one hK x with rfl | rfl
    · rw [zero_smul, ofAdd_zero, map_one]
      exact one_mem _
    · rwa [one_smul]
  exact mul_mem (key _ h1) (key _ h2)

theorem twShortRoot_mem (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    twShortRoot n hirr i s (.ofAdd p) ∈ genB hn hirr hK := by
  have hne : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s : Bool),
      twShortRoot n hirr j true (.ofAdd p) ∈ genB hn hirr hK →
      twShortRoot n hirr i s (.ofAdd p) ∈ genB hn hirr hK := by
    intro i j hij s hj
    have hc := commutator_longRoot_twShortRoot n hirr hij s false (1 : K) p
    rw [Bool.not_false, one_smul, one_mul] at hc
    have hmem := mul_mem (mul_mem (mul_mem (longRoot_mem hn hirr hK hij s false 1) hj)
      (inv_mem (longRoot_mem hn hirr hK hij s false 1))) (inv_mem hj)
    rw [← commutatorElement_def, hc] at hmem
    have := mul_mem hmem (inv_mem (longRoot_mem hn hirr hK hij s true (planeNorm b c p)))
    rwa [mul_inv_cancel_right] at this
  have hA := twShortRoot_iA_mem hn hirr hK p
  by_cases hi : i = iA hn
  · subst hi
    cases s
    · exact hne (iA_ne_iB hn) false (hne (iA_ne_iB hn).symm true hA)
    · exact hA
  · exact hne hi s hA

theorem genB_eq_top : genB hn hirr hK = ⊤ := by
  have := isPerfect_spinGroup_quadMinus hn hirr
  refine (minusFrame n b c).toHypFrame.eq_top_of_longRoot_mem
    (fun hij s t x => longRoot_mem hn hirr hK hij s t x) ?_ ?_
    (range_spinAction_quadMinus hn hirr).le
  · intro i s v hv
    rw [eq_planeVec_of_polar_minusVec n b c hv, minusFrame_vec,
      ← spinAction_twShortRoot_eq_eichler n hirr i s]
    exact Subgroup.mem_map_of_mem _ (twShortRoot_mem hn hirr hK i s _)
  · intro v hv hQ
    rw [eq_planeVec_of_polar_minusVec n b c hv] at hQ ⊢
    rw [quadMinus_planeVec'] at hQ
    by_contra h0
    refine planeNorm_ne_zero hirr (fun hw => h0 ?_) hQ
    rw [hw, planeVec_zero]

end Generation

end CFSG.LargeExtraspecial.A2Mod.FrB
