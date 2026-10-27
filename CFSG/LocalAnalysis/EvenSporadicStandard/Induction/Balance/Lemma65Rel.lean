module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Pts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Ext
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Points
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Dichotomy

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Wong77
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.EvenSporadicStandard.Wong77.Module (Cocode pt coMk cocodeRep golayRep golayEven golayCode
  coMk_eq_zero)
open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24 (theta theta_apply golay res
  mem_golay_iff_ext WWord)
open scoped IsMulCommutative

section

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ}

@[expose] def inclN (E H₁ : Subgroup Γ) : ↥(E.subgroupOf H₁) →* ↥E where
  toFun y := ⟨((y : ↥H₁) : Γ), mem_subgroupOf.1 y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inclN_injective (E H₁ : Subgroup Γ) : Function.Injective (inclN E H₁) :=
  fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : ↥E => (z : Γ)) h))

variable [Finite Γ] [E.Normal] [IsMulCommutative ↥E] [Module (ZMod 2) (Additive ↥E)]
  [(E.subgroupOf H₁).Normal] [IsMulCommutative ↥(E.subgroupOf H₁)]
  [Module (ZMod 2) (Additive ↥(E.subgroupOf H₁))]

theorem exists_points (hS : Setting65 Γ E H₁ e) (φ : ↥H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23) :
    ∃ pE : Fin 24 → ↥E, (∀ (g : Γ) (k : Fin 24), ∃ j, MulAut.conjNormal g (pE k) = pE j) ∧
      ∀ v : Cocode24.Word, theta E pE v = 0 ↔ v ∈ golay := by
  obtain ⟨ρ, hρinj, hρ⟩ := exists_rep (E.subgroupOf H₁) hS.centralizer_N φ
  have hV : Nat.card (Additive ↥(E.subgroupOf H₁)) = 2 ^ 11 :=
    (Nat.card_congr (Additive.ofMul : ↥(E.subgroupOf H₁) ≃ Additive ↥(E.subgroupOf H₁))).symm.trans
      hS.card_N
  rcases module_dichotomy hV ρ hρinj with ⟨F, hF⟩ | ⟨F, hF⟩
  swap
  · exact (not_golayEven hS φ ρ hρ F hF).elim
  let u : Fin 23 → ↥(E.subgroupOf H₁) := fun i => (F.symm (pt i)).toMul
  have hu : ∀ i, F.symm (pt i) = Additive.ofMul (u i) := fun i => (ofMul_toMul _).symm
  let e' : ↥E := ⟨e, hS.mem⟩
  let pE : Fin 24 → ↥E := fun k => if h : k.val < 23 then inclN E H₁ (u ⟨k.val, h⟩) * e' else e'
  have hpEc : ∀ i : Fin 23, pE i.castSucc = inclN E H₁ (u i) * e' := by
    intro i
    simp [pE, i.2]
  have hpEl : pE (Fin.last 23) = e' := by simp [pE]
  choose! κ hκ using fun (n : ↥(E.subgroupOf H₁)) (hn : n ∈ Xset E H₁ e) =>
    points_of_cocode hS φ ρ hρ F hF hn
  have hinj : Set.InjOn κ (Xset E H₁ e) := by
    intro n hn n' hn' h
    have h1 := (hκ n hn).trans ((congrArg pt h).trans (hκ n' hn').symm)
    exact Additive.ofMul.injective (F.injective h1)
  have himg : κ '' Xset E H₁ e = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
    rw [hinj.ncard_image, hS.Xset_ncard, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hsurj : ∀ i : Fin 23, ∃ n ∈ Xset E H₁ e, u i = n := by
    intro i
    obtain ⟨n, hn, hni⟩ : i ∈ κ '' Xset E H₁ e := by rw [himg]; trivial
    refine ⟨n, hn, ?_⟩
    have h1 : F (Additive.ofMul n) = pt i := by rw [hκ n hn, hni]
    have h2 := congrArg F.symm h1
    rw [LinearEquiv.symm_apply_apply, hu] at h2
    exact (Additive.ofMul.injective h2).symm
  have hΩ : ∀ x : Γ, x ∈ omega e ↔ ∃ k, ((pE k : ↥E) : Γ) = x := by
    intro x
    constructor
    · intro hx
      by_cases hxe : x = e
      · exact ⟨Fin.last 23, by rw [hpEl]; exact hxe.symm⟩
      · have hn : toN hS hx (hS.mul_e_mem_H₁ x hx hxe) ∈ Xset E H₁ e := ⟨x, hx, hxe, rfl⟩
        obtain ⟨i, hi⟩ := points_of_cocode hS φ ρ hρ F hF hn
        have h2 : u i = toN hS hx (hS.mul_e_mem_H₁ x hx hxe) := by
          have h3 := congrArg F.symm hi
          rw [LinearEquiv.symm_apply_apply, hu] at h3
          exact (Additive.ofMul.injective h3).symm
        refine ⟨i.castSucc, ?_⟩
        rw [hpEc, h2]
        show x * e * e = x
        rw [mul_assoc, hS.e_mul_e, mul_one]
    · rintro ⟨k, rfl⟩
      induction k using Fin.lastCases with
      | last =>
        rw [hpEl]
        exact e_mem_omega e
      | cast i =>
        obtain ⟨n, hn, hni⟩ := hsurj i
        obtain ⟨ω, hω, hne, hv⟩ := hn
        rw [hpEc, hni]
        show ((n : ↥H₁) : Γ) * e ∈ omega e
        rw [hv, mul_assoc, hS.e_mul_e, mul_one]
        exact hω
  have hconj : ∀ (g : Γ) (k : Fin 24), ∃ j, MulAut.conjNormal g (pE k) = pE j := by
    intro g k
    have h1 : g * ((pE k : ↥E) : Γ) * g⁻¹ ∈ omega e :=
      conj_mem_omega ((hΩ _).2 ⟨k, rfl⟩) g
    obtain ⟨j, hj⟩ := (hΩ _).1 h1
    exact ⟨j, Subtype.ext (by rw [MulAut.conjNormal_apply, hj])⟩
  refine ⟨pE, hconj, ?_⟩
  let ι' : Additive ↥(E.subgroupOf H₁) →ₗ[ZMod 2] Additive ↥E :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (inclN E H₁))
  have hι' : ∀ y, ι' (Additive.ofMul y) = Additive.ofMul (inclN E H₁ y) := fun _ => rfl
  have hι'inj : Function.Injective ι' := by
    intro a b h
    rw [← ofMul_toMul a, ← ofMul_toMul b, hι', hι'] at h
    rw [← ofMul_toMul a, ← ofMul_toMul b,
      inclN_injective E H₁ (Additive.ofMul.injective h)]
  have hsum : ∀ w : WWord, ∑ i : Fin 23, w i • pt i = coMk w := by
    intro w
    conv_rhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w i • coMk (Pi.single i 1) = coMk (Pi.single i (w i))
    rw [← map_smul]
    congr 1
    ext j
    simp [Pi.single_apply]
  have h1 : ∀ v : Cocode24.Word, ∑ i : Fin 23, v i.castSucc • Additive.ofMul (inclN E H₁ (u i)) =
      ι' (F.symm (coMk (res v))) := by
    intro v
    rw [← hsum (res v), map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hu, hι']
    rfl
  have hsplit : ∀ v : Cocode24.Word, theta E pE v = ι' (F.symm (coMk (res v))) +
      (∑ i : Fin 23, v i.castSucc + v (Fin.last 23)) • Additive.ofMul e' := by
    intro v
    rw [theta_apply, Fin.sum_univ_castSucc]
    have h2 : ∀ i : Fin 23, v i.castSucc • Additive.ofMul (pE i.castSucc) =
        v i.castSucc • Additive.ofMul (inclN E H₁ (u i)) + v i.castSucc • Additive.ofMul e' := by
      intro i
      rw [hpEc, ofMul_mul, smul_add]
    rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, h1, hpEl, ← Finset.sum_smul,
      add_assoc, ← add_smul]
  intro v
  rw [mem_golay_iff_ext, hsplit v]
  have hchar : ∀ x y : ZMod 2, x + y = 0 ↔ y = x := by decide
  constructor
  · intro h
    have hc : ∑ i : Fin 23, v i.castSucc + v (Fin.last 23) = 0 := by
      by_contra hc
      have hc1 : ∑ i : Fin 23, v i.castSucc + v (Fin.last 23) = 1 := by
        generalize ∑ i : Fin 23, v i.castSucc + v (Fin.last 23) = t at hc ⊢
        revert t
        decide
      rw [hc1, one_smul] at h
      have h3 : Additive.ofMul e' = ι' (-F.symm (coMk (res v))) := by
        rw [map_neg]
        exact eq_neg_of_add_eq_zero_right h
      have h4 : e' = inclN E H₁ (-F.symm (coMk (res v))).toMul := by
        have h5 : ι' (-F.symm (coMk (res v))) =
            Additive.ofMul (inclN E H₁ (-F.symm (coMk (res v))).toMul) := by
          rw [← hι', ofMul_toMul]
        exact Additive.ofMul.injective (h3.trans h5)
      apply hS.e_not_mem_H₁
      have h6 : e = ((((-F.symm (coMk (res v))).toMul : ↥(E.subgroupOf H₁)) : ↥H₁) : Γ) :=
        congrArg (fun z : ↥E => (z : Γ)) h4
      rw [h6]
      exact (((-F.symm (coMk (res v))).toMul : ↥(E.subgroupOf H₁)) : ↥H₁).2
    rw [hc, zero_smul, add_zero] at h
    have ha : F.symm (coMk (res v)) = 0 := hι'inj (by rw [h, map_zero])
    have hm : coMk (res v) = 0 := F.symm.map_eq_zero_iff.1 ha
    exact ⟨coMk_eq_zero.1 hm, (hchar _ _).1 hc⟩
  · rintro ⟨h1, h2⟩
    have ha : F.symm (coMk (res v)) = 0 := by rw [coMk_eq_zero.2 h1, map_zero]
    have hc : ∑ i : Fin 23, v i.castSucc + v (Fin.last 23) = 0 := (hchar _ _).2 h2
    rw [ha, hc, map_zero, zero_smul, add_zero]

end

end CFSG.EvenSporadicStandard.Induction.Balance
