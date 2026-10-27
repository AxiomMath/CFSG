module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylNormE

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

@[expose] def nSub : Subgroup (Equiv.Perm (Fin 240)) :=
  wE8 ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240)))

theorem exists_act (w : nSub) : ∃ σ : Equiv.Perm (Fin 8), (w : Equiv.Perm (Fin 240)) *
    (permMat σ)⁻¹ ∈ eSub := by
  obtain ⟨σ, h, -⟩ := exists_decomp (mem_inf.1 w.2).1 (mem_inf.1 w.2).2
  exact ⟨σ, h⟩

@[expose] def actE (w : nSub) : Equiv.Perm (Fin 8) := Classical.choose (exists_act w)

theorem actE_spec (w : nSub) : (w : Equiv.Perm (Fin 240)) * (permMat (actE w))⁻¹ ∈ eSub :=
  Classical.choose_spec (exists_act w)

theorem actE_eq {w : nSub} {σ : Equiv.Perm (Fin 8)}
    (h : (w : Equiv.Perm (Fin 240)) * (permMat σ)⁻¹ ∈ eSub) : actE w = σ :=
  (decomp_unique (actE_spec w) h (by rw [inv_mul_cancel_right, inv_mul_cancel_right])).2

theorem permMat_mem_nSub (σ : Equiv.Perm (Fin 8)) : permMat σ ∈ nSub :=
  mem_inf.2 ⟨permMat_mem_wE8 σ, permMat_mem_normalizer σ⟩

theorem eSub_le_nSub : eSub ≤ nSub := fun _ he => mem_inf.2 ⟨eSub_le_wE8 he, le_normalizer he⟩

theorem actE_mul (w w' : nSub) : actE (w * w') = actE w * actE w' := by
  apply actE_eq
  have h1 := actE_spec w
  have h2 := actE_spec w'
  have h3 : (w : Equiv.Perm (Fin 240)) * ((w' : Equiv.Perm (Fin 240)) * (permMat (actE w'))⁻¹) *
      (w : Equiv.Perm (Fin 240))⁻¹ ∈ eSub :=
    (mem_normalizer_iff.1 (mem_inf.1 w.2).2 _).1 h2
  rw [coe_mul, permMat_mul, mul_inv_rev]
  have := mul_mem h3 h1
  rwa [show (w : Equiv.Perm (Fin 240)) * ((w' : Equiv.Perm (Fin 240)) *
    (permMat (actE w'))⁻¹) * (w : Equiv.Perm (Fin 240))⁻¹ * ((w : Equiv.Perm (Fin 240)) *
      (permMat (actE w))⁻¹) = (w : Equiv.Perm (Fin 240)) * w' * ((permMat (actE w'))⁻¹ *
        (permMat (actE w))⁻¹) by group] at this

@[expose] def actHom : nSub →* Equiv.Perm (Fin 8) where
  toFun := actE
  map_one' := actE_eq (by rw [permMat_one, inv_one, mul_one]; exact one_mem _)
  map_mul' := actE_mul

theorem actHom_apply (w : nSub) : actHom w = actE w := rfl

theorem actHom_decomp {v : FrameVec} (hv : v ∈ evenSub) (σ : Equiv.Perm (Fin 8))
    (h : signPerm v * permMat σ ∈ nSub) : actHom ⟨_, h⟩ = σ :=
  actE_eq (by rw [mul_inv_cancel_right]; exact mem_eSub.2 ⟨v, hv, rfl⟩)

theorem mem_ker_actHom {w : nSub} : w ∈ actHom.ker ↔ (w : Equiv.Perm (Fin 240)) ∈ eSub := by
  rw [MonoidHom.mem_ker, actHom_apply]
  constructor
  · intro h
    have := actE_spec w
    rwa [h, permMat_one, inv_one, mul_one] at this
  · intro h
    exact actE_eq (by rw [permMat_one, inv_one, mul_one]; exact h)

theorem conj_signPerm_actE (w : nSub) {v : FrameVec} (hv : v ∈ evenSub) :
    (w : Equiv.Perm (Fin 240)) * signPerm v * (w : Equiv.Perm (Fin 240))⁻¹ =
      signPerm (permVec (actE w) v) := by
  have he := actE_spec w
  have h1 : (w : Equiv.Perm (Fin 240)) = ((w : Equiv.Perm (Fin 240)) *
      (permMat (actE w))⁻¹) * permMat (actE w) := by group
  rw [h1, show (w : Equiv.Perm (Fin 240)) * (permMat (actE w))⁻¹ * permMat (actE w) *
    signPerm v * ((w : Equiv.Perm (Fin 240)) * (permMat (actE w))⁻¹ * permMat (actE w))⁻¹ =
    ((w : Equiv.Perm (Fin 240)) * (permMat (actE w))⁻¹) * (permMat (actE w) * signPerm v *
      (permMat (actE w))⁻¹) * ((w : Equiv.Perm (Fin 240)) * (permMat (actE w))⁻¹)⁻¹ by group,
    permMat_conj_signPerm _ hv, eSub_comm he (mem_eSub.2 ⟨_, permVec_mem_evenSub _ hv, rfl⟩),
    mul_inv_cancel_right]

theorem signPerm_inv {v : FrameVec} (hv : v ∈ evenSub) : (signPerm v)⁻¹ = signPerm v :=
  inv_eq_of_mul_eq_one_right (signPerm_mul_self hv)

theorem mem_closure_decomp (L : List (Equiv.Perm (Fin 8))) {x : Equiv.Perm (Fin 240)} :
    x ∈ closure (signPerm '' (evenSub : Set FrameVec) ∪ {g | ∃ σ ∈ L, permMat σ = g}) ↔
      ∃ v ∈ evenSub, ∃ σ ∈ closure {σ | σ ∈ L}, x = signPerm v * permMat σ := by
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem g hg =>
      rcases hg with ⟨v, hv, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact ⟨v, hv, 1, one_mem _, by rw [permMat_one, mul_one]⟩
      · exact ⟨0, zero_mem _, σ, subset_closure hσ, by rw [signPerm_zero, one_mul]⟩
    | one => exact ⟨0, zero_mem _, 1, one_mem _, by rw [signPerm_zero, permMat_one, one_mul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨v, hv, σ, hσ, rfl⟩ := ha
      obtain ⟨u, hu, τ, hτ, rfl⟩ := hb
      refine ⟨v + permVec σ u, add_mem hv (permVec_mem_evenSub σ hu), σ * τ, mul_mem hσ hτ, ?_⟩
      rw [signPerm_add hv (permVec_mem_evenSub σ hu), ← permMat_conj_signPerm σ hu,
        permMat_mul]
      group
    | inv a _ ha =>
      obtain ⟨v, hv, σ, hσ, rfl⟩ := ha
      refine ⟨permVec σ⁻¹ v, permVec_mem_evenSub _ hv, σ⁻¹, inv_mem hσ, ?_⟩
      rw [← permMat_conj_signPerm σ⁻¹ hv, ← permMat_inv, inv_inv, mul_inv_rev, signPerm_inv hv]
      group
  · rintro ⟨v, hv, σ, hσ, rfl⟩
    refine mul_mem (subset_closure (Or.inl ⟨v, hv, rfl⟩)) ?_
    have h : permMat σ ∈ (closure {σ | σ ∈ L}).map permMatHom := ⟨σ, hσ, rfl⟩
    rw [MonoidHom.map_closure] at h
    refine closure_mono ?_ h
    rintro g ⟨τ, hτ, rfl⟩
    exact Or.inr ⟨τ, hτ, rfl⟩

@[expose] def pSub : Subgroup (Equiv.Perm (Fin 8)) := closure {σ | σ ∈ Equiv.swap 0 1 :: pPlusGens}

@[expose] def pPlusSub : Subgroup (Equiv.Perm (Fin 8)) := closure {σ | σ ∈ pPlusGens}

theorem mem_tSub_iff_decomp {x : Equiv.Perm (Fin 240)} :
    x ∈ tSub ↔ ∃ v ∈ evenSub, ∃ σ ∈ pSub, x = signPerm v * permMat σ :=
  mem_closure_decomp _

theorem mem_tPlusSub_iff_decomp {x : Equiv.Perm (Fin 240)} :
    x ∈ tPlusSub ↔ ∃ v ∈ evenSub, ∃ σ ∈ pPlusSub, x = signPerm v * permMat σ :=
  mem_closure_decomp _

theorem signPerm_mul_permMat_mem_nSub {v : FrameVec} (hv : v ∈ evenSub) (σ : Equiv.Perm (Fin 8)) :
    signPerm v * permMat σ ∈ nSub :=
  mul_mem (eSub_le_nSub (mem_eSub.2 ⟨v, hv, rfl⟩)) (permMat_mem_nSub σ)

theorem tSub_le_nSub : tSub ≤ nSub := by
  intro x hx
  obtain ⟨v, hv, σ, -, rfl⟩ := mem_tSub_iff_decomp.1 hx
  exact signPerm_mul_permMat_mem_nSub hv σ

theorem actE_mem_pSub {x : nSub} (hx : (x : Equiv.Perm (Fin 240)) ∈ tSub) : actE x ∈ pSub := by
  obtain ⟨v, hv, σ, hσ, he⟩ := mem_tSub_iff_decomp.1 hx
  have : x = ⟨_, signPerm_mul_permMat_mem_nSub hv σ⟩ := Subtype.ext he
  rw [this, ← actHom_apply, actHom_decomp hv]
  exact hσ

theorem actE_mem_pPlusSub {x : nSub} (hx : (x : Equiv.Perm (Fin 240)) ∈ tPlusSub) :
    actE x ∈ pPlusSub := by
  obtain ⟨v, hv, σ, hσ, he⟩ := mem_tPlusSub_iff_decomp.1 hx
  have : x = ⟨_, signPerm_mul_permMat_mem_nSub hv σ⟩ := Subtype.ext he
  rw [this, ← actHom_apply, actHom_decomp hv]
  exact hσ

theorem permMat_mem_tSub {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ pSub) : permMat σ ∈ tSub :=
  mem_tSub_iff_decomp.2 ⟨0, zero_mem _, σ, hσ, by rw [signPerm_zero, one_mul]⟩

theorem permMat_mem_tPlusSub {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ pPlusSub) :
    permMat σ ∈ tPlusSub :=
  mem_tPlusSub_iff_decomp.2 ⟨0, zero_mem _, σ, hσ, by rw [signPerm_zero, one_mul]⟩

theorem eSub_le_tSub : eSub ≤ tSub := eSub_le_tPlusSub.trans tPlusSub_le_tSub

theorem swap01_mem_pSub : Equiv.swap (0 : Fin 8) 1 ∈ pSub := subset_closure List.mem_cons_self

theorem pPlusGen_mem_pSub {σ : Equiv.Perm (Fin 8)} (h : σ ∈ pPlusGens) : σ ∈ pSub :=
  subset_closure (List.mem_cons_of_mem _ h)

theorem pPlusGen_mem_pPlusSub {σ : Equiv.Perm (Fin 8)} (h : σ ∈ pPlusGens) : σ ∈ pPlusSub :=
  subset_closure h

theorem swap23_mem_pSub : Equiv.swap (2 : Fin 8) 3 ∈ pSub := by
  rw [show Equiv.swap (2 : Fin 8) 3 = Equiv.swap 0 1 * (Equiv.swap 0 1 * Equiv.swap 2 3) by decide]
  exact mul_mem swap01_mem_pSub (pPlusGen_mem_pSub (by decide))

theorem swap45_mem_pSub : Equiv.swap (4 : Fin 8) 5 ∈ pSub := by
  rw [show Equiv.swap (4 : Fin 8) 5 = Equiv.swap 0 1 * (Equiv.swap 0 1 * Equiv.swap 4 5) by decide]
  exact mul_mem swap01_mem_pSub (pPlusGen_mem_pSub (by decide))

theorem swap67_mem_pSub : Equiv.swap (6 : Fin 8) 7 ∈ pSub := by
  rw [show Equiv.swap (6 : Fin 8) 7 = Equiv.swap 4 5 * (Equiv.swap 4 5 * Equiv.swap 6 7) by decide]
  exact mul_mem swap45_mem_pSub (pPlusGen_mem_pSub (by decide))

theorem swap0167_mem_pPlusSub : Equiv.swap (0 : Fin 8) 1 * Equiv.swap 6 7 ∈ pPlusSub := by
  rw [show Equiv.swap (0 : Fin 8) 1 * Equiv.swap 6 7 =
    (Equiv.swap 0 1 * Equiv.swap 4 5) * (Equiv.swap 4 5 * Equiv.swap 6 7) by decide]
  exact mul_mem (pPlusGen_mem_pPlusSub (by decide)) (pPlusGen_mem_pPlusSub (by decide))

theorem frameRoot_even_idx : ∀ i : Fin 8, (i : ℕ) % 2 = 0 →
    keyPts.getD i 0 = 4 * dPairs.idxOf ((i : ℕ), ((i + 1 : Fin 8) : ℕ)) + 1 := by
  decide

theorem lt_add_one_of_even : ∀ i : Fin 8, (i : ℕ) % 2 = 0 → i < i + 1 := by decide

theorem frameElt_even_eq (i : Fin 8) (hi : (i : ℕ) % 2 = 0) :
    frameElt (frameE i) = permMat (Equiv.swap i (i + 1)) := by
  rw [frameElt_frameE, permMat_swap_lt (lt_add_one_of_even i hi), ← keyPts_getD,
    frameRoot_even_idx i hi]

theorem frameElt_odd_eq (i j : Fin 8) (hi : (i : ℕ) % 2 = 0) (hj : j = i + 1) :
    frameElt (frameE j) = permMat (Equiv.swap i j) * signPerm (vec2 i j) := by
  subst hj
  rw [signPerm_pair i hi, ← frameElt_even_eq i hi, vec2, frameElt_add, ← mul_assoc,
    frameElt_mul_self, one_mul]

theorem frameElt_frameE_mem_tSub (j : Fin 8) : frameElt (frameE j) ∈ tSub := by
  have hS : ∀ i j : Fin 8, i ≠ j → signPerm (vec2 i j) ∈ tSub := fun i j h =>
    eSub_le_tSub (mem_eSub.2 ⟨_, vec2_mem_evenSub i j h, rfl⟩)
  fin_cases j
  · show frameElt (frameE 0) ∈ tSub
    rw [frameElt_even_eq 0 (by decide)]; exact permMat_mem_tSub swap01_mem_pSub
  · show frameElt (frameE 1) ∈ tSub
    rw [frameElt_odd_eq 0 1 (by decide) (by decide)]
    exact mul_mem (permMat_mem_tSub swap01_mem_pSub) (hS 0 1 (by decide))
  · show frameElt (frameE 2) ∈ tSub
    rw [frameElt_even_eq 2 (by decide)]; exact permMat_mem_tSub swap23_mem_pSub
  · show frameElt (frameE 3) ∈ tSub
    rw [frameElt_odd_eq 2 3 (by decide) (by decide)]
    exact mul_mem (permMat_mem_tSub swap23_mem_pSub) (hS 2 3 (by decide))
  · show frameElt (frameE 4) ∈ tSub
    rw [frameElt_even_eq 4 (by decide)]; exact permMat_mem_tSub swap45_mem_pSub
  · show frameElt (frameE 5) ∈ tSub
    rw [frameElt_odd_eq 4 5 (by decide) (by decide)]
    exact mul_mem (permMat_mem_tSub swap45_mem_pSub) (hS 4 5 (by decide))
  · show frameElt (frameE 6) ∈ tSub
    rw [frameElt_even_eq 6 (by decide)]; exact permMat_mem_tSub swap67_mem_pSub
  · show frameElt (frameE 7) ∈ tSub
    rw [frameElt_odd_eq 6 7 (by decide) (by decide)]
    exact mul_mem (permMat_mem_tSub swap67_mem_pSub) (hS 6 7 (by decide))

theorem frameElt_mem_tSub (v : FrameVec) : frameElt v ∈ tSub := by
  rw [← blockVec_frameSupp v]
  induction frameSupp v using Finset.induction_on with
  | empty => rw [blockVec_empty, frameElt_zero]; exact one_mem _
  | insert a s ha ih =>
    rw [blockVec_insert ha, frameElt_add]
    exact mul_mem (frameElt_frameE_mem_tSub a) ih

theorem e1Sub_le_tSub : e1Sub ≤ tSub := by
  rw [e1Sub, closure_le]
  rintro _ ⟨v, rfl⟩
  exact frameElt_mem_tSub v

theorem e1PlusSub_le_tPlusSub : e1PlusSub ≤ tPlusSub := by
  rw [e1PlusSub_eq, tPlusSub_eq_inf]
  exact inf_le_inf_right _ e1Sub_le_tSub

theorem uPrimeSub_le_tPlusSub : uPrimeSub ≤ tPlusSub := by
  have hS : ∀ i j : Fin 8, i ≠ j → signPerm (vec2 i j) ∈ tPlusSub := fun i j h =>
    eSub_le_tPlusSub (mem_eSub.2 ⟨_, vec2_mem_evenSub i j h, rfl⟩)
  rw [uPrimeSub, closure_le]
  rintro g (rfl | rfl | rfl | rfl)
  · exact hS 0 1 (by decide)
  · exact mul_mem (hS 0 2 (by decide)) (permMat_mem_tPlusSub (pPlusGen_mem_pPlusSub (by decide)))
  · exact mul_mem (hS 0 4 (by decide)) (permMat_mem_tPlusSub (pPlusGen_mem_pPlusSub (by decide)))
  · exact mul_mem (hS 0 6 (by decide)) (permMat_mem_tPlusSub swap0167_mem_pPlusSub)

@[expose] def actOn (H : Subgroup (Equiv.Perm (Fin 240))) (hH : H ≤ nSub) :
    H →* Equiv.Perm (Fin 8) :=
  actHom.comp (inclusion hH)

@[expose] def qOf (H : Subgroup (Equiv.Perm (Fin 240))) (hH : H ≤ nSub) :
    Subgroup (Equiv.Perm (Fin 8)) :=
  (actOn H hH).range

theorem mem_ker_actOn {H : Subgroup (Equiv.Perm (Fin 240))} {hH : H ≤ nSub} {x : H} :
    x ∈ (actOn H hH).ker ↔ (x : Equiv.Perm (Fin 240)) ∈ eSub := by
  rw [MonoidHom.mem_ker, actOn, MonoidHom.comp_apply, ← MonoidHom.mem_ker, mem_ker_actHom]
  rfl

theorem card_eq_card_inf_mul_card_qOf (H : Subgroup (Equiv.Perm (Fin 240))) (hH : H ≤ nSub) :
    Nat.card H = Nat.card (H ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) * Nat.card (qOf H hH) := by
  have h1 := Subgroup.card_mul_index (actOn H hH).ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  congr 1
  exact Nat.card_congr
    { toFun := fun x => ⟨(x : H), mem_inf.2 ⟨(x : H).2, mem_ker_actOn.1 x.2⟩⟩
      invFun := fun y => ⟨⟨y, (mem_inf.1 y.2).1⟩, mem_ker_actOn.2 (mem_inf.1 y.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[expose] def fixSet (Q : Subgroup (Equiv.Perm (Fin 8))) : Set FrameVec :=
  {v | v ∈ evenSub ∧ ∀ σ ∈ Q, permVec σ v = v}

theorem exists_vec_of_mem_inf {B : Subgroup (Equiv.Perm (Fin 240))} (e : (B ⊓ eSub :
    Subgroup (Equiv.Perm (Fin 240)))) : ∃ v ∈ evenSub, signPerm v = e :=
  mem_eSub.1 (mem_inf.1 e.2).2

theorem card_inf_le_fixSet (B : Subgroup (Equiv.Perm (Fin 240))) (hB : B ≤ nSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card (B ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) ≤ Nat.card (fixSet (qOf B hB)) := by
  classical
  refine Nat.card_le_card_of_injective (fun e => ⟨Classical.choose (exists_vec_of_mem_inf e),
    (Classical.choose_spec (exists_vec_of_mem_inf e)).1, ?_⟩) ?_
  · rintro σ ⟨x, rfl⟩
    set v := Classical.choose (exists_vec_of_mem_inf e)
    have hv := (Classical.choose_spec (exists_vec_of_mem_inf e)).1
    have hve := (Classical.choose_spec (exists_vec_of_mem_inf e)).2
    have hc : (x : Equiv.Perm (Fin 240)) * signPerm v * (x : Equiv.Perm (Fin 240))⁻¹ =
        signPerm (permVec ((actOn B hB) x) v) := conj_signPerm_actE ⟨x, hB x.2⟩ hv
    have hcomm : (x : Equiv.Perm (Fin 240)) * signPerm v = signPerm v * x := by
      rw [hve]
      exact hab _ x.2 _ (mem_inf.1 e.2).1
    rw [hcomm, mul_inv_cancel_right] at hc
    exact signPerm_inj (permVec_mem_evenSub _ hv) hv hc.symm
  · intro e f h
    have h1 := congrArg Subtype.val h
    simp only at h1
    refine Subtype.ext ?_
    rw [← (Classical.choose_spec (exists_vec_of_mem_inf e)).2,
      ← (Classical.choose_spec (exists_vec_of_mem_inf f)).2, h1]

end CFSG.EvenSmallLie.OmegaEight.Weyl
