module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelian
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylUCheck

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer

theorem centralizer_uPrimeSub_spec {t : Equiv.Perm (Fin 240)} (ht : t ∈ tSub)
    (hc : ∀ u ∈ uPrimeSub, t * u = u * t) : t ∈ uPrimeSub := by
  by_contra htU
  set V := closure ((uPrimeSub : Set (Equiv.Perm (Fin 240))) ∪ {t}) with hVdef
  have hV : V ≤ tSub := by
    rw [hVdef, closure_le]
    rintro g (hg | rfl)
    · exact tPlusSub_le_tSub (uPrimeSub_le_tPlusSub hg)
    · exact ht
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    refine closure_comm_of_comm ?_
    rintro a (ha | rfl) b (hb | rfl)
    · exact uPrimeSub_comm a ha b hb
    · exact (hc a ha).symm
    · exact hc b hb
    · rfl
  have hUV : uPrimeSub ≤ V := fun u hu => subset_closure (Or.inl hu)
  have htV : t ∈ V := subset_closure (Or.inr rfl)
  have hcard : 2 ^ 8 ≤ Nat.card V := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hUV
    rw [card_uPrimeSub] at hk
    have hne : ¬ Nat.card V ≤ 2 ^ 7 := fun h => by
      have := eq_of_le_of_card_ge hUV (by rw [card_uPrimeSub]; exact h)
      exact htU (this ▸ htV)
    have hpos : 0 < Nat.card V := Nat.card_pos
    omega
  have hVE := abelian_t_spec V hV hVab hcard
  obtain ⟨u, hu, hu2⟩ := not_sq_uPrimeSub
  have hu1 : u ∈ e1Sub := hVE ▸ hUV hu
  obtain ⟨v, rfl⟩ := mem_e1Sub.1 hu1
  exact hu2 (frameElt_mul_self v)

@[expose] def sigSub (P : FrameVec → Prop) (h0 : P 0) (hadd : ∀ u v, P u → P v → P (u + v))
    (hev : ∀ v, P v → v ∈ evenSub) : Subgroup (Equiv.Perm (Fin 240)) where
  carrier := {g | ∃ v, P v ∧ signPerm v = g}
  one_mem' := ⟨0, h0, signPerm_zero⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u + v, hadd u v hu hv, signPerm_add (hev u hu) (hev v hv)⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, (signPerm_inv (hev v hv)).symm⟩

theorem card_sigSub {P : FrameVec → Prop} {h0 : P 0} {hadd : ∀ u v, P u → P v → P (u + v)}
    {hev : ∀ v, P v → v ∈ evenSub} : Nat.card (sigSub P h0 hadd hev) = Nat.card {v // P v} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun v => ⟨signPerm v.1, v.1, v.2, rfl⟩) ⟨?_, ?_⟩)
  · intro v w h
    exact Subtype.ext (signPerm_inj (hev _ v.2) (hev _ w.2) (congrArg Subtype.val h))
  · rintro ⟨g, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

@[expose] def aU : FrameVec := vec2 0 1 + vec2 2 3

@[expose] def bU : FrameVec := vec2 4 5 + vec2 6 7

@[expose] def blockConst (v : FrameVec) : Prop :=
  v 0 = v 1 ∧ v 0 = v 2 ∧ v 0 = v 3 ∧ v 4 = v 5 ∧ v 4 = v 6 ∧ v 4 = v 7

instance (v : FrameVec) : Decidable (blockConst v) := by
  unfold blockConst
  infer_instance

theorem blockConst_add {u v : FrameVec} (hu : blockConst u) (hv : blockConst v) :
    blockConst (u + v) := by
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hu
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hv
  simp only [blockConst, Pi.add_apply]
  exact ⟨by rw [u1, v1], by rw [u2, v2], by rw [u3, v3], by rw [u4, v4], by rw [u5, v5],
    by rw [u6, v6]⟩

theorem blockConst_zero : blockConst 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zmod2_four_add : ∀ a b : ZMod 2, a + a + a + a + b + b + b + b = 0 := by decide

theorem blockConst_even {v : FrameVec} (hv : blockConst v) : v ∈ evenSub := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  rw [mem_evenSub, Fin.sum_univ_eight, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  exact zmod2_four_add _ _

theorem blockConst_aU : blockConst aU := by decide

theorem blockConst_bU : blockConst bU := by decide

theorem aU_mem_evenSub : aU ∈ evenSub := blockConst_even blockConst_aU

theorem bU_mem_evenSub : bU ∈ evenSub := blockConst_even blockConst_bU

theorem blockConst_decomp_aux : ∀ a b : ZMod 2,
    (fun i => ![a, a, a, a, b, b, b, b] i : FrameVec) =
      (if a = 1 then aU else 0) + (if b = 1 then bU else 0) := by
  decide

theorem blockConst_decomp {v : FrameVec} (hv : blockConst v) :
    v = (if v 0 = 1 then aU else 0) + (if v 4 = 1 then bU else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  rw [← blockConst_decomp_aux]
  funext i
  fin_cases i <;> simp [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]

theorem frameZ_eq_aU_add_bU : frameZ = aU + bU := by decide

theorem xPlane_eq_aU : xPlane = signPerm aU := rfl

@[expose] def uSig : Subgroup (Equiv.Perm (Fin 240)) :=
  sigSub blockConst blockConst_zero (fun _ _ hu hv => blockConst_add hu hv)
    (fun _ hv => blockConst_even hv)

theorem uSub_eq_uSig : uSub = uSig := by
  apply le_antisymm
  · rw [uSub, closure_le]
    rintro g (rfl | rfl)
    · exact ⟨aU, blockConst_aU, rfl⟩
    · exact ⟨bU, blockConst_bU, rfl⟩
  · rintro g ⟨v, hv, rfl⟩
    have ha : signPerm aU ∈ uSub := subset_closure (Set.mem_insert _ _)
    have hb : signPerm bU ∈ uSub := subset_closure (Set.mem_insert_of_mem _ rfl)
    have hite : ∀ (c : Prop) [Decidable c] (w : FrameVec), w ∈ evenSub → signPerm w ∈ uSub →
        (if c then w else 0) ∈ evenSub ∧ signPerm (if c then w else 0) ∈ uSub := by
      intro c _ w hw hs
      split_ifs
      · exact ⟨hw, hs⟩
      · exact ⟨zero_mem _, by rw [signPerm_zero]; exact one_mem _⟩
    obtain ⟨a1, a2⟩ := hite (v 0 = 1) aU aU_mem_evenSub ha
    obtain ⟨b1, b2⟩ := hite (v 4 = 1) bU bU_mem_evenSub hb
    rw [blockConst_decomp hv, signPerm_add a1 b1]
    exact mul_mem a2 b2

theorem mem_uSub_iff {g : Equiv.Perm (Fin 240)} :
    g ∈ uSub ↔ ∃ v, blockConst v ∧ signPerm v = g := by
  rw [uSub_eq_uSig]
  rfl

@[expose] def blockConstEquiv : {v // blockConst v} ≃ ZMod 2 × ZMod 2 where
  toFun v := (v.1 0, v.1 4)
  invFun p := ⟨fun i => ![p.1, p.1, p.1, p.1, p.2, p.2, p.2, p.2] i,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  left_inv v := by
    obtain ⟨v, h1, h2, h3, h4, h5, h6⟩ := v
    refine Subtype.ext (funext fun i => ?_)
    fin_cases i <;> simp [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  right_inv p := rfl

theorem card_uSub : Nat.card uSub = 4 := by
  rw [uSub_eq_uSig, uSig, card_sigSub, Nat.card_congr blockConstEquiv, Nat.card_prod,
    Nat.card_zmod]

theorem zPerm_mem_uSub : zPerm ∈ uSub :=
  mem_uSub_iff.2 ⟨aU + bU, blockConst_add blockConst_aU blockConst_bU, by
    rw [← frameZ_eq_aU_add_bU, signPerm_frameZ]⟩

theorem xPlane_mem_uSub : xPlane ∈ uSub := subset_closure (Set.mem_insert _ _)

theorem uSub_le_eSub : uSub ≤ eSub := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ := mem_uSub_iff.1 hg
  exact mem_eSub.2 ⟨v, blockConst_even hv, rfl⟩

theorem signPerm_bU : signPerm bU = frameElt bU := by
  rw [bU, signPerm_add (vec2_mem_evenSub 4 5 (by decide)) (vec2_mem_evenSub 6 7 (by decide)),
    signPerm_vec2_45, signPerm_vec2_67, frameElt_add]

theorem uSub_le_e1Sub : uSub ≤ e1Sub := by
  rw [uSub, closure_le]
  rintro g (rfl | rfl)
  · change xPlane ∈ e1Sub
    rw [xPlane_eq_frameElt]
    exact mem_e1Sub.2 ⟨_, rfl⟩
  · change signPerm bU ∈ e1Sub
    rw [signPerm_bU]
    exact mem_e1Sub.2 ⟨_, rfl⟩

@[expose] def uStab : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | (permVec σ aU = aU ∧ permVec σ bU = bU) ∨
    (permVec σ aU = bU ∧ permVec σ bU = aU)}
  one_mem' := Or.inl ⟨permVec_one _, permVec_one _⟩
  mul_mem' {σ τ} hσ hτ := by
    change (permVec (σ * τ) aU = aU ∧ permVec (σ * τ) bU = bU) ∨
      (permVec (σ * τ) aU = bU ∧ permVec (σ * τ) bU = aU)
    rw [permVec_mul, permVec_mul]
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hτ with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨by rw [h3, h1], by rw [h4, h2]⟩
    · exact Or.inr ⟨by rw [h3, h2], by rw [h4, h1]⟩
    · exact Or.inr ⟨by rw [h3, h1], by rw [h4, h2]⟩
    · exact Or.inl ⟨by rw [h3, h2], by rw [h4, h1]⟩
  inv_mem' {σ} hσ := by
    change (permVec σ⁻¹ aU = aU ∧ permVec σ⁻¹ bU = bU) ∨
      (permVec σ⁻¹ aU = bU ∧ permVec σ⁻¹ bU = aU)
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by conv_lhs => rw [← h1]; exact permVec_inv_permVec σ aU,
        by conv_lhs => rw [← h2]; exact permVec_inv_permVec σ bU⟩
    · right
      exact ⟨by conv_lhs => rw [← h2]; exact permVec_inv_permVec σ bU,
        by conv_lhs => rw [← h1]; exact permVec_inv_permVec σ aU⟩

theorem pSub_le_uStab : pSub ≤ uStab := by
  rw [pSub, closure_le]
  intro σ hσ
  simp only [pPlusGens, Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inr ⟨by decide, by decide⟩

theorem blockConst_permVec {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ pSub) {v : FrameVec}
    (hv : blockConst v) : blockConst (permVec σ v) := by
  have hite : ∀ (c : Prop) [Decidable c] (w : FrameVec), blockConst (permVec σ w) →
      blockConst (permVec σ (if c then w else 0)) := by
    intro c _ w hw
    split_ifs
    · exact hw
    · exact blockConst_zero
  have hab : blockConst (permVec σ aU) ∧ blockConst (permVec σ bU) := by
    rcases pSub_le_uStab hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨blockConst_aU, blockConst_bU⟩
    · rw [h1, h2]; exact ⟨blockConst_bU, blockConst_aU⟩
  rw [blockConst_decomp hv, permVec_add]
  exact blockConst_add (hite _ _ hab.1) (hite _ _ hab.2)

theorem uSub_normal {t : Equiv.Perm (Fin 240)} (ht : t ∈ tSub) {u : Equiv.Perm (Fin 240)}
    (hu : u ∈ uSub) : t * u * t⁻¹ ∈ uSub := by
  obtain ⟨w, hw, σ, hσ, rfl⟩ := mem_tSub_iff_decomp.1 ht
  obtain ⟨v, hv, rfl⟩ := mem_uSub_iff.1 hu
  have hve := blockConst_even hv
  rw [show signPerm w * permMat σ * signPerm v * (signPerm w * permMat σ)⁻¹ =
    signPerm w * (permMat σ * signPerm v * (permMat σ)⁻¹) * (signPerm w)⁻¹ by group,
    permMat_conj_signPerm σ hve, eSub_comm (mem_eSub.2 ⟨w, hw, rfl⟩)
      (mem_eSub.2 ⟨_, permVec_mem_evenSub σ hve, rfl⟩), mul_inv_cancel_right]
  exact mem_uSub_iff.2 ⟨_, blockConst_permVec hσ hv, rfl⟩

theorem permVec_aU_of_mem {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ pSub) :
    permVec σ aU = aU ∨ permVec σ aU = bU := by
  rcases pSub_le_uStab hσ with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

theorem conj_xPlane {t : Equiv.Perm (Fin 240)} (ht : t ∈ tSub) :
    t * xPlane * t⁻¹ = xPlane ∨ t * xPlane * t⁻¹ = signPerm bU := by
  obtain ⟨w, hw, σ, hσ, rfl⟩ := mem_tSub_iff_decomp.1 ht
  rw [show signPerm w * permMat σ * xPlane * (signPerm w * permMat σ)⁻¹ =
    signPerm w * (permMat σ * signPerm aU * (permMat σ)⁻¹) * (signPerm w)⁻¹ by
      rw [xPlane_eq_aU]; group,
    permMat_conj_signPerm σ aU_mem_evenSub, eSub_comm (mem_eSub.2 ⟨w, hw, rfl⟩)
      (mem_eSub.2 ⟨_, permVec_mem_evenSub σ aU_mem_evenSub, rfl⟩), mul_inv_cancel_right]
  rcases permVec_aU_of_mem hσ with h | h
  · left; rw [h]; rfl
  · right; rw [h]

theorem signPerm_bU_ne : signPerm bU ≠ xPlane := fun h =>
  absurd (signPerm_inj bU_mem_evenSub aU_mem_evenSub h) (by decide)

theorem xPlane_mul_zPerm : xPlane * zPerm = signPerm bU := by
  rw [← signPerm_frameZ, xPlane_eq_aU, ← signPerm_add aU_mem_evenSub frameZ_mem_evenSub,
    frameZ_eq_aU_add_bU, ← add_assoc, frameVec_add_self, zero_add]

theorem signPerm_bU_mul_zPerm : signPerm bU * zPerm = xPlane := by
  rw [← xPlane_mul_zPerm, mul_assoc, zPerm_mul_self, mul_one]

theorem conj_zPerm {t : Equiv.Perm (Fin 240)} (ht : t ∈ wE8) : t * zPerm * t⁻¹ = zPerm := by
  rw [zPerm_comm t ht, mul_inv_cancel_right]

@[expose] def xChar : tSub →* ℤˣ where
  toFun t := if (t : Equiv.Perm (Fin 240)) * xPlane * (t : Equiv.Perm (Fin 240))⁻¹ = xPlane
    then 1 else -1
  map_one' := by simp
  map_mul' s t := by
    have hs := conj_xPlane s.2
    have ht := conj_xPlane t.2
    have hzs := conj_zPerm (tSub_le_wE8 s.2)
    have hst : ((s * t : tSub) : Equiv.Perm (Fin 240)) * xPlane *
        ((s * t : tSub) : Equiv.Perm (Fin 240))⁻¹ = (s : Equiv.Perm (Fin 240)) *
          ((t : Equiv.Perm (Fin 240)) * xPlane * (t : Equiv.Perm (Fin 240))⁻¹) *
            (s : Equiv.Perm (Fin 240))⁻¹ := by
      rw [coe_mul]; group
    have hy : (s : Equiv.Perm (Fin 240)) * signPerm bU * (s : Equiv.Perm (Fin 240))⁻¹ =
        (s : Equiv.Perm (Fin 240)) * xPlane * (s : Equiv.Perm (Fin 240))⁻¹ * zPerm := by
      calc (s : Equiv.Perm (Fin 240)) * signPerm bU * (s : Equiv.Perm (Fin 240))⁻¹
          = (s : Equiv.Perm (Fin 240)) * xPlane * (s : Equiv.Perm (Fin 240))⁻¹ *
            ((s : Equiv.Perm (Fin 240)) * zPerm * (s : Equiv.Perm (Fin 240))⁻¹) := by
            rw [← xPlane_mul_zPerm]; group
        _ = _ := by rw [hzs]
    rw [hst]
    rcases ht with ht | ht <;> rcases hs with hs | hs
    · simp [ht, hs]
    · simp [ht, hs, signPerm_bU_ne]
    · rw [ht, hy, hs, xPlane_mul_zPerm]
      simp [signPerm_bU_ne]
    · rw [ht, hy, hs, signPerm_bU_mul_zPerm]
      simp [signPerm_bU_ne]

theorem conj_eq_iff_comm {t x : Equiv.Perm (Fin 240)} : t * x * t⁻¹ = x ↔ t * x = x * t := by
  rw [mul_inv_eq_iff_eq_mul]

theorem mem_ker_xChar {t : tSub} :
    t ∈ xChar.ker ↔ (t : Equiv.Perm (Fin 240)) ∈ centralizer {xPlane} := by
  rw [MonoidHom.mem_ker, mem_centralizer_singleton_iff]
  change (if (t : Equiv.Perm (Fin 240)) * xPlane * (t : Equiv.Perm (Fin 240))⁻¹ = xPlane
    then 1 else -1) = 1 ↔ _
  rw [← conj_eq_iff_comm]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem sigma04_mem : Equiv.swap (0 : Fin 8) 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7 ∈
    pPlusSub := pPlusGen_mem_pPlusSub (by decide)

theorem xChar_surjective : Function.Surjective xChar := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · set σ := Equiv.swap (0 : Fin 8) 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7
    have hσ : permMat σ ∈ tSub := tPlusSub_le_tSub (permMat_mem_tPlusSub sigma04_mem)
    refine ⟨⟨permMat σ, hσ⟩, ?_⟩
    change (if permMat σ * xPlane * (permMat σ)⁻¹ = xPlane then 1 else -1) = -1
    rw [xPlane_eq_aU, permMat_conj_signPerm σ aU_mem_evenSub,
      show permVec σ aU = bU by decide, ← xPlane_eq_aU]
    simp [signPerm_bU_ne]

theorem card_cT : Nat.card (tSub ⊓ centralizer {xPlane} : Subgroup (Equiv.Perm (Fin 240))) =
    2 ^ 13 := by
  have h1 := Subgroup.card_mul_index xChar.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 xChar_surjective, card_top,
    Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, card_tSub] at h1
  have h2 : Nat.card xChar.ker = Nat.card (tSub ⊓ centralizer {xPlane} :
      Subgroup (Equiv.Perm (Fin 240))) := Nat.card_congr
    { toFun := fun t => ⟨(t : tSub), mem_inf.2 ⟨(t : tSub).2, mem_ker_xChar.1 t.2⟩⟩
      invFun := fun y => ⟨⟨y, (mem_inf.1 y.2).1⟩, mem_ker_xChar.2 (mem_inf.1 y.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← h2]
  omega

theorem centralizer_iff_uSub {t : Equiv.Perm (Fin 240)} (ht : t ∈ tSub) :
    t * xPlane = xPlane * t ↔ ∀ u ∈ uSub, t * u = u * t := by
  refine ⟨fun h u hu => ?_, fun h => h _ xPlane_mem_uSub⟩
  have hz := zPerm_comm t (tSub_le_wE8 ht)
  have hle : uSub ≤ centralizer {t} := by
    rw [uSub, closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 h.symm
    · change signPerm bU ∈ centralizer {t}
      rw [← xPlane_mul_zPerm, mem_centralizer_singleton_iff]
      rw [mul_assoc, ← hz, ← mul_assoc, ← h, mul_assoc]
  exact (mem_centralizer_singleton_iff.1 (hle hu)).symm

theorem e1Sub_le_centralizer_xPlane : e1Sub ≤ centralizer {xPlane} := by
  intro e he
  rw [mem_centralizer_singleton_iff]
  have hx : xPlane ∈ e1Sub := by rw [xPlane_eq_frameElt]; exact mem_e1Sub.2 ⟨_, rfl⟩
  exact e1Sub_comm he hx

@[expose] def cSub : Subgroup (Equiv.Perm (Fin 240)) := tSub ⊓ centralizer {xPlane}

@[expose] def cGamma : Set (Equiv.Perm (Fin 240)) :=
  signPerm '' (evenSub : Set FrameVec) ∪ {g | ∃ σ ∈ cGens, permMat σ = g}

theorem cGens_spec : ∀ σ ∈ cGens, σ ∈ pSub ∧ permVec σ aU = aU := by
  intro σ hσ
  simp only [cGens, List.mem_cons, List.mem_nil_iff, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨swap01_mem_pSub, by decide⟩
  · exact ⟨pPlusGen_mem_pSub (by decide), by decide⟩
  · exact ⟨pPlusGen_mem_pSub (by decide), by decide⟩
  · exact ⟨pPlusGen_mem_pSub (by decide), by decide⟩
  · exact ⟨pPlusGen_mem_pSub (by decide), by decide⟩
  · exact ⟨pPlusGen_mem_pSub (by decide), by decide⟩

theorem permMat_comm_xPlane {σ : Equiv.Perm (Fin 8)} (h : permVec σ aU = aU) :
    permMat σ * xPlane = xPlane * permMat σ := by
  rw [← conj_eq_iff_comm, xPlane_eq_aU, permMat_conj_signPerm σ aU_mem_evenSub, h]

theorem cGamma_subset : cGamma ⊆ cSub := by
  rintro g (⟨v, hv, rfl⟩ | ⟨σ, hσ, rfl⟩)
  · refine mem_inf.2 ⟨eSub_le_tSub (mem_eSub.2 ⟨v, hv, rfl⟩), ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact eSub_comm (mem_eSub.2 ⟨v, hv, rfl⟩) (mem_eSub.2 ⟨aU, aU_mem_evenSub, rfl⟩)
  · obtain ⟨h1, h2⟩ := cGens_spec σ hσ
    exact mem_inf.2 ⟨permMat_mem_tSub h1, mem_centralizer_singleton_iff.2
      (permMat_comm_xPlane h2)⟩

theorem cList_length : cList.length = 64 := rfl

theorem cList_nodup : cList.Nodup := by decide +kernel

theorem cList_mul : ∀ i < 64, ∀ k < 6,
    cGens.getD k 1 * cList.getD i 1 = cList.getD ((cTab.getD i []).getD k 0) 1 := by
  decide +kernel

theorem cTab_lt : ∀ i < 64, ∀ k < 6, (cTab.getD i []).getD k 0 < 64 := by decide

theorem cGens_getD_mem {k : ℕ} (hk : k < 6) : cGens.getD k 1 ∈ cGens := by
  rw [List.getD_eq_getElem _ _ (by simpa [cGens] using hk)]
  exact List.getElem_mem _

theorem mem_cGens_iff {g : Equiv.Perm (Fin 8)} : g ∈ cGens ↔ ∃ k < 6, cGens.getD k 1 = g := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
    exact ⟨k, by simpa [cGens] using hk, by rw [List.getD_eq_getElem]⟩
  · rintro ⟨k, hk, rfl⟩
    exact cGens_getD_mem hk

theorem cList_mem_closure : ∀ x ∈ cList, x ∈ closure {σ | σ ∈ cGens} := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  refine list_prod_mem fun g hg => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  by_cases hk : k < 6
  · exact subset_closure (cGens_getD_mem hk)
  · rw [List.getD_eq_default _ _ (by simpa [cGens] using hk)]
    exact one_mem _

theorem mem_cList_of_closure {x : Equiv.Perm (Fin 8)} (hx : x ∈ closure {σ | σ ∈ cGens}) :
    x ∈ cList := by
  have step : ∀ g ∈ cGens, ∀ y ∈ cList, g * y ∈ cList := by
    intro g hg y hy
    obtain ⟨k, hk, rfl⟩ := mem_cGens_iff.1 hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    rw [cList_length] at hi
    rw [← List.getD_eq_getElem _ 1 (by rw [cList_length]; exact hi), cList_mul i hi k hk]
    rw [List.getD_eq_getElem _ _ (by rw [cList_length]; exact cTab_lt i hi k hk)]
    exact List.getElem_mem _
  refine closure_induction_left (p := fun y _ => y ∈ cList) (by decide) (fun g hg y _ hy => step g hg y hy)
    (fun g hg y _ hy => ?_) hx
  have hgg : g * g = 1 := by
    obtain ⟨k, hk, rfl⟩ := mem_cGens_iff.1 hg
    interval_cases k <;> decide
  rw [inv_eq_of_mul_eq_one_right hgg]
  exact step g hg y hy

theorem card_closure_cGens : Nat.card (closure {σ | σ ∈ cGens}) = 64 := by
  have e : closure {σ | σ ∈ cGens} ≃ cList.toFinset := Equiv.subtypeEquivRight fun x =>
    ⟨fun h => List.mem_toFinset.2 (mem_cList_of_closure h),
      fun h => cList_mem_closure x (List.mem_toFinset.1 h)⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup cList_nodup, cList_length]

theorem card_closure_cGamma : Nat.card (closure cGamma) = 2 ^ 13 := by
  have e : evenSub × closure {σ | σ ∈ cGens} ≃ closure cGamma :=
    Equiv.ofBijective (fun p => ⟨signPerm p.1 * permMat p.2,
      (mem_closure_decomp cGens).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩) ⟨fun p q h => by
        have h1 := decomp_unique (mem_eSub.2 ⟨p.1, p.1.2, rfl⟩) (mem_eSub.2 ⟨q.1, q.1.2, rfl⟩)
          (congrArg Subtype.val h)
        exact Prod.ext (Subtype.ext (signPerm_inj p.1.2 q.1.2 h1.1)) (Subtype.ext h1.2),
      fun x => by
        obtain ⟨v, hv, σ, hσ, he⟩ := (mem_closure_decomp cGens).1 x.2
        exact ⟨(⟨v, hv⟩, ⟨σ, hσ⟩), Subtype.ext he.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, card_closure_cGens, Nat.card_congr evenSubEquiv.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem cSub_eq_closure : cSub = closure cGamma := by
  symm
  refine eq_of_le_of_card_ge ((closure_le _).2 cGamma_subset) ?_
  rw [card_closure_cGamma, cSub, card_cT]

theorem rep_signArrs {v : ℕ} (hv : v < 256) (he : framePop v % 2 = 0) :
    Rep 240 signArrs[v]! (signPerm (frameDecode v)) := by
  rw [signArrs_get hv]
  exact rep_signArr (decode_mem_evenSub hv he)

theorem tElt_false (c : ArrCert) (i : ℕ) : tElt c i false = c.pts[i]! := by
  simp only [tElt, Bool.false_eq_true, ite_false]

theorem rep_tInv {i : ℕ} (hi : i < 8192) {b : Bool} {X : Equiv.Perm (Fin 240)}
    (hX : Rep 240 (tElt tPlusCert i b) X) : Rep 240 (tInv tPlusCert i b) X⁻¹ := by
  have hv : validA 240 tPlusCert.pts[i]! = true := by
    have := t_facts.valid i hi
    rwa [tElt_false] at this
  have hP := rep_of_validA hv
  have hPi := rep_inv_of_validA hv
  cases b
  · rw [tElt_false] at hX
    rw [hX.unique hP]
    simpa [tInv] using hPi
  · rw [tElt_true, tElt_false] at hX
    rw [hX.unique (rep_compA hP rep_s0Arr), mul_inv_rev,
      inv_eq_of_mul_eq_one_right sZero_mul_self]
    simpa [tInv] using rep_compA rep_s0Arr hPi

theorem rep_commInv {t ti d : Array ℕ} {X D : Equiv.Perm (Fin 240)} (ht : Rep 240 t X)
    (hti : Rep 240 ti X⁻¹) (hd : Rep 240 d D) (hD : D * D = 1) :
    Rep 240 (commInv t ti d) (X * D * X⁻¹ * D⁻¹) := by
  rw [inv_eq_of_mul_eq_one_right hD]
  exact rep_compA (rep_compA (rep_compA ht hd) hti) hd

theorem decode_15 : frameDecode 15 = aU := by decide

theorem decode_240 : frameDecode 240 = bU := by decide

theorem signArrs_15 : Rep 240 signArrs[15]! xPlane := by
  have := rep_signArrs (v := 15) (by norm_num) (by decide)
  rwa [decode_15] at this

theorem signArrs_240 : Rep 240 signArrs[240]! (signPerm bU) := by
  have := rep_signArrs (v := 240) (by norm_num) (by decide)
  rwa [decode_240] at this

theorem cGens_involution : ∀ g ∈ cGens, g * g = 1 := by
  intro g hg
  simp only [cGens, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem permMat_involution {g : Equiv.Perm (Fin 8)} (hg : g ∈ cGens) :
    permMat g * permMat g = 1 := by
  rw [← permMat_mul, cGens_involution g hg, permMat_one]

theorem xPlane_mem_cSub : xPlane ∈ cSub := cGamma_subset (Or.inl ⟨aU, aU_mem_evenSub, rfl⟩)

theorem signPerm_mem_cSub {v : FrameVec} (hv : v ∈ evenSub) : signPerm v ∈ cSub :=
  cGamma_subset (Or.inl ⟨v, hv, rfl⟩)

theorem permMat_mem_cSub {g : Equiv.Perm (Fin 8)} (hg : g ∈ cGens) : permMat g ∈ cSub :=
  cGamma_subset (Or.inr ⟨g, hg, rfl⟩)

theorem mem_uSub_of_signPerm_bU : signPerm bU ∈ uSub := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem center_cT_spec {c : Equiv.Perm (Fin 240)} (hc : c ∈ cSub) :
    (∀ d ∈ cSub, c * d = d * c) ↔ c ∈ uSub := by
  constructor
  · intro hcen
    obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub (mem_inf.1 hc).1
    have hcomm : commGensC (tElt tPlusCert i b) = true := by
      rw [commGensC, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
      refine ⟨⟨commA'_of_comm hrep signArrs_15 (hcen _ xPlane_mem_cSub), fun v hv => ?_⟩,
        fun g hg => commA'_of_comm hrep (rep_permArr g) (hcen _ (permMat_mem_cSub hg))⟩
      rw [Bool.or_eq_true]
      by_cases he : framePop v % 2 = 0
      · right
        exact commA'_of_comm hrep (rep_signArrs (List.mem_range.1 hv) he)
          (hcen _ (signPerm_mem_cSub (decode_mem_evenSub (List.mem_range.1 hv) he)))
      · left
        simpa using he
    have h := centerC_check
    rw [centerCCheck] at h
    have h1 := List.all_eq_true.1 (allLt_spec h hi) b hb
    simp only [hcomm, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
    rcases h1 with ((h2 | h2) | h2) | h2
    · rw [(isId_iff hrep).1 h2]
      exact one_mem _
    · rw [eq_of_eqA hrep signArrs_15 h2]
      exact xPlane_mem_uSub
    · rw [eq_of_eqA hrep signArrs_240 h2]
      exact mem_uSub_of_signPerm_bU
    · rw [(eqA_negArr_iff hrep).1 h2]
      exact zPerm_mem_uSub
  · intro hu d hd
    have hdx : d * xPlane = xPlane * d := mem_centralizer_singleton_iff.1 (mem_inf.1 hd).2
    exact ((centralizer_iff_uSub (mem_inf.1 hd).1).1 hdx c hu).symm

theorem decode_5 : frameDecode 5 = vec2 0 2 := by decide

theorem decode_80 : frameDecode 80 = vec2 4 6 := by decide

theorem signArrs_5 : Rep 240 signArrs[5]! (signPerm (vec2 0 2)) := by
  have := rep_signArrs (v := 5) (by norm_num) (by decide)
  rwa [decode_5] at this

theorem signArrs_80 : Rep 240 signArrs[80]! (signPerm (vec2 4 6)) := by
  have := rep_signArrs (v := 80) (by norm_num) (by decide)
  rwa [decode_80] at this

theorem center_mod_spec {c : Equiv.Perm (Fin 240)} (hc : c ∈ cSub)
    (hmod : ∀ d ∈ cSub, c * d * c⁻¹ * d⁻¹ ∈ e1Sub) :
    c ∈ e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)} := by
  obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub (mem_inf.1 hc).1
  have hinv := rep_tInv hi hrep
  have hmodGens : commModGens (tElt tPlusCert i b) (tInv tPlusCert i b) = true := by
    rw [commModGens, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨⟨commA'_of_comm hrep signArrs_15
      ((mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2)), fun v hv => ?_⟩, fun g hg => ?_⟩
    · rw [Bool.or_eq_true]
      by_cases he : framePop v % 2 = 0
      · right
        have hv' := List.mem_range.1 hv
        have hve := decode_mem_evenSub hv' he
        exact memE1_of_mem (rep_commInv hrep hinv (rep_signArrs hv' he) (signPerm_mul_self hve))
          (hmod _ (signPerm_mem_cSub hve))
      · left
        simpa using he
    · exact memE1_of_mem (rep_commInv hrep hinv (rep_permArr g) (permMat_involution hg))
        (hmod _ (permMat_mem_cSub hg))
  have h := centerMod_check
  rw [centerModCheck] at h
  have h1 := List.all_eq_true.1 (allLt_spec h hi) b hb
  simp only [hmodGens, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  have hS02 : signPerm (vec2 0 2) ∈ (e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)} :
      Subgroup (Equiv.Perm (Fin 240))) := mem_sup_right (subset_closure (Set.mem_insert _ _))
  have hS46 : signPerm (vec2 4 6) ∈ (e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)} :
      Subgroup (Equiv.Perm (Fin 240))) :=
    mem_sup_right (subset_closure (Set.mem_insert_of_mem _ rfl))
  rcases h1 with ((h2 | h2) | h2) | h2
  · exact mem_sup_left (mem_e1Sub_of_memE1 hrep h2)
  · have h3 := mem_sup_left (T := closure {signPerm (vec2 0 2), signPerm (vec2 4 6)})
      (mem_e1Sub_of_memE1 (rep_compA hrep signArrs_5) h2)
    have := mul_mem h3 (inv_mem hS02)
    rwa [mul_inv_cancel_right] at this
  · have h3 := mem_sup_left (T := closure {signPerm (vec2 0 2), signPerm (vec2 4 6)})
      (mem_e1Sub_of_memE1 (rep_compA hrep signArrs_80) h2)
    have := mul_mem h3 (inv_mem hS46)
    rwa [mul_inv_cancel_right] at this
  · have h3 := mem_sup_left (T := closure {signPerm (vec2 0 2), signPerm (vec2 4 6)})
      (mem_e1Sub_of_memE1 (rep_compA (rep_compA hrep signArrs_5) signArrs_80) h2)
    have := mul_mem (mul_mem h3 (inv_mem hS46)) (inv_mem hS02)
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this

theorem conj_mem_e1Sub_of_tSub {t : Equiv.Perm (Fin 240)} (ht : t ∈ tSub)
    {g : Equiv.Perm (Fin 240)} (hg : g ∈ e1Sub) : t * g * t⁻¹ ∈ e1Sub := by
  set B := e1Sub.map (MulAut.conj t).toMonoidHom with hBdef
  have hBT : B ≤ tSub := by
    rintro _ ⟨e, he, rfl⟩
    exact mul_mem (mul_mem ht (e1Sub_le_tSub he)) (inv_mem ht)
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show t * e * t⁻¹ * (t * f * t⁻¹) = t * (e * f) * t⁻¹ by group,
      show t * f * t⁻¹ * (t * e * t⁻¹) = t * (f * e) * t⁻¹ by group, e1Sub_comm he hf]
  have hBc : 2 ^ 8 ≤ Nat.card B := by
    rw [hBdef, card_map_of_injective (MulEquiv.injective _), card_e1Sub]
  have hB := abelian_t_spec B hBT hBab hBc
  rw [← hB]
  exact ⟨g, hg, rfl⟩

theorem tSub_le_normalizer_e1Sub : tSub ≤ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) := by
  intro t ht
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_e1Sub_of_tSub ht, fun h => ?_⟩
  have := conj_mem_e1Sub_of_tSub (inv_mem ht) h
  rwa [inv_inv, show t⁻¹ * (t * g * t⁻¹) * t = g by group] at this

@[expose] def commE1Sub (s : Equiv.Perm (Fin 240)) : Subgroup (Equiv.Perm (Fin 240)) where
  carrier := {d | d ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) ∧ s * d * s⁻¹ * d⁻¹ ∈ e1Sub}
  one_mem' := ⟨one_mem _, by rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact one_mem _⟩
  mul_mem' {d₁ d₂} h₁ h₂ := by
    refine ⟨mul_mem h₁.1 h₂.1, ?_⟩
    have h3 := (mem_normalizer_iff.1 h₁.1 _).1 h₂.2
    have := mul_mem h₁.2 h3
    rwa [show s * d₁ * s⁻¹ * d₁⁻¹ * (d₁ * (s * d₂ * s⁻¹ * d₂⁻¹) * d₁⁻¹) =
      s * (d₁ * d₂) * s⁻¹ * (d₁ * d₂)⁻¹ by group] at this
  inv_mem' {d} h := by
    refine ⟨inv_mem h.1, ?_⟩
    have h3 := (mem_normalizer_iff.1 (inv_mem h.1) _).1 (inv_mem h.2)
    rwa [show d⁻¹ * (s * d * s⁻¹ * d⁻¹)⁻¹ * d⁻¹⁻¹ = s * d⁻¹ * s⁻¹ * d⁻¹⁻¹ by group] at h3

theorem pairConst_add {u v : FrameVec} (hu : pairConst u) (hv : pairConst v) :
    pairConst (u + v) := by
  obtain ⟨u1, u2, u3, u4⟩ := hu
  obtain ⟨v1, v2, v3, v4⟩ := hv
  exact ⟨by simp [u1, v1], by simp [u2, v2], by simp [u3, v3], by simp [u4, v4]⟩

theorem comm_permMat_mem {w : FrameVec} (hw : w ∈ evenSub) {g : Equiv.Perm (Fin 8)}
    (hp : pairConst (w + permVec g w)) :
    signPerm w * permMat g * (signPerm w)⁻¹ * (permMat g)⁻¹ ∈ e1Sub := by
  rw [show signPerm w * permMat g * (signPerm w)⁻¹ * (permMat g)⁻¹ =
    signPerm w * (permMat g * (signPerm w)⁻¹ * (permMat g)⁻¹) by group, signPerm_inv hw,
    permMat_conj_signPerm g hw, ← signPerm_add hw (permVec_mem_evenSub g hw)]
  exact kOneSub_le_e1Sub (signPerm_mem_kOneSub hp)

theorem cGens_pair02 : ∀ g ∈ cGens, pairConst (vec2 0 2 + permVec g (vec2 0 2)) := by
  intro g hg
  simp only [cGens, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem cGens_pair46 : ∀ g ∈ cGens, pairConst (vec2 4 6 + permVec g (vec2 4 6)) := by
  intro g hg
  simp only [cGens, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem cSub_le_commE1Sub {w : FrameVec} (hw : w ∈ evenSub)
    (hg : ∀ g ∈ cGens, pairConst (w + permVec g w)) : cSub ≤ commE1Sub (signPerm w) := by
  rw [cSub_eq_closure, closure_le]
  rintro d (⟨v, hv, rfl⟩ | ⟨g, hgm, rfl⟩)
  · refine ⟨tSub_le_normalizer_e1Sub (eSub_le_tSub (mem_eSub.2 ⟨v, hv, rfl⟩)), ?_⟩
    rw [eSub_comm (mem_eSub.2 ⟨w, hw, rfl⟩) (mem_eSub.2 ⟨v, hv, rfl⟩), mul_inv_cancel_right,
      mul_inv_cancel]
    exact one_mem _
  · exact ⟨tSub_le_normalizer_e1Sub (permMat_mem_tSub (cGens_spec g hgm).1),
      comm_permMat_mem hw (hg g hgm)⟩

@[expose] def centerModSub : Subgroup (Equiv.Perm (Fin 240)) where
  carrier := {c | c ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) ∧
    ∀ d ∈ cSub, c * d * c⁻¹ * d⁻¹ ∈ e1Sub}
  one_mem' := ⟨one_mem _, fun d _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _⟩
  mul_mem' {c₁ c₂} h₁ h₂ := by
    refine ⟨mul_mem h₁.1 h₂.1, fun d hd => ?_⟩
    have h3 := (mem_normalizer_iff.1 h₁.1 _).1 (h₂.2 d hd)
    have := mul_mem h3 (h₁.2 d hd)
    rwa [show c₁ * (c₂ * d * c₂⁻¹ * d⁻¹) * c₁⁻¹ * (c₁ * d * c₁⁻¹ * d⁻¹) =
      c₁ * c₂ * d * (c₁ * c₂)⁻¹ * d⁻¹ by group] at this
  inv_mem' {c} h := by
    refine ⟨inv_mem h.1, fun d hd => ?_⟩
    have h3 := (mem_normalizer_iff.1 (inv_mem h.1) _).1 (inv_mem (h.2 d hd))
    rwa [show c⁻¹ * (c * d * c⁻¹ * d⁻¹)⁻¹ * c⁻¹⁻¹ = c⁻¹ * d * c⁻¹⁻¹ * d⁻¹ by group] at h3

theorem center_mod_rev {c : Equiv.Perm (Fin 240)}
    (hc : c ∈ e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)}) :
    ∀ d ∈ cSub, c * d * c⁻¹ * d⁻¹ ∈ e1Sub := by
  have hle : e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)} ≤ centerModSub := by
    refine sup_le (fun e he => ⟨le_normalizer he, fun d hd => ?_⟩) ?_
    · have h1 := (mem_normalizer_iff.1 (tSub_le_normalizer_e1Sub (mem_inf.1 hd).1) _).1
        (inv_mem he)
      have := mul_mem he h1
      rwa [show e * (d * e⁻¹ * d⁻¹) = e * d * e⁻¹ * d⁻¹ by group] at this
    · rw [closure_le]
      have h02 := vec2_mem_evenSub 0 2 (by decide)
      have h46 := vec2_mem_evenSub 4 6 (by decide)
      rintro s (rfl | rfl)
      · exact ⟨tSub_le_normalizer_e1Sub (eSub_le_tSub (mem_eSub.2 ⟨_, h02, rfl⟩)),
          fun d hd => (cSub_le_commE1Sub h02 cGens_pair02 hd).2⟩
      · exact ⟨tSub_le_normalizer_e1Sub (eSub_le_tSub (mem_eSub.2 ⟨_, h46, rfl⟩)),
          fun d hd => (cSub_le_commE1Sub h46 cGens_pair46 hd).2⟩
  exact (hle hc).2

theorem frameArrs_rep (v : ℕ) (hv : v < 256) :
    Rep 240 frameArrs[v]! (frameElt (frameDecode v)) := by
  rw [frameArrs_get hv]
  exact rep_frameArr _

theorem commSet_spec {s : Array ℕ} {S : Equiv.Perm (Fin 240)} (hs : Rep 240 s S)
    (hS : S * S = 1) {ws : List ℕ} (hws : ∀ w ∈ ws, w < 256 ∧ framePop w % 2 = 0)
    (h : commSetOK s ws = true) (g : Equiv.Perm (Fin 240)) :
    (∃ e ∈ e1Sub, g = e * S * e⁻¹ * S⁻¹) ↔ ∃ w ∈ ws, g = signPerm (frameDecode w) := by
  rw [commSetOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have hrep : ∀ v < 256, Rep 240 (commInv frameArrs[v]! frameArrs[v]! s)
      (frameElt (frameDecode v) * S * (frameElt (frameDecode v))⁻¹ * S⁻¹) := fun v hv =>
    rep_commInv (frameArrs_rep v hv) (by rw [frameElt_inv]; exact frameArrs_rep v hv) hs hS
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨u, rfl⟩ := mem_e1Sub.1 he
    have hu := frameEncode_lt u
    have h1 := h.1 _ (List.mem_range.2 hu)
    rw [List.any_eq_true] at h1
    obtain ⟨w, hw, he'⟩ := h1
    refine ⟨w, hw, ?_⟩
    have := eq_of_eqA (hrep _ hu) (rep_signArrs (hws w hw).1 (hws w hw).2) he'
    rwa [frameDecode_frameEncode] at this
  · rintro ⟨w, hw, rfl⟩
    have h1 := h.2 w hw
    rw [List.any_eq_true] at h1
    obtain ⟨v, hv, he'⟩ := h1
    have hv' := List.mem_range.1 hv
    exact ⟨_, mem_e1Sub.2 ⟨_, rfl⟩,
      (eq_of_eqA (hrep v hv') (rep_signArrs (hws w hw).1 (hws w hw).2) he').symm⟩

theorem commSet_facts : commSetOK signArrs[5]! [0, 3, 12, 15] = true ∧
    commSetOK signArrs[80]! [0, 48, 192, 240] = true ∧
      commSetOK signArrs[85]! pairMasks16 = true := by
  have h := commSet_check
  rw [commSetCheck, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] def p02 (v : FrameVec) : Prop := pairConst v ∧ v 4 = 0 ∧ v 6 = 0

@[expose] def p46 (v : FrameVec) : Prop := pairConst v ∧ v 0 = 0 ∧ v 2 = 0

instance (v : FrameVec) : Decidable (p02 v) := by
  unfold p02 pairConst
  infer_instance

instance (v : FrameVec) : Decidable (p46 v) := by
  unfold p46 pairConst
  infer_instance

theorem p02_masks : ∀ n < 256, p02 (frameDecode n) ↔ n = 0 ∨ n = 3 ∨ n = 12 ∨ n = 15 := by
  unfold p02 pairConst
  decide +kernel

theorem p46_masks : ∀ n < 256, p46 (frameDecode n) ↔ n = 0 ∨ n = 48 ∨ n = 192 ∨ n = 240 := by
  unfold p46 pairConst
  decide +kernel

theorem pair_masks : ∀ n < 256, pairConst (frameDecode n) ↔ n ∈ pairMasks16 := by
  unfold pairConst
  decide +kernel

theorem signPerm_mem_closure_of_decomp {S : Set (Equiv.Perm (Fin 240))} {v : FrameVec}
    (hv : pairConst v) (h01 : v 0 = 1 → signPerm (vec2 0 1) ∈ closure S)
    (h23 : v 2 = 1 → signPerm (vec2 2 3) ∈ closure S)
    (h45 : v 4 = 1 → signPerm (vec2 4 5) ∈ closure S)
    (h67 : v 6 = 1 → signPerm (vec2 6 7) ∈ closure S) : signPerm v ∈ closure S := by
  have hite : ∀ (c : Prop) [Decidable c] {i j : Fin 8}, i ≠ j → (c → signPerm (vec2 i j) ∈
      closure S) → (if c then vec2 i j else 0) ∈ evenSub ∧
        signPerm (if c then vec2 i j else 0) ∈ closure S := by
    intro c _ i j hij h
    split_ifs with hc
    · exact ⟨vec2_mem_evenSub i j hij, h hc⟩
    · exact ⟨zero_mem _, by rw [signPerm_zero]; exact one_mem _⟩
  obtain ⟨a1, a2⟩ := hite (v 0 = 1) (by decide) h01
  obtain ⟨b1, b2⟩ := hite (v 2 = 1) (by decide) h23
  obtain ⟨c1, c2⟩ := hite (v 4 = 1) (by decide) h45
  obtain ⟨d1, d2⟩ := hite (v 6 = 1) (by decide) h67
  rw [pairConst_decomp v hv, signPerm_add (add_mem (add_mem a1 b1) c1) d1,
    signPerm_add (add_mem a1 b1) c1, signPerm_add a1 b1]
  exact mul_mem (mul_mem (mul_mem a2 b2) c2) d2

theorem zmod2_two_add : ∀ a b c d : ZMod 2, a + a + (b + b) + (c + c) + (d + d) = 0 := by decide

theorem pairConst_even {v : FrameVec} (hv : pairConst v) : v ∈ evenSub := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  rw [mem_evenSub, Fin.sum_univ_eight, ← h1, ← h2, ← h3, ← h4]
  have := zmod2_two_add (v 0) (v 2) (v 4) (v 6)
  rw [← this]
  ring

theorem mem_closure_0123 {g : Equiv.Perm (Fin 240)} :
    g ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ↔ ∃ v, p02 v ∧ signPerm v = g := by
  constructor
  · intro hg
    have hle : closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ≤
        sigSub p02 (by decide) (fun u v hu hv => ⟨pairConst_add hu.1 hv.1,
          by simp [hu.2.1, hv.2.1], by simp [hu.2.2, hv.2.2]⟩)
          (fun v hv => pairConst_even hv.1) := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact ⟨vec2 0 1, by decide, rfl⟩
      · exact ⟨vec2 2 3, by decide, rfl⟩
    exact hle hg
  · rintro ⟨v, hv, rfl⟩
    refine signPerm_mem_closure_of_decomp hv.1 (fun _ => subset_closure (Set.mem_insert _ _))
      (fun _ => subset_closure (Set.mem_insert_of_mem _ rfl)) (fun h => ?_) (fun h => ?_)
    · rw [hv.2.1] at h; exact absurd h (by decide)
    · rw [hv.2.2] at h; exact absurd h (by decide)

theorem mem_closure_4567 {g : Equiv.Perm (Fin 240)} :
    g ∈ closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} ↔ ∃ v, p46 v ∧ signPerm v = g := by
  constructor
  · intro hg
    have hle : closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} ≤
        sigSub p46 (by decide) (fun u v hu hv => ⟨pairConst_add hu.1 hv.1,
          by simp [hu.2.1, hv.2.1], by simp [hu.2.2, hv.2.2]⟩)
          (fun v hv => pairConst_even hv.1) := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact ⟨vec2 4 5, by decide, rfl⟩
      · exact ⟨vec2 6 7, by decide, rfl⟩
    exact hle hg
  · rintro ⟨v, hv, rfl⟩
    refine signPerm_mem_closure_of_decomp hv.1 (fun h => ?_) (fun h => ?_)
      (fun _ => subset_closure (Set.mem_insert _ _))
      (fun _ => subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [hv.2.1] at h; exact absurd h (by decide)
    · rw [hv.2.2] at h; exact absurd h (by decide)

theorem mem_kOneSub {g : Equiv.Perm (Fin 240)} :
    g ∈ kOneSub ↔ ∃ v, pairConst v ∧ signPerm v = g := by
  constructor
  · intro hg
    have hle : kOneSub ≤ sigSub pairConst (by decide) (fun u v hu hv => pairConst_add hu hv)
        (fun v hv => pairConst_even hv) := by
      rw [kOneSub, closure_le]
      rintro x (rfl | rfl | rfl | rfl)
      · exact ⟨vec2 0 1, by decide, rfl⟩
      · exact ⟨vec2 2 3, by decide, rfl⟩
      · exact ⟨vec2 4 5, by decide, rfl⟩
      · exact ⟨vec2 6 7, by decide, rfl⟩
    exact hle hg
  · rintro ⟨v, hv, rfl⟩
    exact signPerm_mem_kOneSub hv

theorem exists_mask_iff {P : FrameVec → Prop} {ws : List ℕ}
    (hP : ∀ n < 256, P (frameDecode n) ↔ n ∈ ws) (hws : ∀ w ∈ ws, w < 256)
    (g : Equiv.Perm (Fin 240)) :
    (∃ w ∈ ws, g = signPerm (frameDecode w)) ↔ ∃ v, P v ∧ signPerm v = g := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, (hP w (hws w hw)).2 hw, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨frameEncode v, (hP _ (frameEncode_lt v)).1 ?_, by rw [frameDecode_frameEncode]⟩
    rwa [frameDecode_frameEncode]

theorem comm_02_spec (g : Equiv.Perm (Fin 240)) :
    (∃ e ∈ e1Sub, g = e * signPerm (vec2 0 2) * e⁻¹ * (signPerm (vec2 0 2))⁻¹) ↔
      g ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} := by
  rw [commSet_spec signArrs_5 (signPerm_mul_self (vec2_mem_evenSub 0 2 (by decide)))
    (by decide) commSet_facts.1 g, mem_closure_0123]
  exact exists_mask_iff (fun n hn => by rw [p02_masks n hn]; simp) (by decide) g

theorem comm_46_spec (g : Equiv.Perm (Fin 240)) :
    (∃ e ∈ e1Sub, g = e * signPerm (vec2 4 6) * e⁻¹ * (signPerm (vec2 4 6))⁻¹) ↔
      g ∈ closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} := by
  rw [commSet_spec signArrs_80 (signPerm_mul_self (vec2_mem_evenSub 4 6 (by decide)))
    (by decide) commSet_facts.2.1 g, mem_closure_4567]
  exact exists_mask_iff (fun n hn => by rw [p46_masks n hn]; simp) (by decide) g

theorem decode_85 : frameDecode 85 = vec2 0 2 + vec2 4 6 := by decide

theorem signArrs_85 : Rep 240 signArrs[85]! (signPerm (vec2 0 2 + vec2 4 6)) := by
  have := rep_signArrs (v := 85) (by norm_num) (by decide)
  rwa [decode_85] at this

theorem comm_0246_spec (g : Equiv.Perm (Fin 240)) :
    (∃ e ∈ e1Sub, g = e * signPerm (vec2 0 2 + vec2 4 6) * e⁻¹ *
      (signPerm (vec2 0 2 + vec2 4 6))⁻¹) ↔ g ∈ closure {signPerm (vec2 0 1),
        signPerm (vec2 2 3), signPerm (vec2 4 5), signPerm (vec2 6 7)} := by
  have hv : vec2 0 2 + vec2 4 6 ∈ evenSub :=
    add_mem (vec2_mem_evenSub 0 2 (by decide)) (vec2_mem_evenSub 4 6 (by decide))
  rw [commSet_spec signArrs_85 (signPerm_mul_self hv) (by decide) commSet_facts.2.2 g]
  change _ ↔ g ∈ kOneSub
  rw [mem_kOneSub]
  exact exists_mask_iff pair_masks (by decide) g

theorem inf_uSub_spec {g : Equiv.Perm (Fin 240)} (hg : g ∈ uSub) :
    g ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ↔ g = 1 ∨ g = xPlane := by
  obtain ⟨v, hv, rfl⟩ := mem_uSub_iff.1 hg
  rw [mem_closure_0123]
  constructor
  · rintro ⟨w, hw, he⟩
    have hwv := signPerm_inj (pairConst_even hw.1) (blockConst_even hv) he
    subst hwv
    have h4 : ¬ w 4 = 1 := by rw [hw.2.1]; decide
    rw [blockConst_decomp hv]
    simp only [h4, ↓reduceIte, add_zero]
    split_ifs
    · right; rfl
    · left; exact signPerm_zero
  · rintro (h | h)
    · exact ⟨0, by decide, by rw [signPerm_zero, h]⟩
    · exact ⟨aU, by decide, h.symm⟩

theorem isPGroup_tSub : IsPGroup 2 tSub := IsPGroup.of_card card_tSub

theorem zPerm_mem_of_normal {V : Subgroup (Equiv.Perm (Fin 240))} (hVT : V ≤ tSub)
    (hV1 : Nat.card V ≠ 1) (hnorm : ∀ t ∈ tSub, ∀ v ∈ V, t * v * t⁻¹ ∈ V) : zPerm ∈ V := by
  have : Group.IsNilpotent tSub := isPGroup_tSub.isNilpotent
  set V' := V.subgroupOf tSub with hV'def
  have : V'.Normal := ⟨fun n hn g => by
    rw [hV'def, mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hV' : V' ≠ ⊥ := by
    intro h
    apply hV1
    rw [← Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv, ← hV'def, h, card_bot]
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hV')
  have haV : ((a : tSub) : Equiv.Perm (Fin 240)) ∈ V := mem_subgroupOf.1 (mem_inf.1 a.2).1
  have hac := (mem_inf.1 a.2).2
  rw [Subgroup.mem_center_iff] at hac
  rcases center_tSub (a : tSub).2 (fun y hy => (congrArg Subtype.val (hac ⟨y, hy⟩)).symm) with
    h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) ha1
  · rw [← h]
    exact haV

theorem ncard_le_two_of_subset {V : Set (Equiv.Perm (Fin 240))} (h : V ⊆ {1, zPerm}) :
    V.ncard ≤ 2 := by
  have h1 := Set.ncard_le_ncard h (Set.toFinite _)
  have h2 := Set.ncard_insert_le (1 : Equiv.Perm (Fin 240)) {zPerm}
  rw [Set.ncard_singleton] at h2
  omega

theorem ncard_five {v w : Equiv.Perm (Fin 240)} (hv1 : v ≠ 1) (hvz : v ≠ zPerm)
    (h1 : w ≠ 1) (h2 : w ≠ zPerm) (h3 : w ≠ v) (h4 : w ≠ v * zPerm) :
    ({w, 1, zPerm, v, v * zPerm} : Set (Equiv.Perm (Fin 240))).ncard = 5 := by
  have hz1 : zPerm ≠ 1 := zPerm_ne_one
  have hvz1 : v * zPerm ≠ 1 := fun h => hvz (by
    rw [mul_eq_one_iff_eq_inv, zPerm_inv] at h; exact h)
  have hvzz : v * zPerm ≠ zPerm := fun h => hv1 (mul_eq_right.1 h)
  have hvzv : v * zPerm ≠ v := fun h => hz1 (mul_eq_left.1 h)
  rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3, h4]),
    Set.ncard_insert_of_notMem (by simp [hz1.symm, hv1.symm, hvz1.symm]),
    Set.ncard_insert_of_notMem (by simp [hvz.symm, hvzz.symm]),
    Set.ncard_pair hvzv.symm]

theorem unique_spec {i : ℕ} (hi : i < 8192) {b : Bool} (hb : b ∈ [false, true])
    (h : (isId (compA 240 (tElt tPlusCert i b) (tElt tPlusCert i b)) &&
      !isId (tElt tPlusCert i b) && !eqA 240 (tElt tPlusCert i b) negArr &&
        conjStable (tElt tPlusCert i b)) = true) :
    eqA 240 (tElt tPlusCert i b) signArrs[15]! = true ∨
      eqA 240 (tElt tPlusCert i b) signArrs[240]! = true := by
  have hc := unique_check
  rw [uniqueCheck] at hc
  have h1 := List.all_eq_true.1 (allLt_spec hc hi) b hb
  simp only [h, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  exact h1

theorem uSub_unique (V : Subgroup (Equiv.Perm (Fin 240))) (hVT : V ≤ tSub)
    (hV4 : Nat.card V = 4) (hsq : ∀ v ∈ V, v * v = 1)
    (hnorm : ∀ t ∈ tSub, ∀ v ∈ V, t * v * t⁻¹ ∈ V) : V = uSub := by
  have hz := zPerm_mem_of_normal hVT (by rw [hV4]; norm_num) hnorm
  have hV4' : (V : Set (Equiv.Perm (Fin 240))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV4
  obtain ⟨v, hv, hv1, hvz⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ zPerm := by
    by_contra h
    push Not at h
    have hsub : (V : Set (Equiv.Perm (Fin 240))) ⊆ {1, zPerm} := fun w hw => by
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · exact Or.inr (h w hw hw1)
    have := ncard_le_two_of_subset hsub
    omega
  have hall : ∀ w ∈ V, w = 1 ∨ w = zPerm ∨ w = v ∨ w = v * zPerm := by
    intro w hw
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hsub : ({w, 1, zPerm, v, v * zPerm} : Set (Equiv.Perm (Fin 240))) ⊆ V := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hw
      · exact one_mem _
      · exact hz
      · exact hv
      · exact mul_mem hv hz
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_five hv1 hvz h1 h2 h3 h4] at this
    omega
  have hconj : ∀ g ∈ tSub, g * v * g⁻¹ = v ∨ g * v * g⁻¹ = v * zPerm := by
    intro g hg
    rcases hall _ (hnorm g hg v hv) with h | h | h | h
    · exact absurd (by rwa [mul_inv_eq_one, mul_eq_left] at h) hv1
    · exfalso
      apply hvz
      have := congrArg (fun x => g⁻¹ * x * g) h
      simp only [show g⁻¹ * (g * v * g⁻¹) * g = v by group] at this
      rw [this, zPerm_comm _ (inv_mem (tSub_le_wE8 hg)), mul_assoc, inv_mul_cancel, mul_one]
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub (hVT hv)
  have hzr := rep_compA hrep rep_negArr
  have hstab : conjStable (tElt tPlusCert i b) = true := by
    rw [conjStable, Bool.and_eq_true, allLt_iff]
    refine ⟨fun k hk => ?_, ?_⟩
    · have hg := rep_tPlusGen hk
      have hgi := rep_inv_of_validA (t_facts.gens k hk).1
      have hc := rep_conjA' hg hgi hrep
      rw [Bool.or_eq_true]
      rcases hconj _ (tPlusSub_le_tSub (tPlusGen_mem hk)) with h | h
      · left; exact (eqA_iff hc hrep).2 h
      · right; exact (eqA_iff hc hzr).2 h
    · have hc := rep_compA (rep_compA rep_s0Arr hrep) rep_s0Arr
      rw [Bool.or_eq_true]
      have hs := hconj _ sZero_mem_tSub
      rw [inv_eq_of_mul_eq_one_right sZero_mul_self] at hs
      rcases hs with h | h
      · left; exact (eqA_iff hc hrep).2 h
      · right; exact (eqA_iff hc hzr).2 h
  have hpre : (isId (compA 240 (tElt tPlusCert i b) (tElt tPlusCert i b)) &&
      !isId (tElt tPlusCert i b) && !eqA 240 (tElt tPlusCert i b) negArr &&
        conjStable (tElt tPlusCert i b)) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      Bool.not_eq_true']
    refine ⟨⟨⟨(isId_iff (rep_compA hrep hrep)).2 (hsq v hv), ?_⟩, ?_⟩, hstab⟩
    · by_contra h
      exact hv1 ((isId_iff hrep).1 (Bool.not_eq_false _ ▸ h))
    · by_contra h
      exact hvz ((eqA_negArr_iff hrep).1 (Bool.not_eq_false _ ▸ h))
  have hU : uSub ≤ V := by
    rw [uSub, closure_le]
    rcases unique_spec hi hb hpre with h | h
    · have hx : v = xPlane := eq_of_eqA hrep signArrs_15 h
      rintro g (rfl | rfl)
      · change xPlane ∈ V
        rw [← hx]; exact hv
      · change signPerm bU ∈ V
        rw [← xPlane_mul_zPerm, ← hx]
        exact mul_mem hv hz
    · have hy : v = signPerm bU := eq_of_eqA hrep signArrs_240 h
      rintro g (rfl | rfl)
      · change xPlane ∈ V
        rw [← signPerm_bU_mul_zPerm, ← hy]
        exact mul_mem hv hz
      · change signPerm bU ∈ V
        rw [← hy]; exact hv
  exact (eq_of_le_of_card_ge hU (by rw [hV4, card_uSub])).symm

end CFSG.EvenSmallLie.OmegaEight.Weyl
