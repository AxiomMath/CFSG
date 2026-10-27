module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4FixMain
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Triality

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.LieType.CurtisTits CFSG.LieType.Universal
open scoped commutatorElement

variable {F : Type} [Field F]

theorem VpC_ek (k : Fin 4) : VpC (ek F k) := fun μ hμ => by
  rw [ek_apply]
  have : μ ≠ kap k := fun h => by
    subst h
    fin_cases k <;> simp [kap] at hμ
  simp [this]

theorem elim_idx (i : Fin 4) (s : Bool) : Sum.elim id id (idx i s) = i := by
  cases s <;> simp [idx]

theorem commutator_mem_of_mem {G : Type*} [Group G] {M : Subgroup G} {x y : G} (hx : x ∈ M)
    (hy : y ∈ M) : ⁅x, y⁆ ∈ M := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

section Alpha

variable {p : ℕ} [CharP F p] {α : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)}

@[expose] noncomputable def isoA (hd : FixData p α) : (Idx → F) ≃ₗ[F] (Idx → F) :=
  ALe (wv_VpC hd) (polar_wv hd)

theorem isoA_apply (hd : FixData p α) (v : Idx → F) : isoA hd v = AL (wv hd) v := rfl

theorem Q_isoA (hd : FixData p α) (v : Idx → F) :
    quadPlus 4 F (isoA hd v) = quadPlus 4 F v :=
  Q_AL hd.two_ne_zero (wv_VpC hd) (polar_wv hd) v

@[expose] noncomputable def Msub (hd : FixData p α) : Subgroup (spinGroup (quadPlus 4 F)) :=
  MonoidHom.eqLocus ((spinAction (quadPlus 4 F)).comp α.toMonoidHom)
    ((MulAut.conj (isoA hd)).toMonoidHom.comp (spinAction (quadPlus 4 F)))

theorem mem_Msub (hd : FixData p α) (x : spinGroup (quadPlus 4 F)) :
    x ∈ Msub hd ↔ ∀ v, spinAction (quadPlus 4 F) (α x) (isoA hd v) =
      isoA hd (spinAction (quadPlus 4 F) x v) := by
  change spinAction (quadPlus 4 F) (α x) =
    isoA hd * spinAction (quadPlus 4 F) x * (isoA hd)⁻¹ ↔ _
  constructor
  · intro h v
    have := congrArg (fun m => m (isoA hd v)) h
    simpa [LinearEquiv.mul_apply] using this
  · intro h
    refine LinearEquiv.ext fun v => ?_
    have := h ((isoA hd).symm v)
    simpa [LinearEquiv.mul_apply] using this

theorem longRoot_small_mem (hd : FixData p α) {i j : Fin 4} (hij : i ≠ j) (hi : i.val < 2)
    (hj : j.val < 2) (s t : Bool) (c : F)
    (hfix : α ((fr F).longRoot hij s t (.ofAdd c)) = (fr F).longRoot hij s t (.ofAdd c)) :
    (fr F).longRoot hij s t (.ofAdd c) ∈ Msub hd := by
  rw [mem_Msub]
  intro v
  rw [hfix]
  set x := (fr F).longRoot hij s t (.ofAdd c) with hx
  let N : (Idx → F) →ₗ[F] (Idx → F) := (spinAction (quadPlus 4 F) x).toLinearMap - LinearMap.id
  have hNv : ∀ u, spinAction (quadPlus 4 F) x u = u + N u := fun u => by simp [N]
  have hNapply : ∀ u μ, N u μ = c * u (idx j (!t)) * (if μ = idx i s then 1 else 0) -
      c * u (idx i (!s)) * (if μ = idx j t then 1 else 0) := by
    intro u μ
    have h := spinAction_longRoot_apply hij s t c u μ
    rw [← hx] at h
    simp only [N, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Pi.sub_apply]
    rw [h]
    ring
  have hN1 : ∀ u, N (Pp u) = 0 := by
    intro u
    ext μ
    have e1 : Pp u (idx j (!t)) = 0 := Pp_apply_of_lt u (by rw [elim_idx]; exact hj)
    have e2 : Pp u (idx i (!s)) = 0 := Pp_apply_of_lt u (by rw [elim_idx]; exact hi)
    rw [hNapply, e1, e2]
    simp
  have hN2 : ∀ u, VmC (N u) := by
    intro u μ hμ
    have e1 : μ ≠ idx i s := fun h => hμ (by rw [h, elim_idx]; exact hi)
    have e2 : μ ≠ idx j t := fun h => hμ (by rw [h, elim_idx]; exact hj)
    rw [hNapply]
    simp [e1, e2]
  have key := AL_comm (wv_VpC hd) hN1 hN2 v
  rw [isoA_apply, isoA_apply, hNv (AL (wv hd) v), hNv v, map_add, key]

theorem stdSL2_zero_le (hd : FixData p α) : stdSL2 F 0 ≤ Msub hd := by
  show ((fr F).longSL2 ne01 true false).range ≤ Msub hd
  rw [longSL2_range_eq_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact longRoot_small_mem hd ne01 (by decide) (by decide) true false (Multiplicative.toAdd c)
      (hd.fix0 _ (rA_mem _))
  · rintro _ ⟨c, rfl⟩
    exact longRoot_small_mem hd ne10 (by decide) (by decide) true false (Multiplicative.toAdd c)
      (hd.fix0 _ (lowerA_mem _))

theorem stdSL2_one_le (hd : FixData p α) : stdSL2 F 1 ≤ Msub hd := by
  show ((fr F).longSL2 ne01 true true).range ≤ Msub hd
  rw [longSL2_range_eq_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact longRoot_small_mem hd ne01 (by decide) (by decide) true true (Multiplicative.toAdd c)
      (hd.fix1 _ (rB_mem _))
  · rintro _ ⟨c, rfl⟩
    exact longRoot_small_mem hd ne10 (by decide) (by decide) false false (Multiplicative.toAdd c)
      (hd.fix1 _ (lowerB_mem _))

theorem qq_mem (hd : FixData p α) (k : Fin 4) (a : F) : qq F k a ∈ Msub hd := by
  rw [mem_Msub]
  intro v
  have hc : VpC (-a • ek F k) := fun μ hμ => by simp [VpC_ek k μ hμ]
  rw [theta_alpha_qq_wv hd, spinAction_qq, isoA_apply, isoA_apply,
    AL_eich hd.two_ne_zero (wv_VpC hd) (polar_wv hd) hc]
  congr 1
  rw [map_smul, AL_VpC (VpC_ek k), U0_ek]

theorem yy_mem (hd : FixData p α) (k : Fin 4) (b : F) : yy F k b ∈ Msub hd := by
  have h := nA_conj_qq (F := F) k (-b)
  rw [neg_neg] at h
  rw [← h]
  exact mul_mem (mul_mem (stdSL2_zero_le hd nA_mem) (qq_mem hd k _))
    (inv_mem (stdSL2_zero_le hd nA_mem))

@[expose] noncomputable def yb (F : Type) [Field F] (k : Fin 4) (b : F) :
    spinGroup (quadPlus 4 F) :=
  (fr F).longRoot (jk_ne1 k) false (tk k) (.ofAdd b)

theorem nB_conj_qq (k : Fin 4) (a : F) : nB F * qq F k a * (nB F)⁻¹ = yb F k (-a) := by
  have hi : spinAction (quadPlus 4 F) (nB F) ((fr F).vec 0 true) =
      (-1 : F) • (fr F).vec 1 false := by
    rw [nB, (fr F).spinAction_longWeyl_vec_left ne01 true true]
    simp
  have hj : spinAction (quadPlus 4 F) (nB F) ((fr F).vec (jk k) (tk k)) =
      (1 : F) • (fr F).vec (jk k) (tk k) := by
    rw [nB, (fr F).spinAction_longWeyl_vec_of_ne ne01 true true (jk_ne k).symm (jk_ne1 k).symm]
    simp
  have h := (fr F).conj_longRoot (nB F) (jk_ne k) true (tk k) (jk_ne1 k) false (tk k) hi hj a
  rw [qq, yb, h]
  congr 2
  simp

theorem yb_mem (hd : FixData p α) (k : Fin 4) (b : F) : yb F k b ∈ Msub hd := by
  have h := nB_conj_qq (F := F) k (-b)
  rw [neg_neg] at h
  rw [← h]
  exact mul_mem (mul_mem (stdSL2_one_le hd nB_mem) (qq_mem hd k _))
    (inv_mem (stdSL2_one_le hd nB_mem))

theorem comm_yy_yb {k l : Fin 4} (hkl : jk k ≠ jk l) (a b : F) :
    ⁅yy F k a, yb F l b⁆ = (fr F).longRoot hkl (tk k) (tk l) (.ofAdd (-(a * b))) := by
  have e : yy F k a = (fr F).longRoot (jk_ne1 k).symm (tk k) true (.ofAdd (-a)) := by
    rw [yy, (fr F).longRoot_swap (jk_ne1 k) true (tk k) a]
  have h : ⁅(fr F).longRoot (jk_ne1 k).symm (tk k) true (.ofAdd (-a)),
      (fr F).longRoot (jk_ne1 l) false (tk l) (.ofAdd b)⁆ =
        (fr F).longRoot hkl (tk k) (tk l) (.ofAdd (-a * b)) :=
    (fr F).commutator_longRoot_longRoot (jk_ne1 k).symm (jk_ne1 l) hkl (tk k) true (tk l) (-a) b
  rw [e, yb, h]
  congr 2
  ring

theorem longRoot_ne12_mem (hd : FixData p α) (c : F) :
    (fr F).longRoot ne12 true false (.ofAdd c) ∈ Msub hd :=
  yy_mem hd 1 c

theorem longRoot_ne21_mem (hd : FixData p α) (c : F) :
    (fr F).longRoot ne21 true false (.ofAdd c) ∈ Msub hd := by
  have e : (fr F).longRoot ne21 true false (.ofAdd c) = yb F 0 (-c) := by
    have h := (fr F).longRoot_swap ne12 false true (-c)
    rw [neg_neg] at h
    exact h.symm
  rw [e]
  exact yb_mem hd 0 (-c)

theorem longRoot_ne23_TF_mem (hd : FixData p α) (c : F) :
    (fr F).longRoot ne23 true false (.ofAdd c) ∈ Msub hd := by
  have h := comm_yy_yb (F := F) (k := 0) (l := 3) (by decide) 1 (-c)
  have e : -((1 : F) * -c) = c := by ring
  rw [e] at h
  have hm := commutator_mem_of_mem (yy_mem hd 0 1) (yb_mem hd 3 (-c))
  rw [h] at hm
  exact hm

theorem longRoot_ne32_TF_mem (hd : FixData p α) (c : F) :
    (fr F).longRoot ne32 true false (.ofAdd c) ∈ Msub hd := by
  have h := comm_yy_yb (F := F) (k := 1) (l := 2) (by decide) 1 c
  have hs : (fr F).longRoot ne32 true false (.ofAdd c) =
      (fr F).longRoot ne23 false true (.ofAdd (-c)) := by
    rw [(fr F).longRoot_swap ne23 false true (-c), neg_neg]
  have e : -((1 : F) * c) = -c := by ring
  rw [e] at h
  have hm := commutator_mem_of_mem (yy_mem hd 1 1) (yb_mem hd 2 c)
  rw [h] at hm
  rw [hs]
  exact hm

theorem longRoot_ne23_TT_mem (hd : FixData p α) (c : F) :
    (fr F).longRoot ne23 true true (.ofAdd c) ∈ Msub hd := by
  have h := comm_yy_yb (F := F) (k := 0) (l := 2) (by decide) 1 (-c)
  have e : -((1 : F) * -c) = c := by ring
  rw [e] at h
  have hm := commutator_mem_of_mem (yy_mem hd 0 1) (yb_mem hd 2 (-c))
  rw [h] at hm
  exact hm

theorem longRoot_ne32_FF_mem (hd : FixData p α) (c : F) :
    (fr F).longRoot ne32 false false (.ofAdd c) ∈ Msub hd := by
  have h := comm_yy_yb (F := F) (k := 1) (l := 3) (by decide) 1 c
  have hs : (fr F).longRoot ne32 false false (.ofAdd c) =
      (fr F).longRoot ne23 false false (.ofAdd (-c)) := by
    rw [(fr F).longRoot_swap ne23 false false (-c), neg_neg]
  have e : -((1 : F) * c) = -c := by ring
  rw [e] at h
  have hm := commutator_mem_of_mem (yy_mem hd 1 1) (yb_mem hd 3 c)
  rw [h] at hm
  rw [hs]
  exact hm

theorem rankOne_one :
    rankOne (plusDatum 4 F (by norm_num)).rootGroup (1 : Fin 4) =
      ((fr F).longSL2 ne12 true false).range :=
  rankOne_plusDatum_of_lt (K := F) (m := 4) (by norm_num) (k := 1) (by decide)

theorem Msub_eq_top (hd : FixData p α) : Msub hd = ⊤ := by
  have hn3 : 3 ≤ 4 := by norm_num
  have h := Balance.iSup_rankOne_eq_top (plusDatum 4 F hn3)
    (Spin.plusDatum_isCTGroupDatum hn3 (Spin.plusDatum_iSup_eq_top 4 _ hn3))
  rw [eq_top_iff, ← h]
  have hall : ∀ k : Fin 4, rankOne (plusDatum 4 F hn3).rootGroup k ≤ Msub hd := by
    intro k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl | rfl
    · rw [rankOne_zero]
      exact stdSL2_zero_le hd
    · rw [rankOne_one, longSL2_range_eq_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        exact longRoot_ne12_mem hd (Multiplicative.toAdd c)
      · rintro _ ⟨c, rfl⟩
        exact longRoot_ne21_mem hd (Multiplicative.toAdd c)
    · rw [rankOne_two, longSL2_range_eq_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        exact longRoot_ne23_TF_mem hd (Multiplicative.toAdd c)
      · rintro _ ⟨c, rfl⟩
        exact longRoot_ne32_TF_mem hd (Multiplicative.toAdd c)
    · rw [rankOne_three, longSL2_range_eq_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        exact longRoot_ne23_TT_mem hd (Multiplicative.toAdd c)
      · rintro _ ⟨c, rfl⟩
        exact longRoot_ne32_FF_mem hd (Multiplicative.toAdd c)
  exact iSup_le fun k => hall k

theorem theta_alpha_isoA (hd : FixData p α) (x : spinGroup (quadPlus 4 F)) (v : Idx → F) :
    spinAction (quadPlus 4 F) (α x) (isoA hd v) = isoA hd (spinAction (quadPlus 4 F) x v) := by
  have hx : x ∈ Msub hd := by
    rw [Msub_eq_top]
    exact Subgroup.mem_top x
  exact (mem_Msub hd x).mp hx v

end Alpha

end CFSG.ClassicalInvolution.G2D4Models.Twin
