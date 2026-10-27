module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4FixRoot
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD.Gaps
open scoped commutatorElement MatrixGroups

variable {F : Type} [Field F]

theorem rA_mem (c : F) : rA F c ∈ stdSL2 F 0 :=
  ⟨upperSL2 c, by simp [rA]⟩

theorem rB_mem (c : F) : rB F c ∈ stdSL2 F 1 :=
  ⟨upperSL2 c, by simp [rB]⟩

theorem lowerA_mem (c : F) : (fr F).longRoot ne10 true false (.ofAdd c) ∈ stdSL2 F 0 :=
  ⟨lowerSL2 c, by simp⟩

theorem lowerB_mem (c : F) : (fr F).longRoot ne10 false false (.ofAdd c) ∈ stdSL2 F 1 :=
  ⟨lowerSL2 c, by simp⟩

theorem torA_mem (s : Fˣ) : torA F s ∈ stdSL2 F 0 :=
  ⟨diagSL2 s, rfl⟩

theorem nA_mem : nA F ∈ stdSL2 F 0 :=
  ⟨weylSL2 1, rfl⟩

theorem nB_mem : nB F ∈ stdSL2 F 1 :=
  ⟨weylSL2 1, rfl⟩

section Alpha

variable {p : ℕ} [CharP F p]
variable (α : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))

theorem Dt_neg_one (v : Idx → F) : Dt (-1 : F) v = tauM v := by
  ext μ
  rcases μ with i | i <;> fin_cases i <;> simp [Dt, lamS, tauM_apply]

theorem torA_neg_one_mul_self : torA F (-1) * torA F (-1) = 1 := by
  unfold torA
  rw [← map_mul]
  simp

theorem torA_neg_one_conj_qq (k : Fin 4) (a : F) :
    torA F (-1) * qq F k a * (torA F (-1))⁻¹ = (qq F k a)⁻¹ := by
  rw [torA_conj_qq]
  have h : qq F k (((-1 : Fˣ) : F) * a) * qq F k a = 1 := by
    rw [← qq_add]
    simp [qq_zero]
  simpa using eq_inv_of_mul_eq_one_left h

theorem map_X1_of_commute {g : spinGroup (quadPlus 4 F)} (hc : g * rA F 1 = rA F 1 * g)
    (v : Idx → F) : spinAction (quadPlus 4 F) g (X1 v) = X1 (spinAction (quadPlus 4 F) g v) := by
  have h := congrArg (fun x => spinAction (quadPlus 4 F) x v) hc
  simp only [map_mul, LinearEquiv.mul_apply, spinAction_rA, one_smul, map_add] at h
  exact add_left_cancel h

theorem map_X2_of_commute {g : spinGroup (quadPlus 4 F)} (hc : g * rB F 1 = rB F 1 * g)
    (v : Idx → F) : spinAction (quadPlus 4 F) g (X2 v) = X2 (spinAction (quadPlus 4 F) g v) := by
  have h := congrArg (fun x => spinAction (quadPlus 4 F) x v) hc
  simp only [map_mul, LinearEquiv.mul_apply, spinAction_rB, one_smul, map_add] at h
  exact add_left_cancel h

section Exists

variable (hα0 : ∀ g ∈ stdSL2 F 0, α g = g) (hα1 : ∀ g ∈ stdSL2 F 1, α g = g)
include hα0 hα1

theorem exists_eich_qq (h2 : (2 : F) ≠ 0) (hpodd : Odd p) (k : Fin 4) (a : F) :
    ∃ c : Idx → F, VpC c ∧ ∀ v, spinAction (quadPlus 4 F) (α (qq F k a)) v = eich c v := by
  have hA : α (rA F 1) = rA F 1 := hα0 _ (rA_mem 1)
  have hB : α (rB F 1) = rB F 1 := hα1 _ (rB_mem 1)
  have hZ : α (torA F (-1)) = torA F (-1) := hα0 _ (torA_mem _)
  refine eich_of_commute h2 hpodd (spinAction (quadPlus 4 F) (α (qq F k a))) ?_ ?_ ?_ ?_ ?_
  · apply map_X1_of_commute
    have h := congrArg α (commute_qq_rA k a 1).eq
    rwa [map_mul, map_mul, hA] at h
  · apply map_X2_of_commute
    have h := congrArg α (commute_qq_rB k a 1).eq
    rwa [map_mul, map_mul, hB] at h
  · intro v
    have h := congrArg α (torA_neg_one_conj_qq k a)
    rw [map_mul, map_mul, map_inv, map_inv, hZ] at h
    have hz : (torA F (-1))⁻¹ = torA F (-1) := inv_eq_of_mul_eq_one_right torA_neg_one_mul_self
    rw [hz] at h
    have h1 := congrArg (spinAction (quadPlus 4 F)) h
    rw [map_mul, map_mul, map_inv] at h1
    have h3 : spinAction (quadPlus 4 F) (α (qq F k a)) * spinAction (quadPlus 4 F) (torA F (-1)) *
        spinAction (quadPlus 4 F) (α (qq F k a)) * spinAction (quadPlus 4 F) (torA F (-1)) =
          1 := by
      calc _ = spinAction (quadPlus 4 F) (α (qq F k a)) *
            (spinAction (quadPlus 4 F) (torA F (-1)) * spinAction (quadPlus 4 F) (α (qq F k a)) *
              spinAction (quadPlus 4 F) (torA F (-1))) := by group
        _ = 1 := by rw [h1]; exact mul_inv_cancel _
    have h4 := congrArg (fun m => m v) h3
    simpa [LinearEquiv.mul_apply, spinAction_torA, Dt_neg_one] using h4
  · intro v
    exact map_spinAction _ _ v
  · rw [← map_pow, ← map_pow, qq_pow_char, map_one, map_one]

end Exists

structure FixData (p : ℕ) [CharP F p] (α : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)) :
    Prop where
  two_ne_zero : (2 : F) ≠ 0
  odd : Odd p
  fix0 : ∀ g ∈ stdSL2 F 0, α g = g
  fix1 : ∀ g ∈ stdSL2 F 1, α g = g

variable {α}

noncomputable def cq (hd : FixData p α) (k : Fin 4) (a : F) : Idx → F :=
  Classical.choose (exists_eich_qq α hd.fix0 hd.fix1 hd.two_ne_zero hd.odd k a)

theorem cq_spec (hd : FixData p α) (k : Fin 4) (a : F) :
    VpC (cq hd k a) ∧ ∀ v, spinAction (quadPlus 4 F) (α (qq F k a)) v = eich (cq hd k a) v :=
  Classical.choose_spec (exists_eich_qq α hd.fix0 hd.fix1 hd.two_ne_zero hd.odd k a)

theorem cq_VpC (hd : FixData p α) (k : Fin 4) (a : F) : VpC (cq hd k a) := (cq_spec hd k a).1

theorem theta_alpha_qq (hd : FixData p α) (k : Fin 4) (a : F) (v : Idx → F) :
    spinAction (quadPlus 4 F) (α (qq F k a)) v = eich (cq hd k a) v := (cq_spec hd k a).2 v

theorem cq_add (hd : FixData p α) (k : Fin 4) (a b : F) :
    cq hd k (a + b) = cq hd k a + cq hd k b := by
  refine eich_injective (cq_VpC hd k _) (fun μ hμ => by
    simp [cq_VpC hd k a μ hμ, cq_VpC hd k b μ hμ]) (fun v => ?_)
  have h : spinAction (quadPlus 4 F) (α (qq F k (a + b))) v =
      spinAction (quadPlus 4 F) (α (qq F k a)) (spinAction (quadPlus 4 F) (α (qq F k b)) v) := by
    rw [qq_add, map_mul, map_mul]
    rfl
  rw [theta_alpha_qq hd, theta_alpha_qq hd, theta_alpha_qq hd, eich_eich (cq_VpC hd k a)
    (cq_VpC hd k b)] at h
  exact h

theorem cq_zero (hd : FixData p α) (k : Fin 4) : cq hd k 0 = 0 := by
  have h := cq_add hd k 0 0
  rw [add_zero] at h
  have h' : cq hd k 0 + cq hd k 0 = cq hd k 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem Dt_Dt_inv {s : F} (hs : s ≠ 0) (u : Idx → F) : Dt s (Dt s⁻¹ u) = u := by
  ext μ
  simp only [Dt]
  rcases μ with i | i <;> fin_cases i <;> simp [lamS, hs]

theorem cq_smul (hd : FixData p α) (k : Fin 4) {s : F} (hs : s ≠ 0) (a : F) :
    cq hd k (s * a) = s • cq hd k a := by
  have hu : α (torA F (Units.mk0 s hs)) = torA F (Units.mk0 s hs) := hd.fix0 _ (torA_mem _)
  have hconj := torA_conj_qq (Units.mk0 s hs) k a
  have h1 := congrArg α hconj
  rw [map_mul, map_mul, map_inv, hu] at h1
  have h3 : α (qq F k ((Units.mk0 s hs : F) * a)) * torA F (Units.mk0 s hs) =
      torA F (Units.mk0 s hs) * α (qq F k a) := by
    rw [← h1]
    group
  simp only [Units.val_mk0] at h3
  refine eich_injective (cq_VpC hd k _) (fun μ hμ => by simp [cq_VpC hd k a μ hμ])
    (fun u => ?_)
  have h4 := congrArg (fun x => spinAction (quadPlus 4 F) x (Dt s⁻¹ u)) h3
  simp only [map_mul, LinearEquiv.mul_apply, spinAction_torA, Units.val_mk0] at h4
  rw [Dt_Dt_inv hs] at h4
  rw [theta_alpha_qq hd, theta_alpha_qq hd] at h4
  rw [h4, Dt_eich hs (cq_VpC hd k a), Dt_Dt_inv hs]

theorem cq_eq_smul (hd : FixData p α) (k : Fin 4) (a : F) :
    cq hd k a = a • cq hd k 1 := by
  by_cases ha : a = 0
  · subst ha
    rw [cq_zero, zero_smul]
  · have := cq_smul hd k ha 1
    rwa [mul_one] at this

noncomputable def wv (hd : FixData p α) (k : Fin 4) : Idx → F := -cq hd k 1

theorem wv_VpC (hd : FixData p α) (k : Fin 4) : VpC (wv hd k) := fun μ hμ => by
  simp [wv, cq_VpC hd k 1 μ hμ]

theorem theta_alpha_qq_wv (hd : FixData p α) (k : Fin 4) (a : F) (v : Idx → F) :
    spinAction (quadPlus 4 F) (α (qq F k a)) v = eich (-a • wv hd k) v := by
  rw [theta_alpha_qq hd, cq_eq_smul hd k a]
  congr 1
  simp [wv]

theorem theta_alpha_yy (hd : FixData p α) (l : Fin 4) (b : F) (u : Idx → F) :
    spinAction (quadPlus 4 F) (α (yy F l b)) u = eich1 (b • wv hd l) u := by
  have hn : α (nA F) = nA F := hd.fix0 _ nA_mem
  have h1 : yy F l b = nA F * qq F l (-b) * (nA F)⁻¹ := by
    have := nA_conj_qq (F := F) l (-b)
    rw [neg_neg] at this
    exact this.symm
  have h2 : α (yy F l b) * nA F = nA F * α (qq F l (-b)) := by
    rw [h1, map_mul, map_mul, map_inv, hn]
    group
  obtain ⟨w, hw⟩ : ∃ w, spinAction (quadPlus 4 F) (nA F) w = u :=
    ⟨(spinAction (quadPlus 4 F) (nA F)).symm u, by simp⟩
  have h3 := congrArg (fun x => spinAction (quadPlus 4 F) x w) h2
  simp only [map_mul, LinearEquiv.mul_apply, spinAction_nA] at h3
  have hV : VpC (-(-b) • wv hd l) := fun μ hμ => by simp [wv_VpC hd l μ hμ]
  rw [theta_alpha_qq_wv hd, Nw_eich hV] at h3
  rw [spinAction_nA] at hw
  rw [← hw, h3, neg_neg]

theorem polar_ek_ek (k l : Fin 4) :
    polar (quadPlus 4 F) (ek F k) (ek F l) = if (jk l = jk k ∧ tk l = !tk k) then 1 else 0 := by
  rw [QuadraticMap.polar_comm, polar_ek, ek_apply, kap_eq]
  have key : idx (jk k) (!tk k) = idx (jk l) (tk l) ↔ (jk l = jk k ∧ tk l = !tk k) := by
    cases h1 : tk k <;> cases h2 : tk l <;> simp [idx, eq_comm]
  by_cases h : jk l = jk k ∧ tk l = !tk k
  · simp [h, key.mpr h]
  · simp [h, (not_congr key).mpr h]

theorem rB_zero : rB F 0 = 1 := by
  unfold rB
  rw [ofAdd_zero, map_one]

theorem polar_wv (hd : FixData p α) (k l : Fin 4) :
    polar (quadPlus 4 F) (wv hd k) (wv hd l) = polar (quadPlus 4 F) (ek F k) (ek F l) := by
  rw [polar_ek_ek]
  have hc : VpC (-(1 : F) • wv hd k) := fun μ hμ => by simp [wv_VpC hd k μ hμ]
  have hc' : VpC ((-1 : F) • wv hd l) := fun μ hμ => by simp [wv_VpC hd l μ hμ]
  have hP := theta_alpha_qq_wv hd k 1
  have hP' := theta_alpha_yy hd l (-1)
  have hrel : ∀ κ : F, α (qq F k 1) * α (yy F l (-1)) = rB F κ * (α (yy F l (-1)) * α (qq F k 1)) →
      polar (quadPlus 4 F) (-(1 : F) • wv hd k) ((-1 : F) • wv hd l) = κ := by
    intro κ hκ
    apply polar_eq_of_comm hc hc' κ
    intro v
    have h := congrArg (fun x => spinAction (quadPlus 4 F) x v) hκ
    simp only [map_mul, LinearEquiv.mul_apply, spinAction_rB, hP, hP'] at h
    rw [X2_eich1 hc', X2_eich hc] at h
    exact h
  have hpol : polar (quadPlus 4 F) (-(1 : F) • wv hd k) ((-1 : F) • wv hd l) =
      polar (quadPlus 4 F) (wv hd k) (wv hd l) := by
    simp
  rw [← hpol]
  by_cases h : jk l = jk k ∧ tk l = !tk k
  · simp only [h, and_self, ↓reduceIte]
    apply hrel
    have hcomm := comm_qq_yy_partner (F := F) h.1 h.2 1 (-1)
    have e : qq F k 1 * yy F l (-1) = ⁅qq F k 1, yy F l (-1)⁆ * (yy F l (-1) * qq F k 1) := by
      simp only [commutatorElement_def]
      group
    rw [← map_mul, e, map_mul, map_mul, hcomm]
    have hB : α (rB F (-(1 * -1))) = rB F (-(1 * -1)) := hd.fix1 _ (rB_mem _)
    rw [hB]
    congr 2
    ring
  · simp only [h, ↓reduceIte]
    apply hrel
    have hc2 := (commute_qq_yy (F := F) h 1 (-1)).eq
    rw [rB_zero, one_mul, ← map_mul, ← map_mul, hc2]

end Alpha

end CFSG.ClassicalInvolution.G2D4Models.Twin
