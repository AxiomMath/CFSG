module

public import CFSG.CGT.M24R.L2FC

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

theorem thCodes_getD (k : Fin 3) : thCodes.getD k.val 0 = codeOf (thT k) := by
  have h : thCodes = [codeOf (thT 0), codeOf (thT 1), codeOf (thT 2)] := rfl
  fin_cases k <;> simp [h]

section Tree

variable (hcard : Nat.card N8 = 322560)
include hcard

omit hcard in
theorem fcCheck_spec : (∀ i : Fin 3, codeOf (thT i) < 1048576 ∧
      (mkCtx ()).tab (codeOf (thT i)) = thT i) ∧
    (mkCtx ()).fcTree (mkCtx ()).dList (fcAll (mkCtx ())) thCodes 3 [] = true := by
  have h := Certificates.certificate21193.2.2.2.2.2.2.2.2
  simp only [fcCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem el_thCode (k : Fin 3) : el (codeOf (thT k)) = th8 k := by
  obtain ⟨h1, h2⟩ := fcCheck_spec.1 k
  have := isTab_tab h1
  rw [h2] at this
  exact this.eq_of_eq hcard (isTab_thT k)

theorem fcTree_sound : ∀ (fuel : ℕ) (P : List ℕ), P.length + fuel = 3 →
    (∀ p ∈ P, p < 1048576) →
    (mkCtx ()).fcTree (mkCtx ()).dList (fcAll (mkCtx ())) thCodes fuel P = true →
    ∀ u : Fin 3 → N8, (∀ k, u k ∈ D8) → Adm8 u →
      (∀ k : Fin 3, k.val < P.length → u k = el (P.getD k.val 0)) →
      ∃ e ∈ D8, ∀ k, e * u k * e⁻¹ = th8 k := by
  intro fuel
  induction fuel with
  | zero =>
    intro P hP _ ht u _ _ hagree
    have hP' : P = thCodes := by simpa [Ctx8.fcTree] using ht
    refine ⟨1, one_mem _, fun k => ?_⟩
    rw [hagree k (by omega), hP', thCodes_getD, el_thCode hcard]
    group
  | succ fuel ih =>
    intro P hP hPb ht u huD hu hagree
    rw [fcTree_succ] at ht
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
      List.mem_filter] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    have hj : P.length < 3 := by omega
    obtain ⟨cv, hcv, hv⟩ := el_of_mem_D hcard (huD ⟨P.length, hj⟩)
    have hcv' := (mem_dList_iff hcard).1 hcv
    have hcvb : cv < 1048576 := (mem_codes.1 hcv'.1).1
    have hPmem : ∀ k : ℕ, k < P.length → P.getD k 0 ∈ P := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem _
    have hgood : (mkCtx ()).goodC ((fcAll (mkCtx ())).getD P.length default)
        ((mkCtx ()).asg (P ++ [cv])) = true := by
      refine goodC_of_adm hcard hj hu fun k hk => ?_
      unfold Ctx8.asg
      rcases Nat.lt_or_ge k.val P.length with hlt | hge
      · rw [List.getD_append _ _ _ _ hlt, hagree k hlt]
        exact isTab_tab (hPb _ (hPmem _ hlt))
      · have hk' : k = ⟨P.length, hj⟩ := Fin.ext (by show k.val = P.length; omega)
        rw [List.getD_append_right _ _ _ _ hge, hk', hv]
        simp only [Nat.sub_self, List.getD_cons_zero]
        exact isTab_tab hcvb
    obtain ⟨r, hr, e, ⟨he, heP⟩, hconj⟩ := h2 cv ⟨hcv, hgood⟩
    have hrb : r < 1048576 := h1 r hr
    have he' := (mem_dList_iff hcard).1 he
    have hE := isTab_tab (mem_codes.1 he'.1).1
    have hee : el e ∈ D8 := he'.2
    have hcomm : ∀ p ∈ P, el e * el p = el p * el e := fun p hp =>
      (hE.commT_iff hcard (isTab_tab (hPb p hp))).1 (heP p hp)
    have hc : el e * el cv = el r * el e :=
      ((hE.mul (isTab_tab hcvb)).beq_iff hcard ((isTab_tab hrb).mul hE) (compT_size _ _)
        (compT_size _ _)).1 hconj
    obtain ⟨e', he'D, he'k⟩ := ih (P ++ [r]) (by simp; omega)
      (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hPb p hp
        · rw [List.mem_singleton.1 hp]; exact hrb)
      (h3 r hr) (fun k => el e * u k * (el e)⁻¹)
      (fun k => (D8).mul_mem ((D8).mul_mem hee (huD k)) ((D8).inv_mem hee))
      (hu.conj (T8_normal hcard) hee)
      (fun k hk => by
        simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k.val P.length with hlt | hge
        · rw [List.getD_append _ _ _ _ hlt, hagree k hlt, hcomm _ (hPmem _ hlt),
            mul_inv_cancel_right]
        · have hk' : k = ⟨P.length, hj⟩ := Fin.ext (by show k.val = P.length; omega)
          rw [List.getD_append_right _ _ _ _ hge, hk', hv, hc, mul_inv_cancel_right]
          simp)
    refine ⟨e' * el e, (D8).mul_mem he'D hee, fun k => ?_⟩
    rw [← he'k k]
    group

theorem swap8 (f : N8 → N8) (hfD : ∀ x ∈ D8, f x ∈ D8)
    (hfmul : ∀ x ∈ D8, ∀ y ∈ D8, f (x * y) = f x * f y)
    (hfinj : ∀ x ∈ D8, ∀ y ∈ D8, f x = f y → x = y) (hfA : ∀ a ∈ D8, a ∈ T8 → f a ∈ B8)
    (hfB : ∀ b ∈ B8, f b ∈ T8) : ∃ e ∈ D8, ∀ i, e * f (d8 i) * e⁻¹ = th8 i := by
  have hf1 : f 1 = 1 := by
    have := hfmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  have hwv : ∀ w : List (Fin 3), wv d8 w ∈ D8 ∧ f (wv d8 w) = wv (fun k => f (d8 k)) w := by
    intro w
    induction w with
    | nil => exact ⟨one_mem _, hf1⟩
    | cons k w ih =>
      rw [wv_cons, wv_cons, hfmul _ (d8_mem hcard k) _ ih.1, ih.2]
      exact ⟨(D8).mul_mem (d8_mem hcard k) ih.1, rfl⟩
  have hadm : Adm8 fun k => f (d8 k) := by
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun l r hlr => ?_⟩
    · rw [← (hwv w).2]
      exact hfA _ (hwv w).1 hw
    · rw [← (hwv w).2]
      exact hfB _ hw
    · rw [← (hwv w).2]
      intro h
      exact hw (hfinj _ (hwv w).1 _ (one_mem _) (h.trans hf1.symm))
    · rw [← (hwv l).2, ← (hwv r).2, hlr]
  obtain ⟨e, he, hek⟩ := fcTree_sound hcard 3 [] rfl (by simp) fcCheck_spec.2
    (fun k => f (d8 k)) (fun k => hfD _ (d8_mem hcard k)) hadm (fun k hk => absurd hk (by simp))
  exact ⟨e, he, hek⟩

end Tree

end CFSG.CGT.M24R
