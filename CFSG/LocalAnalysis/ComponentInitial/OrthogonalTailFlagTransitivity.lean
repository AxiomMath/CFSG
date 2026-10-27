module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Fix

variable (r qA) in
@[expose] noncomputable def fixElementary (k : ℕ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | g ∈ orthElementaryGroup (quadTail r qA) ∧
    ∀ i : Fin r, i.val < k → g (hypVec K A (.inl i)) = hypVec K A (.inl i)}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    exact ⟨mul_mem hg hh, fun i hi => by rw [LinearEquiv.mul_apply, hh' i hi, hg' i hi]⟩
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨inv_mem hg, fun i hi => ?_⟩
    have h := congrArg (g⁻¹ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) (hg' i hi)
    rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id_eq] at h
    exact h.symm

theorem mem_fixElementary {k : ℕ} {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} :
    g ∈ fixElementary r qA k ↔ g ∈ orthElementaryGroup (quadTail r qA) ∧
      ∀ i : Fin r, i.val < k → g (hypVec K A (.inl i)) = hypVec K A (.inl i) :=
  Iff.rfl

theorem polar_hypVec_inl_left (i : Fin r) (v : (Fin r ⊕ Fin r → K) × A) :
    polar (quadTail r qA) (hypVec K A (.inl i)) v = v.1 (.inr i) := by
  rw [polar_comm, polar_hypVec]
  rfl

theorem polar_hypVec_inr_left (j : Fin r) (v : (Fin r ⊕ Fin r → K) × A) :
    polar (quadTail r qA) (hypVec K A (.inr j)) v = v.1 (.inl j) := by
  rw [polar_comm, polar_hypVec]
  rfl

theorem polar_inl_apply_of_mem_fixElementary {k : ℕ} {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (hg : g ∈ fixElementary r qA k) {i : Fin r} (hi : i.val < k) (v : (Fin r ⊕ Fin r → K) × A) :
    (g v).1 (.inr i) = v.1 (.inr i) := by
  calc (g v).1 (.inr i) = polar (quadTail r qA) (hypVec K A (.inl i)) (g v) :=
        (polar_hypVec_inl_left i (g v)).symm
    _ = polar (quadTail r qA) (g (hypVec K A (.inl i))) (g v) := by rw [hg.2 i hi]
    _ = polar (quadTail r qA) (hypVec K A (.inl i)) v :=
        polar_map_of_mem (orthElementaryGroup_le _ hg.1) _ _
    _ = v.1 (.inr i) := polar_hypVec_inl_left i v

theorem eichler_mem_fixElementary {k : ℕ} {u x y : (Fin r ⊕ Fin r → K) × A}
    (hu : quadTail r qA u = 0)
    (huk : ∀ i : Fin r, i.val < k → polar (quadTail r qA) (hypVec K A (.inl i)) u = 0)
    {t : K} (htx : polar (quadTail r qA) u x = t) (hty : polar (quadTail r qA) u y = t)
    (hk : ∀ i : Fin r, i.val < k → polar (quadTail r qA) (hypVec K A (.inl i)) x =
      polar (quadTail r qA) (hypVec K A (.inl i)) y) :
    eichler (quadTail r qA) u (t⁻¹ • (y - x)) ∈ fixElementary r qA k := by
  have hw : polar (quadTail r qA) u (t⁻¹ • (y - x)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, htx, hty, sub_self, mul_zero]
  refine ⟨eichler_mem_elementaryGroup _ _ _, fun i hi => ?_⟩
  rw [eichler_apply hu hw, huk i hi, polar_smul_right_eq, polar_sub_right, hk i hi, sub_self,
    mul_zero]
  simp

theorem eichler_tail_mem_fixElementary (k : ℕ) (j : Fin r) (a : A) :
    eichler (quadTail r qA) (hypVec K A (.inl j)) ((0 : Fin r ⊕ Fin r → K), a) ∈
      fixElementary r qA k := by
  refine ⟨eichler_mem_elementaryGroup _ _ _, fun i hi => ?_⟩
  rw [eichler_apply (quadTail_hypVec _) (polar_hypVec_tail _ _), polar_hypVec_hypVec,
    polar_hypVec_tail]
  simp

end Fix

section Move

theorem quadTail_smul_hypVec (c : K) (d : Fin r ⊕ Fin r) :
    quadTail r qA (c • hypVec K A d) = 0 := by
  rw [QuadraticMap.map_smul, quadTail_hypVec, smul_zero]

theorem exists_fix_apply_eq_of_inl {k : ℕ} (hk : k < r) {x : (Fin r ⊕ Fin r → K) × A}
    (hx : quadTail r qA x = 0) (hxk : ∀ i : Fin r, i.val < k → x.1 (.inr i) = 0) {j : Fin r}
    (hj : k ≤ j.val) (hxj : x.1 (.inl j) ≠ 0) :
    ∃ h ∈ fixElementary r qA k, ∃ c : K, c ≠ 0 ∧ h x = c • hypVec K A (.inl ⟨k, hk⟩) := by
  have htx := polar_hypVec_inr_left (qA := qA) j x
  generalize x.1 (.inl j) = t at hxj htx
  have hne : ∀ i : Fin r, i.val < k → i ≠ j := fun i hi h => by rw [h] at hi; omega
  have hpe : ∀ (c : K) (d : Fin r ⊕ Fin r) (a : Fin r),
      polar (quadTail r qA) (hypVec K A d) (c • hypVec K A (.inl a)) =
        c * if Sum.inl a = d.swap then 1 else 0 := fun c d a => by
    rw [polar_smul_right_eq, polar_hypVec_hypVec]
  have hpe1 : ∀ (d : Fin r ⊕ Fin r) (a : Fin r),
      polar (quadTail r qA) (hypVec K A d) (hypVec K A (.inl a)) =
        if Sum.inl a = d.swap then 1 else 0 := fun d a => polar_hypVec_hypVec _ _
  have hty : polar (quadTail r qA) (hypVec K A (.inr j)) (t • hypVec K A (.inl j)) = t := by
    rw [hpe]
    simp
  have hk₁ : ∀ i : Fin r, i.val < k → polar (quadTail r qA) (hypVec K A (.inl i)) x =
      polar (quadTail r qA) (hypVec K A (.inl i)) (t • hypVec K A (.inl j)) := fun i hi => by
    rw [polar_hypVec_inl_left, hxk i hi, hpe]
    simp
  have huj : ∀ i : Fin r, i.val < k →
      polar (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inr j)) = 0 := fun i hi => by
    rw [polar_hypVec_hypVec]
    simp [Ne.symm (hne i hi)]
  have h₁ := eichler_mem_fixElementary (quadTail_hypVec (qA := qA) (.inr j)) huj htx hty hk₁
  have e₁ := eichler_apply_eq_of_polar_eq (quadTail_hypVec (qA := qA) (.inr j))
    (x := x) (y := t • hypVec K A (.inl j)) (by rw [hx, quadTail_smul_hypVec]) htx hty hxj
  by_cases hjk : j = ⟨k, hk⟩
  · refine ⟨_, h₁, t, hxj, ?_⟩
    rw [e₁, hjk]
  · have hjk' : (⟨k, hk⟩ : Fin r) ≠ j := Ne.symm hjk
    set e := hypVec K A (.inl ⟨k, hk⟩) with he
    have hQz : quadTail r qA (t • hypVec K A (.inl j) + e) = 0 := by
      rw [QuadraticMap.map_add (quadTail r qA), quadTail_smul_hypVec, he, quadTail_hypVec,
        polar_smul_left,
        polar_hypVec_hypVec]
      simp
    have hz₁ : polar (quadTail r qA) (hypVec K A (.inr j)) (t • hypVec K A (.inl j) + e) = t := by
      rw [polar_add_right, hpe, he, hpe1]
      simp [hjk']
    have hz₂ : polar (quadTail r qA) (hypVec K A (.inr ⟨k, hk⟩))
        (t • hypVec K A (.inl j) + e) = 1 := by
      rw [polar_add_right, hpe, he, hpe1]
      simp [hjk]
    have he₁ : polar (quadTail r qA) (hypVec K A (.inr ⟨k, hk⟩)) e = 1 := by
      rw [he, hpe1]
      simp
    have hk₂ : ∀ i : Fin r, i.val < k →
        polar (quadTail r qA) (hypVec K A (.inl i)) (t • hypVec K A (.inl j)) =
          polar (quadTail r qA) (hypVec K A (.inl i)) (t • hypVec K A (.inl j) + e) :=
      fun i hi => by
        rw [polar_add_right, he, hpe1]
        simp
    have hk₃ : ∀ i : Fin r, i.val < k →
        polar (quadTail r qA) (hypVec K A (.inl i)) (t • hypVec K A (.inl j) + e) =
          polar (quadTail r qA) (hypVec K A (.inl i)) e := fun i hi => by
      rw [polar_add_right, he, hpe1, hpe]
      simp
    have huk : ∀ i : Fin r, i.val < k →
        polar (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inr ⟨k, hk⟩)) = 0 :=
      fun i hi => by
        rw [polar_hypVec_hypVec]
        simp only [Sum.swap_inl, Sum.inr.injEq]
        rw [ite_eq_right (fun h => by rw [← h] at hi; exact lt_irrefl _ hi)]
    have h₂ := eichler_mem_fixElementary (quadTail_hypVec (qA := qA) (.inr j)) huj hty hz₁ hk₂
    have e₂ := eichler_apply_eq_of_polar_eq (quadTail_hypVec (qA := qA) (.inr j))
      (x := t • hypVec K A (.inl j)) (y := t • hypVec K A (.inl j) + e)
      (by rw [hQz, quadTail_smul_hypVec]) hty hz₁ hxj
    have h₃ := eichler_mem_fixElementary (quadTail_hypVec (qA := qA) (.inr ⟨k, hk⟩)) huk hz₂
      he₁ hk₃
    have e₃ := eichler_apply_eq_of_polar_eq (quadTail_hypVec (qA := qA) (.inr ⟨k, hk⟩))
      (x := t • hypVec K A (.inl j) + e) (y := e) (by rw [hQz, he, quadTail_hypVec]) hz₂ he₁
      one_ne_zero
    refine ⟨_, mul_mem (mul_mem h₃ h₂) h₁, 1, one_ne_zero, ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e₁, e₂, e₃, one_smul]

theorem exists_fix_apply_eq_of_inr (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) {k : ℕ}
    (hk : k < r) {x : (Fin r ⊕ Fin r → K) × A} (hx : quadTail r qA x = 0)
    (hxk : ∀ i : Fin r, i.val < k → x.1 (.inr i) = 0) {j : Fin r} (hj : k ≤ j.val)
    (hxj : x.1 (.inr j) ≠ 0) :
    ∃ h ∈ fixElementary r qA k, ∃ c : K, c ≠ 0 ∧ h x = c • hypVec K A (.inl ⟨k, hk⟩) := by
  have htx := polar_hypVec_inl_left (qA := qA) j x
  generalize x.1 (.inr j) = t at hxj htx
  have hne : ∀ i : Fin r, i.val < k → i ≠ j := fun i hi h => by rw [h] at hi; omega
  have hty : polar (quadTail r qA) (hypVec K A (.inl j)) (t • hypVec K A (.inr j)) = t := by
    rw [polar_smul_right_eq, polar_hypVec_hypVec]
    simp
  have hk₁ : ∀ i : Fin r, i.val < k → polar (quadTail r qA) (hypVec K A (.inl i)) x =
      polar (quadTail r qA) (hypVec K A (.inl i)) (t • hypVec K A (.inr j)) := fun i hi => by
    rw [polar_hypVec_inl_left, hxk i hi, polar_smul_right_eq, polar_hypVec_hypVec]
    simp [Ne.symm (hne i hi)]
  have huj : ∀ i : Fin r, i.val < k →
      polar (quadTail r qA) (hypVec K A (.inl i)) (hypVec K A (.inl j)) = 0 := fun i _ => by
    rw [polar_hypVec_hypVec]
    simp
  have h₁ := eichler_mem_fixElementary (quadTail_hypVec (qA := qA) (.inl j)) huj htx hty hk₁
  have e₁ := eichler_apply_eq_of_polar_eq (quadTail_hypVec (qA := qA) (.inl j))
    (x := x) (y := t • hypVec K A (.inr j)) (by rw [hx, quadTail_smul_hypVec]) htx hty hxj
  have h₂ := eichler_tail_mem_fixElementary (qA := qA) k j a₀
  set x' := eichler (quadTail r qA) (hypVec K A (.inl j)) ((0 : Fin r ⊕ Fin r → K), a₀)
    (t • hypVec K A (.inr j)) with hx'
  have hx'Q : quadTail r qA x' = 0 := by
    rw [hx', map_of_mem (orthElementaryGroup_le _ h₂.1), quadTail_smul_hypVec]
  have hx'k : ∀ i : Fin r, i.val < k → x'.1 (.inr i) = 0 := fun i hi => by
    rw [hx', polar_inl_apply_of_mem_fixElementary h₂ hi]
    simp [hypVec, Ne.symm (hne i hi)]
  have hx'j : x'.1 (.inl j) ≠ 0 := by
    have hq : qA a₀ ≠ 0 := fun h => ha₀ (hani a₀ h)
    rw [hx', eichler_apply (quadTail_hypVec _) (polar_hypVec_tail _ _), polar_smul_left,
      polar_smul_left, polar_hypVec_hypVec, polar_hypVec_tail, quadTail_tail]
    simpa [hypVec] using mul_ne_zero hq hxj
  obtain ⟨h₃, h₃mem, c, hc, e₃⟩ := exists_fix_apply_eq_of_inl hk hx'Q hx'k hj hx'j
  refine ⟨h₃ * _ * _, mul_mem (mul_mem h₃mem h₂) h₁, c, hc, ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e₁, ← hx', e₃]

theorem exists_fix_apply_eq (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) {k : ℕ}
    (hk : k < r) {x : (Fin r ⊕ Fin r → K) × A} (hx : quadTail r qA x = 0)
    (hxk : ∀ i : Fin r, i.val < k → x.1 (.inr i) = 0) (hxF : x ∉ tailFlag K A r k) :
    ∃ h ∈ fixElementary r qA k, ∃ c : K, c ≠ 0 ∧ h x = c • hypVec K A (.inl ⟨k, hk⟩) := by
  by_cases h1 : ∃ j : Fin r, k ≤ j.val ∧ x.1 (.inl j) ≠ 0
  · obtain ⟨j, hj, hxj⟩ := h1
    exact exists_fix_apply_eq_of_inl hk hx hxk hj hxj
  by_cases h2 : ∃ j : Fin r, k ≤ j.val ∧ x.1 (.inr j) ≠ 0
  · obtain ⟨j, hj, hxj⟩ := h2
    exact exists_fix_apply_eq_of_inr hani ha₀ hk hx hxk hj hxj
  exfalso
  simp only [not_exists, not_and, not_not] at h1 h2
  have hy : ∀ j : Fin r, x.1 (.inr j) = 0 := fun j => by
    by_cases hj : k ≤ j.val
    · exact h2 j hj
    · exact hxk j (by omega)
  have ha : x.2 = 0 := by
    refine hani _ ?_
    rw [quadTail_apply, quadPlus_apply, Finset.sum_eq_zero fun i _ => by rw [hy i, mul_zero],
      zero_add] at hx
    exact hx
  exact hxF (mem_tailFlag_iff.2 ⟨mem_flag.2 ⟨hy, h1⟩, ha⟩)

end Move

section Flags

theorem map_tailFlag_of_mem_fixElementary {n : ℕ}
    {h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hh : h ∈ fixElementary r qA n) {m : ℕ} (hm : m ≤ n) :
    (tailFlag K A r m).map (h : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      tailFlag K A r m := by
  rw [tailFlag, Submodule.map_span, ← Set.image_comp]
  congr 1
  refine Set.image_congr fun j hj => ?_
  rw [Function.comp_apply, LinearEquiv.coe_coe]
  exact hh.2 j (lt_of_lt_of_le hj hm)

theorem polar_eq_zero_of_forall_mem {X : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hX : ∀ x ∈ X, quadTail r qA x = 0) {x y : (Fin r ⊕ Fin r → K) × A} (hx : x ∈ X)
    (hy : y ∈ X) : polar (quadTail r qA) x y = 0 := by
  simp only [QuadraticMap.polar, hX _ (X.add_mem hx hy), hX _ hx, hX _ hy, sub_zero]

variable [FiniteDimensional K A]

theorem exists_mem_map_eq_tailFlag (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) {k : ℕ}
    (hk : k ≤ r) {W : Fin k → Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : W ∈ singularFlags (quadTail r qA) k) :
    ∃ g ∈ orthElementaryGroup (quadTail r qA), ∀ i : Fin k,
      (W i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
        tailFlag K A r (i + 1) := by
  obtain ⟨hWd, hWm, hWs⟩ := hW
  suffices key : ∀ n, n ≤ k → ∃ g ∈ orthElementaryGroup (quadTail r qA), ∀ i : Fin k,
      i.val < n → (W i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
        tailFlag K A r (i + 1) by
    obtain ⟨g, hg, hgW⟩ := key k le_rfl
    exact ⟨g, hg, fun i => hgW i i.2⟩
  intro n
  induction n with
  | zero => exact fun _ => ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨g, hg, hgW⟩ := ih (by omega)
    set i₀ : Fin k := ⟨n, by omega⟩ with hi₀
    set X := (W i₀).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A))
      with hX
    have hgO := orthElementaryGroup_le _ hg
    have hXs : ∀ x ∈ X, quadTail r qA x = 0 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [LinearEquiv.coe_coe, map_of_mem hgO]
      exact hWs i₀ y hy
    have hXd : finrank K X = n + 1 := by
      rw [hX, LinearEquiv.finrank_map_eq]
      exact hWd i₀
    have hFX : tailFlag K A r n ≤ X := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · have h00 : tailFlag K A r 0 = ⊥ := by
          rw [tailFlag]
          convert Submodule.span_empty
          ext v
          simp
        rw [h0, h00]
        exact bot_le
      · have h := hgW ⟨n - 1, by omega⟩ (by simp only; omega)
        have hn1 : (⟨n - 1, by omega⟩ : Fin k).val + 1 = n := by simp only; omega
        rw [hn1] at h
        rw [← h]
        exact Submodule.map_mono (hWm (show (⟨n - 1, by omega⟩ : Fin k) ≤ i₀ by
          rw [Fin.le_def]; simp only [hi₀]; omega))
    obtain ⟨w, hwX, hwF⟩ : ∃ w ∈ X, w ∉ tailFlag K A r n := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have := Submodule.finrank_mono (show X ≤ tailFlag K A r n from hcon)
      rw [hXd, finrank_tailFlag (by omega)] at this
      omega
    have hwk : ∀ i : Fin r, i.val < n → w.1 (.inr i) = 0 := fun i hi => by
      rw [← polar_hypVec_inl_left (qA := qA)]
      exact polar_eq_zero_of_forall_mem hXs (hFX (Submodule.subset_span ⟨i, hi, rfl⟩)) hwX
    obtain ⟨h, hh, c, hc, hhw⟩ :=
      exists_fix_apply_eq hani ha₀ (by omega : n < r) (hXs w hwX) hwk hwF
    refine ⟨h * g, mul_mem hh.1 hg, fun i hi => ?_⟩
    rw [map_mul_linearEquiv]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
    · rw [hgW i hlt]
      exact map_tailFlag_of_mem_fixElementary hh (by omega)
    · have hii : i = i₀ := Fin.ext heq
      rw [hii, ← hX]
      have hle : tailFlag K A r (n + 1) ≤
          X.map (h : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) := by
        rw [tailFlag, Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjn | hjn
        · refine ⟨hypVec K A (.inl j), hFX (Submodule.subset_span ⟨j, hjn, rfl⟩), ?_⟩
          rw [LinearEquiv.coe_coe]
          exact hh.2 j hjn
        · have hj' : j = ⟨n, by omega⟩ := Fin.ext hjn
          refine ⟨c⁻¹ • w, X.smul_mem _ hwX, ?_⟩
          rw [LinearEquiv.coe_coe, map_smul, hhw, smul_smul, inv_mul_cancel₀ hc, one_smul, hj']
      refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
      rw [finrank_tailFlag (by omega), LinearEquiv.finrank_map_eq, hXd]

omit [FiniteDimensional K A] in
theorem map_map_inv (W : Submodule K ((Fin r ⊕ Fin r → K) × A))
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    (W.map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _)).map
      ((g⁻¹ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = W := by
  rw [← map_mul_linearEquiv, inv_mul_cancel]
  exact Submodule.map_id W

end Flags

theorem orthogonal_geometry_tail_singular_flag_transitivity {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0) :
    (∀ k, k ≤ r → ∀ W ∈ singularFlags (quadTail r qA) k, ∀ W' ∈ singularFlags (quadTail r qA) k,
      ∃ g ∈ orthElementaryGroup (quadTail r qA), ∀ i,
        (W i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = W' i) ∧
    ∀ k, k ≤ r → ∀ X ∈ singularSubspaces (quadTail r qA) k,
      ∀ X' ∈ singularSubspaces (quadTail r qA) k, ∃ g ∈ orthElementaryGroup (quadTail r qA),
        X.map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = X' := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hflag : ∀ k, k ≤ r → ∀ W ∈ singularFlags (quadTail r qA) k,
      ∀ W' ∈ singularFlags (quadTail r qA) k, ∃ g ∈ orthElementaryGroup (quadTail r qA), ∀ i,
        (W i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = W' i := by
    intro k hk W hW W' hW'
    obtain ⟨g, hg, hgW⟩ := exists_mem_map_eq_tailFlag hani ha₀ hk hW
    obtain ⟨g', hg', hgW'⟩ := exists_mem_map_eq_tailFlag hani ha₀ hk hW'
    refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg') hg, fun i => ?_⟩
    rw [map_mul_linearEquiv, hgW i, ← hgW' i, map_map_inv]
  refine ⟨hflag, fun k hk X hX X' hX' => ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    have hX0 : X = ⊥ := Submodule.finrank_eq_zero.1 hX.1
    have hX'0 : X' = ⊥ := Submodule.finrank_eq_zero.1 hX'.1
    refine ⟨1, one_mem _, ?_⟩
    rw [hX0, hX'0, Submodule.map_bot]
  · obtain ⟨W, hW, hWX⟩ := exists_mem_singularFlags_eq hX hpos
    obtain ⟨W', hW', hWX'⟩ := exists_mem_singularFlags_eq hX' hpos
    obtain ⟨g, hg, hgW⟩ := hflag k hk W hW W' hW'
    exact ⟨g, hg, by rw [← hWX, ← hWX', hgW]⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
