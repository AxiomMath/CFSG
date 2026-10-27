module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidInv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

@[expose] def stdW : Subgroup (stabE (ε := ε) h) where
  carrier := {g | smat h g *ᵥ Pi.single hF 1 = Pi.single hF 1 ∧
    ∀ j : Fin ε, 2 ≤ (j : ℕ) → smat h g *ᵥ Pi.single (.inr (.inl j)) 1 =
      Pi.single (.inr (.inl j)) 1}
  mul_mem' := by
    rintro g g' ⟨hg1, hg2⟩ ⟨hg'1, hg'2⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [smat_mul, ← mulVec_mulVec, hg'1, hg1]
    · rw [smat_mul, ← mulVec_mulVec, hg'2 j hj, hg2 j hj]
  one_mem' := ⟨one_mulVec _, fun _ _ => one_mulVec _⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hgi : smat h g⁻¹ * smat h g = 1 := by
      rw [← smat_mul, inv_mul_cancel]
      rfl
    refine ⟨?_, fun j hj => ?_⟩
    · conv_lhs => rw [← hg1]
      rw [mulVec_mulVec, hgi, one_mulVec]
    · conv_lhs => rw [← hg2 j hj]
      rw [mulVec_mulVec, hgi, one_mulVec]

omit [CharP K 2] in
theorem eichM_mul_blkZM_apply (σ : K →+* K) (a : Fin ε → K) (c : K)
    (C : Matrix (Fin ε) (Fin ε) K) :
    (eichM σ a c * blkZM C) hE hE = 1 ∧ (eichM σ a c * blkZM C) hF hF = 1 ∧
      (eichM σ a c * blkZM C) hE hF = c ∧
      (∀ k, (eichM σ a c * blkZM C) (.inr (.inl k)) hE = 0) ∧
      (∀ l, (eichM σ a c * blkZM C) hF (.inr (.inl l)) = 0) ∧
      (eichM σ a c * blkZM C) hF hE = 0 ∧
      (∀ l, (eichM σ a c * blkZM C) hE (.inr (.inl l)) = ∑ k, σ (a k) * C k l) ∧
      (∀ k l, (eichM σ a c * blkZM C) (.inr (.inl k)) (.inr (.inl l)) = C k l) := by
  refine ⟨?_, ?_, ?_, fun k => ?_, fun l => ?_, ?_, fun l => ?_, fun k l => ?_⟩ <;>
    simp [eichM, blkZM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero]

section Witt

variable {n : ℕ}

omit [CharP K 2] in
theorem exists_orthonormal_in (Y : Submodule K (Fin n → K))
    (hY : ∀ y ∈ Y, (∀ y' ∈ Y, hform h.bar y y' = 0) → y = 0) {r : ℕ}
    (hr : r ≤ Module.finrank K Y) :
    ∃ b : Fin r → Fin n → K, (∀ i, b i ∈ Y) ∧
      ∀ i j, hform h.bar (b i) (b j) = if i = j then 1 else 0 := by
  have hσ : ∀ x, h.bar (h.bar x) = x := h.bar_bar
  let BY : Y →ₛₗ[h.bar] Y →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ h.bar (RingHom.id K) (fun a b => hform h.bar (a : Fin n → K) b)
      (fun a b c => by rw [Submodule.coe_add, hform_add_left])
      (fun t a b => by rw [Submodule.coe_smul, hform_smul_left, smul_eq_mul])
      (fun a b c => by rw [Submodule.coe_add, hform_add_right])
      (fun t a b => by rw [Submodule.coe_smul, hform_smul_right, smul_eq_mul, RingHom.id_apply])
  have hBYapp : ∀ a b : Y, BY a b = hform h.bar (a : Fin n → K) b := fun a b => rfl
  have hBY : BY.IsSymm := ⟨fun a b => by rw [hBYapp, hBYapp, ← hform_comm hσ]⟩
  have hBYl : BY.SeparatingLeft := by
    intro a ha
    exact Subtype.ext (hY a a.2 fun y' hy' => ha ⟨y', hy'⟩)
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hnorm : ∀ d : K, h.bar d = d → d ≠ 0 → ∃ c, h.bar c * c = d := fun d hd _ => by
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, (h.mem_fixedField).mpr hd⟩
    exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩
  obtain ⟨b, hb⟩ := exists_orthonormal_family hBY hBYl hc₀ hnorm hr
  exact ⟨fun i => (b i : Fin n → K), fun i => (b i).2, fun i j => hb i j⟩

omit [CharP K 2] in
theorem exists_su_std [Finite K] (hε : 2 ≤ ε) (S C : Submodule K (Fin ε → K))
    (hS : Module.finrank K S = 2) (hC : Module.finrank K C = ε - 2) (hSC : S ⊓ C = ⊥)
    (horth : ∀ s ∈ S, ∀ c ∈ C, hform h.bar s c = 0) :
    ∃ U : StatedSU ε (2 ^ f) K,
      (∀ j : Fin ε, (j : ℕ) < 2 →
        ((U : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *ᵥ Pi.single j 1 ∈ S) ∧
      ∀ j : Fin ε, 2 ≤ (j : ℕ) →
        ((U : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *ᵥ Pi.single j 1 ∈ C := by
  have hσ : ∀ x, h.bar (h.bar x) = x := h.bar_bar
  have hsup : S ⊔ C = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq S C
    rw [hSC, finrank_bot, add_zero, hS, hC] at this
    rw [this, Module.finrank_fin_fun]
    omega
  have hall : ∀ y : Fin ε → K, (∀ s ∈ S, hform h.bar y s = 0) → (∀ c ∈ C, hform h.bar y c = 0) →
      y = 0 := by
    intro y hyS hyC
    refine eq_zero_of_hform_right hσ fun (v : Fin ε → K) => ?_
    have hv : v ∈ S ⊔ C := by rw [hsup]; trivial
    obtain ⟨s, hs, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hform_add_right, hyS s hs, hyC c hc, add_zero]
  have hSnd : ∀ y ∈ S, (∀ y' ∈ S, hform h.bar y y' = 0) → y = 0 := fun y hy hyS =>
    hall y hyS fun c hc => horth y hy c hc
  have hCnd : ∀ y ∈ C, (∀ y' ∈ C, hform h.bar y y' = 0) → y = 0 := fun y hy hyC =>
    hall y (fun s hs => by rw [hform_comm hσ, horth s hs y hy, map_zero]) hyC
  obtain ⟨bs, hbsS, hbs⟩ := exists_orthonormal_in h S hSnd (r := 2) hS.ge
  obtain ⟨bc, hbcC, hbc⟩ := exists_orthonormal_in h C hCnd (r := ε - 2) hC.ge
  set b : Fin ε → Fin ε → K := fun j =>
    if hj : (j : ℕ) < 2 then bs ⟨j, hj⟩ else bc ⟨j - 2, by omega⟩ with hb_def
  have hbS : ∀ j : Fin ε, (j : ℕ) < 2 → b j ∈ S := fun j hj => by
    simp only [hb_def, dite_eq_left hj]
    exact hbsS _
  have hbC : ∀ j : Fin ε, 2 ≤ (j : ℕ) → b j ∈ C := fun j hj => by
    simp only [hb_def, dite_eq_right (show ¬ (j : ℕ) < 2 by omega)]
    exact hbcC _
  have hbb : ∀ i j, hform h.bar (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hi : (i : ℕ) < 2 <;> by_cases hj : (j : ℕ) < 2
    · simp only [hb_def, dite_eq_left hi, dite_eq_left hj, hbs, Fin.ext_iff]
    · have hij : i ≠ j := fun h' => hj (h' ▸ hi)
      rw [ite_eq_right hij, horth _ (hbS i hi) _ (hbC j (by omega))]
    · have hij : i ≠ j := fun h' => hi (h' ▸ hj)
      rw [ite_eq_right hij, hform_comm hσ, horth _ (hbS j hj) _ (hbC i (by omega)), map_zero]
    · simp only [hb_def, dite_eq_right hi, dite_eq_right hj, hbc, Fin.ext_iff]
      by_cases hij : (i : ℕ) = j
      · rw [ite_eq_left (by omega), ite_eq_left hij]
      · rw [ite_eq_right (by omega), ite_eq_right hij]
  set U₀ : Matrix (Fin ε) (Fin ε) K := Matrix.of fun i j => b j i with hU₀
  have hU₀u : adjM h.bar U₀ * U₀ = 1 := by
    ext i j
    rw [one_apply, ← hbb i j]
    simp [hU₀, adjM, mul_apply, hform, dotProduct]
  set d := U₀.det with hd
  have hdd : h.bar d * d = 1 := by
    have := congrArg Matrix.det hU₀u
    have e : (U₀.map h.bar).det = h.bar U₀.det := (RingHom.map_det h.bar U₀).symm
    rwa [det_mul, det_one, adjM, det_transpose, e] at this
  have hd0 : d ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hdd
    exact zero_ne_one hdd
  set D : Fin ε → K := fun j => if (j : ℕ) = 0 then d⁻¹ else 1 with hD
  have hDD : ∀ j, h.bar (D j) * D j = 1 := fun j => by
    simp only [hD]
    split_ifs
    · rw [map_inv₀, ← mul_inv, hdd, inv_one]
    · rw [map_one, one_mul]
  have hdetD : (diagonal D).det = d⁻¹ := by
    rw [det_diagonal]
    have : ∏ j : Fin ε, D j = ∏ j : Fin ε, if j = ⟨0, by omega⟩ then d⁻¹ else 1 := by
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [hD, Fin.ext_iff]
    rw [this, Finset.prod_ite_eq']
    simp
  have hUdet : (U₀ * diagonal D).det = 1 := by rw [det_mul, hdetD, mul_inv_cancel₀ hd0]
  have hUu : ((U₀ * diagonal D).map (· ^ 2 ^ f))ᵀ * (U₀ * diagonal D) = 1 := by
    have hmap : (U₀ * diagonal D).map (· ^ 2 ^ f) = (U₀ * diagonal D).map h.bar :=
      congrArg _ (funext fun x => (h.bar_apply x).symm)
    rw [hmap]
    change adjM h.bar (U₀ * diagonal D) * (U₀ * diagonal D) = 1
    rw [adjM_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (adjM h.bar U₀), hU₀u, Matrix.one_mul]
    ext i j
    simp [adjM, diagonal, mul_apply, one_apply]
    by_cases hij : i = j
    · subst hij
      simp [hDD]
    · simp [hij, Ne.symm hij]
  obtain ⟨U, hU⟩ := exists_statedSU_eq hUdet hUu
  have hcol : ∀ j,
      ((U : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *ᵥ Pi.single j 1 = D j • b j := by
    intro j
    rw [hU, ← mulVec_mulVec, diagonal_mulVec_single, mul_one]
    ext i
    simp [hU₀, mulVec, dotProduct, Pi.single_apply, mul_comm]
  refine ⟨U, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hcol]
    exact S.smul_mem _ (hbS j hj)
  · rw [hcol]
    exact C.smul_mem _ (hbC j hj)

end Witt

section Prelim

theorem hform_rmat (g : stabE (ε := ε) h) (v w : Fin ε → K) :
    hform h.bar (rmat h g *ᵥ v) (rmat h g *ᵥ w) = hform h.bar v w := by
  rw [hform_mulVec, mulVec_mulVec,
    adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply (zBlockHom h g).2, one_mulVec]

theorem rmat_mul (g g' : stabE (ε := ε) h) : rmat h (g * g') = rmat h g * rmat h g' := by
  rw [rmat, map_mul, Subgroup.coe_mul, Units.val_mul]

theorem rmat_one : rmat h (1 : stabE (ε := ε) h) = 1 := by
  rw [rmat, map_one]
  rfl

theorem rmat_inv_mul (g : stabE (ε := ε) h) : rmat h g⁻¹ * rmat h g = 1 := by
  rw [← rmat_mul, inv_mul_cancel, rmat_one]

@[expose] def cval (g : stabE (ε := ε) h) : K := smat h g hE hF

theorem smat_apply_e_e (g : stabE (ε := ε) h) : smat h g hE hE = 1 := by
  obtain ⟨c, hc⟩ := exists_eq_eichM_avec h g
  rw [hc]
  exact (eichM_mul_blkZM_apply h.bar _ _ _).1

theorem smat_apply_f_f (g : stabE (ε := ε) h) : smat h g hF hF = 1 := by
  obtain ⟨c, hc⟩ := exists_eq_eichM_avec h g
  rw [hc]
  exact (eichM_mul_blkZM_apply h.bar _ _ _).2.1

theorem cval_mul_of_avec (g : stabE (ε := ε) h) {g' : stabE (ε := ε) h} (hg' : avec h g' = 0) :
    cval h (g * g') = cval h g + cval h g' := by
  have hz : ∀ k, smat h g' (.inr (.inl k)) hF = 0 := fun k => congrFun hg' k
  simp only [cval, smat_mul, mul_apply, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, Fin.default_eq_zero]
  rw [show (Sum.inl 0 : HypIndex 1 ε) = hE from rfl, show (Sum.inr (Sum.inr 0) : HypIndex 1 ε) = hF
    from rfl, smat_apply_e_e, smat_apply_f_f]
  simp only [hz, mul_zero, Finset.sum_const_zero, one_mul, mul_one, zero_add]
  ring

theorem mem_stdW_of {g : stabE (ε := ε) h} (ha : avec h g = 0) (hc : cval h g = 0)
    (hρ : ∀ j : Fin ε, 2 ≤ (j : ℕ) → rmat h g *ᵥ Pi.single j 1 = Pi.single j 1) :
    g ∈ stdW h := by
  obtain ⟨c, hgc⟩ := exists_eq_eichM_avec h g
  have hc' : c = 0 := by
    have := hc
    simp only [cval, hgc] at this
    rwa [(eichM_mul_blkZM_apply h.bar (avec h g) c (rmat h g)).2.2.1] at this
  rw [ha, hc', eichM_zero, Matrix.one_mul] at hgc
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hgc]
    ext i
    rcases i with i | k | i <;> simp [blkZM, mulVec, dotProduct, Fin.eq_zero, Pi.single_apply]
  · rw [hgc]
    have hj' := congrFun (hρ j hj)
    ext i
    rcases i with i | k | i
    · simp [blkZM, mulVec, dotProduct, Pi.single_apply]
    · have := hj' k
      simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
      simp [blkZM, mulVec, dotProduct, Pi.single_apply, this]
    · simp [blkZM, mulVec, dotProduct, Pi.single_apply]

end Prelim

section Spaces

variable {H : Subgroup (stabE (ε := ε) h)}

theorem rmat_mulVec_mem_commSub {g : stabE (ε := ε) h}
    (hg : ∀ g' ∈ H, g * g' * g⁻¹ ∈ H) {v : Fin ε → K} (hv : v ∈ commSub h H) :
    rmat h g *ᵥ v ∈ commSub h H := by
  refine AddSubgroup.closure_induction (p := fun v _ => rmat h g *ᵥ v ∈ commSpace h H) ?_ ?_ ?_ ?_
    hv
  · rintro _ ⟨g', hg', w, rfl⟩
    refine AddSubgroup.subset_closure ⟨g * g' * g⁻¹, hg g' hg', rmat h g *ᵥ w, ?_⟩
    rw [mulVec_sub, mulVec_mulVec (M := rmat h g) (N := rmat h g'), rmat_mul, rmat_mul,
      mulVec_mulVec (M := rmat h g * rmat h g' * rmat h g⁻¹),
      Matrix.mul_assoc (rmat h g * rmat h g'), rmat_inv_mul, Matrix.mul_one]
  · rw [mulVec_zero]
    exact zero_mem _
  · intro a b _ _ ha hb
    rw [mulVec_add]
    exact add_mem ha hb
  · intro a _ ha
    rw [mulVec_neg]
    exact neg_mem ha

theorem hform_commSub_fixSub {s c : Fin ε → K} (hs : s ∈ commSub h H) (hc : c ∈ fixSub h H) :
    hform h.bar s c = 0 := by
  refine AddSubgroup.closure_induction (p := fun s _ => hform h.bar s c = 0) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨g, hg, v, rfl⟩
    rw [hform_sub_left]
    conv_lhs => arg 2; rw [← hc g hg]
    rw [hform_rmat, sub_self]
  · exact hform_zero_left _
  · intro a b _ _ ha hb
    rw [hform_add_left, ha, hb, add_zero]
  · intro a _ ha
    have : hform h.bar (-a) c = -hform h.bar a c := by
      simp only [hform, dotProduct, Function.comp, Pi.neg_apply, map_neg, neg_mul,
        Finset.sum_neg_distrib]
    rw [this, ha, neg_zero]

theorem rmat_mulVec_mem_fixSub {z : stabE (ε := ε) h} (hz : ∀ g ∈ H, z * g = g * z)
    {c : Fin ε → K} (hc : c ∈ fixSub h H) : rmat h z *ᵥ c ∈ fixSub h H := by
  intro g hg
  rw [mulVec_mulVec, ← rmat_mul, ← hz g hg, rmat_mul, ← mulVec_mulVec, hc g hg]

end Spaces

section Cohom

variable {S C : Submodule K (Fin ε → K)} (hSC : IsCompl S C)

omit [CharP K 2] in
theorem projection_mulVec_comm {A : Matrix (Fin ε) (Fin ε) K} (hAS : ∀ v ∈ S, A *ᵥ v ∈ S)
    (hAC : ∀ v ∈ C, A *ᵥ v ∈ C) (x : Fin ε → K) :
    S.projection C hSC (A *ᵥ x) = A *ᵥ S.projection C hSC x := by
  set π := S.projection C hSC with hπ
  have hx : x - π x ∈ C := by
    rw [← Submodule.projection_apply_eq_zero_iff hSC, map_sub,
      Submodule.projection_apply_left hSC ⟨π x, Submodule.projection_apply_mem hSC x⟩,
      sub_self]
  have h1 : A *ᵥ x = A *ᵥ π x + A *ᵥ (x - π x) := by rw [← mulVec_add, add_sub_cancel]
  rw [h1, map_add, Submodule.projection_apply_of_mem_right hSC (hAC _ hx), add_zero]
  exact Submodule.projection_apply_left hSC ⟨_, hAS _ (Submodule.projection_apply_mem hSC x)⟩

include hSC in
theorem exists_mem_ker_avec_conj_mem [Finite K] {H : Subgroup (stabE (ε := ε) h)}
    (hHS : ∀ g ∈ H, ∀ v ∈ S, rmat h g *ᵥ v ∈ S) (hHC : ∀ g ∈ H, ∀ v ∈ C, rmat h g *ᵥ v = v)
    {z : stabE (ε := ε) h} (hzH : ∀ g ∈ H, z * g = g * z) (hzS : ∀ v ∈ S, rmat h z *ᵥ v ∈ S)
    (hzC : ∀ v ∈ C, rmat h z *ᵥ v ∈ C) (hzinj : ∀ v ∈ S, rmat h z *ᵥ v = v → v = 0) :
    ∃ x₀ ∈ (zBlockHom (ε := ε) h).ker, ∀ g ∈ H, avec h (x₀⁻¹ * g * x₀) ∈ C := by
  set π := S.projection C hSC with hπ
  let T : S →ₗ[K] S := (Matrix.toLin' (rmat h z - 1)).restrict (p := S) (q := S) (fun v hv => by
    rw [Matrix.toLin'_apply, sub_mulVec, one_mulVec]
    exact sub_mem (hzS v hv) hv)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 := congrArg Subtype.val hv
    simp only [T, LinearMap.coe_restrict_apply, Matrix.toLin'_apply, sub_mulVec, one_mulVec,
      ZeroMemClass.coe_zero] at h1
    exact Subtype.ext (hzinj v v.2 (sub_eq_zero.mp h1))
  obtain ⟨v₀, hv₀⟩ := (LinearMap.injective_iff_surjective.mp hTinj)
    ⟨π (avec h z), Submodule.projection_apply_mem hSC _⟩
  have hv₀' : rmat h z *ᵥ (v₀ : Fin ε → K) - v₀ = π (avec h z) := by
    have := congrArg Subtype.val hv₀
    simpa [T, sub_mulVec] using this
  have hπS : ∀ v ∈ S, π v = v := fun v hv => Submodule.projection_apply_left hSC ⟨v, hv⟩
  have hπg : ∀ g ∈ H, ∀ x, π (rmat h g *ᵥ x) = rmat h g *ᵥ π x := fun g hg =>
    projection_mulVec_comm hSC (hHS g hg) (fun v hv => by rw [hHC g hg v hv]; exact hv)
  have hπz : ∀ x, π (rmat h z *ᵥ x) = rmat h z *ᵥ π x := projection_mulVec_comm hSC hzS hzC
  have hcomm : ∀ g ∈ H, rmat h z * rmat h g = rmat h g * rmat h z := fun g hg => by
    rw [← rmat_mul, ← rmat_mul, hzH g hg]
  have hkey : ∀ g ∈ H, π (avec h g) = rmat h g *ᵥ (v₀ : Fin ε → K) - v₀ := by
    intro g hg
    have e := congrArg (avec h) (hzH g hg)
    rw [avec_mul, avec_mul] at e
    have e' := congrArg π e
    rw [map_add, map_add, hπz, hπg g hg] at e'
    set u := π (avec h g) - (rmat h g *ᵥ (v₀ : Fin ε → K) - v₀) with hu
    have huS : u ∈ S := sub_mem (Submodule.projection_apply_mem hSC _)
      (sub_mem (hHS g hg _ v₀.2) v₀.2)
    have hzu : rmat h z *ᵥ u = u := by
      have h1 : rmat h z *ᵥ π (avec h g) = π (avec h g) + rmat h g *ᵥ π (avec h z) -
          π (avec h z) := by
        rw [← e']
        abel
      rw [hu, mulVec_sub, mulVec_sub, h1, mulVec_mulVec, hcomm g hg, ← mulVec_mulVec, ← hv₀',
        mulVec_sub]
      abel
    have hu0 := hzinj u huS hzu
    rw [hu, sub_eq_zero] at hu0
    exact hu0
  obtain ⟨x₀, hx₀, hx₀v⟩ := exists_mem_ker_avec_eq h (v₀ : Fin ε → K)
  have hx1 : rmat h x₀⁻¹ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp (inv_mem hx₀)]
    rfl
  refine ⟨x₀, hx₀, fun g hg => ?_⟩
  rw [← Submodule.projection_apply_eq_zero_iff hSC]
  rw [avec_mul, avec_mul, rmat_mul, hx1, Matrix.one_mul, one_mulVec, avec_inv, hx1, one_mulVec,
    hx₀v, map_add, map_add, map_neg, hπS _ v₀.2, hkey g hg, hπg g hg, hπS _ v₀.2]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : -(v₀ : Fin ε → K) + (rmat h g *ᵥ (v₀ : Fin ε → K) - v₀) + rmat h g *ᵥ (v₀ : Fin ε → K) =
      (2 : K) • (rmat h g *ᵥ (v₀ : Fin ε → K) - v₀) := by
    rw [two_smul]
    abel
  rw [this, h2, zero_smul]

end Cohom

section Trivial

@[expose] def avecCvalSub : Subgroup (stabE (ε := ε) h) where
  carrier := {g | avec h g = 0 ∧ cval h g = 0}
  mul_mem' := by
    rintro g g' ⟨hg, hgc⟩ ⟨hg', hgc'⟩
    exact ⟨by rw [avec_mul, hg, hg', mulVec_zero, add_zero],
      by rw [cval_mul_of_avec h g hg', hgc, hgc', add_zero]⟩
  one_mem' := ⟨avec_one h, by simp [cval, smat]⟩
  inv_mem' := by
    rintro g ⟨hg, hgc⟩
    have hgi : avec h g⁻¹ = 0 := by rw [avec_inv, hg, mulVec_zero, neg_zero]
    refine ⟨hgi, ?_⟩
    have := cval_mul_of_avec h g hgi
    rw [mul_inv_cancel, hgc, zero_add] at this
    rw [← this]
    simp [cval, smat]

@[expose] def avecSub : Subgroup (stabE (ε := ε) h) where
  carrier := {g | avec h g = 0}
  mul_mem' := by
    rintro g g' hg hg'
    simp only [Set.mem_ofPred_eq] at hg hg' ⊢
    rw [avec_mul, hg, hg', mulVec_zero, add_zero]
  one_mem' := avec_one h
  inv_mem' := by
    rintro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [avec_inv, hg, mulVec_zero, neg_zero]

theorem le_avecCvalSub_of_perfect {H : Subgroup (stabE (ε := ε) h)} (hH : ⁅H, H⁆ = H)
    {C : Submodule K (Fin ε → K)} (hHa : ∀ g ∈ H, avec h g ∈ C)
    (hHC : ∀ g ∈ H, ∀ v ∈ C, rmat h g *ᵥ v = v) : H ≤ avecCvalSub h := by
  have hadd : ∀ x ∈ H, ∀ y ∈ H, avec h (x * y) = avec h x + avec h y := fun x hx y hy => by
    rw [avec_mul, hHC x hx _ (hHa y hy)]
  have hinv : ∀ x ∈ H, avec h x⁻¹ = -avec h x := fun x hx => by
    rw [avec_inv, hHC _ (inv_mem hx) _ (hHa x hx)]
  have h1 : H ≤ avecSub h := by
    rw [← hH, Subgroup.commutator_le]
    intro a ha b hb
    show avec h ⁅a, b⁆ = 0
    rw [commutatorElement_def, hadd _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb),
      hadd _ (mul_mem ha hb) _ (inv_mem ha), hadd _ ha _ hb, hinv _ ha, hinv _ hb]
    abel
  have cadd : ∀ x ∈ H, ∀ y ∈ H, cval h (x * y) = cval h x + cval h y := fun x _ y hy =>
    cval_mul_of_avec h x (h1 hy)
  have cinv : ∀ x ∈ H, cval h x⁻¹ = -cval h x := fun x hx => by
    have := cadd x hx _ (inv_mem hx)
    rw [mul_inv_cancel] at this
    have h0 : cval h (1 : stabE (ε := ε) h) = 0 := by simp [cval, smat]
    rw [h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  rw [← hH, Subgroup.commutator_le]
  intro a ha b hb
  have hab : ⁅a, b⁆ ∈ H := by
    rw [← hH]
    exact Subgroup.commutator_mem_commutator ha hb
  refine ⟨h1 hab, ?_⟩
  rw [commutatorElement_def, cadd _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb),
    cadd _ (mul_mem ha hb) _ (inv_mem ha), cadd _ ha _ hb, cinv _ ha, cinv _ hb]
  abel

end Trivial

omit [CharP K 2] in
theorem avec_blkZHom (U : StatedSU ε (2 ^ f) K) :
    avec h (⟨blkZHom h U, blkZHom_mem_stabE h U⟩ : stabE (ε := ε) h) = 0 := by
  funext k
  simp [avec, smat, coe_blkZHom, blkZM]

omit [CharP K 2] in
theorem cval_blkZHom (U : StatedSU ε (2 ^ f) K) :
    cval h (⟨blkZHom h U, blkZHom_mem_stabE h U⟩ : stabE (ε := ε) h) = 0 := by
  simp [cval, smat, coe_blkZHom, blkZM]

theorem exists_conj_le_stdW [Finite K] (hε : 2 ≤ ε) {H : Subgroup (stabE (ε := ε) h)}
    (hH : ⁅H, H⁆ = H) (hS : Module.finrank K (commSub h H) = 2)
    (hC : Module.finrank K (fixSub h H) = ε - 2) (hSC : commSub h H ⊓ fixSub h H = ⊥)
    {z : stabE (ε := ε) h} (hzH : ∀ g ∈ H, z * g = g * z)
    (hzS : commSub h H ⊓ fixOneSub h z = ⊥) :
    ∃ g₀ : stabE (ε := ε) h, ∀ g ∈ H, g₀⁻¹ * g * g₀ ∈ stdW h := by
  set S := commSub h H with hSdef
  set C := fixSub h H with hCdef
  have hcompl : IsCompl S C := by
    refine ⟨disjoint_iff.mpr hSC, codisjoint_iff.mpr ?_⟩
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq S C
    rw [hSC, finrank_bot, add_zero, hS, hC] at this
    rw [this, Module.finrank_fin_fun]
    omega
  have hHS : ∀ g ∈ H, ∀ v ∈ S, rmat h g *ᵥ v ∈ S := fun g hg v hv =>
    rmat_mulVec_mem_commSub h (fun g' hg' => mul_mem (mul_mem hg hg') (inv_mem hg)) hv
  have hHC : ∀ g ∈ H, ∀ v ∈ C, rmat h g *ᵥ v = v := fun g hg v hv => hv g hg
  have hzS' : ∀ v ∈ S, rmat h z *ᵥ v ∈ S := fun v hv =>
    rmat_mulVec_mem_commSub h (fun g' hg' => by rw [hzH g' hg', mul_inv_cancel_right]; exact hg')
      hv
  have hzC : ∀ v ∈ C, rmat h z *ᵥ v ∈ C := fun v hv => rmat_mulVec_mem_fixSub h hzH hv
  have hzinj : ∀ v ∈ S, rmat h z *ᵥ v = v → v = 0 := fun v hv hzv => by
    have : v ∈ S ⊓ fixOneSub h z := ⟨hv, hzv⟩
    rwa [hzS, Submodule.mem_bot] at this
  obtain ⟨x₀, hx₀, hx₀C⟩ := exists_mem_ker_avec_conj_mem h hcompl hHS hHC hzH hzS' hzC hzinj
  have hx1 : rmat h x₀ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hx₀]
    rfl
  have hx1' : rmat h x₀⁻¹ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp (inv_mem hx₀)]
    rfl
  set H₂ := H.map (MulAut.conj x₀⁻¹).toMonoidHom with hH₂
  have hH₂perf : ⁅H₂, H₂⁆ = H₂ := by rw [hH₂, ← Subgroup.map_commutator, hH]
  have hH₂a : ∀ w ∈ H₂, avec h w ∈ C := by
    rintro _ ⟨g, hg, rfl⟩
    simpa [MulAut.conj_apply] using hx₀C g hg
  have hH₂C : ∀ w ∈ H₂, ∀ v ∈ C, rmat h w *ᵥ v = v := by
    rintro _ ⟨g, hg, rfl⟩ v hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [rmat_mul, rmat_mul, hx1, hx1', Matrix.one_mul, Matrix.mul_one]
    exact hHC g hg v hv
  have htriv := le_avecCvalSub_of_perfect h hH₂perf hH₂a hH₂C
  obtain ⟨U, hUS, hUC⟩ := exists_su_std h hε S C hS hC hSC fun s hs c hc =>
    hform_commSub_fixSub h hs hc
  set g₁ : stabE (ε := ε) h := ⟨blkZHom h U, blkZHom_mem_stabE h U⟩ with hg₁
  have hg₁a := avec_blkZHom h U
  have hg₁c := cval_blkZHom h U
  have hg₁ia : avec h g₁⁻¹ = 0 := by rw [avec_inv, hg₁a, mulVec_zero, neg_zero]
  have hg₁ic : cval h g₁⁻¹ = 0 := by
    have := cval_mul_of_avec h g₁ hg₁ia
    rw [mul_inv_cancel, hg₁c, zero_add] at this
    rw [← this]
    simp [cval, smat]
  refine ⟨x₀ * g₁, fun g hg => ?_⟩
  have hw : x₀⁻¹ * g * x₀ ∈ H₂ := ⟨g, hg, by simp⟩
  obtain ⟨hwa, hwc⟩ := htriv hw
  rw [show (x₀ * g₁)⁻¹ * g * (x₀ * g₁) = g₁⁻¹ * (x₀⁻¹ * g * x₀) * g₁ by group]
  refine mem_stdW_of h ?_ ?_ fun j hj => ?_
  · rw [avec_mul, avec_mul, hwa, hg₁a, mulVec_zero, mulVec_zero, add_zero, add_zero, hg₁ia]
  · rw [cval_mul_of_avec h _ hg₁a, cval_mul_of_avec h _ hwa, hwc, hg₁c, hg₁ic, add_zero,
      add_zero]
  · rw [rmat_mul, rmat_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    have hgj : rmat h g₁ *ᵥ Pi.single j 1 = ((U : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *ᵥ
        Pi.single j 1 := by
      rw [rmat, coe_zBlockHom]
      congr 1
    rw [hgj, hH₂C _ hw _ (hUC j hj), ← hgj, mulVec_mulVec, rmat_inv_mul, one_mulVec]

end CFSG.ComponentClassification.RankTwoClassical.URigid
