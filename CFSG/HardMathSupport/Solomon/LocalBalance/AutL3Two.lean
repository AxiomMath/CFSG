module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATCyc
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem preimage_zpowers_comm (t : Y ⧸ Subgroup.center Y) :
    ∀ a b : ↥((Subgroup.zpowers t).comap (QuotientGroup.mk' (Subgroup.center Y))),
      a * b = b * a := by
  intro a b
  obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective t
  have key : ∀ h : ↥((Subgroup.zpowers (t' : Y ⧸ Subgroup.center Y)).comap
      (QuotientGroup.mk' (Subgroup.center Y))), ∃ (k : ℤ) (z : Y), z ∈ Subgroup.center Y ∧
      (h : Y) = t' ^ k * z := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h.2
    refine ⟨k, (t' ^ k)⁻¹ * h, ?_, by group⟩
    have : ((t' ^ k : Y) : Y ⧸ Subgroup.center Y) = (h : Y ⧸ Subgroup.center Y) := by
      rw [QuotientGroup.mk_zpow]; exact hk
    rw [QuotientGroup.eq] at this
    exact this
  obtain ⟨k₁, z₁, hz₁, h₁⟩ := key a
  obtain ⟨k₂, z₂, hz₂, h₂⟩ := key b
  apply Subtype.ext
  show (a : Y) * b = b * a
  rw [h₁, h₂]
  have c1 : z₁ * (t' ^ k₂) = t' ^ k₂ * z₁ := (Subgroup.mem_center_iff.1 hz₁ _).symm
  have c2 : z₂ * (t' ^ k₁) = t' ^ k₁ * z₂ := (Subgroup.mem_center_iff.1 hz₂ _).symm
  have c3 : z₁ * z₂ = z₂ * z₁ := (Subgroup.mem_center_iff.1 hz₁ _).symm
  have c4 : t' ^ k₁ * t' ^ k₂ = t' ^ k₂ * t' ^ k₁ := by
    rw [← zpow_add, ← zpow_add, add_comm]
  calc t' ^ k₁ * z₁ * (t' ^ k₂ * z₂) = t' ^ k₁ * (z₁ * t' ^ k₂) * z₂ := by group
    _ = t' ^ k₁ * (t' ^ k₂ * z₁) * z₂ := by rw [c1]
    _ = (t' ^ k₁ * t' ^ k₂) * (z₁ * z₂) := by group
    _ = (t' ^ k₂ * t' ^ k₁) * (z₂ * z₁) := by rw [c4, c3]
    _ = t' ^ k₂ * (t' ^ k₁ * z₂) * z₁ := by group
    _ = t' ^ k₂ * (z₂ * t' ^ k₁) * z₁ := by rw [c2]
    _ = t' ^ k₂ * z₂ * (t' ^ k₁ * z₁) := by group


theorem exists_invariant_two_group (Ab : Subgroup (MulAut Y)) (t : Y ⧸ Subgroup.center Y)
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (hfix : ∀ α ∈ Ab, centerDescend Y α t = t) :
    ∃ T : Subgroup Y, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ α ∈ Ab, T.map α.toMonoidHom = T := by
  set H := (Subgroup.zpowers t).comap (QuotientGroup.mk' (Subgroup.center Y)) with hH
  have hcomm := preimage_zpowers_comm t
  have hcom : ∀ a b : Y, a ∈ H → b ∈ H → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  let T : Subgroup Y :=
    { carrier := {h | h ∈ H ∧ ∃ k : ℕ, h ^ (2 ^ k) = 1}
      mul_mem' := by
        rintro a b ⟨haH, k₁, hk₁⟩ ⟨hbH, k₂, hk₂⟩
        refine ⟨H.mul_mem haH hbH, k₁ + k₂, ?_⟩
        have hc : Commute a b := hcom a b haH hbH
        rw [hc.mul_pow]
        have h1 : a ^ (2 ^ (k₁ + k₂)) = 1 :=
          orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hk₁).trans
            (pow_dvd_pow 2 (Nat.le_add_right _ _)))
        have h2 : b ^ (2 ^ (k₁ + k₂)) = 1 :=
          orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hk₂).trans
            (pow_dvd_pow 2 (Nat.le_add_left _ _)))
        rw [h1, h2, one_mul]
      one_mem' := ⟨H.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨haH, k, hk⟩
        exact ⟨H.inv_mem haH, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hTH : ∀ h ∈ T, h ∈ H := fun h hh => hh.1
  have hpres : ∀ α ∈ Ab, ∀ y ∈ H, α y ∈ H := by
    intro α hα y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : centerDescend Y α ((y : Y ⧸ Subgroup.center Y)) = ((α y : Y) : Y ⧸ Subgroup.center Y) :=
      centerDescend_mk Y α y
    show ((α y : Y) : Y ⧸ Subgroup.center Y) ∈ Subgroup.zpowers t
    rw [← h1, show ((y : Y) : Y ⧸ Subgroup.center Y) = t ^ k from hk.symm, map_zpow,
      hfix α hα]
    exact Subgroup.zpow_mem_zpowers t k
  refine ⟨T, ?_, ?_, ?_⟩
  ·
    obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective t
    have ht'H : t' ∈ H := by
      show ((t' : Y) : Y ⧸ Subgroup.center Y) ∈ Subgroup.zpowers _
      exact Subgroup.mem_zpowers _
    have hev : 2 ∣ orderOf t' := by
      have h1 : orderOf ((t' : Y) : Y ⧸ Subgroup.center Y) = 2 :=
        orderOf_eq_prime ht2 ht1
      rw [← h1]
      exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center Y)) t'
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t').ne'
    have ha : a ≠ 0 := by
      rintro rfl
      rw [hn, pow_zero, one_mul] at hev
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hev)
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨t' ^ m, ?_⟩, ?_⟩
    · refine ⟨H.pow_mem ht'H m, a, ?_⟩
      rw [← pow_mul, mul_comm, ← hn]
      exact pow_orderOf_eq_one t'
    · intro h1
      have h2 : t' ^ m = 1 := congrArg Subtype.val h1
      have h3 : orderOf t' ∣ m := orderOf_dvd_of_pow_eq_one h2
      have h4 : 2 ∣ m := hev.trans h3
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h4)
  · intro g
    obtain ⟨-, k, hk⟩ := g.2
    exact ⟨k, Subtype.ext hk⟩
  · intro α hα
    have hle : ∀ β ∈ Ab, T.map β.toMonoidHom ≤ T := by
      intro β hβ
      rintro _ ⟨h, ⟨hhH, k, hk⟩, rfl⟩
      refine ⟨hpres β hβ h hhH, k, ?_⟩
      show (β.toMonoidHom h) ^ (2 ^ k) = 1
      rw [← map_pow, hk, map_one]
    refine le_antisymm (hle α hα) ?_
    intro h hh
    refine ⟨α⁻¹ h, hle α⁻¹ (Ab.inv_mem hα) ⟨h, hh, rfl⟩ , ?_⟩
    simp

end Lift

section Invol

variable {K : Type} [Field K]

@[expose] def wMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem wMat_mul_self : (wMat : Matrix (Fin 3) (Fin 3) K) * wMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem wMat_det : (wMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [wMat, Matrix.det_fin_three]

theorem wMat_map (σ : K →+* K) : (wMat : Matrix (Fin 3) (Fin 3) K).map σ = wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

theorem wMat_transpose : Matrix.transpose (wMat : Matrix (Fin 3) (Fin 3) K) = wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

theorem wMat_not_scalar (c : K) : (wMat : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [wMat, Matrix.scalar_apply, Matrix.diagonal_apply] at this

@[expose] def wSL : Matrix.SpecialLinearGroup (Fin 3) K := ⟨wMat, wMat_det⟩

theorem wSL_sq : (wSL : Matrix.SpecialLinearGroup (Fin 3) K) * wSL = 1 := by
  apply Subtype.ext
  show wMat * wMat = (1 : Matrix (Fin 3) (Fin 3) K)
  exact wMat_mul_self

theorem proj_wSL_sq : (proj 3 K (wSL : Matrix.SpecialLinearGroup (Fin 3) K)) ^ 2 = 1 := by
  rw [sq, ← map_mul, wSL_sq, map_one]

theorem proj_wSL_ne_one : proj 3 K (wSL : Matrix.SpecialLinearGroup (Fin 3) K) ≠ 1 := by
  rw [Ne, proj_eq_one_iff]
  rintro ⟨c, -, hc⟩
  exact wMat_not_scalar (c : K) hc

theorem fieldAut_proj_wSL (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K (wSL : Matrix.SpecialLinearGroup (Fin 3) K)) =
      proj 3 K wSL := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  exact wMat_map σ.toRingHom

end Invol

section InvolU

variable {p f : ℕ} {K : Type} [Field K]

theorem wGL_mem_unitarySU (h : UnitaryFieldData p f K) :
    (Matrix.SpecialLinearGroup.toGL (wSL : Matrix.SpecialLinearGroup (Fin 3) K) : GL (Fin 3) K) ∈
      unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  have hm : ((Matrix.SpecialLinearGroup.toGL (wSL : Matrix.SpecialLinearGroup (Fin 3) K) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = wMat := rfl
  rw [hm]
  refine ⟨wMat_det, ?_⟩
  rw [wMat_map h.bar]
  have := wMat_transpose (K := K)
  rw [this]
  exact wMat_mul_self

@[expose] noncomputable def tU (h : UnitaryFieldData p f K) : unitaryPSU h 3 :=
  unitaryProj h 3 ⟨_, wGL_mem_unitarySU h⟩

theorem tU_sq (h : UnitaryFieldData p f K) : tU h ^ 2 = 1 := by
  rw [sq, tU, ← map_mul]
  have : (⟨_, wGL_mem_unitarySU h⟩ : ↥(unitarySU p f K 3)) * ⟨_, wGL_mem_unitarySU h⟩ = 1 := by
    apply Subtype.ext
    show Matrix.SpecialLinearGroup.toGL (wSL : Matrix.SpecialLinearGroup (Fin 3) K) *
      Matrix.SpecialLinearGroup.toGL wSL = 1
    rw [← map_mul, wSL_sq, map_one]
  rw [this, map_one]

theorem tU_ne_one (h : UnitaryFieldData p f K) : tU h ≠ 1 := by
  rw [tU]
  change (QuotientGroup.mk _ : unitaryPSU h 3) ≠ 1
  rw [Ne, QuotientGroup.eq_one_iff]
  rintro ⟨c, -, -, hzc⟩
  have h1 := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) hzc
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h1
  exact wMat_not_scalar (c : K) h1

theorem psuField_tU (h : UnitaryFieldData p f K) (σ : K ≃+* K) : psuField h σ (tU h) = tU h := by
  rw [tU]
  change psuField h σ (QuotientGroup.mk _) = _
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  apply Units.ext
  rw [UnitaryHigher.coe_glAut]
  exact wMat_map σ.toRingHom

end InvolU

section Fixed

variable {Y : Type*} [Group Y]

theorem exists_fixed_involution {α : MulAut Y}
    (hα : IsFieldAutPSL3 α ∨ IsFieldAutPSU3 α) :
    ∃ t : Y ⧸ Subgroup.center Y, t ≠ 1 ∧ t ^ 2 = 1 ∧ centerDescend Y α t = t := by
  rcases hα with hL | hU
  · obtain ⟨F, _, _, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    refine ⟨e.symm (γ (proj 3 F (wSL : Matrix.SpecialLinearGroup (Fin 3) F))), ?_, ?_, ?_⟩
    · intro h1
      apply proj_wSL_ne_one (K := F)
      apply γ.injective
      rw [map_one]
      have := congrArg e h1
      simpa using this
    · rw [← map_pow e.symm, ← map_pow γ, proj_wSL_sq, map_one, map_one]
    · apply e.injective
      have h1 := congrArg (fun τ : MulAut (projectiveSL 3 F) =>
        τ (γ (proj 3 F (wSL : Matrix.SpecialLinearGroup (Fin 3) F)))) he
      simp only [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_apply,
        MulEquiv.symm_apply_apply] at h1
      rw [fieldAut_proj_wSL] at h1
      simpa using h1
  · obtain ⟨p, f, F, _, hF, e, σ, γ, -, he⟩ := fieldAutPSU3_data hU
    refine ⟨e.symm (γ (tU hF)), ?_, ?_, ?_⟩
    · intro h1
      apply tU_ne_one hF
      apply γ.injective
      rw [map_one]
      have := congrArg e h1
      simpa using this
    · rw [← map_pow e.symm, ← map_pow γ, tU_sq, map_one, map_one]
    · apply e.injective
      have h1 := congrArg (fun τ : MulAut (unitaryPSU hF 3) => τ (γ (tU hF))) he
      simp only [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_apply,
        MulEquiv.symm_apply_apply] at h1
      rw [psuField_tU] at h1
      simpa using h1

end Fixed

section Cyclic

theorem orderOf_map_eq_three_pow {Y N : Type*} [Group Y] [Group N] (Φ : Y →* N)
    (Ab : Subgroup Y) (hAb : IsPGroup 3 Ab) {α : Y} (hα : α ∈ Ab) :
    ∃ k : ℕ, orderOf (Φ α) = 3 ^ k := by
  obtain ⟨n, hn⟩ := hAb ⟨α, hα⟩
  have h1 : α ^ 3 ^ n = 1 := congrArg Subtype.val hn
  have h2 : orderOf (Φ α) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h1, map_one])
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  exact ⟨k, hk⟩

theorem descend_eq_one_of_inndiag_field {Y M : Type*} [Group Y] [Group M]
    (e : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M) (hP : GoodPinned P) {α : MulAut Y}
    (h : MulAut.congr e (centerDescend Y α) ∈ P.inndiag) (hf : IsFieldAutThree α) :
    centerDescend Y α = 1 :=
  descend_eq_one_of_inndiag_field_model e P hP h hf

theorem isCyclic_descend_of_model {Y M C : Type} [Group Y] [Finite Y] [Group M] [Finite M]
    [Group C] [IsCyclic C] (e : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M)
    (hP : GoodPinned P) (fld : C →* MulAut M)
    (h3 : ∀ (β : MulAut M) (k : ℕ), orderOf β = 3 ^ k → ∃ d ∈ P.inndiag, ∃ c : C, β = d * fld c)
    (Ab : Subgroup (MulAut Y)) (hAb : IsPGroup 3 Ab)
    (hker : ∀ α ∈ Ab, MulAut.congr e (centerDescend Y α) ∈ P.inndiag → centerDescend Y α = 1) :
    IsCyclic ↥(Ab.map (centerDescend Y)) :=
  isCyclic_descend_of_members e P hP fld Ab (fun α hα => by
    obtain ⟨k, hk⟩ := orderOf_map_eq_three_pow
      ((MulAut.congr e).toMonoidHom.comp (centerDescend Y)) Ab hAb hα
    exact h3 _ k hk) hker

end Cyclic

section Final

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem inputFieldAutTwo_holds : Lemma55Ns.InputFieldAutTwo := by
  intro Y _ _ Ab hAb hf ⟨α₀, hα₀, hne⟩
  have hα₀' : IsFieldAutPSL3 α₀ ∨ IsFieldAutPSU3 α₀ := by
    rcases hf α₀ hα₀ with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  by_cases hall : ∀ α ∈ Ab, centerDescend Y α = 1
  · obtain ⟨t, ht1, ht2, -⟩ := exists_fixed_involution hα₀'
    exact exists_invariant_two_group Ab t ht1 ht2 (fun α hα => by rw [hall α hα]; rfl)
  · push Not at hall
    obtain ⟨αs, hαs, hαsne⟩ := hall
    have hcyc : IsCyclic ↥(Ab.map (centerDescend Y)) := by
      rcases hf αs hαs with h | hL | hU
      · exact absurd (by rw [h, map_one]) hαsne
      · obtain ⟨F, _, hfin, e, σ, γ, he⟩ := fieldAutPSL3_data hL
        have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
        exact isCyclic_descend_of_model e (stdPinnedPSL 3 F) (goodPinned_psl F) (fieldAut 3 F)
          (fun β k hk => by
            obtain ⟨A, σ', hA⟩ := mem_semilinearAutGroup_iff.1
              (CFSG.Quasithin.A318P.mem_semilinear_of_orderOf_three_pow hk)
            exact ⟨conjAut 3 F A, by
              rw [stdPinnedPSL_inndiag]; exact conjAut_mem_linearAutGroup A, σ', hA⟩)
          Ab hAb (fun α hα hin => descend_eq_one_of_inndiag_field e _ (goodPinned_psl F) hin
            (hf α hα))
      · obtain ⟨p, f, F, _, hF, e, σ, γ, hodd, he⟩ := fieldAutPSU3_data hU
        have hfin := hF.finite
        have hq : 2 < p ^ f := by
          by_contra hq
          have h2 : p ^ f = 2 := pow_eq_two_of_not_two_lt hF hq
          have hcard : Nat.card F = 2 ^ 2 := by rw [hF.card, pow_mul', h2]
          have hσ := eq_one_of_odd_orderOf_card_four hcard hodd
          apply hαsne
          rw [hσ, map_one, mul_one, mul_inv_cancel] at he
          exact (MulAut.congr e).injective (by rw [he, map_one])
        have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
        exact isCyclic_descend_of_model e (stdPinnedPSU3 hF) (goodPinned_psu hF hq) (psuField hF)
          (fun β k hk => by
            obtain ⟨A, σ', hA⟩ := exists_psuConj_mul_psuField hq β
            exact ⟨psuConj hF A, ⟨A, rfl⟩, σ', hA⟩)
          Ab hAb (fun α hα hin => descend_eq_one_of_inndiag_field e _ (goodPinned_psu hF hq) hin
            (hf α hα))
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Ab.map (centerDescend Y)))
    obtain ⟨α₁, hα₁, hgα₁⟩ := g.2
    have hg1 : g ≠ 1 := by
      intro h1
      have : centerDescend Y αs = 1 := by
        have := hg ⟨centerDescend Y αs, αs, hαs, rfl⟩
        rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      exact hαsne this
    have hα₁data : IsFieldAutPSL3 α₁ ∨ IsFieldAutPSU3 α₁ := by
      rcases hf α₁ hα₁ with h | h | h
      · exfalso
        apply hg1
        apply Subtype.ext
        rw [← hgα₁, h, map_one]
        rfl
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨t, ht1, ht2, htfix⟩ := exists_fixed_involution hα₁data
    refine exists_invariant_two_group Ab t ht1 ht2 (fun α hα => ?_)
    have hmem : (⟨centerDescend Y α, α, hα, rfl⟩ : ↥(Ab.map (centerDescend Y))) ∈
        Subgroup.zpowers g := hg _
    have hstab : Subgroup.zpowers g ≤ (MulAction.stabilizer (MulAut (Y ⧸ Subgroup.center Y)) t).comap
        (Ab.map (centerDescend Y)).subtype := by
      rw [Subgroup.zpowers_le]
      show (g : MulAut (Y ⧸ Subgroup.center Y)) ∈ MulAction.stabilizer _ t
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← hgα₁]
      exact htfix
    have := hstab hmem
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at this
    simpa [MulAut.smul_def] using this

end Final

end CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
