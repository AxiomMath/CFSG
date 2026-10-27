module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow

public section

namespace CFSG.OddStandard.Seitz77.Levi

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification
  CFSG.ComponentClassification.PSL3Four CFSG.OddStandard.Seitz77.L34

theorem F4_two : (2 : F4) = 0 := two_eq_zero_of_card natCard_F4

@[expose] def eLow32 (γ : F4) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, γ, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def eLow21 (γ : F4) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![1, 0, 0; γ, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_eLow32 (γ : F4) :
    (eLow32 γ : Matrix (Fin 3) (Fin 3) F4) = !![1, 0, 0; 0, 1, 0; 0, γ, 1] := rfl

theorem coe_eLow21 (γ : F4) :
    (eLow21 γ : Matrix (Fin 3) (Fin 3) F4) = !![1, 0, 0; γ, 1, 0; 0, 0, 1] := rfl

theorem eLow32_mul_unipU (γ a c : F4) :
    eLow32 γ * unipU F4 a 0 c = unipU F4 (a + γ * c) 0 c * eLow32 γ := by
  have h2 := F4_two
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_eLow32, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination (-(γ * c)) * h2

theorem eLow21_mul_unipU (γ b c : F4) :
    eLow21 γ * unipU F4 0 b c = unipU F4 0 (b + γ * c) c * eLow21 γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_eLow21, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three]
  ring


variable {A : Type*} [Group A] [Finite A]

theorem exists_chart_of_hom_proj {q : A →* LinearFlag.projectiveSL 3 F4}
    (hq : Function.Surjective q) (hker : q.ker ≤ center A) (hodd : Odd (Nat.card q.ker))
    (hP : Nat.card (LinearFlag.projectiveSL 3 F4) = 20160) (V : Sylow 2 A) :
    ∃ (ι : ↥(unipAll F4) →* A) (h g : A), Function.Injective ι ∧ ι.range = (V : Subgroup A) ∧
      h ∈ normalizer (V : Set A) ∧ Odd (orderOf h) ∧
      (∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c))) ∧
      ∀ u : ↥(unipAll F4), q (ι u) =
        q g * LinearFlag.proj 3 F4 (u : SpecialLinearGroup (Fin 3) F4) * (q g)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (LinearFlag.projectiveSL 3 F4) := Finite.of_surjective q hq
  have hUcard : Nat.card (projUnip F4) = 64 := by
    rw [card_projUnip, natCard_F4]
  have hU2 : IsPGroup 2 (projUnip F4) := IsPGroup.of_card (n := 6) (by rw [hUcard]; norm_num)
  have hUidx : ¬ 2 ∣ (projUnip F4).index := by
    have h := Subgroup.card_mul_index (projUnip F4)
    rw [hUcard, hP] at h
    have : (projUnip F4).index = 315 := by omega
    rw [this]
    norm_num
  let U₂ : Sylow 2 (LinearFlag.projectiveSL 3 F4) := hU2.toSylow hUidx
  obtain ⟨V₀, hV₀⟩ := Sylow.mapSurjective_surjective hq 2 U₂
  have hV₀map : (V₀ : Subgroup A).map q = projUnip F4 := by
    have := congrArg (fun P : Sylow 2 (LinearFlag.projectiveSL 3 F4) => P.toSubgroup) hV₀
    simpa [U₂] using this
  have hkodd : ∀ k : A, q k = 1 → Odd (orderOf k) := fun k hk => by
    have hk' : k ∈ q.ker := hk
    have := orderOf_dvd_natCard (⟨k, hk'⟩ : q.ker)
    rw [Subgroup.orderOf_mk] at this
    exact hodd.of_dvd_nat this
  have h2elt : ∀ x ∈ (V₀ : Subgroup A), ∃ m, orderOf x = 2 ^ m := fun x hx => by
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp V₀.isPGroup' ⟨x, hx⟩
    exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm⟩
  have hinj₀ : Function.Injective (q.comp (V₀ : Subgroup A).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    obtain ⟨m, hm⟩ := h2elt x x.2
    have := eq_one_of_two_power_of_odd (y := (x : A)) (v := 1) (k := (x : A)) (one_mul _).symm
      ⟨0, by simp⟩ ⟨m, hm⟩ (Commute.one_left _) (hkodd _ hx)
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  let ρ : ↥(unipAll F4) →* LinearFlag.projectiveSL 3 F4 :=
    (LinearFlag.proj 3 F4).comp (unipAll F4).subtype
  have hρinj : Function.Injective ρ := by
    intro u u' h
    obtain ⟨a, b, c, rfl⟩ := exists_ofCoords u
    obtain ⟨a', b', c', rfl⟩ := exists_ofCoords u'
    exact ofCoords_inj.2 (unipU_eq_of_proj_eq h)
  have hrange : (q.comp (V₀ : Subgroup A).subtype).range = ρ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hV₀map]
    simp only [ρ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_of_range_eq hinj₀ hρinj hrange
  let ι₀ : ↥(unipAll F4) →* A := (V₀ : Subgroup A).subtype.comp φ₀.symm.toMonoidHom
  have hι₀inj : Function.Injective ι₀ :=
    (V₀ : Subgroup A).subtype_injective.comp φ₀.symm.injective
  have hι₀range : ι₀.range = (V₀ : Subgroup A) := by
    rw [MonoidHom.range_eq_map]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact (φ₀.symm u).2
    · intro hx
      exact ⟨φ₀ ⟨x, hx⟩, trivial, by simp [ι₀]⟩
  have hmemV₀ : ∀ u, ι₀ u ∈ (V₀ : Subgroup A) := fun u => by
    rw [← hι₀range]
    exact ⟨u, rfl⟩
  have hqι₀ : ∀ u, q (ι₀ u) = ρ u := fun u => by
    have := hφ₀ (φ₀.symm u)
    simpa [ι₀] using this.symm
  obtain ⟨h₀, hh₀⟩ := hq (LinearFlag.proj 3 F4 torusDelta)
  have hconj : ∀ a b c : F4, h₀ * ι₀ (ofCoords a b c) * h₀⁻¹ =
      ι₀ (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
    intro a b c
    set u := ofCoords a b c with hu
    set u' := ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c) with hu'
    have hq1 : q (h₀ * ι₀ u * h₀⁻¹) = q (ι₀ u') := by
      rw [map_mul, map_mul, map_inv, hh₀, hqι₀, hqι₀, mul_inv_eq_iff_eq_mul]
      show LinearFlag.proj 3 F4 torusDelta * LinearFlag.proj 3 F4 (unipU F4 a b c) =
        LinearFlag.proj 3 F4 (unipU F4 (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) *
          LinearFlag.proj 3 F4 torusDelta
      rw [← map_mul, ← map_mul, torusDelta_mul_unipU]
    set k := (ι₀ u')⁻¹ * (h₀ * ι₀ u * h₀⁻¹) with hk
    have hkq : q k = 1 := by rw [hk, map_mul, map_inv, hq1, inv_mul_cancel]
    have hkc : k ∈ center A := hker hkq
    have hyk : h₀ * ι₀ u * h₀⁻¹ = ι₀ u' * k := by rw [hk]; group
    have hv2 : ∃ n, orderOf (ι₀ u') = 2 ^ n := h2elt _ (hmemV₀ u')
    have hy2 : ∃ m, orderOf (h₀ * ι₀ u * h₀⁻¹) = 2 ^ m := by
      obtain ⟨m, hm⟩ := h2elt _ (hmemV₀ u)
      exact ⟨m, by rw [← (SemiconjBy.conj_mk h₀ (ι₀ u)).orderOf_eq]; exact hm⟩
    have := eq_one_of_two_power_of_odd hyk hv2 hy2 (Subgroup.mem_center_iff.mp hkc (ι₀ u'))
      (hkodd k hkq)
    rw [hyk, this, mul_one]
  have hodd₀ : Odd (orderOf h₀) := by
    have h3 : q (h₀ ^ 3) = 1 := by
      rw [map_pow, hh₀, ← map_pow, torusDelta_pow_three, map_one]
    have hdvd : orderOf h₀ ∣ 3 * orderOf (h₀ ^ 3) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact (Odd.mul (by decide) (hkodd _ h3)).of_dvd_nat hdvd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A V₀ V
  have hVeq : (V : Subgroup A) = (V₀ : Subgroup A).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hcompat : ∀ a b c : F4, g * h₀ * g⁻¹ * ((MulAut.conj g).toMonoidHom.comp ι₀
      (ofCoords a b c)) * (g * h₀ * g⁻¹)⁻¹ = (MulAut.conj g).toMonoidHom.comp ι₀
      (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c)) := by
    intro a b c
    have := congrArg (fun x => g * x * g⁻¹) (hconj a b c)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this ⊢
    rw [← this]
    group
  refine ⟨(MulAut.conj g).toMonoidHom.comp ι₀, g * h₀ * g⁻¹, g,
    (MulAut.conj g).injective.comp hι₀inj, ?_, ?_, ?_, hcompat, fun u => ?_⟩
  · rw [MonoidHom.range_comp, hι₀range, hVeq]
  · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ ((MulAut.conj g).toMonoidHom.comp ι₀).range := by
      rw [MonoidHom.range_comp, hι₀range, ← hVeq]
      exact hn
    obtain ⟨u, rfl⟩ := hn'
    obtain ⟨a, b, c, rfl⟩ := exists_ofCoords u
    rw [hcompat]
    have : ((MulAut.conj g).toMonoidHom.comp ι₀) (ofCoords (F4.ω * F4.ω * a)
        (F4.ω * F4.ω * b) (F4.ω * c)) ∈ ((MulAut.conj g).toMonoidHom.comp ι₀).range := ⟨_, rfl⟩
    rw [MonoidHom.range_comp, hι₀range, ← hVeq] at this
    exact this
  · rw [← (SemiconjBy.conj_mk g h₀).orderOf_eq]
    exact hodd₀
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hqι₀]
    rfl


omit [Finite A] in
theorem eq_of_map_eq_of_two_power {B : Type*} [Group B] {q : A →* B} (hker : q.ker ≤ center A)
    (hkodd : ∀ k : A, q k = 1 → Odd (orderOf k)) {x y : A} (hx : ∃ n, orderOf x = 2 ^ n)
    (hy : ∃ n, orderOf y = 2 ^ n) (h : q x = q y) : x = y := by
  set k := y⁻¹ * x with hk
  have hkq : q k = 1 := by rw [hk, map_mul, map_inv, h, inv_mul_cancel]
  have hkc : k ∈ center A := hker hkq
  have hxy : x = y * k := by rw [hk]; group
  have := eq_one_of_two_power_of_odd hxy hy hx (Subgroup.mem_center_iff.mp hkc y)
    (hkodd k hkq)
  rw [hxy, this, mul_one]

omit [Finite A] in
theorem exists_lift_conj {q : A →* LinearFlag.projectiveSL 3 F4} (hq : Function.Surjective q)
    (hker : q.ker ≤ center A) (hodd : Odd (Nat.card q.ker)) {V : Subgroup A} (hV : IsPGroup 2 V)
    {ι : ↥(unipAll F4) →* A} (hι : ∀ u, ι u ∈ V) {g : A}
    (hg : ∀ u : ↥(unipAll F4), q (ι u) =
      q g * LinearFlag.proj 3 F4 (u : SpecialLinearGroup (Fin 3) F4) * (q g)⁻¹)
    (m : SpecialLinearGroup (Fin 3) F4) :
    ∃ l : A, ∀ u u' : ↥(unipAll F4),
      m * (u : SpecialLinearGroup (Fin 3) F4) = (u' : SpecialLinearGroup (Fin 3) F4) * m →
        l * ι u * l⁻¹ = ι u' := by
  obtain ⟨a₀, ha₀⟩ := hq (LinearFlag.proj 3 F4 m)
  refine ⟨g * a₀ * g⁻¹, fun u u' hmu => ?_⟩
  have hkodd : ∀ k : A, q k = 1 → Odd (orderOf k) := fun k hk => by
    have hk' : k ∈ q.ker := hk
    have := orderOf_dvd_natCard (⟨k, hk'⟩ : q.ker)
    rw [Subgroup.orderOf_mk] at this
    exact hodd.of_dvd_nat this
  have h2elt : ∀ x ∈ V, ∃ m, orderOf x = 2 ^ m := fun x hx => by
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hV ⟨x, hx⟩
    exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm⟩
  have hconj : LinearFlag.proj 3 F4 m * LinearFlag.proj 3 F4 (u : SpecialLinearGroup (Fin 3) F4) *
      (LinearFlag.proj 3 F4 m)⁻¹ = LinearFlag.proj 3 F4 (u' : SpecialLinearGroup (Fin 3) F4) := by
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, hmu]
  have hq1 : q (g * a₀ * g⁻¹ * ι u * (g * a₀ * g⁻¹)⁻¹) = q (ι u') := by
    rw [hg u', ← hconj]
    simp only [map_mul, map_inv, hg u, ha₀]
    group
  refine eq_of_map_eq_of_two_power hker hkodd ?_ (h2elt _ (hι u')) hq1
  obtain ⟨m, hm⟩ := h2elt _ (hι u)
  exact ⟨m, by rw [← (SemiconjBy.conj_mk (g * a₀ * g⁻¹) (ι u)).orderOf_eq]; exact hm⟩

theorem exists_chart_lifts_of_hom {q : A →* LinearFlag.projectiveSL 3 F4}
    (hq : Function.Surjective q) (hker : q.ker ≤ center A) (hodd : Odd (Nat.card q.ker))
    (hP : Nat.card (LinearFlag.projectiveSL 3 F4) = 20160) (V : Sylow 2 A) :
    ∃ (ι : ↥(unipAll F4) →* A) (h : A), Function.Injective ι ∧ ι.range = (V : Subgroup A) ∧
      h ∈ normalizer (V : Set A) ∧ Odd (orderOf h) ∧
      (∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c))) ∧
      (∀ γ : F4, ∃ l : A, ∀ a c : F4, l * ι (ofCoords a 0 c) * l⁻¹ =
        ι (ofCoords (a + γ * c) 0 c)) ∧
      (∀ γ : F4, ∃ l : A, ∀ b c : F4, l * ι (ofCoords 0 b c) * l⁻¹ =
        ι (ofCoords 0 (b + γ * c) c)) := by
  obtain ⟨ι, h, g, hι, hr, hn, ho, hact, hg⟩ := exists_chart_of_hom_proj hq hker hodd hP V
  have hmem : ∀ u, ι u ∈ (V : Subgroup A) := fun u => by
    rw [← hr]
    exact ⟨u, rfl⟩
  refine ⟨ι, h, hι, hr, hn, ho, hact, fun γ => ?_, fun γ => ?_⟩
  · obtain ⟨l, hl⟩ := exists_lift_conj hq hker hodd V.isPGroup' hmem hg (eLow32 γ)
    exact ⟨l, fun a c => hl _ _ (eLow32_mul_unipU γ a c)⟩
  · obtain ⟨l, hl⟩ := exists_lift_conj hq hker hodd V.isPGroup' hmem hg (eLow21 γ)
    exact ⟨l, fun b c => hl _ _ (eLow21_mul_unipU γ b c)⟩

theorem exists_chart_lifts (hZ : Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* PSL3Four.S) (V : Sylow 2 A) :
    ∃ (ι : ↥(unipAll F4) →* A) (h : A), Function.Injective ι ∧ ι.range = (V : Subgroup A) ∧
      h ∈ normalizer (V : Set A) ∧ Odd (orderOf h) ∧
      (∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c))) ∧
      (∀ γ : F4, ∃ l : A, ∀ a c : F4, l * ι (ofCoords a 0 c) * l⁻¹ =
        ι (ofCoords (a + γ * c) 0 c)) ∧
      (∀ γ : F4, ∃ l : A, ∀ b c : F4, l * ι (ofCoords 0 b c) * l⁻¹ =
        ι (ofCoords 0 (b + γ * c) c)) := by
  let q : A →* LinearFlag.projectiveSL 3 F4 :=
    theta.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center A)))
  have hq : Function.Surjective q :=
    theta.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : q.ker = center A := by
    ext x
    simp [q]
  have hP : Nat.card (LinearFlag.projectiveSL 3 F4) = 20160 := by
    rw [Nat.card_congr theta.toEquiv, card_S]
  exact exists_chart_lifts_of_hom hq hker.le (by rw [hker]; exact hZ) hP V

theorem exists_chart_lifts_of_isSylowOf {G : Type*} [Group G]
    [Finite G] {A V : Subgroup G} (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* PSL3Four.S) (hV : CFSG.ABGLocalTools.IsSylowOf 2 V A) :
    ∃ (ι : ↥(unipAll F4) →* G) (h : G), Function.Injective ι ∧ ι.range = V ∧ h ∈ A ∧
      Odd (orderOf h) ∧
      (∀ a b c : F4, h * ι (ofCoords a b c) * h⁻¹ =
        ι (ofCoords (F4.ω * F4.ω * a) (F4.ω * F4.ω * b) (F4.ω * c))) ∧
      (∀ γ : F4, ∃ l ∈ A, ∀ a c : F4, l * ι (ofCoords a 0 c) * l⁻¹ =
        ι (ofCoords (a + γ * c) 0 c)) ∧
      (∀ γ : F4, ∃ l ∈ A, ∀ b c : F4, l * ι (ofCoords 0 b c) * l⁻¹ =
        ι (ofCoords 0 (b + γ * c) c)) := by
  obtain ⟨Q, hQ⟩ := hV
  obtain ⟨ι, h, hι, hr, -, hodd, hact, hl1, hl2⟩ := exists_chart_lifts hZ e Q
  refine ⟨A.subtype.comp ι, (h : G), A.subtype_injective.comp hι, ?_, h.2, ?_, fun a b c => ?_,
    fun γ => ?_, fun γ => ?_⟩
  · rw [MonoidHom.range_comp, hr, ← hQ]
  · rw [Subgroup.orderOf_coe]
    exact hodd
  · have := congrArg A.subtype (hact a b c)
    simpa using this
  · obtain ⟨l, hl⟩ := hl1 γ
    refine ⟨(l : G), l.2, fun a c => ?_⟩
    have := congrArg A.subtype (hl a c)
    simpa using this
  · obtain ⟨l, hl⟩ := hl2 γ
    refine ⟨(l : G), l.2, fun b c => ?_⟩
    have := congrArg A.subtype (hl b c)
    simpa using this

end CFSG.OddStandard.Seitz77.Levi
