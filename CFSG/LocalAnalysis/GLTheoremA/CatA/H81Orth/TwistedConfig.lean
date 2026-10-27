module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Weights
public import CFSG.RankThree.PartOne.S15K.FamilyForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Module CFSG.GroupTheory.WeirSylow QuadraticMap

section Plane

variable {K : Type} [Field K] [Finite K]

theorem int_dvd_of_plane {U : Type} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {QU : QuadraticForm K U} (hQU : (polarBilin QU).Nondegenerate) (hdim : finrank K U = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : U ≃ₗ[K] U}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup QU) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    (IsPlusType QU → (p : ℤ) ∣ (Nat.card K : ℤ) - 1) ∧
      (¬ IsPlusType QU → (p : ℤ) ∣ (Nat.card K : ℤ) + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup QU)) = p :=
    orderOf_eq_prime (Subtype.ext hgp) fun h => hg1 (congrArg Subtype.val h)
  have hdvd : (p : ℤ) ∣ (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup QU) : ℤ) := by
    rw [← hord]
    exact Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard _)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2' : ¬ (p : ℤ) ∣ 2 := fun h => by
    have : p ∣ 2 := Int.natCast_dvd_natCast.mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hd : finrank K U = 2 * (0 + 1) := by rw [hdim]
  constructor
  · intro hplus
    rw [natCard_orthogonalGroup_of_type hQU hd (Or.inl ⟨rfl, hplus⟩)] at hdvd
    simp only [zero_mul, pow_zero, mul_one, zero_add, pow_one, Finset.Icc_eq_empty_of_lt
      zero_lt_one, Finset.prod_empty] at hdvd
    exact (hpZ.dvd_mul.mp hdvd).resolve_left hp2'
  · intro hnplus
    rw [natCard_orthogonalGroup_of_type hQU hd (Or.inr ⟨rfl, hnplus⟩)] at hdvd
    simp only [zero_mul, pow_zero, mul_one, zero_add, pow_one, Finset.Icc_eq_empty_of_lt
      zero_lt_one, Finset.prod_empty, sub_neg_eq_add] at hdvd
    exact (hpZ.dvd_mul.mp hdvd).resolve_left hp2'

theorem exists_singular_of_isPlusType {U : Type} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {QU : QuadraticForm K U} (hdim : finrank K U = 2)
    (h : IsPlusType QU) : ∃ u : U, u ≠ 0 ∧ QU u = 0 := by
  obtain ⟨W, hW, hWs⟩ := h
  have h1 : finrank K W = 1 := by omega
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show W ≠ ⊥ from fun hb => by rw [hb, finrank_bot] at h1; exact absurd h1 (by norm_num))
  exact ⟨w, hw0, hWs w hwW⟩

theorem eq_zero_of_not_isPlusType {U : Type} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {QU : QuadraticForm K U} (hdim : finrank K U = 2)
    (h : ¬ IsPlusType QU) {u : U} (hu : QU u = 0) : u = 0 := by
  by_contra hu0
  apply h
  refine ⟨K ∙ u, by rw [finrank_span_singleton hu0, hdim], fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [QuadraticMap.map_smul, hu, smul_zero]

end Plane

section Four

variable {K : Type} [Field K] [Finite K] {A : Type} [CommGroup A] {p : ℕ} [Finite A]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)
variable (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
variable (h2 : (2 : K) ≠ 0) (hρQ : ∀ (a : A) (v : V), Q (ρ a v) = Q v) (hp2 : p ≠ 2)

theorem polar_comp_subtype' (U : Submodule K V) (u w : U) :
    polar (Q.comp U.subtype) u w = polar Q (u : V) (w : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

@[expose] noncomputable def restrictRep (U : Submodule K V) (hU : ∀ (b : A), ∀ v ∈ U, ρ b v ∈ U)
    (a : A) : U ≃ₗ[K] U :=
  LinearEquiv.ofLinearMap ((ρ a).restrict (hU a)) ((ρ a⁻¹).restrict (hU a⁻¹))
    (LinearMap.ext fun v => Subtype.ext (by
      show ρ a (ρ a⁻¹ v) = v
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl))
    (LinearMap.ext fun v => Subtype.ext (by
      show ρ a⁻¹ (ρ a v) = v
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl))

theorem coe_restrictRep_apply (U : Submodule K V) (hU : ∀ (b : A), ∀ v ∈ U, ρ b v ∈ U) (a : A)
    (v : U) : (restrictRep ρ U hU a v : V) = ρ a v := rfl

include hp hA hpK Q hQ hρQ hp2 in
theorem int_dvd_of_weightPlane {H : Wt.Hyperplane A p} (hH : Wt.weightSpace ρ H.1 ≠ ⊥)
    (hd : finrank K (Wt.weightSpace ρ H.1) = 2) :
    (IsPlusType (Q.comp (Wt.weightSpace ρ H.1).subtype) → (p : ℤ) ∣ (Nat.card K : ℤ) - 1) ∧
      (¬ IsPlusType (Q.comp (Wt.weightSpace ρ H.1).subtype) →
        (p : ℤ) ∣ (Nat.card K : ℤ) + 1) := by
  classical
  set U := Wt.weightSpace ρ H.1 with hUdef
  have hU : ∀ (b : A), ∀ v ∈ U, ρ b v ∈ U := fun b v hv => Wt.apply_mem_weightSpace ρ H.1 b hv
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ H.1 := by
    by_contra hcon
    push Not at hcon
    have htop : H.1 = ⊤ := (Subgroup.eq_top_iff' _).mpr hcon
    have h := H.2
    rw [htop, Subgroup.index_top] at h
    exact hp.ne_one h.symm
  have hQU : (polarBilin (Q.comp U.subtype)).Nondegenerate := by
    have key : ∀ u : U, (∀ w : U, polar Q (u : V) (w : V) = 0) → u = 0 := fun u hu =>
      Subtype.ext (Wt.nondegenerate_weightFamily ρ hp hA hpK Q hQ hρQ (some H) u.2
        fun w hw => hu ⟨w, hw⟩)
    refine ⟨fun u hu => key u fun w => ?_, fun u hu => key u fun w => ?_⟩
    · have := hu w
      rwa [polarBilin_apply_apply, polar_comp_subtype' Q] at this
    · have := hu w
      rwa [polarBilin_apply_apply, polar_comp_subtype' Q,
        polar_comm] at this
  have hgO : restrictRep ρ U hU a ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => hρQ a v
  have hpow : ∀ n : ℕ, ∀ v : U, (((restrictRep ρ U hU a) ^ n) v : V) = ρ (a ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', LinearEquiv.mul_apply, coe_restrictRep_apply, ih, pow_succ', map_mul,
        Module.End.mul_apply]
  have hgp : (restrictRep ρ U hU a) ^ p = 1 := LinearEquiv.ext fun v => Subtype.ext (by
    rw [hpow, hA a, map_one]; rfl)
  have hg1 : restrictRep ρ U hU a ≠ 1 := by
    intro h1
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
    apply hv0
    refine Wt.eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK ha hv ?_
    have := congrArg (fun f : U ≃ₗ[K] U => (f ⟨v, hv⟩ : V)) h1
    simpa [coe_restrictRep_apply] using this
  exact int_dvd_of_plane hQU hd hp hp2 hgO hgp hg1

include hp hA hpK Q hQ hρQ hp2 in
theorem isPlusType_of_four_planes (hV : finrank K V = 8) {T : Finset (Wt.Hyperplane A p)}
    (hT : ∀ H : Wt.Hyperplane A p, H ∈ T ↔ Wt.weightSpace ρ H.1 ≠ ⊥) (hTc : T.card = 4)
    (hd : ∀ H ∈ T, finrank K (Wt.weightSpace ρ H.1) = 2) : IsPlusType Q := by
  classical
  have horth : ∀ H ∈ T, ∀ H' ∈ T, H ≠ H' → ∀ v ∈ Wt.weightSpace ρ H.1,
      ∀ w ∈ Wt.weightSpace ρ H'.1, polar Q v w = 0 := fun H _ H' _ hne v hv w hw =>
    Wt.polar_eq_zero_of_mem_weightFamily ρ hp hA hpK Q hρQ (i := some H) (j := some H')
      (fun h => hne (Option.some_injective _ h)) hv hw
  have htype := fun H (hH : H ∈ T) =>
    int_dvd_of_weightPlane ρ hp hA hpK Q hQ hρQ hp2 ((hT H).mp hH) (hd H hH)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hboth : ¬ ((p : ℤ) ∣ (Nat.card K : ℤ) - 1 ∧ (p : ℤ) ∣ (Nat.card K : ℤ) + 1) := by
    rintro ⟨h1, h2'⟩
    have h3 : (p : ℤ) ∣ 2 := by
      have := dvd_sub h2' h1
      rwa [show (Nat.card K : ℤ) + 1 - ((Nat.card K : ℤ) - 1) = 2 by ring] at this
    have : p ∣ 2 := Int.natCast_dvd_natCast.mp h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  by_cases hq : (p : ℤ) ∣ (Nat.card K : ℤ) - 1
  ·
    have hplus : ∀ H ∈ T, IsPlusType (Q.comp (Wt.weightSpace ρ H.1).subtype) := fun H hH => by
      by_contra hn
      exact hboth ⟨hq, (htype H hH).2 hn⟩
    choose e he0 heQ using fun (H : ↥T) =>
      exists_singular_of_isPlusType (hd H.1 H.2) (hplus H.1 H.2)
    let v : ↥T → V := fun H => ((e H : Wt.weightSpace ρ H.1.1) : V)
    have hv0 : ∀ H, v H ≠ 0 := fun H h => he0 H (Subtype.ext h)
    have hvQ : ∀ H, Q (v H) = 0 := fun H => heQ H
    have hind : iSupIndep (fun H : ↥T => Wt.weightFamily (p := p) ρ (some H.1)) :=
      (Wt.iSupIndep_weightFamily ρ hp hA hpK).comp (f := fun H : ↥T => some H.1)
        fun a b h => Subtype.ext (Option.some_injective _ h)
    have hli : LinearIndependent K v :=
      hind.linearIndependent _ (fun H => (e H).2) hv0
    refine ⟨Submodule.span K (Set.range v), ?_, fun x hx => ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_coe, hTc, hV]
    · refine CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span ?_ ?_ hx
      · rintro _ ⟨H, rfl⟩
        exact hvQ H
      · rintro _ ⟨H, rfl⟩ _ ⟨H', rfl⟩
        by_cases hHH : H = H'
        · subst hHH
          rw [polar_self, hvQ, smul_zero]
        · exact horth H.1 H.2 H'.1 H'.2 (fun h => hHH (Subtype.ext h)) _ (e H).2 _ (e H').2
  ·
    have hnplus : ∀ H ∈ T, ¬ IsPlusType (Q.comp (Wt.weightSpace ρ H.1).subtype) := fun H hH h =>
      hq ((htype H hH).1 h)
    obtain ⟨H₀, T', hH₀, rfl, hT'⟩ := Finset.card_eq_succ.mp hTc
    obtain ⟨H₁, H₂, H₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hT'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hH₀
    obtain ⟨h01, h02, h03⟩ := hH₀
    have hmem : ∀ H, H = H₀ ∨ H = H₁ ∨ H = H₂ ∨ H = H₃ →
        H ∈ (insert H₀ {H₁, H₂, H₃} : Finset (Wt.Hyperplane A p)) := by
      intro H h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact h
    have hm0 := hmem H₀ (Or.inl rfl)
    have hm1 := hmem H₁ (Or.inr (Or.inl rfl))
    have hm2 := hmem H₂ (Or.inr (Or.inr (Or.inl rfl)))
    have hm3 := hmem H₃ (Or.inr (Or.inr (Or.inr rfl)))
    have hn : ∀ H ∈ (insert H₀ {H₁, H₂, H₃} : Finset (Wt.Hyperplane A p)),
        ∀ v ∈ Wt.weightSpace ρ H.1,
        (∀ u ∈ Wt.weightSpace ρ H.1, polar Q v u = 0) → v = 0 := fun H _ v hv h =>
      Wt.nondegenerate_weightFamily ρ hp hA hpK Q hQ hρQ (some H) hv h
    have ha : ∀ H ∈ (insert H₀ {H₁, H₂, H₃} : Finset (Wt.Hyperplane A p)),
        ∀ v ∈ Wt.weightSpace ρ H.1, Q v = 0 → v = 0 :=
      fun H hH v hv hQv => congrArg Subtype.val
        (eq_zero_of_not_isPlusType (u := (⟨v, hv⟩ : Wt.weightSpace ρ H.1)) (hd H hH)
          (hnplus H hH) hQv)
    exact CFSG.RankThree.PartOne.S15K.isPlusType_of_four_aniso_planes hV (hd _ hm0) (hd _ hm1)
      (hd _ hm2) (hd _ hm3) (hn _ hm0) (hn _ hm1) (hn _ hm2) (hn _ hm3) (ha _ hm0) (ha _ hm1)
      (ha _ hm2) (ha _ hm3) (horth _ hm0 _ hm1 h01) (horth _ hm0 _ hm2 h02)
      (horth _ hm0 _ hm3 h03) (horth _ hm1 _ hm2 h12) (horth _ hm1 _ hm3 h13)
      (horth _ hm2 _ hm3 h23)

include hp hA hpK Q hQ h2 hρQ hp2 in
theorem exists_planes_eight_three_of_not_isPlusType (hρ : Function.Injective ρ)
    (hcard : Nat.card A = p ^ 3) (hV : finrank K V = 8) (hnp : ¬ IsPlusType Q) :
    ∃ yy zz : A, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
      finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy)) = 6 ∧
      finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) = 4 ∧
      (∀ a : A, (∀ v ∈ Wt.fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
        a ∈ Subgroup.zpowers yy) ∧
      (∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v) ∧
      finrank K (Wt.fixedSpace ρ ⊤) < 4 := by
  classical
  by_cases hfix : Wt.fixedSpace ρ ⊤ = ⊥
  · obtain ⟨T, hT, hrT, hsum, hge, -⟩ :=
      Wt.exists_support ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard
    have hd0 : finrank K (Wt.fixedSpace ρ ⊤) = 0 := by rw [hfix, finrank_bot]
    rw [hd0, zero_add, hV] at hsum
    have hcardle : T.card ≤ 4 := by
      have := Finset.card_nsmul_le_sum T _ 2 hge
      rw [smul_eq_mul] at this
      omega
    rcases (show T.card = 3 ∨ T.card = 4 by omega) with h3 | h4
    ·
      have finish : ∀ H₁ ∈ T, ∀ H₂ ∈ T, H₁ ≠ H₂ → finrank K (Wt.weightSpace ρ H₁.1) = 2 →
          finrank K (Wt.weightSpace ρ H₂.1) = 2 → ∃ yy zz : A, yy ≠ 1 ∧
            zz ∉ Subgroup.zpowers yy ∧ finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy)) = 6 ∧
            finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) = 4 ∧
            (∀ a : A, (∀ v ∈ Wt.fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
              a ∈ Subgroup.zpowers yy) ∧
            (∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v) ∧ finrank K (Wt.fixedSpace ρ ⊤) < 4 := by
        intro H₁ hH₁ H₂ hH₂ h12 hd₁ hd₂
        obtain ⟨yy, zz, h1, h2', hy3, hy4, h5, h6⟩ :=
          Wt.exists_planes_of_mem ρ hp hA hpK hρ hcard hT h3 hH₁ hH₂ h12
        have hs1 := Finset.add_sum_erase T (fun H => finrank K (Wt.weightSpace ρ H.1)) hH₁
        have hH₂' : H₂ ∈ T.erase H₁ := Finset.mem_erase.mpr ⟨Ne.symm h12, hH₂⟩
        have hs2 := Finset.add_sum_erase (T.erase H₁)
          (fun H => finrank K (Wt.weightSpace ρ H.1)) hH₂'
        rw [hd0, zero_add] at hy3 hy4
        exact ⟨yy, zz, h1, h2', by omega, by omega, h5, h6, by omega⟩
      obtain ⟨Ha, Hb, Hc, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
      have hma : Ha ∈ ({Ha, Hb, Hc} : Finset (Wt.Hyperplane A p)) := by simp
      have hmb : Hb ∈ ({Ha, Hb, Hc} : Finset (Wt.Hyperplane A p)) := by simp
      have hmc : Hc ∈ ({Ha, Hb, Hc} : Finset (Wt.Hyperplane A p)) := by simp
      have hs : finrank K (Wt.weightSpace ρ Ha.1) + finrank K (Wt.weightSpace ρ Hb.1) +
          finrank K (Wt.weightSpace ρ Hc.1) = 8 := by
        rw [hsum, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
          Finset.sum_singleton, add_assoc]
      have hea := Wt.even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 Ha
      have heb := Wt.even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 Hb
      have hec := Wt.even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 Hc
      obtain ⟨ka, hka⟩ := hea
      obtain ⟨kb, hkb⟩ := heb
      obtain ⟨kc, hkc⟩ := hec
      have hga := hge Ha hma
      have hgb := hge Hb hmb
      have hgc := hge Hc hmc
      rcases (show (finrank K (Wt.weightSpace ρ Ha.1) = 2 ∧ finrank K (Wt.weightSpace ρ Hb.1) = 2) ∨
          (finrank K (Wt.weightSpace ρ Ha.1) = 2 ∧ finrank K (Wt.weightSpace ρ Hc.1) = 2) ∨
          (finrank K (Wt.weightSpace ρ Hb.1) = 2 ∧ finrank K (Wt.weightSpace ρ Hc.1) = 2) by
        omega) with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩
      · exact finish Ha hma Hb hmb hab h1 h2'
      · exact finish Ha hma Hc hmc hac h1 h2'
      · exact finish Hb hmb Hc hmc hbc h1 h2'
    ·
      exfalso
      apply hnp
      have hsum2 : ∑ _H ∈ T, 2 = ∑ H ∈ T, finrank K (Wt.weightSpace ρ H.1) := by
        rw [Finset.sum_const, smul_eq_mul, ← hsum, h4]
      exact isPlusType_of_four_planes ρ hp hA hpK Q hQ hρQ hp2 hV hT h4
        fun H hH => ((Finset.sum_eq_sum_iff_of_le hge).mp hsum2 H hH).symm
  · obtain ⟨yy, zz, h1, h2', h3, h4, h5, h6⟩ :=
      Wt.exists_planes_eight_three ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard hV hfix
    obtain ⟨-, -, -, -, -, -, -, hd0, -⟩ :=
      Wt.exists_config_eight_three ρ hp hA hpK Q hQ h2 hρQ hp2 hρ hcard hV hfix
    exact ⟨yy, zz, h1, h2', h3, h4, h5, h6, by omega⟩

end Four

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
