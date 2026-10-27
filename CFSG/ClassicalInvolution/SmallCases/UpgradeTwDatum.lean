module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedDatum
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcRoots
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsBasic

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.Upgrade

theorem map_neg_one_sl2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (-1 : SL(2, R)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem list_prod_units_act_scalar {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} (l : List ι) (g : ι → (Module.End R M)ˣ) (s : ι → R) (v : M)
    (hg : ∀ i, ((g i : Module.End R M)) v = s i • v) :
    (((l.map g).prod : (Module.End R M)ˣ) : Module.End R M) v = (l.map s).prod • v := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, map_smul, hg i,
      List.map_cons, List.prod_cons, smul_smul, mul_comm]


theorem false_of_commuting_involutions_odd_quotient {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {Y : Type} [Group Y] (O : Subgroup Y) [O.Normal]
    (hO : Odd (Nat.card O)) (e : Y ⧸ O ≃* SL(2, F)) {a b : Y} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) : False := by
  have hnot : ∀ x : Y, orderOf x = 2 → x ∉ O := fun x hx hxO => by
    have h1 := Subgroup.orderOf_dvd_natCard O hxO
    rw [hx] at h1
    obtain ⟨k, hk⟩ := hO
    omega
  have himg : ∀ x : Y, orderOf x = 2 → e (QuotientGroup.mk' O x) = -1 := fun x hx => by
    refine (sl2_orderOf_eq_two_iff hodd _).mp ?_
    rw [MulEquiv.orderOf_eq]
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this
    have h1 : (QuotientGroup.mk' O x) ^ 2 = 1 := by
      rw [← map_pow, pow_two, hx2, map_one]
    have h2 : QuotientGroup.mk' O x ≠ 1 := fun h => hnot x hx (by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h)
    exact orderOf_eq_prime h1 h2
  have h1 := himg a ha
  have h2 := himg b hb
  have hq : QuotientGroup.mk' O a = QuotientGroup.mk' O b := e.injective (h1.trans h2.symm)
  have hmem : a⁻¹ * b ∈ O := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
    exact hq
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hb2 : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, pow_two] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  rw [hainv] at hmem
  apply hnot (a * b) _ hmem
  have hsq : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hne1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rwa [inv_eq_of_mul_eq_one_right hb2] at this)
  exact orderOf_eq_prime hsq hne1


theorem exists_sl2_anticommuting_pair {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ A B : SL(2, F), A * A = -1 ∧ B * B = -1 ∧ A * B = (-1) * (B * A) ∧
      A ≠ 1 ∧ A ≠ -1 ∧ B ≠ 1 ∧ B ≠ -1 ∧ ∀ ε : SL(2, F), (ε = 1 ∨ ε = -1) → A * ε ≠ B := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_card hodd)
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 + Polynomial.C 1)
    (by rw [Polynomial.degree_X_pow]; rfl)
    (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; rfl) hcard
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C] at hab
  have hab' : a ^ 2 + b ^ 2 = -1 := by linear_combination hab
  let A : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let B : SL(2, F) := ⟨!![a, b; b, -a], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination -hab'⟩
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hab'
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [A] at this
  · intro h
    have := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [A] at this
  · intro h
    have h1 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
    have h2' := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [B] at h1 h2'
    subst h1
    have h3 : a ^ 2 = 1 := by rw [h2']; norm_num
    exact h2 (by linear_combination hab' - h3)
  · intro h
    have h1 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
    have h2' := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [B] at h1 h2'
    subst h1
    have h3 : a ^ 2 = 1 := by rw [h2']; norm_num
    exact h2 (by linear_combination hab' - h3)
  · rintro ε (rfl | rfl) h
    · rw [mul_one] at h
      have h1 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
      have h2' := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp [A, B] at h1 h2'
      rw [← h1, ← h2'] at hab'
      norm_num at hab'
      exact h2 (by linear_combination hab')
    · have h1 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
      have h2' := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] at h1 h2'
      simp [A, B] at h1 h2'
      rw [← h1, ← h2'] at hab'
      norm_num at hab'
      exact h2 (by linear_combination hab')


theorem card_eq_of_quasisimple_equiv_sl2 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) (O : Subgroup Y) [O.Normal] (hOodd : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (eY : Y ⧸ O ≃* SL(2, F₂)) {K : Type} [Field K] [Finite K]
    (e : SL(2, K) ≃* Y) : Nat.card K = Nat.card F₂ := by
  have hcenter : Nat.card (Subgroup.center Y) ≤ 2 := by
    have h1 : Nat.card (Subgroup.center Y) = Nat.card (Subgroup.center SL(2, K)) :=
      (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    rw [h1, Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2)
      (R := K)).toEquiv]
    have : NeZero (max (Fintype.card (Fin 2)) 1) := ⟨by simp⟩
    have := card_rootsOfUnity (k := max (Fintype.card (Fin 2)) 1) (R := K)
    simpa using this
  have hq₂ : 2 ≤ Nat.card F₂ := Finite.one_lt_card
  have hOle : Nat.card O ≤ 2 := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hY O with hle | htop
    · exact (Subgroup.card_le_of_le hle).trans hcenter
    · exfalso
      have h1 : Nat.card (Y ⧸ O) = 1 := by
        have : O.index = 1 := by rw [htop, Subgroup.index_top]
        exact this
      rw [Nat.card_congr eY.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
      have h6 : 3 ≤ Nat.card F₂ ^ 2 - 1 := by
        have : 4 ≤ Nat.card F₂ ^ 2 := by nlinarith
        omega
      have : 2 * 3 ≤ Nat.card F₂ * (Nat.card F₂ ^ 2 - 1) := Nat.mul_le_mul hq₂ h6
      omega
  have hO1 : Nat.card O = 1 := by
    obtain ⟨k, hk⟩ := hOodd
    have : 0 < Nat.card O := Nat.card_pos
    omega
  have hcardY : Nat.card Y = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hmul := Subgroup.card_mul_index O
  rw [hO1, one_mul] at hmul
  have hidx : O.index = Nat.card (Y ⧸ O) := rfl
  rw [hidx, Nat.card_congr eY.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    hcardY] at hmul
  have hqK : 2 ≤ Nat.card K := Finite.one_lt_card
  exact eq_of_mul_sq_sub_one_eq (by omega) (by omega) hmul.symm


section Datum

open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

noncomputable def orbitPairing (O : Set (Fin τ.rank → ℤ)) (δ : Fin τ.rank → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (orbitCard O), corootPair (D.orbitVec O j) δ

theorem orbitMap_neg_one_act {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    ((D.orbitMap O (-1) : ModGL τ k) : Module.End k (RootModule τ k)) (rootVec τ k δ) =
      (((-1 : kˣ) ^ orbitPairing D O δ : kˣ) : k) • rootVec τ k δ := by
  rw [orbitMap_eq_prod]
  have hfac : ∀ j, ((D.orbitFactor O j (-1) : ModGL τ k) :
      Module.End k (RootModule τ k)) (rootVec τ k δ) =
      (((-1 : kˣ) ^ corootPair (D.orbitVec O j) δ : kˣ) : k) • rootVec τ k δ := by
    intro j
    rw [orbitFactor_apply, map_neg_one_sl2, map_neg_one_sl2, sl2_neg_one_eq_HSL]
    exact (exceptional_Lang_root_rank_one_torus_transport τ k
      (D.isRoot_orbitVec hO j)).2.2.2.2.1 (-1) |>.2 δ hδ
  have h := list_prod_units_act_scalar (List.range (orbitCard O))
    (fun j => D.orbitFactor O j (-1))
    (fun j => (((-1 : kˣ) ^ corootPair (D.orbitVec O j) δ : kˣ) : k)) (rootVec τ k δ) hfac
  rw [h]
  congr 1
  have key : ∀ n : ℕ, (((List.range n).map fun j =>
      (((-1 : kˣ) ^ corootPair (D.orbitVec O j) δ : kˣ) : k)).prod) =
      (((-1 : kˣ) ^ ∑ j ∈ Finset.range n, corootPair (D.orbitVec O j) δ : kˣ) : k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.sum_range_succ,
        zpow_add]
      simp
  rw [orbitPairing]
  exact key _


include D in
theorem corootPair_eq_iform {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (δ : Fin τ.rank → ℤ) :
    corootPair β δ = iform β δ := by
  have h := corootPair_mul hβ δ
  rw [D.iform_self_eq_two hβ] at h
  omega

theorem iform_orbitVec_succ {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (j i : ℕ) :
    iform (D.orbitVec O₁ (j + 1)) (D.orbitVec O₂ (i + 1)) =
      iform (D.orbitVec O₁ j) (D.orbitVec O₂ i) := by
  have h := D.isometry (toReal (D.orbitVec O₁ j)) (toReal (D.orbitVec O₂ i))
  rw [D.theta_orbitVec hO₁, D.theta_orbitVec hO₂, rform_toReal, rform_toReal] at h
  exact_mod_cast h

theorem orbitVec_add_card {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (n : ℕ) :
    D.orbitVec O (n + orbitCard O) = D.orbitVec O n := by
  rw [D.orbitVec_eq_iff hO, Function.iterate_add_apply, D.orbitCard_eq_minimalPeriod hO,
    Function.iterate_minimalPeriod]

theorem sum_range_shift (f : ℕ → ℤ) (d : ℕ) (h : f d = f 0) :
    ∑ i ∈ Finset.range d, f (i + 1) = ∑ i ∈ Finset.range d, f i := by
  have h1 := Finset.sum_range_succ f d
  have h2 := Finset.sum_range_succ' f d
  linarith


theorem iform_orbitVec_eq {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {j j' : ℕ}
    (hj : j < orbitCard O) (hj' : j' < orbitCard O) :
    iform (D.orbitVec O j) (D.orbitVec O j') = if j = j' then 2 else 0 := by
  split_ifs with h
  · subst h
    exact D.iform_self_eq_two (D.isRoot_orbitVec hO j)
  · have hK := D.orbitRoot_mem_kernelRoots hO
    have hne : D.orbitVec O j ≠ D.orbitVec O j' := fun h' => h (D.orbitVec_injOn hO hj hj' h')
    exact D.orbit_orthogonal _ hK _ (D.thetaPowVec_spec hK j).2.1 _
      (D.thetaPowVec_spec hK j').2.1 hne

theorem orbitVec_ne_of_ne {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (hne : O₁ ≠ O₂) (j i : ℕ) : D.orbitVec O₁ j ≠ D.orbitVec O₂ i := by
  intro h
  apply hne
  rw [D.eq_thetaOrbit_of_mem_orbits hO₁ (D.orbitVec_mem hO₁ j),
    D.eq_thetaOrbit_of_mem_orbits hO₂ (D.orbitVec_mem hO₂ i), h]

theorem iform_orbitVec_nonpos {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (hne : O₁ ≠ O₂) (j i : ℕ) :
    iform (D.orbitVec O₁ j) (D.orbitVec O₂ i) ≤ 0 :=
  iform_nonpos_of_mem_unionSimpleRoots (D.orbitVec_mem_unionSimpleRoots hO₁ j)
    (D.orbitVec_mem_unionSimpleRoots hO₂ i) (orbitVec_ne_of_ne D hO₁ hO₂ hne j i)


theorem exists_odd_orbitPairing {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (hne : O₁ ≠ O₂) (hadj : ∃ β ∈ O₁, ∃ γ ∈ O₂, iform β γ ≠ 0) :
    (∃ γ ∈ O₂, Odd (orbitPairing D O₁ γ)) ∨ ∃ β ∈ O₁, Odd (orbitPairing D O₂ β) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hev₂', hev₁'⟩ := hcon
  have he₁ : ∀ γ ∈ O₂, Even (orbitPairing D O₁ γ) := fun γ hγ => by
    simpa using hev₂' γ hγ
  have he₂ : ∀ β ∈ O₁, Even (orbitPairing D O₂ β) := fun β hβ => by
    simpa using hev₁' β hβ
  obtain ⟨β₀, hβ₀, γ₀, hγ₀, hadj⟩ := hadj
  set d₁ := orbitCard O₁ with hd₁
  set d₂ := orbitCard O₂ with hd₂
  have hd₁pos : 0 < d₁ := D.orbitCard_pos hO₁
  have hd₂pos : 0 < d₂ := D.orbitCard_pos hO₂
  set M : ℕ → ℕ → ℤ := fun j i => iform (D.orbitVec O₁ j) (D.orbitVec O₂ i) with hM
  have hMθ : ∀ j i, M (j + 1) (i + 1) = M j i := fun j i => iform_orbitVec_succ D hO₁ hO₂ j i
  have hMper₁ : ∀ j i, M (j + d₁) i = M j i := fun j i => by
    simp only [hM]
    rw [orbitVec_add_card D hO₁]
  have hMper₂ : ∀ j i, M j (i + d₂) = M j i := fun j i => by
    simp only [hM]
    rw [orbitVec_add_card D hO₂]
  have hrow : ∀ j, ∑ i ∈ Finset.range d₂, M j i = ∑ i ∈ Finset.range d₂, M 0 i := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← sum_range_shift (M (j + 1)) d₂ (by simpa using hMper₂ (j + 1) 0)]
      simp only [hMθ]
      exact ih
  have hcol : ∀ i, ∑ j ∈ Finset.range d₁, M j i = ∑ j ∈ Finset.range d₁, M j 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← sum_range_shift (fun j => M j (i + 1)) d₁ (by simpa using hMper₁ 0 (i + 1))]
      simp only [hMθ]
      exact ih
  have hpair₂ : ∀ j, orbitPairing D O₂ (D.orbitVec O₁ j) = ∑ i ∈ Finset.range d₂, M j i := by
    intro j
    rw [orbitPairing]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corootPair_eq_iform D (D.isRoot_orbitVec hO₂ i), iform_comm]
  have hpair₁ : ∀ i, orbitPairing D O₁ (D.orbitVec O₂ i) = ∑ j ∈ Finset.range d₁, M j i := by
    intro i
    rw [orbitPairing]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [corootPair_eq_iform D (D.isRoot_orbitVec hO₁ j)]
  set c := ∑ i ∈ Finset.range d₂, M 0 i with hc
  set a := ∑ j ∈ Finset.range d₁, M j 0 with ha
  have hc_even : Even c := by
    have := he₂ _ (D.orbitVec_mem hO₁ 0)
    rwa [hpair₂ 0] at this
  have ha_even : Even a := by
    have := he₁ _ (D.orbitVec_mem hO₂ 0)
    rwa [hpair₁ 0] at this
  obtain ⟨j₀, hj₀, hβ₀eq⟩ := D.exists_orbitVec_eq hO₁ hβ₀
  obtain ⟨i₀, hi₀, hγ₀eq⟩ := D.exists_orbitVec_eq hO₂ hγ₀
  have hMneg : M j₀ i₀ < 0 := by
    have h1 : M j₀ i₀ = iform β₀ γ₀ := by simp only [hM, hβ₀eq, hγ₀eq]
    have h2 : M j₀ i₀ ≤ 0 := iform_orbitVec_nonpos D hO₁ hO₂ hne j₀ i₀
    rcases h2.lt_or_eq with h | h
    · exact h
    · exact absurd (h1 ▸ h) hadj
  have hc_neg : c < 0 := by
    have h1 : c = ∑ i ∈ Finset.range d₂, M j₀ i := (hrow j₀).symm
    have h2 : ∑ i ∈ Finset.range d₂, M j₀ i ≤ M j₀ i₀ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi₀)]
      have : ∑ i ∈ (Finset.range d₂).erase i₀, M j₀ i ≤ 0 :=
        Finset.sum_nonpos fun i _ => iform_orbitVec_nonpos D hO₁ hO₂ hne j₀ i
      linarith
    linarith
  have ha_neg : a < 0 := by
    have h1 : a = ∑ j ∈ Finset.range d₁, M j i₀ := (hcol i₀).symm
    have h2 : ∑ j ∈ Finset.range d₁, M j i₀ ≤ M j₀ i₀ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hj₀)]
      have : ∑ j ∈ (Finset.range d₁).erase j₀, M j i₀ ≤ 0 :=
        Finset.sum_nonpos fun j _ => iform_orbitVec_nonpos D hO₁ hO₂ hne j i₀
      linarith
    linarith
  have hc2 : c ≤ -2 := by
    obtain ⟨m, hm⟩ := hc_even
    omega
  have ha2 : a ≤ -2 := by
    obtain ⟨m, hm⟩ := ha_even
    omega
  set b₁ : Fin τ.rank → ℤ := ∑ j ∈ Finset.range d₁, D.orbitVec O₁ j with hb₁
  set b₂ : Fin τ.rank → ℤ := ∑ i ∈ Finset.range d₂, D.orbitVec O₂ i with hb₂
  set S : ℤ := ∑ j ∈ Finset.range d₁, ∑ i ∈ Finset.range d₂, M j i with hS
  have hSb : iform b₁ b₂ = S := by
    rw [hb₁, hb₂, iform_finset_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iform_finset_sum_right]
  have hS1 : S = d₁ * c := by
    rw [hS]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp [hc]
  have hS2 : S = d₂ * a := by
    rw [hS, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun i _ => hcol i]
    simp [ha]
  have hN₁ : iform b₁ b₁ = 2 * d₁ := by
    have h1 : ∀ j ∈ Finset.range d₁, iform (D.orbitVec O₁ j) b₁ = 2 := by
      intro j hj
      have hjlt : j < orbitCard O₁ := Finset.mem_range.1 hj
      rw [hb₁, iform_finset_sum_right, Finset.sum_eq_single j]
      · exact D.iform_self_eq_two (D.isRoot_orbitVec hO₁ j)
      · intro j' hj' hne'
        have := iform_orbitVec_eq D hO₁ hjlt (Finset.mem_range.1 hj' : j' < orbitCard O₁)
        simpa [Ne.symm hne'] using this
      · intro h
        exact absurd hj h
    conv_lhs => rw [hb₁, iform_finset_sum_left]
    rw [Finset.sum_congr rfl h1]
    simp [mul_comm]
  have hN₂ : iform b₂ b₂ = 2 * d₂ := by
    have h1 : ∀ i ∈ Finset.range d₂, iform (D.orbitVec O₂ i) b₂ = 2 := by
      intro i hi
      have hilt : i < orbitCard O₂ := Finset.mem_range.1 hi
      rw [hb₂, iform_finset_sum_right, Finset.sum_eq_single i]
      · exact D.iform_self_eq_two (D.isRoot_orbitVec hO₂ i)
      · intro i' hi' hne'
        have := iform_orbitVec_eq D hO₂ hilt (Finset.mem_range.1 hi' : i' < orbitCard O₂)
        simpa [Ne.symm hne'] using this
      · intro h
        exact absurd hi h
    conv_lhs => rw [hb₂, iform_finset_sum_left]
    rw [Finset.sum_congr rfl h1]
    simp [mul_comm]
  have hd₁z : (0 : ℤ) < d₁ := by exact_mod_cast hd₁pos
  have hd₂z : (0 : ℤ) < d₂ := by exact_mod_cast hd₂pos
  set v : Fin τ.rank → ℤ := (2 * (d₂ : ℤ)) • b₁ - S • b₂ with hv
  have hvv : iform v v = 2 * d₂ * (4 * d₁ * d₂ - S ^ 2) := by
    rw [hv]
    simp only [iform_sub_left, iform_sub_right, iform_smul_left, iform_smul_right]
    rw [iform_comm b₂ b₁, hSb, hN₁, hN₂]
    ring
  have hSsq : S ^ 2 = d₁ * d₂ * (a * c) := by
    calc S ^ 2 = S * S := pow_two S
      _ = (d₁ * c) * (d₂ * a) := by rw [← hS1, ← hS2]
      _ = d₁ * d₂ * (a * c) := by ring
  have hac : 4 ≤ a * c := by nlinarith
  have hpos : 0 ≤ (d₁ : ℤ) * d₂ * (a * c - 4) := mul_nonneg (by positivity) (by linarith)
  have hle : iform v v ≤ 0 := by
    rw [hvv, hSsq]
    nlinarith
  have hv0 : v = 0 := by
    by_contra hne0
    have := iform_self_pos hne0
    linarith
  have hvv0 : iform v v = 0 := by
    rw [hv0]
    simp [iform]
  have hSsq4 : S ^ 2 = 4 * d₁ * d₂ := by
    rw [hvv] at hvv0
    have h2d : (2 : ℤ) * d₂ ≠ 0 := by positivity
    have := (mul_eq_zero.mp hvv0).resolve_left h2d
    linarith
  have hac4 : a * c = 4 := by
    rw [hSsq] at hSsq4
    have h12 : (d₁ : ℤ) * d₂ ≠ 0 := by positivity
    have : (d₁ : ℤ) * d₂ * (a * c) = (d₁ : ℤ) * d₂ * 4 := by linarith
    exact mul_left_cancel₀ h12 this
  have ha_eq : a = -2 := by nlinarith
  have hc_eq : c = -2 := by nlinarith
  have hSval : S = -(2 * (d₂ : ℤ)) := by rw [hS2, ha_eq]; ring
  have hsum0 : (2 * (d₂ : ℤ)) • (b₁ + b₂) = 0 := by
    have h := sub_eq_zero.mp hv0
    rw [hSval, neg_smul] at h
    rw [smul_add, h]
    simp
  have hb12 : b₁ + b₂ = 0 := by
    rcases smul_eq_zero.mp hsum0 with h | h
    · exact absurd h (by positivity)
    · exact h
  have hheight : height (b₁ + b₂) = 0 := by rw [hb12]; simp [height]
  have hh₁ : 0 < height b₁ := by
    rw [hb₁, height_finset_sum]
    refine Finset.sum_pos (fun j _ => ?_) ⟨0, Finset.mem_range.2 hd₁pos⟩
    exact (mem_posRoots_of_mem_unionSimpleRoots (D.orbitVec_mem_unionSimpleRoots hO₁ j)).2
  have hh₂ : 0 < height b₂ := by
    rw [hb₂, height_finset_sum]
    refine Finset.sum_pos (fun i _ => ?_) ⟨0, Finset.mem_range.2 hd₂pos⟩
    exact (mem_posRoots_of_mem_unionSimpleRoots (D.orbitVec_mem_unionSimpleRoots hO₂ i)).2
  rw [height_add] at hheight
  omega

end Datum


theorem torus_mul_comm {τ : Tag} {k : Type} [Field k] {x y : ModGL τ k}
    (hx : x ∈ torusGroup τ k) (hy : y ∈ torusGroup τ k) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a hy

section Main

open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem finite_orbits : D.orbits.Finite := by
  have : D.orbits = (thetaOrbit D.θ) '' D.simpleRootsJ := by
    ext O
    exact ⟨fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩, fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩⟩
  rw [this]
  exact (D.finite_roots.subset fun _ h => h.2).image _

theorem orbitMap_neg_one_eq_orbitH {O : Set (Fin τ.rank → ℤ)} :
    D.orbitMap O (-1) = D.orbitH O (-1) := by
  rw [sl2_neg_one_eq_HSL]
  rfl

theorem orbitMap_neg_one_mem_torusGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitMap O (-1) ∈ torusGroup τ k := by
  rw [orbitMap_neg_one_eq_orbitH]
  exact D.orbitH_mem_torusGroup hO (-1)

theorem orbitMap_neg_one_mul_self {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitMap O (-1) * D.orbitMap O (-1) = 1 := by
  have h : ∀ A B : SL(2, D.orbitField O), D.orbitMap O A * D.orbitMap O B =
      D.orbitMap O (A * B) := fun A B => (D.orbitMap_mul hO A B).symm
  rw [h]
  have : (-1 : SL(2, D.orbitField O)) * (-1) = 1 := by simp
  rw [this, orbitMap_one]


theorem orbitPairing_self {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ O) : orbitPairing D O γ = 2 := by
  obtain ⟨i₀, hi₀, rfl⟩ := D.exists_orbitVec_eq hO hγ
  rw [orbitPairing, Finset.sum_eq_single i₀]
  · rw [corootPair_eq_iform D (D.isRoot_orbitVec hO i₀)]
    exact D.iform_self_eq_two (D.isRoot_orbitVec hO i₀)
  · intro j hj hne
    rw [corootPair_eq_iform D (D.isRoot_orbitVec hO j)]
    have := iform_orbitVec_eq D hO (Finset.mem_range.1 hj : j < orbitCard O) hi₀
    simpa [hne] using this
  · intro h
    exact absurd (Finset.mem_range.2 hi₀) h

theorem orbitPairing_parity_eq {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (h : D.orbitMap O₁ (-1) = D.orbitMap O₂ (-1))
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (((-1 : kˣ) ^ orbitPairing D O₁ δ : kˣ) : k) =
      (((-1 : kˣ) ^ orbitPairing D O₂ δ : kˣ) : k) := by
  have h1 := orbitMap_neg_one_act D hO₁ hδ
  have h2 := orbitMap_neg_one_act D hO₂ hδ
  rw [h] at h1
  have hv0 : rootVec τ k δ ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hδ]
    exact Finsupp.single_ne_zero.mpr one_ne_zero
  exact smul_left_injective k hv0 (h1.symm.trans h2)


theorem orbits_eq_singleton_of_classical_cross {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) (φ : Y ≃* D.orbitGroup) (O : Subgroup Y) [O.Normal]
    (hOodd : Odd (Nat.card O)) {F₂ : Type} [Field F₂] [Finite F₂] (hodd₂ : Odd (Nat.card F₂))
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ O₀, O₀ ∈ D.orbits ∧ D.orbits = {O₀} ∧ Nat.card F₂ = D.q ^ orbitCard O₀ := by
  classical
  have hring : ringChar k ≠ 2 := D.ringChar_ne_two
  have h2k : (2 : k) ≠ 0 := Ring.two_ne_zero hring
  have huniq : ∀ (x y : ModGL τ k) (hx : x ∈ D.orbitGroup) (hy : y ∈ D.orbitGroup),
      x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x * y = y * x → x = y := by
    intro x y hx hy hx2 hy2 hx1 hy1 hxy
    by_contra hne
    have hφa : φ (φ.symm ⟨x, hx⟩) = ⟨x, hx⟩ := φ.apply_symm_apply _
    have hφb : φ (φ.symm ⟨y, hy⟩) = ⟨y, hy⟩ := φ.apply_symm_apply _
    have ha2 : φ.symm ⟨x, hx⟩ * φ.symm ⟨x, hx⟩ = 1 := by
      apply φ.injective
      rw [map_mul, hφa, map_one]
      exact Subtype.ext hx2
    have hb2 : φ.symm ⟨y, hy⟩ * φ.symm ⟨y, hy⟩ = 1 := by
      apply φ.injective
      rw [map_mul, hφb, map_one]
      exact Subtype.ext hy2
    have ha1 : φ.symm ⟨x, hx⟩ ≠ 1 := fun h => hx1 (by
      have := congrArg (fun z => ((φ z : D.orbitGroup) : ModGL τ k)) h
      simpa [hφa] using this)
    have hb1 : φ.symm ⟨y, hy⟩ ≠ 1 := fun h => hy1 (by
      have := congrArg (fun z => ((φ z : D.orbitGroup) : ModGL τ k)) h
      simpa [hφb] using this)
    refine false_of_commuting_involutions_odd_quotient hodd₂ O hOodd eY
      (a := φ.symm ⟨x, hx⟩) (b := φ.symm ⟨y, hy⟩)
      (orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1)
      (orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1) ?_ (fun h => hne (by
        have := congrArg (fun z => ((φ z : D.orbitGroup) : ModGL τ k)) h
        simpa [hφa, hφb] using this))
    apply φ.injective
    rw [map_mul, map_mul, hφa, hφb]
    exact Subtype.ext hxy
  have hne1 : ∀ {O' : Set (Fin τ.rank → ℤ)}, O' ∈ D.orbits → D.orbitMap O' (-1) ≠ 1 := by
    intro O' hO' h1
    have := ModelFacts.finite_orbitField D hO'
    have hodd' := ModelFacts.odd_card_orbitField D hO'
    obtain ⟨A, B, hAA, hBB, hAB, hA1, hAm, hB1, hBm, hAB'⟩ := exists_sl2_anticommuting_pair hodd'
    set R := D.orbitMapHom hO' with hR
    have hRapp : ∀ X, R X = D.orbitMap O' X := fun X => rfl
    have hRneg : R (-1) = 1 := h1
    have hxm : R A ∈ D.orbitGroup := D.orbitMap_mem_orbitGroup hO' A
    have hym : R B ∈ D.orbitGroup := D.orbitMap_mem_orbitGroup hO' B
    have hx2 : R A * R A = 1 := by rw [← map_mul, hAA, hRneg]
    have hy2 : R B * R B = 1 := by rw [← map_mul, hBB, hRneg]
    have hx1 : R A ≠ 1 := fun h => by
      rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO' (by rw [← hRapp]; exact h) with h' | h'
      exacts [hA1 h', hAm h']
    have hy1 : R B ≠ 1 := fun h => by
      rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO' (by rw [← hRapp]; exact h) with h' | h'
      exacts [hB1 h', hBm h']
    have hxy : R A * R B = R B * R A := by
      rw [← map_mul, ← map_mul, hAB, map_mul, hRneg, one_mul]
    have heq := huniq (R A) (R B) hxm hym hx2 hy2 hx1 hy1 hxy
    have h3 : D.orbitMap O' (A⁻¹ * B) = 1 := by
      rw [← hRapp, map_mul, map_inv, heq, inv_mul_cancel]
    rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO' h3 with h' | h'
    · exact hAB' _ (Or.inl h') (mul_inv_cancel_left A B)
    · exact hAB' _ (Or.inr h') (mul_inv_cancel_left A B)
  have hinvmem : ∀ {O' : Set (Fin τ.rank → ℤ)}, O' ∈ D.orbits →
      D.orbitMap O' (-1) ∈ D.orbitGroup := fun hO' => D.orbitMap_mem_orbitGroup hO' _
  have heq : ∀ {O₁ O₂ : Set (Fin τ.rank → ℤ)}, O₁ ∈ D.orbits → O₂ ∈ D.orbits →
      D.orbitMap O₁ (-1) = D.orbitMap O₂ (-1) := by
    intro O₁ O₂ h₁ h₂
    exact huniq _ _ (hinvmem h₁) (hinvmem h₂) (orbitMap_neg_one_mul_self D h₁)
      (orbitMap_neg_one_mul_self D h₂) (hne1 h₁) (hne1 h₂)
      (torus_mul_comm (orbitMap_neg_one_mem_torusGroup D h₁)
        (orbitMap_neg_one_mem_torusGroup D h₂))
  have hsingle : ∀ {O₁ O₂ : Set (Fin τ.rank → ℤ)}, O₁ ∈ D.orbits → O₂ ∈ D.orbits → O₁ = O₂ := by
    intro O₁ O₂ h₁ h₂
    by_contra hne
    have h2ncard : 2 ≤ D.orbits.ncard := by
      have : ({O₁, O₂} : Set (Set (Fin τ.rank → ℤ))).ncard = 2 := Set.ncard_pair hne
      calc 2 = ({O₁, O₂} : Set (Set (Fin τ.rank → ℤ))).ncard := this.symm
        _ ≤ D.orbits.ncard := Set.ncard_le_ncard
          (Set.insert_subset h₁ (Set.singleton_subset_iff.2 h₂)) (finite_orbits D)
    obtain ⟨P, hP, hOP, hadj⟩ := D.exists_adjacent_orbit h2ncard h₁
    have hm1 : ((-1 : kˣ) : k) = -1 := by simp
    have hneg : (-1 : k) ≠ 1 := fun h => h2k (by linear_combination -h)
    rcases exists_odd_orbitPairing D h₁ hP hOP hadj with ⟨γ, hγ, hodd⟩ | ⟨β, hβ, hodd⟩
    · have h := orbitPairing_parity_eq D h₁ hP (heq h₁ hP) (D.isRoot_of_mem_orbits hP hγ)
      rw [orbitPairing_self D hP hγ, hodd.neg_one_zpow] at h
      apply hneg
      simpa using h
    · have h := orbitPairing_parity_eq D hP h₁ (heq hP h₁) (D.isRoot_of_mem_orbits h₁ hβ)
      rw [orbitPairing_self D h₁ hβ, hodd.neg_one_zpow] at h
      apply hneg
      simpa using h
  have hnonempty : D.orbits.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : D.orbitGroup = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨O', hO', -⟩
      rw [h] at hO'
      exact absurd hO' (Set.notMem_empty O')
    have hY1 : ∀ y : Y, y = 1 := fun y => φ.injective (Subtype.ext (by
      have h2 : ((φ y : D.orbitGroup) : ModGL τ k) ∈ (⊥ : Subgroup (ModGL τ k)) := by
        rw [← hbot]
        exact (φ y).2
      rw [Subgroup.mem_bot] at h2
      rw [h2]
      exact (congrArg Subtype.val (map_one φ)).symm))
    obtain ⟨x, hx⟩ := eY.surjective (-1)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hY1 y, QuotientGroup.mk_one, map_one] at hx
    exact sl2_neg_one_ne_one hodd₂ hx.symm
  obtain ⟨O₀, hO₀⟩ := hnonempty
  have hA : D.orbits = {O₀} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hO₀, fun O' hO' => hsingle hO' hO₀⟩
  let ι : SL(2, D.orbitField O₀) →* Y := φ.symm.toMonoidHom.comp (D.orbitGroupHom hO₀)
  have hsurj : Function.Surjective ι :=
    φ.symm.surjective.comp (D.orbitGroupHom_surjective hO₀ hA)
  have hinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA'
    rw [MonoidHom.mem_ker] at hA'
    have h1 : D.orbitMap O₀ A = 1 := by
      have h2 : D.orbitGroupHom hO₀ A = 1 := φ.symm.injective (by simpa [ι] using hA')
      exact congrArg Subtype.val h2
    rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO₀ h1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ h1) (hne1 hO₀)
  let e : SL(2, D.orbitField O₀) ≃* Y := MulEquiv.ofBijective ι ⟨hinj, hsurj⟩
  refine ⟨O₀, hO₀, hA, ?_⟩
  have := ModelFacts.finite_orbitField D hO₀
  rw [← D.card_orbitField hO₀]
  exact (card_eq_of_quasisimple_equiv_sl2 hY O hOodd eY e).symm

end Main


theorem iform_neg_right_eq {τ : Tag} (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

section Classes

theorem false_of_orthogonal_simpleRoots {τ : Tag} {M : Type*} [CommGroup M]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {β₀ : Fin τ.rank → ℤ}
    (hβ₀ : β₀ ∈ simpleRoots (componentRoots χ i))
    (horth : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ β' ∈ simpleRoots (componentRoots χ i),
      β ≠ β' → iform β β' = 0)
    (hnon : ∀ β ∈ kernelRoots χ, ∃ γ ∈ kernelRoots χ, iform β γ = 1) : False := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨hβ₀K, hclass⟩ := simpleRoots_subset hβ₀
  obtain ⟨γ, hγK, hγ⟩ := hnon β₀ hβ₀K
  have hsame : (⟦⟨γ, hγK⟩⟧ : KernelComponent χ) = i := by
    rw [← hclass]
    refine mk_eq_of_iform_ne_zero ?_
    change iform γ β₀ ≠ 0
    rw [iform_comm, hγ]
    exact one_ne_zero
  have hγΨ : γ ∈ componentRoots χ i := ⟨hγK, hsame⟩
  have hββ : iform β₀ β₀ = 2 := by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (simpleRoots_isRoot hβ₀)
  have heven : ∀ α : Fin τ.rank → ℤ, α ∈ posRoots (componentRoots χ i) →
      ∃ m : ℤ, iform β₀ α = 2 * m := by
    intro α hα
    obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ hα
    refine ⟨c β₀, ?_⟩
    rw [e, iform_finset_sum_right, Finset.sum_eq_single β₀]
    · rw [iform_smul_right, hββ]
      ring
    · intro β hβ hne
      rw [iform_smul_right, horth β₀ hβ₀ β hβ (Ne.symm hne), mul_zero]
    · intro h
      exact absurd hβ₀ h
  rcases mem_posRoots_or_mem_negRoots hΨ hγΨ with h | h
  · obtain ⟨m, hm⟩ := heven γ h
    omega
  · obtain ⟨m, hm⟩ := heven (-γ) h
    rw [iform_neg_right_eq] at hm
    omega

end Classes

section TwoComponents

open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exists_orbits_singleton_of_isPComponent_cross (hX : Finite D.totalFixedGroup)
    {J₀ : Subgroup (adjointGroup τ k)} (hle : J₀ ≤ D.totalFixedGroup)
    (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    {Y : Type} [Group Y] (φ : Y ≃* J₀) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hodd₂ : Odd (Nat.card F₂))
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ (J' : Set.range D.classOrbit) (O₀ : Set (Fin τ.rank → ℤ)),
      O₀ ∈ (D.withOrbit J').orbits ∧ (D.withOrbit J').orbits = {O₀} ∧
        Nat.card F₂ = D.q ^ orbitCard O₀ := by
  obtain ⟨J', hJ', hq⟩ := exists_eq_orbitGroupC_of_isPComponent D hX hle hJ₀
  have hfinJ : Finite J₀ := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hfinY : Finite Y := Finite.of_equiv _ φ.symm.toEquiv
  let eC : (D.withOrbit J').orbitGroupC ≃* (D.withOrbit J').orbitGroup :=
    Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup
  let φ' : Y ≃* (D.withOrbit J').orbitGroup := (φ.trans (MulEquiv.subgroupCongr hJ')).trans eC
  have hY : CFSG.IsQuasisimple Y := (isQuasisimple_congr φ').2 hq
  obtain ⟨O₀, hO₀, hA, hcard⟩ := orbits_eq_singleton_of_classical_cross (D.withOrbit J') hY φ' O
    hO hodd₂ eY
  exact ⟨J', O₀, hO₀, hA, hcard⟩

theorem exists_orbits_singleton_of_isPComponent_of_mulEquiv_cross (hX : Finite D.totalFixedGroup)
    {X : Type*} [Group X] (eqv : D.totalFixedGroup ≃* X) {J : Subgroup X}
    (hJ : CFSG.IsPComponent 2 J) {Y : Type} [Group Y] (φ : Y ≃* J) (O : Subgroup Y)
    [O.Normal] (hO : Odd (Nat.card O)) {F₂ : Type} [Field F₂] [Finite F₂]
    (hodd₂ : Odd (Nat.card F₂)) (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ (J' : Set.range D.classOrbit) (O₀ : Set (Fin τ.rank → ℤ)),
      O₀ ∈ (D.withOrbit J').orbits ∧ (D.withOrbit J').orbits = {O₀} ∧
        Nat.card F₂ = D.q ^ orbitCard O₀ := by
  set J₁ : Subgroup D.totalFixedGroup := J.map eqv.symm.toMonoidHom with hJ₁
  set J₀ : Subgroup (adjointGroup τ k) := J₁.map D.totalFixedGroup.subtype with hJ₀
  have hle : J₀ ≤ D.totalFixedGroup := Subgroup.map_subtype_le _
  have hsub : J₀.subgroupOf D.totalFixedGroup = J₁ :=
    Subgroup.comap_map_eq_self_of_injective D.totalFixedGroup.subtype_injective J₁
  have hcomp : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup) := by
    rw [hsub]
    exact isPComponent_map_of_isPComponent 2 eqv.symm hJ
  let φ' : Y ≃* J₀ := φ.trans ((J.equivMapOfInjective eqv.symm.toMonoidHom
    eqv.symm.injective).trans (J₁.equivMapOfInjective D.totalFixedGroup.subtype
      D.totalFixedGroup.subtype_injective))
  exact exists_orbits_singleton_of_isPComponent_cross D hX hle hcomp φ' O hO hodd₂ eY

theorem simpleRoots_orthogonal_of_orbits_eq {J' : Set.range D.classOrbit}
    {O₀ : Set (Fin τ.rank → ℤ)} (hA : (D.withOrbit J').orbits = {O₀}) {i : KernelComponent D.χ}
    (hi : i ∈ (J' : Set (KernelComponent D.χ))) :
    ∀ β ∈ simpleRoots (componentRoots D.χ i), ∀ β' ∈ simpleRoots (componentRoots D.χ i),
      β ≠ β' → iform β β' = 0 := by
  intro β hβ β' hβ' hne
  set D' := D.withOrbit J' with hD'
  have hΔ : ∀ γ ∈ simpleRoots (componentRoots D.χ i), γ ∈ D'.simpleRootsJ := fun γ hγ =>
    D'.mem_simpleRootsJ_iff.2 ⟨i, hi, hγ⟩
  have hO₀ : O₀ ∈ D'.orbits := by rw [hA]; exact Set.mem_singleton O₀
  have hmem : ∀ γ ∈ simpleRoots (componentRoots D.χ i), γ ∈ O₀ := fun γ hγ => by
    have h1 := D'.thetaOrbit_mem_orbits (hΔ γ hγ)
    rw [hA, Set.mem_singleton_iff] at h1
    rw [← h1]
    exact self_mem_thetaOrbit _ _
  have hβK : β ∈ kernelRoots D.χ := D'.mem_kernelRoots_of_mem_simpleRootsJ (hΔ β hβ)
  have hO₀β := D'.eq_thetaOrbit_of_mem_orbits hO₀ (hmem β hβ)
  exact D'.orbit_orthogonal β hβK β (self_mem_thetaOrbit _ _) β' (by rw [← hO₀β]; exact hmem β' hβ')
    hne

end TwoComponents
end CFSG.ClassicalInvolution.Upgrade
