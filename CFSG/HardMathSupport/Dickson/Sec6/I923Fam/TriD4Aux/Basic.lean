module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem fixSubgroup_inv_eq {P : Type*} [Group P] (ψ : MulAut P) :
    fixSubgroup ψ⁻¹ = fixSubgroup ψ := by
  ext x
  show ψ⁻¹ x = x ↔ ψ x = x
  constructor
  · intro h
    calc ψ x = ψ (ψ⁻¹ x) := by rw [h]
      _ = x := MulAut.apply_inv_self _ ψ x
  · intro h
    calc ψ⁻¹ x = ψ⁻¹ (ψ x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ ψ x

theorem noL2Layer_inv_iff {P : Type} [Group P] (ψ : MulAut P) :
    NoL2Layer ψ⁻¹ ↔ NoL2Layer ψ := by
  unfold NoL2Layer
  rw [fixSubgroup_inv_eq]

theorem noL2Layer_of_conj {P : Type} [Group P] [Finite P] (γ f : MulAut P)
    (h : NoL2Layer (γ * f * γ⁻¹)) : NoL2Layer f := by
  have := noL2Layer_conj γ⁻¹ h
  have e : γ⁻¹ * (γ * f * γ⁻¹) * (γ⁻¹)⁻¹ = f := by group
  rwa [e] at this

theorem not_typeL2_of_order {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (ht : t ≠ .Tits) (hA : ¬ (t = .PSL ∧ n = 2))
    (hM : Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f))
    (hZ : Subgroup.center X = ⊥) {r : ℕ} (hr : 10 ≤ r) : ¬ IsTypeL2 r X := by
  intro hT
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card X hT
  have hcard : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
  exact lie_order_ne_l2 hadm ht hA hM hr (fun h => by rw [← hcard]; exact hodd h)
    (fun h => by rw [← hcard]; exact (heven h).1)

theorem cube_sub_mono {R r : ℕ} (hR : 1 ≤ R) (h : R ≤ r) : R ^ 3 - R ≤ r ^ 3 - r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : d ≤ 3 * R ^ 2 * d := by
    have : 1 ≤ 3 * R ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul_right d this]
  have h2 : R ^ 3 + (R + d) ≤ (R + d) ^ 3 + R := by
    nlinarith [Nat.zero_le (3 * R * d ^ 2), Nat.zero_le (d ^ 3)]
  have h3 : R ≤ R ^ 3 := Nat.le_self_pow (by norm_num) R
  have h4 : R + d ≤ (R + d) ^ 3 := Nat.le_self_pow (by norm_num) (R + d)
  omega

theorem not_typeL2_of_card_dvd {X : Type} [Group X] [Finite X] {N : ℕ} (hN0 : 0 < N)
    (hN : Nat.card X ∣ N) (R : ℕ) (hRN : 2 * N < R ^ 3 - R)
    (hcheck : ∀ r : ℕ, 10 ≤ r → r < R →
      (Odd r → ¬ ((r ^ 3 - r) / 2 ∣ N)) ∧ (Even r → ¬ ((r ^ 3 - r) ∣ N)))
    {r : ℕ} (hr : 10 ≤ r) : ¬ IsTypeL2 r X := by
  intro hT
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card X hT
  have hdvd : Nat.card (X ⧸ Subgroup.center X) ∣ N :=
    (Subgroup.card_quotient_dvd_card (Subgroup.center X)).trans hN
  have hMle : Nat.card (X ⧸ Subgroup.center X) ≤ N := Nat.le_of_dvd hN0 hdvd
  have hR1 : 1 ≤ R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · subst h
      simp at hRN
    · exact h
  have hrR : r < R := by
    by_contra hcon
    push Not at hcon
    have h1 : R ^ 3 - R ≤ r ^ 3 - r := cube_sub_mono hR1 hcon
    have hr1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    rcases Nat.even_or_odd r with hev | hod
    · have := (heven hev).1
      omega
    · have := hodd hod
      omega
  rcases Nat.even_or_odd r with hev | hod
  · refine (hcheck r hr hrR).2 hev ?_
    have := (heven hev).1
    have hr1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    have h3 : r ^ 3 - r = Nat.card (X ⧸ Subgroup.center X) := by omega
    rw [h3]
    exact hdvd
  · refine (hcheck r hr hrR).1 hod ?_
    have := hodd hod
    have hr1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    have h3 : (r ^ 3 - r) / 2 = Nat.card (X ⧸ Subgroup.center X) := by omega
    rw [h3]
    exact hdvd

theorem noL2Layer_of_card_dvd {P : Type} [Group P] [Finite P] (ψ : MulAut P) {N : ℕ}
    (hN0 : 0 < N) (hN : Nat.card ↥(fixSubgroup ψ) ∣ N) (R : ℕ) (hRN : 2 * N < R ^ 3 - R)
    (hcheck : ∀ r : ℕ, 10 ≤ r → r < R →
      (Odd r → ¬ ((r ^ 3 - r) / 2 ∣ N)) ∧ (Even r → ¬ ((r ^ 3 - r) ∣ N))) : NoL2Layer ψ := by
  intro A hA r hr hT
  have hAle : A ≤ fixSubgroup ψ := hA.1
  have h1 : Nat.card ↥A ∣ N := (Subgroup.card_dvd_of_le hAle).trans hN
  have h2 : Nat.card (barOf 3 A) ∣ Nat.card ↥A := Subgroup.card_quotient_dvd_card _
  exact not_typeL2_of_card_dvd hN0 (h2.trans h1) R hRN hcheck hr hT

theorem isSimple_of_isQuasisimple_center_bot {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) : IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI := hs
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

theorem isSolvable_quotient_of_eq' {A : Type*} [Group A] {X Y : Subgroup A} [X.Normal]
    [Y.Normal] (hXY : X = Y) (h : Group.IsSolvable (A ⧸ X)) : Group.IsSolvable (A ⧸ Y) := by
  subst hXY
  exact h

theorem noL2Layer_of_equiv_normal_simple {P R : Type} [Group P] [Finite P] [Group R]
    (δ : MulAut P) (e : ↥(fixSubgroup δ) ≃* R) (S : Subgroup R) [S.Normal]
    (hsol : Group.IsSolvable (R ⧸ S)) (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥S) : NoL2Layer δ := by
  set X := fixSubgroup δ with hX
  set S' : Subgroup ↥X := S.comap e.toMonoidHom with hS'
  haveI : S'.Normal := Subgroup.normal_comap _
  set J : Subgroup P := S'.map X.subtype with hJ
  have hJC : J ≤ X := Subgroup.map_subtype_le S'
  have hJsub : J.subgroupOf X = S' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective S'
  haveI : (J.subgroupOf X).Normal := by rw [hJsub]; infer_instance
  have hsolX : Group.IsSolvable (↥X ⧸ J.subgroupOf X) := by
    refine isSolvable_quotient_of_eq' hJsub.symm ?_
    let f : (↥X ⧸ S') →* (R ⧸ S) := QuotientGroup.map S' S e.toMonoidHom (fun x hx => hx)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H x =>
        have : e x ∈ S := (QuotientGroup.eq_one_iff _).1 hx
        exact (QuotientGroup.eq_one_iff x).2 this
    exact Group.isSolvable_of_isSolvable_injective hf
  have hSS : S'.map e.toMonoidHom = S := Subgroup.map_comap_eq_self_of_surjective e.surjective S
  let eS' : ↥S' ≃* ↥S :=
    (Subgroup.equivMapOfInjective S' e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hSS)
  let eJ : ↥J ≃* ↥S := (Subgroup.equivMapOfInjective S' X.subtype X.subtype_injective).symm.trans eS'
  haveI := hs
  refine OrthAux.noL2Layer_of_normal_simple δ J hJC hsolX eJ.isSimpleGroup ?_ fun r hr hT =>
    hL2 r hr (l2fld_isTypeL2_of_mulEquiv eJ hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨eJ.symm a, eJ.symm b, fun h => hab (by
    have := congrArg eJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
