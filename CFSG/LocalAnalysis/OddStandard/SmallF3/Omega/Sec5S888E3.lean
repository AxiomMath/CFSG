module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveGeneral

public section

open Subgroup
open scoped IsKleinFour

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X]

structure InvolAct (A : Subgroup X) (y : X) : Prop where
  mem : ∀ a ∈ A, y * a * y⁻¹ ∈ A
  sq : ∀ a ∈ A, y * y * a * (y * y)⁻¹ = a

@[expose] def ActsNontriv (A : Subgroup X) (y : X) : Prop :=
  ∃ a ∈ A, y * a * y⁻¹ ≠ a

private noncomputable def conjAut {A : Subgroup X} {y : X} (hy : InvolAct A y) : MulAut A where
  toFun a := ⟨y * (a : X) * y⁻¹, hy.mem a a.2⟩
  invFun a := ⟨y * (a : X) * y⁻¹, hy.mem a a.2⟩
  left_inv a := Subtype.ext (by convert hy.sq a a.2 using 1 <;> group)
  right_inv a := Subtype.ext (by convert hy.sq a a.2 using 1 <;> group)
  map_mul' a b := Subtype.ext (by
    show y * ((a : X) * (b : X)) * y⁻¹ = (y * (a : X) * y⁻¹) * (y * (b : X) * y⁻¹)
    group)

private lemma conjAut_mul_self {A : Subgroup X} {y : X} (hy : InvolAct A y) :
    conjAut hy * conjAut hy = 1 := by
  ext a
  show y * (y * (a : X) * y⁻¹) * y⁻¹ = (a : X)
  convert hy.sq a a.2 using 1 <;> group

private lemma actsNontriv_iff {A : Subgroup X} {y : X} (hy : InvolAct A y) :
    ActsNontriv A y ↔ conjAut hy ≠ 1 := by
  constructor
  · rintro ⟨a, ha, hne⟩ h
    apply hne
    have h' := congrArg (fun f : MulAut A => (f ⟨a, ha⟩ : A)) h
    simp only [MulAut.one_apply] at h'
    exact congrArg Subtype.val h'
  · intro h
    by_contra hcon
    simp only [ActsNontriv, not_exists, not_and, not_not] at hcon
    apply h
    ext a
    show y * (a : X) * y⁻¹ = (a : X)
    exact hcon (a : X) a.2

private lemma exists_unique_fixed_of_ne_one {A : Type*} [Group A] [IsKleinFour A]
    {f : MulAut A} (hf2 : f * f = 1) (hf : f ≠ 1) :
    ∃ e : A, e ≠ 1 ∧ f e = e ∧ ∀ c : A, f c = c → c = 1 ∨ c = e := by
  haveI : IsMulCommutative A := IsKleinFour.isMulCommutative
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ a := by
    by_contra h; push Not at h; exact hf (MulEquiv.ext h)
  have hff : f (f a) = a := by
    simpa [MulAut.mul_apply] using congrArg (fun g : MulAut A => g a) hf2
  have ha1 : a ≠ 1 := fun h => ha (by rw [h, map_one])
  refine ⟨a * f a, fun h => ha (mul_left_cancel (by rw [h, IsKleinFour.mul_self a])),
    (by rw [map_mul, hff]; exact mul_comm' (f a) a), ?_⟩
  intro c hc
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  by_cases hca : c = a
  · exact absurd (hca ▸ hc) ha
  by_cases hcfa : c = f a
  · rw [hcfa, hff] at hc
    exact absurd hc.symm ha
  · exact Or.inr (IsKleinFour.eq_mul_of_ne_all (G := A) ha1
      (fun h => ha1 (by rw [← hff, h, map_one])) (fun h => ha h.symm) hc1 hca hcfa)

private lemma card_fixed_of_ne_one {A : Type*} [Group A] [IsKleinFour A]
    {f : MulAut A} (hf2 : f * f = 1) (hf : f ≠ 1) :
    Nat.card {c : A // f c = c} = 2 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  obtain ⟨e, he1, hef, hfix⟩ := exists_unique_fixed_of_ne_one hf2 hf
  have hset : (Finset.univ.filter (fun c : A => f c = c)) = {1, e} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨fun hc => hfix c hc, by rintro (rfl | rfl); exacts [map_one f, hef]⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset]
  exact Finset.card_pair he1.symm

private lemma eq_of_comm_of_ne_one {A : Type*} [Group A] [IsKleinFour A]
    {f g : MulAut A} (hf2 : f * f = 1) (hg2 : g * g = 1)
    (hcomm : f * g = g * f) (hf : f ≠ 1) (hg : g ≠ 1) : f = g := by
  haveI : IsMulCommutative A := IsKleinFour.isMulCommutative
  obtain ⟨e, he1, hef, hfixf⟩ := exists_unique_fixed_of_ne_one hf2 hf
  obtain ⟨e', _, _, hfixg⟩ := exists_unique_fixed_of_ne_one hg2 hg
  have hge : g e = e := by
    have h : f (g e) = g e := by
      simpa [hef] using congrArg (fun h : MulAut A => h e) hcomm
    rcases hfixf (g e) h with h' | h'
    · exact absurd (g.injective (by rw [h', map_one])) he1
    · exact h'
  have hee' : e = e' := (hfixg e hge).elim (absurd · he1) id
  ext c
  by_cases hc1 : c = 1
  · rw [hc1, map_one, map_one]
  by_cases hce : c = e
  · rw [hce, hef, hge]
  have key : ∀ k : MulAut A, k e = e → k c ≠ c → k c = c * e := by
    intro k hke hkc
    exact IsKleinFour.eq_mul_of_ne_all (G := A) hc1 he1 hce
      (fun h => hc1 (k.injective (by rw [h, map_one])))
      hkc (fun h => hce (k.injective (by rw [h, hke])))
  rw [key f hef (fun h => (hfixf c h).elim hc1 (fun h' => hce h')),
    key g hge (fun h => (hfixg c h).elim hc1 (fun h' => hce (h'.trans hee'.symm)))]

private lemma mul_ne_one_iff {A : Type*} [Group A] [IsKleinFour A]
    {f g : MulAut A} (hf2 : f * f = 1) (hg2 : g * g = 1)
    (hcomm : f * g = g * f) : f * g ≠ 1 ↔ (f ≠ 1 ↔ g = 1) := by
  by_cases hf : f = 1; · subst hf; simp
  by_cases hg : g = 1; · subst hg; simp
  have hfg : f = g := eq_of_comm_of_ne_one hf2 hg2 hcomm hf hg
  subst hfg
  rw [hg2]
  exact ⟨fun h => absurd rfl h, fun h _ => hg (h.mp hg)⟩

theorem InvolAct.mul {A : Subgroup X} {y y' : X} (hy : InvolAct A y) (hy' : InvolAct A y')
    (hcomm : ∀ a ∈ A, y * y' * a * (y * y')⁻¹ = y' * y * a * (y' * y)⁻¹) :
    InvolAct A (y * y') := by
  refine ⟨?_, ?_⟩
  · intro a ha
    exact (by convert hy.mem (y' * a * y'⁻¹) (hy'.mem a ha) using 1 <;> group)
  · intro a ha
    have hz : y' * a * y'⁻¹ ∈ A := hy'.mem a ha
    have h1 : y * (y' * (y' * a * y'⁻¹) * y'⁻¹) * y⁻¹ =
        y' * (y * (y' * a * y'⁻¹) * y⁻¹) * y'⁻¹ := by
      convert hcomm (y' * a * y'⁻¹) hz using 1 <;> group
    calc
      (y * y') * (y * y') * a * ((y * y') * (y * y'))⁻¹
          = y * (y' * (y * (y' * a * y'⁻¹) * y⁻¹) * y'⁻¹) * y⁻¹ := by group
      _ = y * (y * (y' * (y' * a * y'⁻¹) * y'⁻¹) * y⁻¹) * y⁻¹ := by rw [← h1]
      _ = y * (y * a * y⁻¹) * y⁻¹ := by
            rw [show y' * (y' * a * y'⁻¹) * y'⁻¹ = a by
              convert hy'.sq a ha using 1 <;> group]
      _ = a := by convert hy.sq a ha using 1 <;> group

private lemma conjAut_mul {A : Subgroup X} {y y' : X} (hy : InvolAct A y) (hy' : InvolAct A y')
    (hcomm : ∀ a ∈ A, y * y' * a * (y * y')⁻¹ = y' * y * a * (y' * y)⁻¹) :
    conjAut (InvolAct.mul hy hy' hcomm) = conjAut hy * conjAut hy' := by
  ext a
  show (y * y') * (a : X) * (y * y')⁻¹ = y * (y' * (a : X) * y'⁻¹) * y⁻¹
  group

private lemma conjAut_mul_comm {A : Subgroup X} {y y' : X} (hy : InvolAct A y)
    (hy' : InvolAct A y')
    (hcomm : ∀ a ∈ A, y * y' * a * (y * y')⁻¹ = y' * y * a * (y' * y)⁻¹) :
    conjAut hy * conjAut hy' = conjAut hy' * conjAut hy := by
  ext a
  show y * (y' * (a : X) * y'⁻¹) * y⁻¹ = y' * (y * (a : X) * y⁻¹) * y'⁻¹
  convert hcomm (a : X) a.2 using 1 <;> group

theorem actsNontriv_mul_iff {A : Subgroup X} (hA : Nat.card A = 4) (hsq : ∀ a ∈ A, a * a = 1)
    {y y' : X} (hy : InvolAct A y) (hy' : InvolAct A y')
    (hcomm : ∀ a ∈ A, y * y' * a * (y * y')⁻¹ = y' * y * a * (y' * y)⁻¹) :
    ActsNontriv A (y * y') ↔ (ActsNontriv A y ↔ ¬ ActsNontriv A y') := by
  haveI : IsKleinFour A := isKleinFour_of_card_four_of_mul_self hA fun x => Subtype.ext (hsq x x.2)
  rw [actsNontriv_iff hy, actsNontriv_iff hy',
    actsNontriv_iff (InvolAct.mul hy hy' hcomm), conjAut_mul hy hy' hcomm, not_not]
  exact mul_ne_one_iff (conjAut_mul_self hy) (conjAut_mul_self hy')
    (conjAut_mul_comm hy hy' hcomm)

theorem card_fixed_of_actsNontriv {A : Subgroup X} (hA : Nat.card A = 4)
    (hsq : ∀ a ∈ A, a * a = 1) {y : X} (hy : InvolAct A y) (hn : ActsNontriv A y) :
    Nat.card {a : A // y * (a : X) * y⁻¹ = a} = 2 := by
  haveI : IsKleinFour A := isKleinFour_of_card_four_of_mul_self hA fun x => Subtype.ext (hsq x x.2)
  have hne : conjAut hy ≠ 1 := (actsNontriv_iff hy).mp hn
  have hfixed : Nat.card {a : A // conjAut hy a = a} = 2 :=
    card_fixed_of_ne_one (conjAut_mul_self hy) hne
  let e : {a : A // y * (a : X) * y⁻¹ = a} ≃ {a : A // conjAut hy a = a} :=
    Equiv.subtypeEquivRight fun a => by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h
  rw [Nat.card_congr e]
  exact hfixed

theorem not_actsNontriv_iff {A : Subgroup X} {y : X} :
    ¬ ActsNontriv A y ↔ ∀ a ∈ A, y * a * y⁻¹ = a := by
  simp only [ActsNontriv, not_exists, not_and, not_not]

end CFSG.OddStandard.SmallF3.Omega
