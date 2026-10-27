module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GroupTheory.SteinbergBS

open Subgroup

variable {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]

omit hp in
theorem isElementaryAbelian_of_le' {H K : Subgroup P} [IsElementaryAbelian p K] (hHK : H ≤ K) :
    IsElementaryAbelian p H := CFSG.IsElementaryAbelian.of_le inferInstance hHK

theorem pow_le_of_dvd_card_GL_two {k : ℕ} (h : p ^ k ∣ (p ^ 2 - 1) * (p ^ 2 - p)) : p ^ k ≤ p := by
  have hp1 : 1 < p := hp.out.one_lt
  have hfac : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
    have h2 : p ^ 2 - p = p * (p - 1) := by
      rw [Nat.mul_sub, mul_one, sq]
    rw [h2]
    ring
  have hndvd : ¬ p ∣ (p ^ 2 - 1) * (p - 1) := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h1 | h1
    · have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
      have h3 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h2 h1
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h3
      exact hp.out.one_lt.ne' (Nat.dvd_one.1 h3)
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
  have hcop : Nat.Coprime (p ^ k) ((p ^ 2 - 1) * (p - 1)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd)
  rw [hfac] at h
  exact Nat.le_of_dvd hp.out.pos (hcop.dvd_of_dvd_mul_right h)

theorem index_centralizer_le [Finite P] (hP : IsPGroup p P) (V : Subgroup P) [V.Normal]
    [IsElementaryAbelian p V] (hV : Nat.card V = p ^ 2) :
    (centralizer (V : Set P)).index ≤ p := by
  have hker : (MulAut.conjNormal : P →* MulAut V).ker = centralizer (V : Set P) := by
    ext x
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro h v hv
      have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : P)) h
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc v * x = x * v * x⁻¹ * x := by rw [h1]
        _ = x * v := by group
    · intro h
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h v v.2, mul_inv_cancel_right]
  have hcomm : ∀ a b : V, a * b = b * a := fun a b => mul_comm' a b
  have hpow : ∀ a : V, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact elemPow_eq_one_of_isElementaryAbelian (A := V) (a : P) a.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hV
  have hAut : Nat.card (MulAut V) = (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp [Fin.prod_univ_succ]
  have hdvd : (centralizer (V : Set P)).index ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [← hker, Subgroup.index_ker, ← hAut]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := hP.index (centralizer (V : Set P))
  rw [hk] at hdvd ⊢
  exact pow_le_of_dvd_card_GL_two hdvd

theorem normal_plane_centralizer_rank_three [Finite P] (hP : IsPGroup p P) (V A : Subgroup P)
    [V.Normal] [IsElementaryAbelian p V] (hV : Nat.card V = p ^ 2) [IsElementaryAbelian p A]
    (hA : Nat.card A = p ^ 3) :
    (centralizer (V : Set P)).Normal ∧ V ≤ centralizer (V : Set P) ∧
      (centralizer (V : Set P)).index ≤ p ∧
      p ^ 2 ≤ Nat.card ↥(A ⊓ centralizer (V : Set P)) ∧
      (A ⊓ centralizer (V : Set P)) ⊔ V ≤ centralizer (V : Set P) ∧
      V ≤ (A ⊓ centralizer (V : Set P)) ⊔ V ∧
      IsElementaryAbelian p ↥((A ⊓ centralizer (V : Set P)) ⊔ V) ∧
      p ^ 3 ≤ Nat.card ↥((A ⊓ centralizer (V : Set P)) ⊔ V) ∧
      3 ≤ CFSG.pRank p ↥(centralizer (V : Set P)) := by
  set C := centralizer (V : Set P) with hC
  set B := A ⊓ C with hB
  have hp1 : 1 < p := hp.out.one_lt
  have hVC : V ≤ C := le_centralizer V
  have hidx := index_centralizer_le hP V hV
  have hBcard : p ^ 2 ≤ Nat.card B := by
    have h1 := relIndex_mul_card C A
    have h2 : C.relIndex A ≤ p :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (relIndex_dvd_index_of_normal C A)).trans hidx
    rw [inf_comm, hA] at h1
    by_contra hlt
    push Not at hlt
    have h3 : C.relIndex A * Nat.card B < p * p ^ 2 :=
      Nat.mul_lt_mul_of_le_of_lt h2 hlt hp.out.pos
    rw [hB, h1] at h3
    exact absurd h3 (by rw [← pow_succ']; exact lt_irrefl _)
  have : IsElementaryAbelian p B := isElementaryAbelian_of_le' (K := A) inf_le_left
  have hBC : B ≤ centralizer (V : Set P) := inf_le_right
  have hU : IsElementaryAbelian p ↥(B ⊔ V) := by
    rw [sup_comm]
    exact IsElementaryAbelian.sup_of_le_centralizer hBC
  have hUC : B ⊔ V ≤ C := sup_le hBC hVC
  have hVU : V ≤ B ⊔ V := le_sup_right
  have hUcard : p ^ 3 ≤ Nat.card ↥(B ⊔ V) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p ↥(B ⊔ V)).exists_card_eq
    have hVle : p ^ 2 ≤ p ^ k := by
      rw [← hV, ← hk]
      exact Subgroup.card_le_of_le hVU
    have hk3 : k < 3 := by
      rw [hk] at hlt
      exact (Nat.pow_lt_pow_iff_right hp1).1 hlt
    have hk2 : k = 2 := le_antisymm (by omega) ((Nat.pow_le_pow_iff_right hp1).1 hVle)
    have hUV : V = B ⊔ V := Subgroup.eq_of_le_of_card_ge hVU (by rw [hk, hk2, hV])
    have hBV : B = V := (Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hUV.symm.le)
      (by rw [hV]; exact hBcard))
    have hVA : V ≤ A := hBV ▸ inf_le_left
    have hAC : A ≤ C := fun a ha => mem_centralizer_iff.2 fun v hv => by
      have h := mul_comm' (⟨v, hVA hv⟩ : A) ⟨a, ha⟩
      exact congrArg Subtype.val h
    have hBA : B = A := inf_of_le_left hAC
    have h1 : Nat.card A = p ^ 2 := by rw [← hBA, hBV, hV]
    rw [hA] at h1
    have h3 : (3 : ℕ) = 2 := Nat.pow_right_injective hp.out.two_le h1
    omega
  have hrank : 3 ≤ CFSG.pRank p C := by
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p ↥(B ⊔ V)).exists_card_eq
    have hk3 : 3 ≤ k := by
      rw [hk] at hUcard
      exact (Nat.pow_le_pow_iff_right hp1).1 hUcard
    have : IsElementaryAbelian p ((B ⊔ V).subgroupOf C) := IsElementaryAbelian.subgroupOf hUC
    have hmem : k ∈ {r : ℕ | ∃ E : Subgroup C, IsElementaryAbelian p E ∧ Nat.card E = p ^ r} :=
      ⟨(B ⊔ V).subgroupOf C, inferInstance, by
        rw [← hk]
        exact Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv⟩
    have hbdd : BddAbove {r : ℕ | ∃ E : Subgroup C, IsElementaryAbelian p E ∧
        Nat.card E = p ^ r} := by
      refine ⟨Nat.card C, ?_⟩
      rintro r ⟨E, -, hE⟩
      have h1 : r < p ^ r := Nat.lt_pow_self hp1
      have h2 : Nat.card E ≤ Nat.card C := Subgroup.card_le_card_group E
      change r ≤ Nat.card C
      omega
    exact hk3.trans (le_csSup hbdd hmem)
  exact ⟨normal_centralizer, hVC, hidx, hBcard, hUC, hVU, hU, hUcard, hrank⟩

end CFSG.GroupTheory.SteinbergBS
