module

public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.MaximalNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.MaximalNormalElementaryAbelianCentralizer
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p n d : ℕ} {P : Type*} [Group P] {A : Subgroup P}

theorem isElementaryAbelian_of_nonempty_mulEquiv_pi
    (h : Nonempty (↥A ≃* (Fin d → Multiplicative (ZMod p)))) : IsElementaryAbelian p A := by
  obtain ⟨f⟩ := h
  refine isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun a b => f.injective (by simpa using mul_comm (f a) (f b)),
      fun x hx => ?_⟩
  have h1 : (⟨x, hx⟩ : ↥A) ^ p = 1 :=
    f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
  exact congrArg Subtype.val h1

theorem natCard_eq_pow_of_nonempty_mulEquiv_pi
    (h : Nonempty (↥A ≃* (Fin d → Multiplicative (ZMod p)))) : Nat.card A = p ^ d := by
  obtain ⟨f⟩ := h
  rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]

theorem nonempty_mulEquiv_pi_of_isElementaryAbelian (hp : p.Prime)
    (hA : IsElementaryAbelian p A) (hd : Nat.card A = p ^ d) :
    Nonempty (↥A ≃* (Fin d → Multiplicative (ZMod p))) := by
  have : IsMulCommutative ↥A := hA.isMulCommutative
  let _ : CommGroup ↥A := IsMulCommutative.instCommGroup
  exact nonempty_mulEquiv_pi_of_exponent hp
    (fun x => Subtype.ext (by simpa using hA.pow_eq_one x.2)) hd

theorem not_isCyclic_of_isElementaryAbelian_of_natCard_eq_pow [Finite P]
    (hp : p.Prime) (hA : IsElementaryAbelian p A) (hd : Nat.card A = p ^ d) (hd2 : 2 ≤ d) :
    ¬ IsCyclic P := by
  intro hc
  have hAc : IsCyclic ↥A := Subgroup.isCyclic A
  have hexp : Monoid.exponent ↥A ∣ p ^ 1 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hA.pow_eq_one x.2)
  rw [IsCyclic.exponent_eq_card, hd] at hexp
  have : d ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hexp
  omega

theorem exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hrank : 3 ≤ elementaryAbelianPRank p P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative ↥A ∧
      3 ≤ elementaryAbelianPRank p ↥A ∧ centralizer (A : Set P) = A := by
  have hfp := Fact.mk hp
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  have hPp : IsPGroup p P := IsPGroup.of_card hcard
  obtain ⟨E, hE⟩ := mem_elementaryAbelianRanks.1
    ((le_elementaryAbelianPRank_iff hp.one_lt).1 hrank)
  have hEea : IsElementaryAbelian p E := isElementaryAbelian_of_nonempty_mulEquiv_pi hE
  have hEcard : Nat.card E = p ^ 3 := natCard_eq_pow_of_nonempty_mulEquiv_pi hE
  have hPnc : ¬ IsCyclic P :=
    not_isCyclic_of_isElementaryAbelian_of_natCard_eq_pow hp hEea hEcard (by omega)
  obtain ⟨D₀, -, hD₀n, hD₀⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hPp ⊤
    (fun _ => hPnc (isCyclic_of_surjective (⊤ : Subgroup P).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩))
  have hD₀ea : IsElementaryAbelian p D₀ := isElementaryAbelian_of_nonempty_mulEquiv_pi hD₀
  have hD₀card : Nat.card D₀ = p ^ 2 := natCard_eq_pow_of_nonempty_mulEquiv_pi hD₀
  obtain ⟨D, hD₀D, hD⟩ := Set.Finite.exists_le_maximal
    (s := {B : Subgroup P | B.Normal ∧ IsElementaryAbelian p B}) (Set.toFinite _) ⟨hD₀n, hD₀ea⟩
  have hDn := hD.prop.1
  obtain ⟨e, he⟩ := hD.prop.2.exists_natCard_eq_pow hp
  have he2 : 2 ≤ e := by
    have h := Subgroup.card_le_of_le hD₀D
    rw [hD₀card, he] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  by_cases he3 : 3 ≤ e
  ·
    obtain ⟨A, hDA, hA⟩ :=
      exists_maximal_normal_isMulCommutative_ge hD.prop.1 hD.prop.2.isMulCommutative
    exact ⟨A, hA.prop.1, hA.prop.2,
      he3.trans (hD.prop.2.le_elementaryAbelianPRank hp he hDA),
      centralizer_eq_of_maximal_normal_isMulCommutative hp hcard hA⟩
  ·
    exfalso
    have he' : e = 2 := by omega
    subst he'
    obtain ⟨fD⟩ := nonempty_mulEquiv_pi_of_isElementaryAbelian hp hD.prop.2 he
    obtain ⟨fE⟩ := hE
    obtain ⟨K, hKle, hK⟩ := exists_elementaryAbelian_rank_two_le_inf_centralizer (D := D) (E := E)
      ⟨fD.trans (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod p).symm⟩
      ⟨fE.trans (MulEquiv.piMultiplicative fun _ : Fin 3 => ZMod p).symm⟩
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hK' : Nonempty (↥K ≃* (Fin 2 → Multiplicative (ZMod p))) := by
      obtain ⟨fK⟩ := hK
      exact ⟨fK.trans (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod p)⟩
    have hKea : IsElementaryAbelian p K := isElementaryAbelian_of_nonempty_mulEquiv_pi hK'
    have hKcard : Nat.card K = p ^ 2 := natCard_eq_pow_of_nonempty_mulEquiv_pi hK'
    have hKD : K ≤ D := fun x hx =>
      mem_of_mem_centralizer_of_pow_eq_one_of_maximal hp hodd hcard hD
        (Subgroup.mem_inf.1 (hKle hx)).2 (hKea.pow_eq_one hx)
    have hKeqD : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [he, hKcard])
    have hDE : D ≤ E := by rw [← hKeqD]; exact hKle.trans inf_le_left
    have hED : E ≤ D := fun x hx =>
      mem_of_mem_centralizer_of_pow_eq_one_of_maximal hp hodd hcard hD
        (hEea.le_centralizer hDE hx) (hEea.pow_eq_one hx)
    have h := Subgroup.card_le_of_le hED
    rw [hEcard, he] at h
    have h3 : (3 : ℕ) ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h
    omega

theorem exists_abelian_normal_forall_mem_of_three_le_elementaryAbelianPRank
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hrank : 3 ≤ elementaryAbelianPRank p P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative ↥A ∧ 3 ≤ elementaryAbelianPRank p ↥A ∧
      ∀ x : P, (∀ a ∈ A, x * a = a * x) ↔ x ∈ A := by
  obtain ⟨A, hAn, hAc, hArank, hAcent⟩ :=
    exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank hp hodd hcard hrank
  refine ⟨A, hAn, hAc, hArank, fun x => ⟨fun hx => hAcent ▸ mem_centralizer_coe_iff.2 hx,
    fun hx => mem_centralizer_coe_iff.1 (hAcent.ge hx)⟩⟩

theorem exists_abelian_normal_mulEquiv_pi_of_three_le_elementaryAbelianPRank
    (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card P = p ^ n)
    (hrank : 3 ≤ elementaryAbelianPRank p P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative ↥A ∧ centralizer (A : Set P) = A ∧
      ∃ B : Subgroup P, B ≤ A ∧ Nonempty (↥B ≃* (Fin 3 → Multiplicative (ZMod p))) := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨A, hAn, hAc, hArank, hAcent⟩ :=
    exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank hp hodd hcard hrank
  obtain ⟨B, hB⟩ := mem_elementaryAbelianRanks.1
    ((le_elementaryAbelianPRank_iff hp.one_lt).1 hArank)
  exact ⟨A, hAn, hAc, hAcent, B.map A.subtype, Subgroup.map_subtype_le B,
    ⟨(B.equivMapOfInjective A.subtype A.subtype_injective).symm.trans hB.some⟩⟩

theorem exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank_of_isPGroup
    [Finite P] (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hrank : 3 ≤ elementaryAbelianPRank p P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative ↥A ∧
      3 ≤ elementaryAbelianPRank p ↥A ∧ centralizer (A : Set P) = A := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank hp hodd hn hrank

end

end CFSG.FeitThompson
