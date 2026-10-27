module

public import CFSG.FeitThompson.Local.SecondCenterTorsionNoncyclic
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.MaximalPlaneCentralizerPrimeTorsion
import CFSG.FeitThompson.Local.NormalPlaneNotMaximalHighRank
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
public import CFSG.FeitThompson.Local.HighRankCentralTorsionLine

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped commutatorElement

variable {p : ℕ} {R : Type*} [Group R] {E : Subgroup R}

theorem maximal_isElementaryAbelian_iff_maximal :
    Maximal (IsElementaryAbelian p) E ↔
      Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E := by
  simp only [Maximal, isElementaryAbelian_iff]

theorem not_isCyclic_of_three_le_elementaryAbelianPRank [Finite R] (hp : p.Prime)
    (hrank : 3 ≤ elementaryAbelianPRank p R) : ¬ IsCyclic R := by
  intro hcyc
  obtain ⟨H, ⟨f⟩⟩ := exists_subgroup_mulEquiv_of_elementaryAbelianPRank (p := p) (X := R) hp.one_lt
  have hcard : Nat.card ↥H = p ^ elementaryAbelianPRank p R := by
    rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
  have : IsCyclic ↥H := Subgroup.isCyclic_of_le (le_top (a := H))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥H)
  have hgp : g ^ p = 1 := f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
  have h3 : p ^ 3 ≤ p := Nat.le_of_dvd hp.pos
    (dvd_trans (pow_dvd_pow p hrank) (by rw [← hcard, ← hg]; exact orderOf_dvd_of_pow_eq_one hgp))
  have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h4
  omega

private theorem natCard_range_dvd_of_mulAut_plane [Fact p.Prime] {A : Type*} [Group A]
    [Finite A] {Q : Type*} [Group Q] (hQ : IsPGroup p Q)
    (e : A ≃* Multiplicative (Fin 2 → ZMod p)) (f : Q →* MulAut A) :
    Nat.card f.range ∣ p := by
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p f.range :=
    IsPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective (hG := hQ)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p)).1 hpg
  have hdvd : p ^ j ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
    rw [← natCard_mulAut_eq_natCard_GL e, ← hj]
    exact natCard_range_dvd_natCard_codomain f
  have hj1 : j ≤ 1 := (pow_dvd_card_GL_two_zmod_iff p).1 hdvd
  rw [hj]
  interval_cases j <;> simp

theorem secondCenterTorsion_le_normalizer (hodd : Odd p) (hZE : centerTorsionBy R p ≤ E) :
    secondCenterTorsion p R ≤ normalizer (E : Set R) := by
  have key : ∀ w ∈ secondCenterTorsion p R, ∀ h ∈ E, w * h * w⁻¹ ∈ E := by
    intro w hw h hh
    have hc : ⁅w, h⁆ ∈ centerTorsionBy R p :=
      commutator_secondCenterTorsion_top_le_centerTorsionBy hodd
        (commutator_mem_commutator hw (mem_top h))
    have heq : w * h * w⁻¹ = ⁅w, h⁆ * h := by rw [commutatorElement_def]; group
    rw [heq]
    exact mul_mem (hZE hc) hh
  intro w hw
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key w hw h hh, fun hh => ?_⟩
  simpa [mul_assoc] using key w⁻¹ (inv_mem hw) _ hh

theorem normal_of_le_secondCenterTorsion (hodd : Odd p) (hZE : centerTorsionBy R p ≤ E)
    (hEW : E ≤ secondCenterTorsion p R) : E.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc : ⁅n, g⁆ ∈ centerTorsionBy R p :=
    commutator_secondCenterTorsion_top_le_centerTorsionBy hodd
      (commutator_mem_commutator (hEW hn) (mem_top g))
  have heq : g * n * g⁻¹ = ⁅n, g⁆⁻¹ * n := by rw [commutatorElement_def]; group
  rw [heq]
  exact mul_mem (inv_mem (hZE hc)) hn

variable [Finite R]

theorem inf_centralizer_secondCenterTorsion_eq_centerTorsionBy (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    secondCenterTorsion p R ⊓ centralizer (E : Set R) = centerTorsionBy R p := by
  have hfp := Fact.mk hp
  set W := secondCenterTorsion p R with hW
  set C := W ⊓ centralizer (E : Set R) with hC
  have hZE : centerTorsionBy R p ≤ E := centerTorsionBy_le_of_maximal hE
  have hZcard : Nat.card (centerTorsionBy R p) = p :=
    natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have hle : C ≤ E := fun x hx =>
    mem_of_maximal_of_mem_centralizer_of_pow_eq_one hE hx.2
      (pow_eq_one_of_mem_secondCenterTorsion hodd hx.1)
  have hZle : centerTorsionBy R p ≤ C :=
    le_inf centerTorsionBy_le_secondCenterTorsion fun z hz =>
      Subgroup.center_le_centralizer _ (centerTorsionBy_le_center p hz)
  have hne : C ≠ E := by
    intro heq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 hRp
    have hEW : E ≤ W := heq ▸ inf_le_left
    have : E.Normal := normal_of_le_secondCenterTorsion hodd hZE hEW
    exact not_maximal_isElementaryAbelian_of_normal_of_natCard_eq_sq hp hodd hn hrank
      (isElementaryAbelian_iff.2 hE.prop) hplane (maximal_isElementaryAbelian_iff_maximal.2 hE)
  refine (Subgroup.eq_of_le_of_card_ge hZle ?_).symm
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1 (hplane ▸ Subgroup.card_dvd_of_le hle)
  have hZC : Nat.card ↥(centerTorsionBy R p) ≤ Nat.card ↥C := Subgroup.card_le_of_le hZle
  rw [hZcard, hk] at hZC
  rw [hZcard, hk]
  interval_cases k
  · simp only [pow_zero] at hZC
    have := hp.one_lt; omega
  · rw [pow_one]
  · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hplane, hk])) hne

theorem natCard_secondCenterTorsion_eq_sq (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    Nat.card (secondCenterTorsion p R) = p ^ 2 := by
  have hfp := Fact.mk hp
  set W := secondCenterTorsion p R with hW
  have hZE : centerTorsionBy R p ≤ E := centerTorsionBy_le_of_maximal hE
  have hZcard : Nat.card (centerTorsionBy R p) = p :=
    natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have hWN : W ≤ normalizer (E : Set R) := secondCenterTorsion_le_normalizer hodd hZE
  set f := conjOnNormalized E hWN with hf
  have hker : Nat.card ↥f.ker = p := by
    rw [hf, ker_conjOnNormalized, natCard_subgroupOf_eq_natCard_inf, inf_comm,
      inf_centralizer_secondCenterTorsion_eq_centerTorsionBy hp hodd hRp hE hplane hrank, hZcard]
  have heE : ↥E ≃* Multiplicative (Fin 2 → ZMod p) :=
    (nonempty_mulEquiv_pi_of_isElementaryAbelian hp (isElementaryAbelian_iff.2 hE.prop)
      hplane).some.trans (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod p).symm
  have hrangedvd : Nat.card ↥f.range ∣ p :=
    natCard_range_dvd_of_mulAut_plane (hRp.to_subgroup W) heE f
  have hmul : Nat.card ↥f.range * Nat.card ↥f.ker = Nat.card ↥W := natCard_range_mul_natCard_ker f
  have hub : Nat.card ↥W ≤ p ^ 2 := by
    rw [← hmul, hker, pow_two]
    exact Nat.mul_le_mul_right p (Nat.le_of_dvd hp.pos hrangedvd)
  obtain ⟨B, hBW, hBcard, -⟩ := exists_le_secondCenterTorsion_natCard_eq_sq hp hodd hRp
    (not_isCyclic_of_three_le_elementaryAbelianPRank hp hrank)
  have hlb : p ^ 2 ≤ Nat.card ↥W := hBcard ▸ Subgroup.card_le_of_le hBW
  omega

theorem isElementaryAbelian_and_natCard_eq_sq_secondCenterTorsion (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    IsElementaryAbelian p (secondCenterTorsion p R) ∧
      Nat.card (secondCenterTorsion p R) = p ^ 2 := by
  have hfp := Fact.mk hp
  have hWcard := natCard_secondCenterTorsion_eq_sq hp hodd hRp hE hplane hrank
  exact ⟨isElementaryAbelian_iff.2
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hWcard,
      fun x hx => pow_eq_one_of_mem_secondCenterTorsion hodd hx⟩, hWcard⟩

theorem not_le_centralizer_secondCenterTorsion (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    ¬ E ≤ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) := by
  intro hET
  have hWC : secondCenterTorsion p R ≤ centralizer (E : Set R) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro g hg
    exact ((mem_centralizer_iff.1 (hET hg)) w hw).symm
  have h1 : secondCenterTorsion p R = centerTorsionBy R p := by
    rw [← inf_centralizer_secondCenterTorsion_eq_centerTorsionBy hp hodd hRp hE hplane hrank,
      inf_eq_left.2 hWC]
  have h2 : Nat.card (secondCenterTorsion p R) = p := by
    rw [h1]; exact natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have h3 := natCard_secondCenterTorsion_eq_sq hp hodd hRp hE hplane hrank
  rw [h2, pow_two] at h3
  nlinarith [hp.one_lt]

theorem characteristic_and_index_centralizer_secondCenterTorsion (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    (centralizer ((secondCenterTorsion p R : Subgroup R) : Set R)).Characteristic ∧
      (centralizer ((secondCenterTorsion p R : Subgroup R) : Set R)).index = p := by
  have hfp := Fact.mk hp
  set W := secondCenterTorsion p R with hW
  obtain ⟨hWea, hWcard⟩ :=
    isElementaryAbelian_and_natCard_eq_sq_secondCenterTorsion hp hodd hRp hE hplane hrank
  have heW : ↥W ≃* Multiplicative (Fin 2 → ZMod p) :=
    (nonempty_mulEquiv_pi_of_isElementaryAbelian hp hWea hWcard).some.trans
      (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod p).symm
  set f : R →* MulAut ↥W := MulAut.conjNormal with hf
  have hidx : (centralizer (W : Set R)).index = Nat.card ↥f.range := by
    rw [← ker_conjNormal W, Subgroup.index_ker]
  have hdvd : Nat.card ↥f.range ∣ p := natCard_range_dvd_of_mulAut_plane hRp heW f
  refine ⟨inferInstance, ?_⟩
  have hne1 : (centralizer (W : Set R)).index ≠ 1 := fun h =>
    not_le_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank
      (by rw [Subgroup.index_eq_one.1 h]; exact le_top)
  rw [hidx] at hne1 ⊢
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact absurd h hne1
  · exact h

theorem secondCenterTorsion_plane_spec (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    (IsElementaryAbelian p (secondCenterTorsion p R) ∧
        Nat.card (secondCenterTorsion p R) = p ^ 2) ∧
      secondCenterTorsion p R ⊓ centralizer (E : Set R) = centerTorsionBy R p ∧
      ¬ E ≤ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) ∧
      (centralizer ((secondCenterTorsion p R : Subgroup R) : Set R)).Characteristic ∧
      (centralizer ((secondCenterTorsion p R : Subgroup R) : Set R)).index = p :=
  ⟨isElementaryAbelian_and_natCard_eq_sq_secondCenterTorsion hp hodd hRp hE hplane hrank,
    inf_centralizer_secondCenterTorsion_eq_centerTorsionBy hp hodd hRp hE hplane hrank,
    not_le_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank,
    (characteristic_and_index_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank).1,
    (characteristic_and_index_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank).2⟩

end

end CFSG.FeitThompson
