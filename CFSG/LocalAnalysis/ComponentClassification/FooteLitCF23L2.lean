module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Assembly.LowTwoRank

theorem not_prime_small_ord {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q) : ¬ (q * (q ^ 2 - 1) / 2).Prime := by
  have h2 : 2 ∣ q ^ 2 - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hq.pow odd_one)
  rw [Nat.mul_div_assoc q h2, Nat.prime_mul_iff]
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  omega

theorem simple_of_psl2 {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (h5 : 5 ≤ p ^ e) (hm : Blueprint.LieModel X .PSL 2 p e) :
    IsSimpleGroup X ∧ ∃ x y : X, x * y ≠ y * x := by
  have hs : IsSimpleGroup X := (LieType.Simplicity.fam_classical_converse X
    ⟨.PSL, 2, p, e, RestrictedStd.statedClassicalModel_of_lieModel_PSL hm⟩).2.2
  refine ⟨hs, ?_⟩
  by_contra hc
  push Not at hc
  have : IsMulCommutative X := ⟨⟨hc⟩⟩
  have hpr := Group.is_simple_iff_prime_card.mp hs
  rcases card_small (Or.inl ⟨p, e, hp, hp2, he, h5, hm⟩) with ⟨q, hq, hq5, hX⟩ | hX
  · rw [hX] at hpr
    exact not_prime_small_ord hq hq5 hpr
  · rw [hX] at hpr
    exact absurd hpr (by norm_num)

theorem psl2 : CF23InnerFusionFor fun Y _ =>
    ∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ 5 ≤ p ^ e ∧ Blueprint.LieModel Y .PSL 2 p e := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ _ _ hexc
  obtain ⟨p, e, hp, hp2, he, h5, hm⟩ := hY
  exfalso
  apply hexc
  have := hN
  have := Fact.mk hp
  obtain ⟨-, -, hK4, K, _, _, hK, ⟨φ⟩⟩ :=
    RestrictedStd.exists_coordinateG_of_statedClassicalModel'
      (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm)
  obtain ⟨hs, hnab⟩ := simple_of_psl2 hp hp2 he h5 hm
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  obtain ⟨hev, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJ0, hJm, -⟩ :=
    SymmetricLocal.faithful_projective_linear_two_socle_involution_component_model hs hnab hC hα
      hJN hJc he hK hK4 φ
  let eZ : ↥J ≃* ↥J ⧸ center ↥J := MulEquiv.ofBijective (QuotientGroup.mk' (center ↥J))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hJ0),
      QuotientGroup.mk'_surjective _⟩
  have hodd : (p ^ (e / 2)) % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  obtain ⟨r, hr⟩ := hev
  refine Or.inr (Or.inr ⟨p, e / 2, hp, hp2, by omega, by omega, Or.inl ⟨by decide,
    SectionRank.statedClassicalModel_of_mulEquiv eZ.symm hJm⟩, ?_⟩)
  rwa [show 2 * (e / 2) = e by omega]

end CFSG.ComponentClassification.GSThmB.CF23I
