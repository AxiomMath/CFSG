module

public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8D8
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.HardMathSupport.Lang.AnisoF4

section Arith

theorem not_dvd_pred_of_orderOf_eq_eight {p : ℕ} (hp : p.Prime) {q : ℕ} (hq : 1 ≤ q)
    (he : orderOf ((q : ℕ) : ZMod p) = 8) : ¬ p ∣ q - 1 := by
  have := Fact.mk hp
  intro hd
  have h : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
  rw [h, orderOf_one] at he
  omega

theorem not_dvd_of_orderOf_eq_eight {p : ℕ} (hp : p.Prime) {q : ℕ}
    (he : orderOf ((q : ℕ) : ZMod p) = 8) : ¬ p ∣ q := by
  have := Fact.mk hp
  intro hd
  have h : ((q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [h, orderOf_zero] at he
  omega

theorem ne_two_of_orderOf_eq_eight {p : ℕ} (hp : p.Prime) {q : ℕ}
    (he : orderOf ((q : ℕ) : ZMod p) = 8) : p ≠ 2 := by
  rintro rfl
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h ((q : ℕ) : ZMod 2) with h0 | h0
  · rw [h0, orderOf_zero] at he
    omega
  · rw [h0, orderOf_one] at he
    omega

end Arith

section Main


theorem iSup_d8Chain_le_closure_centralizers {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := ne_two_of_orderOf_eq_eight hp he
  have hpK : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_eq_eight hp he
  have hpq1 : ¬ p ∣ Nat.card K - 1 :=
    not_dvd_pred_of_orderOf_eq_eight hp Nat.card_pos he
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
      rw [hZ]
    exact hd.trans this
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 8 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hE8 : RankLE2 p (adjointGroup .E8 K) :=
    (sylowTorus_E8_eight K hp he).rankLE2 hp le_rfl
  have hrk : RankLE2 p (StatedProj (StatedOmega (StatedQuadPlus 8 K))) :=
    rankLE2_of_cover π hπsurj hπcop Ψ hΨcop hE8
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : spinGroup (quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ := exists_lift_elemAbelian Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← card_map_eq_of_disjoint Ψ' hdisE', hmapE', hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, card_map_eq_of_disjoint π (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthogonalPlusLow_of_residual orthSelfDualTwoBlocks (r := 8) (by norm_num) hp hp2
    hpK hrk Ebar hEbarea hcardEbar
  have hG := closure_centralizers_of_quotient π hπsurj hZ.le hπcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg

end Main

end CFSG.HardMathSupport.Lang.AnisoE8
