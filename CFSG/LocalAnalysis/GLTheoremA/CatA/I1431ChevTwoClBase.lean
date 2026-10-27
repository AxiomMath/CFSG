module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.RkYQuot
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem cl_fixSubgroup_conj_eq_centralizer {S : Type} [Group S] (x : S) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set S) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem cl_primePower_card_two {q : TauCeti.PrimePower} (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  rw [TauCeti.PrimePower.card_def] at h
  exact (Nat.Prime.pow_eq_iff Nat.prime_two).1 h

theorem cl_center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hn : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · obtain ⟨a, c, hac⟩ := hn
    exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c)) a) hac

theorem cl_card_psimple_dvd {S : Type} [Group S] [Finite S] (J : Subgroup S) :
    Nat.card (PSimple 3 J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card (Subgroup.center (PQuot 3 J))).trans
    (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥J))

theorem three_pow_five_dvd_card_of_pumpup {S : Type} [Group S] [Finite S] {x : S} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (J : Subgroup S) (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J)
    (hT : catalogIs (PSimple 3 J) S9.isU4two) : 3 ^ 5 ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc : J ≤ Subgroup.centralizer ({x} : Set S) := by
    rw [← cl_fixSubgroup_conj_eq_centralizer]
    exact hJ.1
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcard : Nat.card (PSimple 3 J) = 25920 :=
    CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT
  have hd1 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have hd2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have hJS : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
  have hcomm : ∀ j : J, x * (j : S) = (j : S) * x := fun j =>
    Subgroup.mem_centralizer_iff.1 (hJc j.2) x rfl
  by_cases hxJ : x ∈ J
  · set y : J := ⟨x, hxJ⟩ with hy
    have hyo : orderOf y = 3 := by rw [← Subgroup.orderOf_coe, hy]; exact hxo
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    have hcen : (QuotientGroup.mk y : PQuot 3 J) ∈ Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hcomm j).symm
    have hne : (QuotientGroup.mk y : PQuot 3 J) ≠ 1 := by
      intro h
      have hmem : y ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff y).1 h
      have h3 : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
        have := orderOf_dvd_natCard (⟨y, hmem⟩ : GLAPPrimeCore 3 ↥J)
        rwa [Subgroup.orderOf_mk, hyo] at this
      have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) :=
        CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
    have h3bar : (QuotientGroup.mk y : PQuot 3 J) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one]
    have hordbar : orderOf (QuotientGroup.mk y : PQuot 3 J) = 3 := orderOf_eq_prime h3bar hne
    have h3Z : 3 ∣ Nat.card (Subgroup.center (PQuot 3 J)) := by
      have := orderOf_dvd_natCard
        (⟨(QuotientGroup.mk y : PQuot 3 J), hcen⟩ : Subgroup.center (PQuot 3 J))
      rwa [Subgroup.orderOf_mk, hordbar] at this
    have hsplit : Nat.card (PQuot 3 J) =
        Nat.card (PSimple 3 J) * Nat.card (Subgroup.center (PQuot 3 J)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h5 : 3 ^ 5 ∣ Nat.card (PQuot 3 J) := by
      rw [hsplit, hcard]
      exact (by norm_num : 3 ^ 5 ∣ 25920 * 3).trans (Nat.mul_dvd_mul_left 25920 h3Z)
    exact h5.trans (hd1.trans hJS)
  · have h3J : 3 ^ 4 ∣ Nat.card J := by
      have : 3 ^ 4 ∣ Nat.card (PSimple 3 J) := by rw [hcard]; norm_num
      exact this.trans ((hd2).trans hd1)
    set Z : Subgroup S := Subgroup.zpowers x with hZ
    have hcommZ : ∀ (j : J) (z : Z), Commute (J.subtype j) (Z.subtype z) := by
      rintro j ⟨z, hz⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact Commute.zpow_right (show Commute (j : S) x from (hcomm j).symm) k
    have hZcard : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hxo]
    haveI : Fact (Nat.card Z).Prime := ⟨by rw [hZcard]; exact Nat.prime_three⟩
    have hJZ : ∀ z : Z, (z : S) ∈ J → z = 1 := by
      intro z hz
      rcases (J.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with h | h
      · have : z ∈ J.subgroupOf Z := hz
        rw [h] at this
        exact this
      · exfalso
        have : (⟨x, Subgroup.mem_zpowers x⟩ : Z) ∈ J.subgroupOf Z := by rw [h]; trivial
        exact hxJ this
    let φ : J × Z →* S := J.subtype.noncommCoprod Z.subtype hcommZ
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨j, z⟩ h
      have h1 : (j : S) * (z : S) = 1 := h
      have hzJ : (z : S) ∈ J := by
        have : (z : S) = (j : S)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact J.inv_mem j.2
      have hz1 : z = 1 := hJZ z hzJ
      have hj1 : (j : S) = 1 := by rw [hz1] at h1; simpa using h1
      exact Prod.ext (Subtype.ext hj1) hz1
    have hdvd : Nat.card (J × Z) ∣ Nat.card S := Subgroup.card_dvd_of_injective φ hinj
    rw [Nat.card_prod, hZcard] at hdvd
    exact (by norm_num : 3 ^ 5 = 3 ^ 4 * 3) ▸ (Nat.mul_dvd_mul_right h3J 3).trans hdvd

theorem false_of_pumpup_of_inner {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    {α : MulAut S} (hP : U42Pumpup S α) (hinn : α ∈ inner S)
    (h5 : ¬ 3 ^ 5 ∣ Nat.card S) : False := by
  obtain ⟨hα3, hα1, J, hJ, hT⟩ := hP
  obtain ⟨x, rfl⟩ := hinn
  have hx3 : x ^ 3 = 1 := by
    have h : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hα3
    exact CFSG.mulAutConj_injective_of_center_eq_bot hZ (h.trans (map_one _).symm)
  have hx1 : x ≠ 1 := fun h => hα1 (by rw [h, map_one])
  exact h5 (three_pow_five_dvd_card_of_pumpup hx3 hx1 J hJ hT)

theorem false_of_pumpup_of_card_le {S : Type} [Group S] [Finite S] {α : MulAut S}
    (hP : U42Pumpup S α) (hS : Nat.card S ≤ 25920) : False := by
  obtain ⟨-, hα1, J, hJ, hT⟩ := hP
  have hcard : Nat.card (PSimple 3 J) = 25920 :=
    CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT
  have hJ25 : 25920 ≤ Nat.card J := by
    rw [← hcard]
    exact Nat.le_of_dvd Nat.card_pos (cl_card_psimple_dvd J)
  have hJle : Nat.card J ≤ Nat.card S :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card J)
  have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (le_antisymm hJle (hS.trans hJ25))
  apply hα1
  ext g
  have hg : g ∈ fixSubgroup α := hJ.1 (by rw [hJtop]; exact Subgroup.mem_top g)
  exact hg

theorem cl_not_three_dvd_center (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {d : TauCeti.ValidLieTypeIndex}
    (hd : ¬ CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  intro h3
  refine hd (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA d Y
    ⟨(CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1.symm.1 hY, h3, ⟨e⟩⟩)

@[expose] def Local81 (G : Type) [Group G] : Prop :=
  ∃ U : Subgroup G, IsPGroup 2 U ∧ U ≠ ⊥ ∧ ∃ E : Subgroup G,
    E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4

theorem Local81.congr {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (h : Local81 G) :
    Local81 G' := by
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ := h
  refine ⟨U.map e.toMonoidHom, hU2.map _, fun hbot =>
    hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).mp hbot), E.map e.toMonoidHom, ?_,
    hEe.map _, by rw [Subgroup.card_map_of_injective e.injective, hEc]⟩
  exact (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)

theorem false_of_local81 {Y : Type} [Group Y] [Finite Y] (hRk : RkY Y)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center Y)) (h : Local81 (Y ⧸ Subgroup.center Y)) : False := by
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ := h
  have := hRk.card_le_quotient hZ hU1 hU2 hEN hEe
  rw [hEc] at this
  norm_num at this

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
