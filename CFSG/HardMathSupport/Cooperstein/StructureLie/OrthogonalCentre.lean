module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.HardMathSupport.Cooperstein.StructureLie.Nodes
import CFSG.Alternating.Multipliers.Main
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Quasithin.H13.NQCatSubnormalCore
import CFSG.Quasithin.Background.A3ComponentsQuotient
import CFSG.Quasithin.Background.G2
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.Blueprint.Multiplier
  CFSG.Assembly.LowTwoRank
open CFSG.Milestones
open CFSG.AGLEmbedding (IsOrthogonalTwo IsTwoPrimeComponent barM)

section Generic

theorem card_center_dvd_card_hopfMultiplier {K X : Type} [Group K] [Group X] [Finite K] [Finite X]
    (hK : Group.IsPerfect K) (hX : Group.IsPerfect X) (e : K ⧸ Subgroup.center K ≃* X) :
    Nat.card (Subgroup.center K) ∣ Nat.card (hopfMultiplier X) := by
  have hfin := finite_hopfMultiplier hX
  have hs := hopfMultiplierToKer_surjective (centralQuotientMap e)
    (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
  have h := Subgroup.card_dvd_of_surjective hs
  rwa [centralQuotientMap_ker e] at h

theorem eq_one_of_odd_of_dvd_two_pow {a k : ℕ} (hodd : Odd a) (h : a ∣ 2 ^ k) : a = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) h

theorem nonempty_mulEquiv_quotient_center_of_card_eq_one {K : Type} [Group K]
    (h : Nat.card (Subgroup.center K) = 1) : Nonempty (K ≃* K ⧸ Subgroup.center K) := by
  have hb : Subgroup.center K = ⊥ := Subgroup.eq_bot_of_card_eq _ h
  exact ⟨QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hb.symm)⟩

theorem isOrthogonalTwo_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsOrthogonalTwo Y') : IsOrthogonalTwo Y := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.trans f⟩⟩

end Generic

section Multiplier

theorem card_multiplicative_zmod (a : ℕ) [NeZero a] :
    Nat.card (Multiplicative (ZMod a)) = a := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exceptionalOrders_dvd_two (t : StatedLieTag) (n : ℕ) :
    (exceptionalOrders t n 2 1).1 ∣ 2 ∧ (exceptionalOrders t n 2 1).2 ∣ 2 := by
  unfold exceptionalOrders
  split <;> simp_all

theorem card_hopfMultiplier_dvd_four_of_model 
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {t : StatedLieTag} {n : ℕ}
    (hm : Models.LieModel X t n 2 1) (hg : genericOrders t n 2 1 = (1, 1)) :
    Nat.card (hopfMultiplier X) ∣ 4 := by
  obtain ⟨-, ⟨e⟩⟩ := cl_lit_griess_schur_multipliers_all_models X t n 2 1 hm
  obtain ⟨h1, h2⟩ := exceptionalOrders_dvd_two t n
  have hn1 : NeZero (exceptionalOrders t n 2 1).1 :=
    ⟨fun h => by rw [h] at h1; simp at h1⟩
  have hn2 : NeZero (exceptionalOrders t n 2 1).2 :=
    ⟨fun h => by rw [h] at h2; simp at h2⟩
  have hg1 : NeZero (genericOrders t n 2 1).1 := ⟨by rw [hg]; exact one_ne_zero⟩
  have hg2 : NeZero (genericOrders t n 2 1).2 := ⟨by rw [hg]; exact one_ne_zero⟩
  have hcard : Nat.card (hopfMultiplier X) =
      ((genericOrders t n 2 1).1 * (genericOrders t n 2 1).2) *
        ((exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2) := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr e.toEquiv]
    simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod]
  rw [hcard, hg]
  simpa using Nat.mul_dvd_mul h1 h2


theorem genericOrders_POmegaPlus_two (n : ℕ) : genericOrders .POmegaPlus n 2 1 = (1, 1) := by
  simp [genericOrders]

theorem genericOrders_POmegaMinus_two {n : ℕ} (hn : 1 ≤ n) :
    genericOrders .POmegaMinus n 2 1 = (1, 1) := by
  have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have h : Nat.Coprime 4 (2 ^ n + 1) := by
    simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  simp [genericOrders, h.gcd_eq_one]

theorem genericOrders_PSU_four_two : genericOrders .PSU 4 2 1 = (1, 1) := by
  simp [genericOrders]

theorem card_hopfMultiplier_dvd_four_of_orthogonal 
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (h : ∃ d : TauCeti.ValidLieTypeIndex, (∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.card = 2 ∧
      (d.1 = .D m q ∨ d.1 = .twistedD m q ∨ (m = 3 ∧ d.1 = .twistedA 3 q))) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (hopfMultiplier X) ∣ 4 := by
  obtain ⟨⟨idx, hv⟩, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ := h
  have hpe : q.p = 2 ∧ q.exponent = 1 := (Nat.Prime.pow_eq_iff Nat.prime_two).mp
    ((TauCeti.PrimePower.card_def q).symm.trans hq)
  rcases hd with hd | hd | ⟨rfl, hd⟩
  · have hd' : idx = .D m q := hd
    subst hd'
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hpe.1 e
    rw [hpe.1, hpe.2] at hm
    exact card_hopfMultiplier_dvd_four_of_model (t := .POmegaPlus) (n := m) ⟨hm.1, Or.inl hm⟩
      (genericOrders_POmegaPlus_two m)
  · have hd' : idx = .twistedD m q := hd
    subst hd'
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hpe.1 e
    rw [hpe.1, hpe.2] at hm
    have h4 : 4 ≤ m := hm.1.2.2
    exact card_hopfMultiplier_dvd_four_of_model (t := .POmegaMinus) (n := m) ⟨hm.1, Or.inl hm⟩
      (genericOrders_POmegaMinus_two (by omega))
  · have hd' : idx = .twistedA 3 q := hd
    subst hd'
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hpe.1, hpe.2] at hm
    exact card_hopfMultiplier_dvd_four_of_model (t := .PSU) (n := 3 + 1) ⟨hm.1, Or.inl hm⟩
      genericOrders_PSU_four_two

end Multiplier

section Main

theorem orthOrTripleA6_of_orthogonal_quotient 
    {Γ : Type} [Group Γ] [Finite Γ] {Lb : Subgroup Γ} (hq : CFSG.IsQuasisimple ↥Lb)
    (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hY : IsOrthogonalTwo (↥Lb ⧸ Subgroup.center ↥Lb)) :
    IsOrthogonalTwo ↥Lb ∨ (Nat.card (Subgroup.center ↥Lb) = 3 ∧
      Nonempty (↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 6))) := by
  have hperf : Group.IsPerfect ↥Lb := hq.1
  have hperfY : Group.IsPerfect (↥Lb ⧸ Subgroup.center ↥Lb) :=
    isPerfect_of_quasisimple_quotient hq (MulEquiv.refl _)
  rcases hY with hLie | ⟨n, hn, ⟨e⟩⟩
  · have hdvd := card_center_dvd_card_hopfMultiplier hperf hperfY (MulEquiv.refl _)
    have h4 := card_hopfMultiplier_dvd_four_of_orthogonal hLie
    have hZ : Nat.card (Subgroup.center ↥Lb) = 1 :=
      eq_one_of_odd_of_dvd_two_pow (k := 2) hodd (hdvd.trans h4)
    obtain ⟨b⟩ := nonempty_mulEquiv_quotient_center_of_card_eq_one hZ
    exact Or.inl (isOrthogonalTwo_of_mulEquiv b (Or.inl hLie))
  · have hperfA : Group.IsPerfect (alternatingGroup (Fin n)) :=
      isPerfect_of_quasisimple_quotient hq e
    have hdvd := card_center_dvd_card_hopfMultiplier hperf hperfA e
    rcases hn with rfl | rfl | rfl
    · have hZ : Nat.card (Subgroup.center ↥Lb) = 1 := by
        refine eq_one_of_odd_of_dvd_two_pow (k := 1) hodd ?_
        rw [(hopfMultiplier_alternatingGroup_five).2] at hdvd
        simpa using hdvd
      obtain ⟨b⟩ := nonempty_mulEquiv_quotient_center_of_card_eq_one hZ
      exact Or.inl (isOrthogonalTwo_of_mulEquiv b (Or.inr ⟨5, Or.inl rfl, ⟨e⟩⟩))
    · rw [(hopfMultiplier_alternatingGroup_six).2] at hdvd
      have h3 : Nat.card (Subgroup.center ↥Lb) ∣ 3 :=
        (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd)
          (show Nat.card (Subgroup.center ↥Lb) ∣ 3 * 2 from hdvd))
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
      · obtain ⟨b⟩ := nonempty_mulEquiv_quotient_center_of_card_eq_one h1
        exact Or.inl (isOrthogonalTwo_of_mulEquiv b (Or.inr ⟨6, Or.inr (Or.inl rfl), ⟨e⟩⟩))
      · exact Or.inr ⟨h1, ⟨e⟩⟩
    · have hZ : Nat.card (Subgroup.center ↥Lb) = 1 := by
        refine eq_one_of_odd_of_dvd_two_pow (k := 1) hodd ?_
        rw [card_hopfMultiplier_alternatingGroup (by norm_num : 8 ≤ 8)] at hdvd
        simpa using hdvd
      obtain ⟨b⟩ := nonempty_mulEquiv_quotient_center_of_card_eq_one hZ
      exact Or.inl (isOrthogonalTwo_of_mulEquiv b (Or.inr ⟨8, Or.inr (Or.inr rfl), ⟨e⟩⟩))

end Main

section Barm

theorem odd_card_center_of_subnormal {Γ : Type} [Group Γ] [Finite Γ] (hO : CFSG.pCore 2 Γ = ⊥)
    {Lb : Subgroup Γ} (hs : Lb.IsSubnormal) : Odd (Nat.card (Subgroup.center ↥Lb)) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥Lb) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥Lb) 2 h2
  have hzc : Subgroup.zpowers (z : ↥Lb) ≤ Subgroup.center ↥Lb :=
    (Subgroup.zpowers_le (H := Subgroup.center ↥Lb)).mpr z.2
  have hzo : orderOf (z : ↥Lb) = 2 := by rw [Subgroup.orderOf_coe, hz]
  set P : Subgroup Γ := (Subgroup.zpowers (z : ↥Lb)).map Lb.subtype with hP
  have hPn : (P.subgroupOf Lb).Normal := by
    rw [hP, CFSG.Quasithin.map_subtype_subgroupOf']
    exact Subgroup.normal_of_le_center hzc
  have hPs : P.IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le _) hs hPn
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by
    rw [hP, Subgroup.card_map_of_injective Lb.subtype_injective, Nat.card_zpowers, hzo, pow_one])
  have htop : CFSG.pCore 2 P = ⊤ := top_unique (le_sSup ⟨Subgroup.normal_top, hPp.of_equiv Subgroup.topEquiv.symm⟩)
  have h1 := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2) hPs
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hO] at h1
  have hzP : ((z : ↥Lb) : Γ) ∈ P := ⟨(z : ↥Lb), Subgroup.mem_zpowers _, rfl⟩
  have h3 : (z : ↥Lb) = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 hzP))
  rw [h3, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

variable {G : Type} [Group G]

theorem odd_card_center_barM [Finite G] {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    Odd (Nat.card (Subgroup.center ↥(barM X L))) :=
  odd_card_center_of_subnormal CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
    (CFSG.Quasithin.A3.subnormal_top_iff.mp hL.component.2.1)

theorem isQuasisimple_barM {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    CFSG.IsQuasisimple ↥(barM X L) :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hL.component.2.2

theorem orthOrTripleA6_of_orthogonal_quotient_barM 
    [Finite G] {X L : Subgroup G} (hL : IsTwoPrimeComponent X L)
    (hodd : Odd (Nat.card (Subgroup.center ↥(barM X L))))
    (hY : IsOrthogonalTwo (↥(barM X L) ⧸ Subgroup.center ↥(barM X L))) :
    OrthOrTripleA6 X L :=
  orthOrTripleA6_of_orthogonal_quotient (isQuasisimple_barM hL) hodd hY

theorem orthOrTripleA6_of_isTwoPrimeComponent 
    [Finite G] {X L : Subgroup G} (hL : IsTwoPrimeComponent X L)
    (hY : IsOrthogonalTwo (↥(barM X L) ⧸ Subgroup.center ↥(barM X L))) :
    OrthOrTripleA6 X L :=
  orthOrTripleA6_of_orthogonal_quotient_barM hL (odd_card_center_barM hL) hY

end Barm

end CFSG.HardMathSupport.Cooperstein.StructureLie
