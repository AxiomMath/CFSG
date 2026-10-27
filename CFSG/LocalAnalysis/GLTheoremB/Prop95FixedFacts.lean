module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95FixedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.PPrimeCompEven
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.NearFixed
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion ffChevConclusion_of_mulEquiv)


namespace Prop95FixedFacts

theorem exists_odd_mem_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (C : Subgroup X)
    (e : ↥C ≃* Y) {q : ℕ} (hq : Odd q) (hq1 : q ≠ 1) (hY : ∃ h : Y, orderOf h = q) :
    ∃ y ∈ C, y ≠ 1 ∧ Odd (orderOf y) := by
  obtain ⟨h, hh⟩ := hY
  have h2 : orderOf (e.symm h) = orderOf h :=
    orderOf_injective e.symm.toMonoidHom e.symm.injective h
  have hx : orderOf ((e.symm h : ↥C) : X) = q := by
    rw [Subgroup.orderOf_coe, h2, hh]
  refine ⟨((e.symm h : ↥C) : X), (e.symm h).2, fun h1 => hq1 ?_, by rw [hx]; exact hq⟩
  rw [← hx, h1, orderOf_one]

theorem exists_orderOf_three_psl2_zmod_two :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2), orderOf x = 3 := by
  let a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 1], by decide⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], by decide⟩
  let x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) := a
  have hx3 : x ^ 3 = 1 := by
    have : a ^ 3 = 1 := Subtype.ext (by decide)
    change ((a ^ 3 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) = 1
    rw [this]; rfl
  have hx1 : x ≠ 1 := by
    intro h
    have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
      (QuotientGroup.eq_one_iff a).mp h
    have hab := Subgroup.mem_center_iff.mp ha b
    have : b * a ≠ a * b := by
      intro h'
      have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) =>
        (z : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) h'
      revert this; decide
    exact this hab
  exact ⟨x, orderOf_eq_prime hx3 hx1⟩

theorem exists_orderOf_three_psl2_zmod_three :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3), orderOf x = 3 := by
  let u : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨!![1, 0; 1, 1], by decide⟩
  let x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3) := u
  have hx3 : x ^ 3 = 1 := by
    have : u ^ 3 = 1 := Subtype.ext (by decide)
    change ((u ^ 3 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) = 1
    rw [this]; rfl
  have hx1 : x ≠ 1 := by
    intro h
    have hu : u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
      (QuotientGroup.eq_one_iff u).mp h
    have hub := Subgroup.mem_center_iff.mp hu b
    have : b * u ≠ u * b := by
      intro h'
      have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) =>
        (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0) h'
      revert this; decide
    exact this hub
  exact ⟨x, orderOf_eq_prime hx3 hx1⟩

theorem exists_odd_prime_dvd_card {H : Type} [Group H] [Finite H] (hs : IsSimpleGroup H)
    (hnc : ∃ a b : H, a * b ≠ b * a) : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card H := by
  by_contra hcon
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) (Nat.card_pos (α := H)).ne'
    (fun hd hdvd => by
      by_contra hd2
      exact hcon ⟨_, hd, hd2, hdvd⟩)
  have hP : IsPGroup 2 H := IsPGroup.of_card hpow
  haveI := IsPGroup.isNilpotent hP
  obtain ⟨a, b, hab⟩ := hnc
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := H)).mpr inferInstance a b)

theorem exists_odd_of_fitting {S : Type} [Group S] [Finite S] (C : Subgroup S)
    (hF : IsSimpleGroup (signalizerGeneralizedFitting C) ∧
      ∃ a b : signalizerGeneralizedFitting C, a * b ≠ b * a) :
    ∃ y ∈ C, y ≠ 1 ∧ Odd (orderOf y) := by
  obtain ⟨hs, hnc⟩ := hF
  obtain ⟨q, hq, hq2, hdvd⟩ := exists_odd_prime_dvd_card hs hnc
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hyo : orderOf ((x : ↥C) : S) = q := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  refine ⟨((x : ↥C) : S), (x : ↥C).2, fun h1 => ?_, by rw [hyo]; exact hq.odd_of_ne_two hq2⟩
  rw [h1, orderOf_one] at hyo
  exact hq.one_lt.ne hyo

open CFSG.SignalizerFunctorTheorem.NearModels in
theorem exists_odd_of_nearModel {p : ℕ} (hp : p.Prime) {S : Type}
    [Group S] (hsm : signalizerNearSimpleModel p S) (hcop : Nat.Coprime p (Nat.card S))
    (f : MulAut S) (hf : orderOf f = p) :
    ∃ y ∈ signalizerFixedSubgroup f, y ≠ 1 ∧ Odd (orderOf y) := by
  rcases hsm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 2 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    exact exists_odd_mem_of_mulEquiv (signalizerFixedSubgroup f)
      ((fixedSubgroupCongr e f).trans φ) (q := 3) ⟨1, rfl⟩ (by norm_num)
      exists_orderOf_three_psl2_zmod_two
  · obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 3 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    exact exists_odd_mem_of_mulEquiv (signalizerFixedSubgroup f)
      ((fixedSubgroupCongr e f).trans φ) (q := 3) ⟨1, rfl⟩ (by norm_num)
      exists_orderOf_three_psl2_zmod_three
  · obtain ⟨φ⟩ := sz_fixedSubgroup_mulEquiv n hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    refine exists_odd_mem_of_mulEquiv (signalizerFixedSubgroup f)
      ((fixedSubgroupCongr e f).trans φ) (q := 5) ⟨2, rfl⟩ (by norm_num) ?_
    obtain ⟨E⟩ := Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
    have h20 : Nat.card (Sz 0) = 20 := by
      rw [← Nat.card_congr E.toEquiv, CFSG.LieType.Ree.suzuki_order (by simp)]
      norm_num
    haveI : Finite (Sz 0) := Nat.finite_of_card_ne_zero (by rw [h20]; norm_num)
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact exists_prime_orderOf_dvd_card' 5 (by rw [h20]; norm_num)
  · obtain ⟨φ⟩ := psu3_fixedSubgroup_mulEquiv hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    refine exists_odd_mem_of_mulEquiv (signalizerFixedSubgroup f)
      ((fixedSubgroupCongr e f).trans φ) (q := 3) ⟨1, rfl⟩ (by norm_num) ?_
    have h72 : Nat.card (PSU3 2 1) = 72 :=
      CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one
    haveI : Finite (PSU3 2 1) := Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
    exact exists_prime_orderOf_dvd_card' 3 (by rw [h72]; norm_num)

theorem pCore_fixed_eq_bot {S : Type} [Group S] [Finite S] (C : Subgroup S)
    (h31 : ∀ T : Subgroup S, T ≠ ⊥ → Group.IsSolvable T → ¬ C ≤ Subgroup.normalizer (T : Set S)) :
    CFSG.pCore 2 ↥C = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (CFSG.pCore 2 ↥C).Normal := CFSG.pCore_normal
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥C) := by
    haveI := CFSG.pCore_isNilpotent (p := 2) (G := ↥C)
    infer_instance
  set P := CFSG.pCore 2 ↥C with hPdef
  have hT : P.map C.subtype ≠ ⊥ := by
    intro h
    apply hne
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_bot]
    exact h
  have hTs : Group.IsSolvable ↥(P.map C.subtype) :=
    CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective P C.subtype C.subtype_injective).symm
  have hinc : ∀ d ∈ C, ∀ x ∈ P.map C.subtype, d * x * d⁻¹ ∈ P.map C.subtype := by
    intro d hd x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨d, hd⟩ * y * (⟨d, hd⟩ : ↥C)⁻¹, hPn.conj_mem y hy _, rfl⟩
  refine h31 (P.map C.subtype) hT hTs ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hinc c hc x hx
  · intro hx
    have hx' : c * x * c⁻¹ ∈ P.map C.subtype := hx
    have := hinc c⁻¹ (C.inv_mem hc) _ hx'
    rw [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
    exact this

theorem two_element_eq_one {S : Type} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (C : Subgroup S)
    (h33 : ∀ g : MulAut S, Nat.Coprime p (orderOf g) → (∀ x ∈ C, g x = x) → g = 1)
    (g : MulAut S) (hg : IsPGroup 2 (Subgroup.zpowers g)) (hfix : ∀ x ∈ C, g x = x) : g = 1 := by
  refine h33 g ?_ hfix
  obtain ⟨k, hk⟩ := hg ⟨g, Subgroup.mem_zpowers g⟩
  have hgk : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hgk)
  rw [hi]
  exact Nat.Coprime.pow_right i ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

end Prop95FixedFacts

open Prop95FixedFacts

section Certs


theorem fixedOddFact_holds : FixedOddFact := by
  intro S _ _ p hp _ hs hn hcat hpS f hf
  have hA := CFSG.AGLEmbedding.KFactProofs.PPrimeComp.hypA_of_catalog hs hn hcat hp hpS
  rcases hA.2.2.2.2.2 with hnear | hA3
  · exact exists_odd_of_nearModel hp
      (CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.signalizerNearSimpleModel_of_nearPSolvable
        hs hn hnear) hA.2.2.2.1 f hf
  · obtain ⟨-, hF, -⟩ := hA3 f hf
    exact exists_odd_of_fitting (signalizerFixedSubgroup f) hF

theorem fixedTwoFacts_of (hNS : NearSolvableTwoFacts) (hL2 : L2ThreeNotChevTwoOrAlt) :
    FixedTwoFacts := by
  intro S _ _ p hp hp2 hs hn hcat hpS hFF f hf
  have hA := CFSG.AGLEmbedding.KFactProofs.PPrimeComp.hypA_of_catalog hs hn hcat hp hpS
  rcases hA.2.2.2.2.2 with hnear | hA3
  · have hsm :=
      CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.signalizerNearSimpleModel_of_nearPSolvable
        hs hn hnear
    by_cases h3 : Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))
    · exact (hL2 p hp hp2 (ffChevConclusion_of_mulEquiv h3.some hFF)).elim
    · exact hNS S p hp hp2 hs hpS hsm h3 f hf
  · obtain ⟨h31, -, h33⟩ := hA3 f hf
    exact ⟨pCore_fixed_eq_bot _ h31, fun g hg hfix => two_element_eq_one hp hp2 _ h33 g hg hfix⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
