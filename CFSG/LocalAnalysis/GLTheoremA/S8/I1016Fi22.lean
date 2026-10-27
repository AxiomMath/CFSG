module

public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLiftCert
public import Certificates.Certificate431001
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016CoRows
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census
open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem five_le_localRank_of_liftConfig {G X : Type} [Group G] [Finite G] [Group X]
    {φ : G →* X} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) {P : Subgroup X} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (y : Fin 4 → X) (hy3 : ∀ i, y i ^ 3 = 1) (hcommy : ∀ i j, Commute (y i) (y j))
    (hEP : Subgroup.closure (Set.range y) ≤ Subgroup.normalizer (P : Set X))
    (hE : 81 ≤ Nat.card (Subgroup.closure (Set.range y)))
    (hinv : ∀ i, ∃ n : X, n * y i * n⁻¹ = (y i)⁻¹)
    (hpair : ∀ i j : Fin 4, i < j → ∃ n : X,
      (n * y i * n⁻¹ = y i ∧ n * y j * n⁻¹ = (y j)⁻¹) ∨
      (n * y j * n⁻¹ = y j ∧ n * y i * n⁻¹ = (y i)⁻¹) ∨
      (n * y i * n⁻¹ = y j ∧ n * y j * n⁻¹ = y i)) :
    5 ≤ localRank 3 G := by
  set E := Subgroup.closure (Set.range y)
  have hodd : Odd 3 := by decide
  have key : ∀ (a b : G) (i j : Fin 4), φ a = y i → φ b = y j → i < j → a * b = b * a := by
    intro a b i j hi hj hlt
    have hc : Commute (φ a) (φ b) := by
      rw [hi, hj]
      exact hcommy i j
    obtain ⟨n, hn | hn | hn⟩ := hpair i j hlt
    · exact TripleCoverLift.commute_of_conj hφ hker hodd hc (by rw [hj]; exact hy3 j)
        (n := n) (Or.inl ⟨by rw [hi]; exact hn.1, by rw [hj]; exact hn.2⟩)
    · exact (TripleCoverLift.commute_of_conj hφ hker hodd hc.symm (by rw [hi]; exact hy3 i)
        (n := n) (Or.inl ⟨by rw [hj]; exact hn.1, by rw [hi]; exact hn.2⟩)).symm
    · exact TripleCoverLift.commute_of_conj hφ hker hodd hc (by rw [hj]; exact hy3 j)
        (n := n) (Or.inr ⟨by rw [hi, hj]; exact hn.1, by rw [hi, hj]; exact hn.2⟩)
  have hS : ∀ a b : G, φ a ∈ Set.range y → φ b ∈ Set.range y → φ a ≠ φ b → a * b = b * a := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key a b i j hi.symm hj.symm hlt
    · exact (key b a j i hj.symm hi.symm hlt).symm
  have hcomm : ∀ x ∈ E.comap φ, ∀ z ∈ E.comap φ, x * z = z * x := fun x hx z hz =>
    TripleCoverLift.commute_of_mem_closure hφ hker hS hx hz
  have hlift : ∀ e ∈ E, ∃ g : G, φ g = e ∧ g ^ 3 = 1 := by
    intro e he
    refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hcomm Subgroup.subset_closure
      ?_ he
    rintro s ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hinv i
    exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd (hy3 i) hn
  exact TripleCoverLift.succ_le_localRank_of_lift_normalizer hφ hker Nat.prime_three h3
    hcomm hlift hP hP2 hEP (r := 4) (by norm_num; exact hE)


@[expose] def liftCovers4 (D : LiftData) : Bool :=
  D.base.outs.length == 4 && invCovered D.rels 0 && invCovered D.rels 1 &&
    invCovered D.rels 2 && invCovered D.rels 3 && pairCovered D.rels 0 1 &&
    pairCovered D.rels 0 2 && pairCovered D.rels 0 3 && pairCovered D.rels 1 2 &&
    pairCovered D.rels 1 3 && pairCovered D.rels 2 3

namespace LiftCert

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem five_le_localRank_of_check [Inhabited M] (D : LiftData)
    (h : LiftData.check O D = true) (hcov : liftCovers4 D = true) {G : Type} [Group G] [Finite G]
    {φ : G →* (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) : 5 ≤ localRank 3 G := by
  classical
  set X := (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ
  have : Finite X := Finite.of_surjective φ hφ
  obtain ⟨P, y, unit, hP, hP2, hy3, hyc, hEN, hkerY, hrel⟩ := exists_of_liftCheck Sp D h
  simp only [liftCovers4, Bool.and_eq_true, beq_iff_eq] at hcov
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr3, hi0⟩, hi1⟩, hi2⟩, hi3⟩, hp01⟩, hp02⟩, hp03⟩, hp12⟩, hp13⟩, hp23⟩ := hcov
  let z : Fin 4 → X := fun i => y (Fin.cast hr3.symm i)
  have hz : ∀ i : Fin 4, z i = y ⟨i, by rw [hr3]; exact i.isLt⟩ := fun i => rfl
  have hrange : Set.range z = Set.range y := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hr3 i, by simp [z]⟩
  set C := Subgroup.closure (Set.range z)
  have hC : 81 ≤ Nat.card C := by
    let v : Fin 4 → C := fun i => ⟨z i, Subgroup.subset_closure ⟨i, rfl⟩⟩
    obtain ⟨E', -, hE'⟩ := CFSG.SectionRank.exists_elemAbelian_of_commuting v
      (fun i => Subtype.ext (by simpa [v] using hy3 _))
      (fun i j => Subtype.ext (hyc _ _).eq)
      (fun a ha hprod => by
        let a' : Fin D.base.outs.length → Fin 3 := fun j => a (Fin.cast hr3 j)
        have ha' : a' ≠ 0 := by
          intro h0
          apply ha
          funext i
          have := congrFun h0 (Fin.cast hr3.symm i)
          simpa [a'] using this
        apply hkerY a' ha'
        have h1 := congrArg C.subtype hprod
        rw [map_list_prod, List.map_ofFn, map_one] at h1
        rw [List.ofFn_congr hr3]
        convert h1 using 3
        funext i
        simp [a', v, z])
    calc 81 = Nat.card E' := by rw [hE']; norm_num
      _ ≤ Nat.card C := Subgroup.card_le_card_group E'
  have hzN : C ≤ Subgroup.normalizer (P : Set X) := by
    rw [show C = Subgroup.closure (Set.range y) by rw [← hrange]]
    exact hEN
  refine five_le_localRank_of_liftConfig hφ hker h3 hP hP2 z (fun i => hy3 _)
    (fun i j => hyc _ _) hzN hC ?_ ?_
  · intro i
    fin_cases i
    · exact exists_inv_of_invCovered hrel _ hi0
    · exact exists_inv_of_invCovered hrel _ hi1
    · exact exists_inv_of_invCovered hrel _ hi2
    · exact exists_inv_of_invCovered hrel _ hi3
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact exists_pair_of_pairCovered hrel _ _ hp01
    · exact exists_pair_of_pairCovered hrel _ _ hp02
    · exact exists_pair_of_pairCovered hrel _ _ hp03
    · exact exists_pair_of_pairCovered hrel _ _ hp12
    · exact exists_pair_of_pairCovered hrel _ _ hp13
    · exact exists_pair_of_pairCovered hrel _ _ hp23


theorem five_le_localRank_of_check' [Inhabited M] (D : LiftData)
    (h : LiftData.check O D = true) (hcov : liftCovers4 D = true) {G X : Type} [Group G]
    [Finite G] [Group X]
    (ψ : X ≃* (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ) {φ : G →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) : 5 ≤ localRank 3 G := by
  have hk : (ψ.toMonoidHom.comp φ).ker = φ.ker := by
    ext g
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.injective]
  exact five_le_localRank_of_check Sp D h hcov (ψ.surjective.comp hφ) (hk ▸ hker) (hk ▸ h3)

end LiftCert

theorem fi22Lift_covers : liftCovers4 fi22Lift = true := by decide

theorem fi22Lift_check : LiftData.check (ops3 77) fi22Lift = true :=
  Certificates.certificate431001

end CFSG.RankThree.PartTwo.Sec4.Census

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CoRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.RankThree.PartTwo.Sec4.Census
  CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartTwo.Census
  CFSG.Assembly.RankThreeEven

theorem i1016At89_fi22
    (G : Type) [Group G] [Finite G] :
    ∀ X J : Subgroup G, CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X J →
      IsTypeWithCenter 3 J (sporIs .Fi22) 3 →
      ∃ E V : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ V ≤ J ∧ IsPGroup 2 V ∧
        V ≠ ⊥ ∧ E ≤ Subgroup.normalizer (V : Set G) := by
  intro X J _ hJ ⟨hcat, hZ3⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hJ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [sporIs] at hi
  subst hi
  haveI : IsSimpleGroup (PSimple 3 J) := hq.2
  haveI : IsSimpleGroup TauCeti.SporadicName.Fi22.Group :=
    (e.symm : TauCeti.SporadicName.Fi22.Group ≃* PSimple 3 J).isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Fi22
  let ψ₁ : NativeSporadic.Carrier .Fi22 ≃* NativeSporadic.Fi22 := MulEquiv.refl _
  let ψ₂ : NativeSporadic.Fi22 ≃*
      (NativeSporadic.seedMonoid 3 77 1 fi22Lift.base.seedA fi22Lift.base.seedB)ˣ := MulEquiv.refl _
  set φ := CFSG.GH74.Generic.centralQuotientMap e with hφdef
  have hφs : Function.Surjective φ := CFSG.GH74.Generic.centralQuotientMap_surjective e
  have hφk : φ.ker = Subgroup.center (PQuot 3 J) := CFSG.GH74.Generic.centralQuotientMap_ker e
  have h5 : 5 ≤ localRank 3 (PQuot 3 J) := by
    refine LiftCert.five_le_localRank_of_check' (spec3 77) fi22Lift fi22Lift_check fi22Lift_covers
      (b.trans (ψ₁.trans ψ₂)) hφs hφk.le ?_
    rw [hφk, hZ3]
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hp3 (k := 5) (by norm_num) h5
  obtain ⟨W, V, hWJ, hWe, hWc, hVJ, hV1, hV2, hWV⟩ :=
    L84.lift_quot hp3 (by norm_num) (X := J) (isElemAbelian_of_class hEe) hU2 hU1 hEN
  exact ⟨W, V, hWJ, hWe, hWc.trans hEc, hVJ, hV2, hV1, hWV⟩

theorem i1016At89_holds
    (G : Type) [Group G] [Finite G] : L89.I1016At89 G :=
  ⟨i1016At89_fi22 G, i1016At89_co1 G⟩

end CFSG.LocalAnalysis.GLTheoremA.S8.CoRows
