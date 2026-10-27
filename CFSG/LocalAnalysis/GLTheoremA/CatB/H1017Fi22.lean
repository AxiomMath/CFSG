module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016Fi22
public import CFSG.Sporadic.Bridge.Catalogue
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartTwo.Census

private theorem comm_of_elemAbelian_fi {X : Type} [Group X] {p : ℕ} {E : Subgroup X}
    (hE : IsElemAbelian p E) {x y : X} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  haveI := hE.1
  have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  simpa using this

theorem attained_of_mulEquiv {p r : ℕ} {X K : Type} [Group X] [Group K] (φ : X ≃* K)
    (h : ∃ E T : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set X)) :
    ∃ E T : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set K) := by
  obtain ⟨E, T, hE, hc, hT, hT2, hET⟩ := h
  refine ⟨E.map φ.toMonoidHom, T.map φ.toMonoidHom, ?_, ?_, ?_, hT2.map _, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      show φ x * φ y = φ y * φ x
      rw [← map_mul, ← map_mul, comm_of_elemAbelian_fi hE hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      show φ x ^ p = 1
      rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective, hc]
  · exact fun h0 => hT ((Subgroup.map_eq_bot_iff_of_injective T φ.injective).1 h0)
  · exact (Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _)

theorem isElemAbelian_map_subtype {X : Type} [Group X] {p : ℕ} {C : Subgroup X} {E : Subgroup C}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map C.subtype) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    show (x : X) * y = y * x
    exact congrArg Subtype.val (comm_of_elemAbelian_fi hE hx hy)
  · rintro _ ⟨x, hx, rfl⟩
    show (x : X) ^ p = 1
    exact congrArg Subtype.val (hE.2 x hx)

section Generic

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem attained_of_liftCheck [Inhabited M] (D : LiftData) (h : LiftData.check O D = true)
    {K : Type} [Group K] (ψ : K ≃* (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ) :
    ∃ E T : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ D.base.outs.length ∧ T ≠ ⊥ ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set K) := by
  classical
  obtain ⟨P, y, -, hP, hP2, hy3, hyc, hEN, hkerY, -⟩ := LiftCert.exists_of_liftCheck Sp D h
  set C := Subgroup.closure (Set.range y)
  let v : Fin D.base.outs.length → C := fun i => ⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv3 : ∀ i, v i ^ 3 = 1 := fun i => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hy3 i)
  have hvc : ∀ i j, Commute (v i) (v j) := fun i j => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (hyc i j).eq)
  have hvk : ∀ a : Fin D.base.outs.length → Fin 3, a ≠ 0 →
      (List.ofFn fun i => v i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha hprod
    apply hkerY a ha
    have h1 := congrArg C.subtype hprod
    rw [map_list_prod, List.map_ofFn, map_one] at h1
    have e : (C.subtype ∘ fun i => v i ^ (a i : ℕ)) = fun i => y i ^ (a i : ℕ) := by
      funext i
      rw [Function.comp_apply, map_pow]
      rfl
    rw [e] at h1
    exact h1
  obtain ⟨E', hE'e, hE'c⟩ := exists_elemAbelian_of_commuting v hv3 hvc hvk
  refine attained_of_mulEquiv ψ.symm ⟨E'.map C.subtype, P, isElemAbelian_map_subtype hE'e, ?_, hP,
    hP2, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hE'c]
  · exact (Subgroup.map_subtype_le E').trans hEN

end Generic


set_option maxRecDepth 100000 in
theorem i1017FiTwoTwoAttained_holds : I1017FiTwoTwoAttained := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi22
  let ψ : NativeSporadic.Carrier .Fi22 ≃*
      (NativeSporadic.seedMonoid 3 77 1 fi22Lift.base.seedA fi22Lift.base.seedB)ˣ := MulEquiv.refl _
  have hlen : fi22Lift.base.outs.length = 4 := by
    have h := fi22Lift_covers
    simp only [liftCovers4, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1.1.1.1.1.1.1.1
  have key := attained_of_liftCheck (spec3 77) fi22Lift fi22Lift_check ((e.trans b.symm).trans ψ)
  rw [hlen] at key
  exact key

set_option maxRecDepth 100000 in
theorem i1017CoverFiTwoTwo_holds : I1017CoverFiTwoTwo := by
  intro H _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi22
  let ψ : NativeSporadic.Carrier .Fi22 ≃*
      (NativeSporadic.seedMonoid 3 77 1 fi22Lift.base.seedA fi22Lift.base.seedB)ˣ := MulEquiv.refl _
  have hk : (QuotientGroup.mk' (Subgroup.center H)).ker = Subgroup.center H :=
    QuotientGroup.ker_mk' _
  have h5 : 5 ≤ CFSG.Assembly.RankThreeEven.localRank 3 H := by
    refine LiftCert.five_le_localRank_of_check' (spec3 77) fi22Lift fi22Lift_check fi22Lift_covers
      ((e.trans b.symm).trans ψ) (QuotientGroup.mk'_surjective _) hk.le ?_
    rw [hk, hZ]
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three (k := 5)
      (by norm_num) h5
  exact ⟨E, U, S8.CoRows.isElemAbelian_of_class hEe, hEc, hU1, hU2, hEN⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
