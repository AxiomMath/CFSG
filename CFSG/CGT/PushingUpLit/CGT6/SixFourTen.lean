module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourNine
public import CFSG.CGT.Timmesfeld75.Statements

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open CFSG.CGT.Timmesfeld75 (CorBHyp ThmAConclusion CorollaryBStmt)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem conjSubgroup_map_mk {R : Subgroup G} [R.Normal] (J : Subgroup G) (g : G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup (QuotientGroup.mk' R g) (J.map (QuotientGroup.mk' R)) =
      (conjugate J g⁻¹).map (QuotientGroup.mk' R) := by
  unfold CFSG.CGT.Timmesfeld75.conjSubgroup conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

section Ten

variable [Finite G]

omit [Finite G] in
theorem card_map_jIn_eq {R : Subgroup G} {T : Sylow 2 G} [R.Normal]
    {A : Subgroup G} (hAJ : A ≤ jIn (T : Subgroup G)) (hJA : jIn (T : Subgroup G) ≤ A ⊔ R) :
    (jIn (T : Subgroup G)).map (QuotientGroup.mk' R) = A.map (QuotientGroup.mk' R) ∧
      Nat.card ↥((jIn (T : Subgroup G)).map (QuotientGroup.mk' R)) = (A ⊓ R).relIndex A := by
  have hmap : (jIn (T : Subgroup G)).map (QuotientGroup.mk' R) = A.map (QuotientGroup.mk' R) := by
    apply le_antisymm
    · calc (jIn (T : Subgroup G)).map (QuotientGroup.mk' R)
          ≤ (A ⊔ R).map (QuotientGroup.mk' R) := Subgroup.map_mono hJA
        _ = A.map (QuotientGroup.mk' R) := by
          rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    · exact Subgroup.map_mono hAJ
  refine ⟨hmap, ?_⟩
  rw [hmap]
  let f : ↥A →* G ⧸ R := (QuotientGroup.mk' R).comp A.subtype
  have hrange : f.range = A.map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = (A ⊓ R).subgroupOf A := by
    rw [Subgroup.inf_subgroupOf_left]
    ext a
    simp [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have := Subgroup.index_ker f
  rw [hrange, hker] at this
  exact this.symm

theorem eight_sl_corB {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n) :
    CorBHyp ((jIn (T : Subgroup G)).map (QuotientGroup.mk' R)) := by
  classical
  obtain ⟨A, hA, hnot, hJA, hJY, hrel, hcomm, hsq, hbot, hTI, hCom⟩ := eight_sl_nine h hn hnat
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  set J : Subgroup G := jIn (T : Subgroup G) with hJ
  have hπR : ∀ r ∈ R, π r = 1 := fun r hr => (QuotientGroup.eq_one_iff r).mpr hr
  have hπcomm : ∀ x y : G, ⁅x, y⁆ ∈ R → π x * π y = π y * π x := by
    intro x y hxy
    have : π ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hxy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hel : CFSG.Open.IsElemAbelian 2 (J.map π) := by
    refine isElemAbelian_of_forall' ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hπcomm x y (hcomm x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsq x hx)
  have hconjeq : ∀ g : G, conjugate J g⁻¹ = J → CFSG.CGT.Timmesfeld75.conjSubgroup (π g) (J.map π) = J.map π := by
    intro g hg
    rw [conjSubgroup_map_mk, hg]
  refine ⟨hel, ?_, ?_⟩
  · intro gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have hπg : (QuotientGroup.mk g : G ⧸ R) = π g := rfl
    rw [hπg, conjSubgroup_map_mk]
    by_cases hint : ∃ z ∈ J.map π ⊓ (conjugate J g⁻¹).map π, z ≠ 1
    · right
      obtain ⟨z, hz, hz1⟩ := hint
      obtain ⟨⟨x, hx, rfl⟩, ⟨b, hb, hbx⟩⟩ := Subgroup.mem_inf.mp hz
      have hxR : x ∉ R := fun hxR => hz1 (hπR x hxR)
      have hbxR : b⁻¹ * x ∈ R := by
        have : π b = π x := hbx
        exact QuotientGroup.eq.mp this
      have hxb : x = b * (b⁻¹ * x) := by group
      have := hTI g⁻¹ ⟨x, hx, hxR, b, hb, b⁻¹ * x, hbxR, hxb⟩
      rw [this]
      exact inf_idem _
    · left
      push Not at hint
      rw [eq_bot_iff]
      intro z hz
      exact (Subgroup.mem_bot).mpr (hint z hz)
  · intro gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have hπg : (QuotientGroup.mk g : G ⧸ R) = π g := rfl
    rw [hπg, conjSubgroup_map_mk]
    constructor
    · intro hc
      have := hCom g⁻¹ (fun x hx y hy => by
        have h1 : π x * π y = π y * π x := hc (π x) (Subgroup.mem_map_of_mem _ hx) (π y)
          (Subgroup.mem_map_of_mem _ hy)
        have h2 : π ⁅x, y⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact h1
        exact (QuotientGroup.eq_one_iff _).mp h2)
      rw [this]
    · intro heq x hx y hy
      rw [heq] at hy
      exact isElemAbelian_comm' hel hx hy

end Ten

end CFSG.CGT.PushingUpLit.CGT6
