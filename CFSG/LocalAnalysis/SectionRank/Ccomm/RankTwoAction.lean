module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.Ccomm

open Subgroup CFSG.Open CFSG.SectionRank Matrix
open scoped commutatorElement

theorem map_center_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (center G).map e.toMonoidHom = center G' := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_center_iff]
    intro h'
    obtain ⟨g', rfl⟩ := e.surjective h'
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, mem_center_iff.1 hg g']
  · intro hh
    refine ⟨e.symm h, mem_center_iff.2 fun g => e.injective ?_, by simp⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.1 hh (e g)

variable {p : ℕ} [hp : Fact p.Prime]

theorem critical_rank_two_action_recognition
    (hp2 : p ≠ 2) {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (hrank : pRank p (⊤ : Subgroup Q) ≤ 2) (D : Subgroup Q)
    [D.Characteristic] (hexp : ∀ x ∈ D, x ^ p = 1) (hker : IsPGroup p (frattiniAction D).ker)
    {H : Type*} [Group H] [Group.IsPerfect H] (α : H →* MulAut Q) (hα : α ≠ 1)
    (J : Subgroup (MulAut (D ⧸ frattini D))) (hJ : J = ((frattiniAction D).comp α).range) :
    Nat.card (D ⧸ frattini D) = p ^ 2 ∧ J ≠ ⊥ ∧ Group.IsPerfect J ∧
      (∀ U : Subgroup (D ⧸ frattini D), Nat.card U = p → ∃ g ∈ J, ∃ u ∈ U, g u ∉ U) ∧
      5 ≤ p ∧ IsQuasisimple J ∧
      (∀ g : J, g ∈ center J ↔
        (g : MulAut (D ⧸ frattini D)) = 1 ∨ ∀ w, (g : MulAut (D ⧸ frattini D)) w = w⁻¹) ∧
      (∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s = p ∨ s = 5) ∧
        Nonempty (J ⧸ center J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))) ∧
      ((IsMulCommutative D ∧ Nat.card D = p ^ 2) ∨
        (¬ IsMulCommutative D ∧ Nat.card D = p ^ 3 ∧ frattini D = center D ∧
          Nat.card (frattini D) = p)) := by
  set W := D ⧸ frattini D
  set ρ : H →* MulAut W := (frattiniAction D).comp α with hρ
  have hDp : IsPGroup p D := hQ.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hJperf : Group.IsPerfect J := hJ ▸ Group.IsPerfect.range ρ
  have hρ1 : ρ ≠ 1 := by
    intro hρ1
    apply hα
    have hle : α.range ≤ (frattiniAction D).ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      exact congrArg (· x) hρ1
    have hpg : IsPGroup p α.range := hker.to_le hle
    have : Group.IsPerfect α.range := Group.IsPerfect.range α
    by_contra hne
    have : Nontrivial α.range := by
      rw [nontrivial_iff_ne_bot]
      intro hbot
      apply hne
      ext x
      have : α x ∈ α.range := ⟨x, rfl⟩
      rw [hbot, mem_bot] at this
      rw [this]
      rfl
    exact Group.IsPerfect.not_isNilpotent α.range hpg.isNilpotent
  have hJne : J ≠ ⊥ := by
    rw [hJ]
    intro hbot
    apply hρ1
    ext x
    have : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rw [hbot, mem_bot] at this
    rw [this]
    rfl
  have hDrank : pRank p (⊤ : Subgroup D) ≤ 2 :=
    (pRank_top_le_of_injective hp.out.one_lt D.subtype D.subtype_injective).trans hrank
  have hDexp : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hexp _ x.2)
  obtain ⟨hD3, hW2⟩ := rank_two_exponent_prime_order_bound hDp hDexp hDrank
  obtain ⟨k, hk⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hk ▸ hW2)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  have hk2' : k = 2 := by
    by_contra hk2'
    apply hρ1
    apply perfect_hom_eq_one_of_range_comm
    intro a _ b _
    apply (elemAutEquivGL e).injective
    rw [map_mul, map_mul]
    exact GL_comm_of_le_one (by omega) _ _
  subst hk2'
  set ψ := elemAutEquivGL e with hψ
  set J' := J.map ψ.toMonoidHom with hJ'
  have : Group.IsPerfect J' := Group.IsPerfect.map _
  have hJ'ne : J' ≠ ⊥ := by
    rw [hJ', Ne, map_eq_bot_iff_of_injective _ ψ.injective]
    exact hJne
  let eJ : J ≃* J' := J.equivMapOfInjective ψ.toMonoidHom ψ.injective
  have heJ : ∀ g : J, ((eJ g : J') : GL (Fin 2) (ZMod p)) = ψ g := fun _ => rfl
  obtain ⟨h5, hcen', hquasi', ⟨s, hs, hs5, hsp, ⟨eQ⟩⟩, -, -⟩ :=
    perfect_prime_linear_recognition hp2 J' hJ'ne
  have hcenmap : (center J).map eJ.toMonoidHom = center J' := map_center_mulEquiv eJ
  let eQuot : J ⧸ center J ≃* J' ⧸ center J' := QuotientGroup.congr _ _ eJ hcenmap
  have hcenJ : ∀ g : J, g ∈ center J ↔ eJ g ∈ center J' := by
    intro g
    rw [← hcenmap]
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g', hg', hgg'⟩
      rwa [eJ.injective hgg'] at hg'
  have hcen : ∀ g : J, g ∈ center J ↔
      (g : MulAut W) = 1 ∨ ∀ w, (g : MulAut W) w = w⁻¹ := by
    intro g
    rw [hcenJ, hcen', heJ, ← elemAutEquivGL_eq_neg_one_iff e]
    constructor
    · rintro (h | h)
      · left
        exact ψ.injective (h.trans (map_one ψ).symm)
      · right
        exact h
    · rintro (h | h)
      · left
        rw [h, map_one]
      · right
        exact h
  have hirr : ∀ U : Subgroup W, Nat.card U = p → ∃ g ∈ J, ∃ u ∈ U, g u ∉ U := by
    intro U hU
    obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : U = ⊥ := (eq_bot_iff_forall U).2 h
      rw [hbot, card_bot] at hU
      exact hp.out.one_lt.ne hU
    have hUz : U = zpowers u := by
      symm
      refine eq_of_le_of_card_ge (zpowers_le.2 huU) ?_
      rw [hU, Nat.card_zpowers]
      exact (orderOf_eq_prime (hWpow u) hu1).ge
    set v := Multiplicative.toAdd (e u) with hvdef
    have hv : v ≠ 0 := by
      intro hv
      apply hu1
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (hv.trans toAdd_one.symm)
    obtain ⟨g', hg'J, hg'⟩ := (perfect_linear_two_basics J' hJ'ne).2.1 v hv
    obtain ⟨g, hgJ, rfl⟩ := mem_map.1 hg'J
    refine ⟨g, hgJ, u, huU, fun hgu => ?_⟩
    rw [hUz] at hgu
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hgu
    apply hg' (n : ZMod p)
    rw [MulEquiv.coe_toMonoidHom, elemAutEquivGL_mulVec, ← hn, map_zpow, toAdd_zpow,
      Int.cast_smul_eq_zsmul]
  have hDstr : (IsMulCommutative D ∧ Nat.card D = p ^ 2) ∨
      (¬ IsMulCommutative D ∧ Nat.card D = p ^ 3 ∧ frattini D = center D ∧
        Nat.card (frattini D) = p) := by
    have hcardD := card_eq_card_quotient_mul_card_subgroup (frattini D)
    rw [hk] at hcardD
    by_cases hab : IsMulCommutative D
    · left
      refine ⟨hab, ?_⟩
      have hΦ : frattini D = ⊥ := (frattini_eq_bot_iff hDp).2 ⟨fun a b => mul_comm' a b, hDexp⟩
      rw [hcardD, hΦ, card_bot, mul_one]
    · right
      have hΦne : frattini D ≠ ⊥ := fun h => hab ⟨⟨((frattini_eq_bot_iff hDp).1 h).1⟩⟩
      obtain ⟨j, hj⟩ := (hDp.to_subgroup (frattini D)).exists_card_eq
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, card_eq_one] at hj
        exact hΦne hj
      have hj1 : j = 1 := by
        rw [hj, ← pow_add] at hcardD
        have h3 := hcardD ▸ hD3
        have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h3
        omega
      subst hj1
      rw [pow_one] at hj
      have hD3' : Nat.card D = p ^ 3 := by rw [hcardD, hj]; ring
      have hnc : ∃ a b : D, a * b ≠ b * a := by
        by_contra h
        push Not at h
        exact hab ⟨⟨h⟩⟩
      obtain ⟨hcomZ, hZp, -⟩ := nonabelian_prime_cube_central_structure hD3' hnc
      have hcomΦ : commutator D ≤ frattini D := by
        rw [_root_.commutator_def, commutator_le]
        intro a _ b _
        exact commutator_mem_frattini hDp a b
      have hΦZ : frattini D = center D := by
        rw [← hcomZ]
        symm
        exact eq_of_le_of_card_ge hcomΦ (by rw [hj, hcomZ, hZp])
      exact ⟨hab, hD3', hΦZ, hj⟩
  have := hquasi'.2
  exact ⟨hk, hJne, hJperf, hirr, h5,
    ⟨Group.IsPerfect.commutator_eq_top, MulEquiv.isSimpleGroup eQuot⟩, hcen,
    ⟨s, hs, hs5, hsp, ⟨eQuot.trans eQ⟩⟩, hDstr⟩

end CFSG.SectionRank.Ccomm
