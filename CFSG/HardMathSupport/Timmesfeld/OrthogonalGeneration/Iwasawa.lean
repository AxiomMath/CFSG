module

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_12
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
public import Mathlib.GroupTheory.GroupAction.Primitive

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type*} [Field K] [IsF2 K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem linearIndependent_pair_of_ne {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    LinearIndependent K ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases IsF2.eq_zero_or_one s with rfl | rfl <;> rcases IsF2.eq_zero_or_one t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, one_smul, zero_add] at hst
    exact absurd hst hv
  · rw [zero_smul, one_smul, add_zero] at hst
    exact absurd hst hu
  · rw [one_smul, one_smul] at hst
    refine absurd ?_ huv
    rw [← neg_eq_of_add_eq_zero_right hst]
    exact (neg_eq_self_of_two_eq_zero (K := K) IsF2.two_eq_zero u).symm

variable [FiniteDimensional K V]

theorem exists_polar_prescribed (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} {s : Fin n → V}
    (hs : LinearIndependent K s) (c : Fin n → K) : ∃ v, ∀ i, polar Q (s i) v = c i := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ hs
  refine ⟨∑ j, c j • g j, fun i => ?_⟩
  have : polar Q (s i) (∑ j, c j • g j) = ∑ j, c j * polar Q (s i) (g j) := by
    rw [← polarBilin_apply_apply, map_sum]
    simp only [polarBilin_apply_apply, polar_smul_right_eq]
  rw [this]
  simp [hg]

theorem exists_common_nonperp (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V) {u v : V}
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) (hu : Q u = 0) (hv : Q v = 0) :
    ∃ z, Q z = 0 ∧ polar Q u z = 1 ∧ polar Q v z = 1 := by
  rcases IsF2.eq_zero_or_one (polar Q u v) with h | h
  · obtain ⟨v₀, hv₀⟩ := exists_polar_prescribed hQ (linearIndependent_pair_of_ne hu0 hv0 huv)
      ![1, 1]
    have h1 : polar Q u v₀ = 1 := by simpa using hv₀ 0
    have h2 : polar Q v v₀ = 1 := by simpa using hv₀ 1
    have hvu : polar Q v u = 0 := by rw [polar_comm, h]
    refine ⟨v₀ + Q v₀ • u, ?_, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu, mul_zero, add_zero, polar_smul_right_eq,
        polar_comm Q v₀ u, h1, mul_one]
      exact IsF2.add_self_eq_zero _
    · rw [polar_add_right, polar_smul_right_eq, polar_self_f2, h1, mul_zero, add_zero]
    · rw [polar_add_right, polar_smul_right_eq, hvu, h2, mul_zero, add_zero]
  · obtain ⟨w, hw, huw, hvw⟩ := exists_map_eq_one_polar_eq_zero hQ hd h
    have hvu : polar Q v u = 1 := by rw [polar_comm, h]
    refine ⟨u + v + w, ?_, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, hu, hv, hw, h, polar_add_left, huw, hvw]
      simp only [zero_add, add_zero]
      exact IsF2.one_add_one
    · rw [polar_add_right, polar_add_right, polar_self_f2, h, huw]
      simp
    · rw [polar_add_right, polar_add_right, hvu, polar_self_f2, hvw]
      simp

theorem exists_mem_elementaryGroup_apply_eq_f2 (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) {u v : V} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : Q u = 0) (hv : Q v = 0) :
    ∃ g ∈ elementaryGroup Q, g u = v := by
  by_cases huv : u = v
  · exact ⟨1, one_mem _, by simp [huv]⟩
  obtain ⟨z, hz, h1, h2⟩ := exists_common_nonperp hQ hd hu0 hv0 huv hu hv
  refine ⟨eichler Q z ((1 : K)⁻¹ • (v - u)), eichler_mem_elementaryGroup Q _ _, ?_⟩
  exact eichler_apply_eq_of_polar_eq hz (by rw [hu, hv]) (t := 1) (by rw [polar_comm]; exact h1)
    (by rw [polar_comm]; exact h2) one_ne_zero

theorem exists_singular_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) (hd : 3 ≤ finrank K V)
    {x : V} (hx : Q x = 1) : ∃ u, Q u = 0 ∧ polar Q x u = 1 := by
  obtain ⟨u₀, hu₀0, hu₀⟩ := exists_ne_zero_map_eq_zero' (Q := Q) hd
  rcases IsF2.eq_zero_or_one (polar Q x u₀) with h | h
  · have hx0 : x ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hx; exact zero_ne_one hx
    have hxu : u₀ ≠ x := fun h0 => by rw [h0, hx] at hu₀; exact one_ne_zero hu₀
    obtain ⟨h₀, hh₀⟩ := exists_polar_prescribed hQ (linearIndependent_pair_of_ne hu₀0 hx0 hxu)
      ![1, 1]
    have h1 : polar Q u₀ h₀ = 1 := by simpa using hh₀ 0
    have h2 : polar Q x h₀ = 1 := by simpa using hh₀ 1
    refine ⟨h₀ + Q h₀ • u₀, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu₀, mul_zero, add_zero, polar_smul_right_eq,
        polar_comm Q h₀ u₀, h1, mul_one]
      exact IsF2.add_self_eq_zero _
    · rw [polar_add_right, polar_smul_right_eq, h, h2, mul_zero, add_zero]
  · exact ⟨u₀, hu₀, h⟩

theorem eq_one_of_fixes_singular (hQ : (polarBilin Q).Nondegenerate) (hd : 3 ≤ finrank K V)
    {g : V ≃ₗ[K] V} (hg : ∀ v, v ≠ 0 → Q v = 0 → g v = v) : g = 1 := by
  refine LinearEquiv.ext fun x => ?_
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]; rfl
  by_cases hx : Q x = 0
  · exact hg x hx0 hx
  have hx1 : Q x = 1 := IsF2.eq_one_of_ne_zero hx
  obtain ⟨u, hu, hxu⟩ := exists_singular_polar_eq_one hQ hd hx1
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, polar_zero_right] at hxu; exact zero_ne_one hxu
  have hQxu : Q (x + u) = 0 := by
    rw [QuadraticMap.map_add Q, hx1, hu, hxu, add_zero]
    exact IsF2.one_add_one
  have hxu0 : x + u ≠ 0 := fun h0 => by
    have : x = -u := eq_neg_of_add_eq_zero_left h0
    rw [this, QuadraticMap.map_neg, hu] at hx1
    exact zero_ne_one hx1
  have h1 := hg _ hxu0 hQxu
  have h2 := hg _ hu0 hu
  rw [map_add, h2] at h1
  exact add_right_cancel h1

abbrev SingVec (Q : QuadraticForm K V) : Type _ := {v : V // v ≠ 0 ∧ Q v = 0}

instance : MulAction (elementaryGroup Q) (SingVec Q) where
  smul g v := ⟨(g : V ≃ₗ[K] V) v.1, fun h => v.2.1 ((g : V ≃ₗ[K] V).map_eq_zero_iff.mp h),
    by rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2), v.2.2]⟩
  one_smul v := Subtype.ext rfl
  mul_smul g h v := Subtype.ext rfl

theorem coe_smul_singVec (g : elementaryGroup Q) (v : SingVec Q) :
    ((g • v : SingVec Q) : V) = (g : V ≃ₗ[K] V) v.1 := rfl

theorem faithfulSMul_singVec (hQ : (polarBilin Q).Nondegenerate) (hd : 3 ≤ finrank K V) :
    FaithfulSMul (elementaryGroup Q) (SingVec Q) := by
  refine faithfulSMul_iff.mpr fun g hg => ?_
  refine Subtype.ext (eq_one_of_fixes_singular hQ hd fun v hv0 hv => ?_)
  have := congrArg Subtype.val (hg ⟨v, hv0, hv⟩)
  exact this

theorem isPretransitive_singVec (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V) :
    MulAction.IsPretransitive (elementaryGroup Q) (SingVec Q) := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg, hgp⟩ := exists_mem_elementaryGroup_apply_eq_f2 hQ hd p.2.1 q.2.1 p.2.2 q.2.2
  exact ⟨⟨g, hg⟩, Subtype.ext hgp⟩

theorem exists_plane_of_orth_singular {u w : V} (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hwu : w ≠ u)
    (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ x ∈ W, Q x = 0 := by
  refine ⟨Submodule.span K {u, w}, ?_, fun x hx => map_eq_zero_of_mem_span (Q := Q) ?_ ?_ hx⟩
  · have hli := linearIndependent_pair_of_ne (K := K) hu0 hw0 (Ne.symm hwu)
    rw [← Matrix.range_cons_cons_empty u w ![], finrank_span_eq_card hli, Fintype.card_fin]
  · rintro z (rfl | rfl)
    · exact hu
    · exact hw
  · rintro z (rfl | rfl) z' (rfl | rfl)
    · exact polar_self_eq_zero hu
    · exact huw
    · rw [polar_comm]; exact huw
    · exact polar_self_eq_zero hw

private theorem smul_mem_block {B : Set (SingVec Q)}
    (hB : MulAction.IsBlock (elementaryGroup Q) B) {p q : SingVec Q} (hp : p ∈ B) (hq : q ∈ B)
    {g : elementaryGroup Q} (hg : g • p = p) : g • q ∈ B := by
  have h := hB.smul_eq_of_mem hp (by rwa [hg])
  rw [← h]
  exact Set.smul_mem_smul_set hq

theorem mem_block_of_polar {B : Set (SingVec Q)} (hB : MulAction.IsBlock (elementaryGroup Q) B)
    {p q r : SingVec Q} (hp : p ∈ B) (hq : q ∈ B) (hpq : polar Q p.1 q.1 = 1)
    (hpr : polar Q p.1 r.1 = 1) : r ∈ B := by
  set g : elementaryGroup Q :=
    ⟨eichler Q p.1 ((1 : K)⁻¹ • (r.1 - q.1)), eichler_mem_elementaryGroup Q _ _⟩ with hg
  have hgp : g • p = p := Subtype.ext (eichler_apply_self _ _)
  have hgq : g • q = r := Subtype.ext
    (eichler_apply_eq_of_polar_eq p.2.2 (by rw [q.2.2, r.2.2]) hpq hpr one_ne_zero)
  have := smul_mem_block hB hp hq hgp
  rwa [hgq] at this

theorem eq_univ_of_block_polar (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V)
    {B : Set (SingVec Q)} (hB : MulAction.IsBlock (elementaryGroup Q) B) {p q : SingVec Q}
    (hp : p ∈ B) (hq : q ∈ B) (hpq : polar Q p.1 q.1 = 1) : B = Set.univ := by
  refine Set.eq_univ_of_forall fun r => ?_
  rcases IsF2.eq_zero_or_one (polar Q p.1 r.1) with h | h
  · by_cases hrp : r = p
    · rw [hrp]; exact hp
    · obtain ⟨z, hz, h1, h2⟩ := exists_common_nonperp hQ hd p.2.1 r.2.1
        (fun h => hrp (Subtype.ext h.symm)) p.2.2 r.2.2
      have hz0 : z ≠ 0 := fun h0 => by rw [h0, polar_zero_right] at h1; exact zero_ne_one h1
      have hzB : (⟨z, hz0, hz⟩ : SingVec Q) ∈ B := mem_block_of_polar hB hp hq hpq h1
      exact mem_block_of_polar hB hzB hp (p := ⟨z, hz0, hz⟩) (by rw [polar_comm]; exact h1)
        (by rw [polar_comm]; exact h2)
  · exact mem_block_of_polar hB hp hq hpq h

theorem isPreprimitive_singVec (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    MulAction.IsPreprimitive (elementaryGroup Q) (SingVec Q) := by
  have := isPretransitive_singVec hQ hd
  obtain ⟨u₀, hu00, hu₀⟩ := exists_ne_zero_map_eq_zero' (Q := Q) (by omega)
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base (⟨u₀, hu00, hu₀⟩ : SingVec Q)
    fun {B} hα hB => ?_
  set α : SingVec Q := ⟨u₀, hu00, hu₀⟩ with hαdef
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨q, hqB, hqα⟩ : ∃ q ∈ B, q ≠ α := by
    by_contra hcon
    push Not at hcon
    exact hsub fun p hp q hq => by rw [hcon p hp, hcon q hq]
  rcases IsF2.eq_zero_or_one (polar Q α.1 q.1) with h | h
  · rcases hE with h5 | hplane
    ·
      obtain ⟨f, hf⟩ := exists_polar_prescribed hQ
        (linearIndependent_pair_of_ne α.2.1 q.2.1 (fun h => hqα (Subtype.ext h.symm))) ![0, 1]
      have hf0 : polar Q α.1 f = 0 := by simpa using hf 0
      have hf1 : polar Q q.1 f = 1 := by simpa using hf 1
      have hqq : polar Q q.1 q.1 = 0 := polar_self_f2 _
      obtain ⟨a, haQ, haα, haq⟩ : ∃ a, Q a = 0 ∧ polar Q α.1 a = 0 ∧ polar Q q.1 a = 1 := by
        refine ⟨f + Q f • q.1, ?_, ?_, ?_⟩
        · rw [QuadraticMap.map_add Q, map_smul_eq_sq, q.2.2, mul_zero, add_zero,
            polar_smul_right_eq, polar_comm Q f q.1, hf1, mul_one]
          exact IsF2.add_self_eq_zero _
        · rw [polar_add_right, polar_smul_right_eq, hf0, h, mul_zero, add_zero]
        · rw [polar_add_right, polar_smul_right_eq, hf1, hqq, mul_zero, add_zero]
      obtain ⟨b, hαb, hab, hb⟩ := exists_polar_eq_zero_map_ne_zero hQ h5 α.1 a
      have hb1 : Q b = 1 := IsF2.eq_one_of_ne_zero hb
      set g : elementaryGroup Q := ⟨eichler Q a b, eichler_mem_elementaryGroup Q a b⟩ with hg
      have hgα : g • α = α :=
        Subtype.ext (eichler_apply_of_polar_eq_zero haα hαb)
      have hgq := smul_mem_block hB hα hqB hgα
      refine eq_univ_of_block_polar hQ hd hB hqB hgq ?_
      rw [coe_smul_singVec, hg]
      change polar Q q.1 (eichler Q a b q.1) = 1
      rw [eichler_apply haQ hab, polar_sub_right, polar_add_right, polar_smul_right_eq,
        polar_smul_right_eq, hqq, haq, hb1]
      linear_combination (-1 : K) * (IsF2.two_eq_zero (K := K))
    · exfalso
      exact hplane (exists_plane_of_orth_singular α.2.1 q.2.1 (fun h => hqα (Subtype.ext h))
        α.2.2 q.2.2 h)
  · exact eq_univ_of_block_polar hQ hd hB hα hqB h

theorem normalClosure_rootGroup_eq_top_f2 (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) {u₀ : V} (hu₀0 : u₀ ≠ 0) (hu₀ : Q u₀ = 0) :
    Subgroup.normalClosure
      (((rootGroup Q u₀).subgroupOf (elementaryGroup Q) : Subgroup (elementaryGroup Q)) :
        Set (elementaryGroup Q)) = ⊤ := by
  set N := Subgroup.normalClosure
    (((rootGroup Q u₀).subgroupOf (elementaryGroup Q) : Subgroup (elementaryGroup Q)) :
      Set (elementaryGroup Q))
  have hN : N.Normal := Subgroup.normalClosure_normal
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 →
      (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ∈ N := by
    intro u w hu hw
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact N.one_mem
    obtain ⟨g, hg, hgu⟩ := exists_mem_elementaryGroup_apply_eq_f2 hQ hd hu₀0 hu0 hu₀ hu
    have hgO := elementaryGroup_le_orthogonalGroup Q hg
    have hv : polar Q u₀ (g⁻¹ w) = 0 := by
      rw [← polar_map_of_mem hgO, hgu, LinearEquiv.apply_inv_apply', hw]
    have hmemU : (⟨eichler Q u₀ (g⁻¹ w), eichler_mem_elementaryGroup Q _ _⟩ :
        elementaryGroup Q) ∈ N :=
      Subgroup.subset_normalClosure (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact eichler_mem_rootGroup hv)
    have hmem := hN.conj_mem _ hmemU ⟨g, hg⟩
    convert hmem using 1
    apply Subtype.ext
    change eichler Q u w = g * eichler Q u₀ (g⁻¹ w) * g⁻¹
    rw [eichler_conj hgO, hgu, LinearEquiv.apply_inv_apply']
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    exact hgen u w hu hw
  | one => exact N.one_mem
  | mul x y hx hy ihx ihy => exact N.mul_mem ihx ihy
  | inv x hx ihx => exact N.inv_mem ihx

theorem isSimpleGroup_elementaryGroup_of_perfect (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hperf : commutator (elementaryGroup Q) = ⊤) : IsSimpleGroup (elementaryGroup Q) := by
  obtain ⟨u₀, hu₀0, hu₀⟩ := exists_ne_zero_map_eq_zero' (Q := Q) (by omega)
  have hF := faithfulSMul_singVec hQ (by omega : 3 ≤ finrank K V)
  have hP := isPreprimitive_singVec hQ hd hE
  have hT := isPretransitive_singVec hQ hd
  obtain ⟨P, hPe⟩ := exists_hypPair hQ hu₀ hu₀0
  have hnt : Nontrivial (elementaryGroup Q) := by
    obtain ⟨g, hg, hgf⟩ := exists_mem_elementaryGroup_apply_eq_f2 hQ hd P.e_ne_zero P.f_ne_zero
      P.Q_e P.Q_f
    refine ⟨⟨⟨g, hg⟩, 1, fun h1 => ?_⟩⟩
    have hx := congrArg (fun z : elementaryGroup Q => ((z • (⟨P.e, P.e_ne_zero, P.Q_e⟩ : SingVec Q)
      : SingVec Q) : V)) h1
    simp only [one_smul, coe_smul_singVec] at hx
    have : P.f = P.e := hgf ▸ hx
    have h3 := P.polar_ef
    rw [this, P.polar_ee] at h3
    exact zero_ne_one h3
  set α : SingVec Q := ⟨u₀, hu₀0, hu₀⟩ with hα
  set T := (rootGroup Q u₀).subgroupOf (elementaryGroup Q) with hTdef
  have hTle : T ≤ MulAction.stabilizer (elementaryGroup Q) α := by
    intro t ht
    rw [MulAction.mem_stabilizer_iff]
    rw [hTdef, Subgroup.mem_subgroupOf, mem_rootGroup] at ht
    obtain ⟨w, -, hw⟩ := ht
    exact Subtype.ext (by
      rw [coe_smul_singVec, ← hw, eichler_apply_self])
  have hTnormal : (T.subgroupOf (MulAction.stabilizer (elementaryGroup Q) α)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTle]
    intro t g ht hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have hgu : (g : V ≃ₗ[K] V) u₀ = (1 : K) • u₀ := by
      rw [one_smul]
      exact congrArg Subtype.val hg
    rw [hTdef, Subgroup.mem_subgroupOf] at ht ⊢
    exact conj_mem_rootGroup_of_apply_eq_smul (elementaryGroup_le_orthogonalGroup Q g.2) hgu ht
  have hTsolv : Group.IsSolvable T := by
    apply Group.isSolvable_of_comm
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [hTdef, Subgroup.mem_subgroupOf] at ha hb
    exact rootGroup_commute ha hb
  have hTgen := normalClosure_rootGroup_eq_top_f2 hQ hd hu₀0 hu₀
  exact CFSG.BenderSuzuki.External.huppert_II_6_12 hperf α T hTle hTnormal hTsolv hTgen

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
