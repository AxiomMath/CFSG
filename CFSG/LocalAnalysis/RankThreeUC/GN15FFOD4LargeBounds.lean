module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4OuterIndex
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4OuterOnly
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4ElemBound
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderOrder
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Quasithin CFSG.QuasithinUnique.Setup

theorem card_orthElementaryGroup_lt {K : Type} [Field K] [Finite K] [CharP K 2] :
    Nat.card (orthElementaryGroup (quadPlus 4 K)) < Nat.card K ^ 28 := by
  rw [orthElementaryGroup]
  have hq2 : 2 ≤ Nat.card K := by
    have h : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  have hqZ : (2 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq2
  have hqpos : (0 : ℤ) < (Nat.card K : ℤ) := by linarith
  set q : ℤ := (Nat.card K : ℤ) with hqdef
  have hpowpos : ∀ m : ℕ, (0 : ℤ) < q ^ m := fun m => pow_pos hqpos m
  have h1 : q ^ 2 - 1 < q ^ 2 := by linarith
  have h2 : q ^ 4 - 1 < q ^ 4 := by linarith
  have h3 : q ^ 6 - 1 < q ^ 6 := by linarith
  have h2pos : (0 : ℤ) < q ^ 2 - 1 := by nlinarith [hpowpos 2]
  have h4pos : (0 : ℤ) < q ^ 4 - 1 := by nlinarith [hpowpos 4]
  have h6pos : (0 : ℤ) < q ^ 6 - 1 := by nlinarith [hpowpos 6]
  have hprod : (∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1)) =
      (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) := by
    have hIcc : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
    rw [hIcc]
    norm_num
    ring
  have hprod_lt : (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) < q ^ 2 * q ^ 4 * q ^ 6 := by
    have hA : (q ^ 2 - 1) * (q ^ 4 - 1) < q ^ 2 * q ^ 4 :=
      mul_lt_mul h1 (le_of_lt h2) h4pos (le_of_lt (hpowpos 2))
    refine mul_lt_mul hA (le_of_lt h3) h6pos (le_of_lt ?_)
    exact mul_pos (hpowpos 2) (hpowpos 4)
  have hord := CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadPlus
    (K := K) (n := 4) (by norm_num)
  have hltZ : (Nat.card (elementaryGroup (quadPlus 4 K)) : ℤ) < q ^ 28 := by
    rw [hord]
    show q ^ (4 * (4 - 1)) * (q ^ 4 - 1) *
      (∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1)) < q ^ 28
    rw [show 4 * (4 - 1) = 12 by norm_num, show 4 - 1 = 3 by norm_num, hprod]
    have hq12 : (0 : ℤ) < q ^ 12 := hpowpos 12
    have hq4 : (0 : ℤ) < q ^ 4 := hpowpos 4
    have hprodpos : (0 : ℤ) < (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
      mul_pos (mul_pos h2pos h4pos) h6pos
    calc q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))
        < q ^ 12 * q ^ 4 * (q ^ 2 * q ^ 4 * q ^ 6) :=
          mul_lt_mul (mul_lt_mul_of_pos_left h2 hq12) (le_of_lt hprod_lt) hprodpos
            (le_of_lt (mul_pos hq12 hq4))
      _ = q ^ 28 := by ring
  rw [hqdef] at hltZ
  exact_mod_cast hltZ

theorem card_lt_of_quadratic_offender
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (L E : Subgroup (MulAut V))
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    Nat.card V < 4 * Nat.card K ^ 28 := by
  have hLq : CFSG.IsQuasisimple ↥L := by
    refine CFSG.IsQuasisimple.of_mulEquiv
      (θ.trans (statedOmegaEquiv (coe_quadPlus 4 K)
        (commutator_orthogonalGroup_quadPlus (by norm_num))).symm) ?_
    exact CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (n := 4) (by norm_num)
  have hsup := CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_le_card_sup_of_offender
    hV hLq hirr hEN hE hEel hoff
  have hfour := card_le_four_mul_card_inf hV L E θ hirr hEN hEel
  have hcard : Nat.card ↥(L ⊔ E) * Nat.card (L ⊓ E : Subgroup (MulAut V)) =
      Nat.card ↥L * Nat.card ↥E := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := E) (K := L) hEN
    rw [sup_comm E L, inf_comm E L, mul_comm (Nat.card ↥E) (Nat.card ↥L)] at h
    exact h
  have hsup_le : Nat.card ↥(L ⊔ E) ≤ 4 * Nat.card ↥L := by
    have hfour' : Nat.card ↥E ≤ 4 * Nat.card (L ⊓ E : Subgroup (MulAut V)) := by
      simpa [inf_comm] using hfour
    have hpos : 0 < Nat.card (L ⊓ E : Subgroup (MulAut V)) := Nat.card_pos
    apply Nat.le_of_mul_le_mul_right (c := Nat.card (L ⊓ E : Subgroup (MulAut V))) _ hpos
    calc Nat.card ↥(L ⊔ E) * Nat.card (L ⊓ E : Subgroup (MulAut V))
        = Nat.card ↥L * Nat.card ↥E := hcard
      _ ≤ Nat.card ↥L * (4 * Nat.card (L ⊓ E : Subgroup (MulAut V))) :=
          Nat.mul_le_mul_left _ hfour'
      _ = (4 * Nat.card ↥L) * Nat.card (L ⊓ E : Subgroup (MulAut V)) := by ring
  have hLlt : Nat.card ↥L < Nat.card K ^ 28 := by
    rw [Nat.card_congr θ.toEquiv]
    exact card_orthElementaryGroup_lt
  calc Nat.card V ≤ Nat.card ↥(L ⊔ E) := hsup
    _ ≤ 4 * Nat.card ↥L := hsup_le
    _ < 4 * Nat.card K ^ 28 := Nat.mul_lt_mul_of_pos_left hLlt (by norm_num)

theorem exists_involution_card_le_of_offender
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (L E : Subgroup (MulAut V))
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    ∃ x ∈ L, x ≠ 1 ∧ x * x = 1 ∧
      Nat.card V ≤ 2 ^ (7 * n + 2) * Nat.card {v : V // x v = v} := by
  have hfour := card_le_four_mul_card_inf hV L E θ hirr hEN hEel
  by_cases hInt : E ⊓ L ≠ ⊥
  ·
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hInt
    have hxE : (x : MulAut V) ∈ E := (Subgroup.mem_inf.mp x.2).1
    have hxL : (x : MulAut V) ∈ L := (Subgroup.mem_inf.mp x.2).2
    have hx1 : (x : MulAut V) ≠ 1 := fun h => hxne (Subtype.ext h)
    have hx2 : (x : MulAut V) * (x : MulAut V) = 1 := by
      simpa [pow_two] using hEel.2 (x : MulAut V) hxE
    have hEL7 : Nat.card (E ⊓ L : Subgroup (MulAut V)) ≤ 2 ^ (7 * n) := by
      let A : Subgroup (orthElementaryGroup (quadPlus 4 K)) :=
        ((E ⊓ L).subgroupOf L).map θ.toMonoidHom
      have hcardA : Nat.card A = Nat.card (E ⊓ L : Subgroup (MulAut V)) := by
        rw [Subgroup.card_map_of_injective θ.injective]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := E ⊓ L) (K := L)
          (inf_le_right)).toEquiv
      have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg θ (Subtype.ext (hEel.1 (a : MulAut V)
          (Subgroup.mem_subgroupOf.mp ha).1 (b : MulAut V)
          (Subgroup.mem_subgroupOf.mp hb).1))
      have hsq : ∀ a ∈ A, a * a = 1 := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_mul, ← map_one θ]
        exact congrArg θ (Subtype.ext (by
          simpa [pow_two] using hEel.2 (a : MulAut V)
            (Subgroup.mem_subgroupOf.mp ha).1))
      have h7 := card_le_pow_seven_of_elemAbelian A hcomm hsq
      have hq7 : Nat.card K ^ 7 = 2 ^ (7 * n) := by
        rw [hK, ← pow_mul, Nat.mul_comm n 7]
      calc Nat.card (E ⊓ L : Subgroup (MulAut V)) = Nat.card A := hcardA.symm
        _ ≤ Nat.card K ^ 7 := h7
        _ = 2 ^ (7 * n) := hq7
    have hEbound : Nat.card E ≤ 2 ^ (7 * n + 2) := by
      calc Nat.card E ≤ 4 * Nat.card (E ⊓ L : Subgroup (MulAut V)) := hfour
        _ ≤ 4 * 2 ^ (7 * n) := Nat.mul_le_mul_left 4 hEL7
        _ = 2 ^ 2 * 2 ^ (7 * n) := by norm_num
        _ = 2 ^ (2 + 7 * n) := by rw [← pow_add]
        _ = 2 ^ (7 * n + 2) := by rw [Nat.add_comm]
    have hfix : Nat.card (fixV E) ≤ Nat.card {v : V // (x : MulAut V) v = v} := by
      refine Nat.card_le_card_of_injective
        (fun u : fixV E => (⟨u.1, u.2 (x : MulAut V) hxE⟩ :
          {v : V // (x : MulAut V) v = v})) ?_
      intro u w huw
      exact Subtype.ext (congrArg
        (fun z : {v : V // (x : MulAut V) v = v} => z.1) huw)
    refine ⟨(x : MulAut V), hxL, hx1, hx2, ?_⟩
    calc Nat.card V ≤ Nat.card E * Nat.card (fixV E) := hoff
      _ ≤ Nat.card E * Nat.card {v : V // (x : MulAut V) v = v} :=
          Nat.mul_le_mul_left _ hfix
      _ ≤ 2 ^ (7 * n + 2) * Nat.card {v : V // (x : MulAut V) v = v} :=
          Nat.mul_le_mul_right _ hEbound
  ·
    push Not at hInt
    have hE2 : Nat.card E ≤ 4 := by
      rw [hInt, Subgroup.card_bot] at hfour
      simpa using hfour
    obtain ⟨e, hene⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    have heE : (e : MulAut V) ∈ E := e.2
    have he1 : (e : MulAut V) ≠ 1 := fun h => hene (Subtype.ext h)
    have he2 : (e : MulAut V) * (e : MulAut V) = 1 := by
      simpa [pow_two] using hEel.2 (e : MulAut V) heE
    have heN : (e : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) := hEN heE
    have heL : (e : MulAut V) ∉ L := by
      intro heL
      have hmem : (e : MulAut V) ∈ E ⊓ L := Subgroup.mem_inf.mpr ⟨heE, heL⟩
      rw [hInt] at hmem
      exact he1 (Subgroup.mem_bot.mp hmem)
    obtain ⟨t, htL, ht1, ht2, hineq⟩ :=
      exists_involution_index_le_of_outer hV θ hirr heN he2 heL
    have hfixe : Nat.card (fixV E) ≤ Nat.card {v : V // (e : MulAut V) v = v} := by
      refine Nat.card_le_card_of_injective
        (fun u : fixV E => (⟨u.1, u.2 (e : MulAut V) heE⟩ :
          {v : V // (e : MulAut V) v = v})) ?_
      intro u w huw
      exact Subtype.ext (congrArg
        (fun z : {v : V // (e : MulAut V) v = v} => z.1) huw)
    have hV4 : Nat.card V ≤ 4 * Nat.card {v : V // (e : MulAut V) v = v} := by
      calc Nat.card V ≤ Nat.card E * Nat.card (fixV E) := hoff
        _ ≤ 4 * Nat.card {v : V // (e : MulAut V) v = v} := Nat.mul_le_mul hE2 hfixe
    let A : ℕ := Nat.card V
    let B : ℕ := Nat.card {v : V // (e : MulAut V) v = v}
    let C : ℕ := Nat.card {v : V // t v = v}
    have hApos : 0 < A := Finite.card_pos_iff.mpr ⟨1⟩
    have hA : A ≤ 4 * B := hV4
    have hBC : A * B ^ 2 ≤ A ^ 2 * C := hineq
    have hA16 : A ≤ 16 * C := by
      have hA2pos : 0 < A ^ 2 := pow_pos hApos 2
      have h1 : A ^ 3 ≤ 16 * (A * B ^ 2) := by
        calc A ^ 3 = A * A ^ 2 := by ring
          _ ≤ A * (16 * B ^ 2) := Nat.mul_le_mul_left A (by
              calc A ^ 2 ≤ (4 * B) ^ 2 := Nat.pow_le_pow_left hA 2
                _ = 16 * B ^ 2 := by ring)
          _ = 16 * (A * B ^ 2) := by ring
      have h2 : 16 * (A * B ^ 2) ≤ 16 * (A ^ 2 * C) := Nat.mul_le_mul_left 16 hBC
      have h3 : A ^ 3 ≤ 16 * A ^ 2 * C := by
        calc A ^ 3 ≤ 16 * (A * B ^ 2) := h1
          _ ≤ 16 * (A ^ 2 * C) := h2
          _ = 16 * A ^ 2 * C := by ring
      have h4 : A * A ^ 2 ≤ (16 * C) * A ^ 2 := by
        calc A * A ^ 2 = A ^ 3 := by ring
          _ ≤ 16 * A ^ 2 * C := h3
          _ = (16 * C) * A ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right h4 hA2pos
    have h16 : (16 : ℕ) ≤ 2 ^ (7 * n + 2) := by
      have h9 : 4 ≤ 7 * n + 2 := by omega
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (7 * n + 2) := Nat.pow_le_pow_right (by norm_num) h9
    refine ⟨t, htL, ht1, ht2, ?_⟩
    calc Nat.card V = A := rfl
      _ ≤ 16 * C := hA16
      _ ≤ 2 ^ (7 * n + 2) * C := Nat.mul_le_mul_right _ h16
      _ = 2 ^ (7 * n + 2) * Nat.card {v : V // t v = v} := rfl

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
