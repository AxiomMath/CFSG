module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLinearCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLinearRow
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLinearAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] {n : ℕ}

theorem blockSpecialLinear_pair_le_sup_of_ne {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hcb : c ≠ b) :
    blockSpecialLinear (K := K) ({a, b} : Finset (Fin n)) ≤
      blockSpecialLinear {a, c} ⊔ blockSpecialLinear {c, b} := by
  rw [LinearPilot.blockSpecialLinear_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, i', hii, s, hi, hi', rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
  have hcomm : ∀ {H₁ H₂ : Subgroup (SpecialLinearGroup (Fin n) K)}
      {x y : SpecialLinearGroup (Fin n) K}, x ∈ H₁ → y ∈ H₂ → x * y * x⁻¹ * y⁻¹ ∈ H₁ ⊔ H₂ :=
    fun {H₁ H₂ x y} hx hy => mul_mem (mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right hy))
      (inv_mem (mem_sup_left hx))) (inv_mem (mem_sup_right hy))
  have hmem1 : ∀ {u v : Fin n}, u ∈ ({u, v} : Finset (Fin n)) := fun {u v} =>
    Finset.mem_insert_self u {v}
  have hmem2 : ∀ {u v : Fin n}, v ∈ ({u, v} : Finset (Fin n)) := fun {u v} =>
    Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
  · exact absurd rfl hii
  · have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hac hcb hab s (1 : K)
    rw [mul_one, commutatorElement_def] at h
    rw [SetLike.mem_coe, ← h]
    exact hcomm (LinearPilot.transvection_mem_blockSpecialLinear hac hmem1 hmem2 s)
      (LinearPilot.transvection_mem_blockSpecialLinear hcb hmem1 hmem2 1)
  · have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hcb.symm hac.symm hab.symm
      s (1 : K)
    rw [mul_one, commutatorElement_def] at h
    rw [SetLike.mem_coe, ← h, sup_comm]
    exact hcomm (LinearPilot.transvection_mem_blockSpecialLinear hcb.symm hmem2 hmem1 s)
      (LinearPilot.transvection_mem_blockSpecialLinear hac.symm hmem2 hmem1 1)
  · exact absurd rfl hii

end Model

section Commute

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {hK : Nat.card K = 2}
  {e : L ≃* StatedSp 4 K}

theorem blockSpecialLinear_pair_le_q2Block {a b : Fin (2 * 4 + 1)} {R : Finset (Fin 4)}
    (ha : a ∉ planeCoordsQ2 1 R) (hb : b ∉ planeCoordsQ2 1 R) :
    blockSpecialLinear (K := K) ({a, b} : Finset (Fin (2 * 4 + 1))) ≤ q2Block 1 K R := by
  refine LinearPilot.blockSpecialLinear_mono fun x hx => ?_
  rw [Finset.mem_compl]
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  · rw [Finset.mem_singleton.1 hx]
    exact hb

theorem commute_of_nsLinParamAgree_four_odd [CharP K 2] (P : ∀ k : Fin 4, NsLinParam hK 1 e k)
    (hagree : NsLinParamAgree P) :
    ∀ x ∈ blockSpecialLinear ({ctF 4 1 0, ctE 4 1 1} : Finset (Fin (2 * 4 + 1))),
      ∀ y ∈ blockSpecialLinear ({ctF 4 1 2, ctE 4 1 3} : Finset (Fin (2 * 4 + 1))),
      ∀ (hx : x ∈ q2Block 1 K {2}) (hy : y ∈ q2Block 1 K {0}),
        Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩) := by
  intro x hx y hy hx2 hy0
  set v : Fin (2 * 4 + 1) := q2Coord 4 1 (Sum.inr 0) with hv
  have hvR : ∀ R : Finset (Fin 4), v ∉ planeCoordsQ2 1 R := fun R => by
    rw [hv, q2Coord_mem_planeCoordsQ2]
    exact not_inPlanes_inr R 0
  have hoff : ∀ {p k : Fin 4} (u : Fin 4 ⊕ Fin 4), planeOf u = p → p ≠ k →
      q2Coord 4 1 (Sum.inl u) ∉ planeCoordsQ2 1 {k} := fun u hu hpk =>
    q2Coord_inl_notMem hpk u hu
  have hy1 : y ∈ q2Block 1 K {1} :=
    blockSpecialLinear_pair_le_q2Block (hoff (p := 2) _ rfl (by decide))
      (hoff (p := 3) _ rfl (by decide)) hy
  have hdisj : ∀ {R : Finset (Fin 4)}, 2 ∈ R → 3 ∈ R →
      Disjoint ((planeCoordsQ2 1 R)ᶜ) ({ctF 4 1 2, ctE 4 1 3} : Finset (Fin (2 * 4 + 1))) := by
    intro R h2 h3
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_compl] at ha
    apply ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl]
      exact h2
    · rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl]
      exact h3
  set C : Subgroup G := centralizer ({(P 0).Φ ⟨y, hy0⟩} : Set G) with hC
  set M : Subgroup (SpecialLinearGroup (Fin (2 * 4 + 1)) K) :=
    (C.comap (P 2).Φ).map (q2Block 1 K {2}).subtype with hM
  have hmemM : ∀ (z : SpecialLinearGroup (Fin (2 * 4 + 1)) K) (hz : z ∈ q2Block 1 K {2}),
      (P 2).Φ ⟨z, hz⟩ ∈ C → z ∈ M := fun z hz h => ⟨⟨z, hz⟩, h, rfl⟩
  have h1 : blockSpecialLinear ({ctF 4 1 0, v} : Finset (Fin (2 * 4 + 1))) ≤ M := by
    intro z hz
    have hz2 : z ∈ q2Block 1 K {2} :=
      blockSpecialLinear_pair_le_q2Block (hoff (p := 0) _ rfl (by decide)) (hvR _) hz
    have hz1 : z ∈ q2Block 1 K {1} :=
      blockSpecialLinear_pair_le_q2Block (hoff (p := 0) _ rfl (by decide)) (hvR _) hz
    have hz123 : z ∈ q2Block 1 K {1, 2, 3} :=
      blockSpecialLinear_pair_le_q2Block (by
        rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl]
        decide) (hvR _) hz
    refine hmemM z hz2 ?_
    rw [hC, mem_centralizer_singleton_iff, hagree 2 1 z hz2 hz1, hagree 0 1 y hy0 hy1,
      ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (LinearPilot.commute_blockSpecialLinear_of_disjoint
      (hdisj (by decide) (by decide)) hz123 hy).eq
  have h2 : blockSpecialLinear ({v, ctE 4 1 1} : Finset (Fin (2 * 4 + 1))) ≤ M := by
    intro z hz
    have hz2 : z ∈ q2Block 1 K {2} :=
      blockSpecialLinear_pair_le_q2Block (hvR _) (hoff (p := 1) _ rfl (by decide)) hz
    have hz0 : z ∈ q2Block 1 K {0} :=
      blockSpecialLinear_pair_le_q2Block (hvR _) (hoff (p := 1) _ rfl (by decide)) hz
    have hz023 : z ∈ q2Block 1 K {0, 2, 3} :=
      blockSpecialLinear_pair_le_q2Block (hvR _) (by
        rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl]
        decide) hz
    refine hmemM z hz2 ?_
    rw [hC, mem_centralizer_singleton_iff, hagree 2 0 z hz2 hz0, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (LinearPilot.commute_blockSpecialLinear_of_disjoint
      (hdisj (by decide) (by decide)) hz023 hy).eq
  have hne1 : ctF 4 1 0 ≠ ctE 4 1 1 := fun h => ctE_ne_ctF (N := 4) (ε := 1) 1 0 h.symm
  have hne2 : ctF 4 1 0 ≠ v := fun h => Sum.inl_ne_inr ((q2Coord 4 1).injective h)
  have hne3 : v ≠ ctE 4 1 1 := fun h => Sum.inl_ne_inr ((q2Coord 4 1).injective h.symm)
  have hxM := (blockSpecialLinear_pair_le_sup_of_ne hne1 hne2 hne3).trans (sup_le h1 h2) hx
  obtain ⟨⟨x', hx'⟩, hx'C, hxx⟩ := hxM
  have hxx' : (⟨x', hx'⟩ : q2Block 1 K {2}) = ⟨x, hx2⟩ := Subtype.ext hxx
  rw [hxx'] at hx'C
  exact (mem_centralizer_singleton_iff.1 hx'C)

end Commute

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem sp2mKindType_nsGlobal_linearOdd_four (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* StatedSp 4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin 4, NsKindSp e t k .linearOdd) :
    Sp2mKindType (nsGlobal e) 4 1 .linearOdd := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have P : ∀ k : Fin 4, NsLinParam hK 1 e k := fun k =>
    (nonempty_nsLinParam (m := 3) hset hK le_rfl le_rfl e htC ht k (Or.inr ⟨rfl, rfl⟩)
      (hroot k)).some
  obtain ⟨Q, hQ⟩ := exists_nsLinParamAgree_odd le_rfl P
  obtain ⟨-, -, -, hty⟩ := exists_injective_nsLinRow_four_of_agree le_rfl Q hQ
    (commute_of_nsLinParamAgree_four_odd Q hQ)
  exact hty

end Recognition

section Rows

theorem spTwoRowEightInput_linearOdd_holds : SpTwoRowEightInput .linearOdd := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  subst hn
  exact false_of_sp2mKindType_nsGlobal_linearOdd hset hK le_rfl e ht hKt
    (sp2mKindType_nsGlobal_linearOdd_four hset hK e ht hKt hroot)

theorem spTwoRowInput_linearOdd_holds : SpTwoRowInput .linearOdd :=
  spTwoRowInput_of_eight_of_four_le spTwoRowEightInput_linearOdd_holds
    spTwoRowInput_linearOdd_of_five_le

end Rows

@[expose] def SpTwoGraphKindEightInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k κ) → Sp2mKindType (nsGlobal e) 4 1 κ

@[expose] def SpTwoLinearEvenEightAgreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k .linearEven) →
      ∃ P : ∀ k : Fin 4, NsLinParam hK 0 e k, NsLinParamAgree P ∧
        ∀ x ∈ blockSpecialLinear ({ctF 4 0 0, ctE 4 0 1} : Finset (Fin (2 * 4 + 0))),
        ∀ y ∈ blockSpecialLinear ({ctF 4 0 2, ctE 4 0 3} : Finset (Fin (2 * 4 + 0))),
        ∀ (hx : x ∈ q2Block 0 K {2}) (hy : y ∈ q2Block 0 K {0}),
          Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩)

theorem spTwoGraphKindEightInput_linearEven_of_agree (h : SpTwoLinearEvenEightAgreeInput) :
    SpTwoGraphKindEightInput .linearEven := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  obtain ⟨P, hP, hcomm⟩ := h G L hset K hK e t ht hKt hroot
  obtain ⟨-, -, -, hty⟩ := exists_injective_nsLinRow_four_of_agree (zero_le_one) P hP hcomm
  exact hty

@[expose] def SpTwoLinearEvenSecondClassEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k .linearEven) → NsRowGlobal e t .linearEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ¬ IsCharacteristicP 2
          (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩))

section RowsEven

theorem spTwoRowEightInput_linearEven_of_inputs (hkind : SpTwoGraphKindEightInput .linearEven)
    (h2 : SpTwoLinearEvenSecondClassEightInput) : SpTwoRowEightInput .linearEven := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  subst hn
  exact false_of_sp2mKindType_nsGlobal_linearEven hset hK le_rfl e ht hKt
    (hkind G L hset K hK e t ht hKt hroot)
    (fun hglob => h2 G L hset K hK e t ht hKt hroot hglob)

theorem spTwoRowInput_linearEven_of_inputs (hagree : SpTwoLinearEvenEightAgreeInput)
    (h8 : SpTwoLinearEvenSecondClassEightInput) (h2 : SpTwoLinearEvenSecondClassInput) :
    SpTwoRowInput .linearEven :=
  spTwoRowInput_of_eight_of_four_le
    (spTwoRowEightInput_linearEven_of_inputs (spTwoGraphKindEightInput_linearEven_of_agree hagree)
      h8)
    (spTwoRowInput_linearEven_of_five_le h2)

end RowsEven

end CFSG.SeitzReduction.SymplecticPilot
