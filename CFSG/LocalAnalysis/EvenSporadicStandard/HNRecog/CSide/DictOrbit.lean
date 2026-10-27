module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Section3
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

private abbrev abOf (q : Q) : Additive (Abelianization Q) :=
  Additive.ofMul (Abelianization.of q)

theorem cSide_orbit_partition [Finite Q] (hE : IsExtraspecialPGroup 2 Q)
    (O : Fin 2 → Set (Additive (Abelianization Q)))
    (hcover : ∀ v, (v ≠ 0 ∧ extraspecialQuadForm hE v = 0) ↔ ∃ i, v ∈ O i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j)) (hne : ∀ i, (O i).Nonempty)
    (hinv : ∀ i, ∀ c : C, ∀ v ∈ O i, conjLinEquiv hQn c v ∈ O i)
    (htrans : ∀ i, ∀ v ∈ O i, ∀ w ∈ O i, ∃ c : C, conjLinEquiv hQn c v = w) :
    ∃ S : Fin 2 → Set C,
      IsOrbitPartition (⊤ : Subgroup C) {q | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} S ∧
        ∀ i, Nat.card ↥(S i) = 2 * Nat.card ↥(O i) := by
  classical
  have h_mul : ∀ u v : Q, abOf (u * v) = abOf u + abOf v := fun u v => ofMul_of_mul u v
  have h_inv : ∀ u : Q, abOf u⁻¹ = -abOf u := fun u => by
    show Additive.ofMul (Abelianization.of u⁻¹) = -Additive.ofMul (Abelianization.of u)
    rw [map_inv, ofMul_inv]
  have h_zero : ∀ u : Q, abOf u = 0 ↔ u ∈ Subgroup.center Q := fun u =>
    ofMul_of_eq_zero_iff hE u
  have h_qform : ∀ u : Q, extraspecialQuadForm hE (abOf u) = 0 ↔ u ^ 2 = 1 := by
    intro u
    have h := extraspecialQuadForm_apply hE u
    show extraspecialQuadForm hE (Additive.ofMul (Abelianization.of u)) = 0 ↔ u ^ 2 = 1
    rw [h]
    by_cases h2 : u ^ 2 = 1
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]; simp [h2]
  have h_conj : ∀ (g : C) (u : Q), conjLinEquiv hQn g (abOf u) = abOf (conjAut hQn g u) :=
    fun g u => conjLinEquiv_apply hQn g u
  have fib : ∀ u v : Q, abOf u = abOf v ↔ u * v⁻¹ ∈ Subgroup.center Q := by
    intro u v
    have hsub : abOf u - abOf v = abOf (u * v⁻¹) := by
      rw [h_mul, h_inv]
      abel
    rw [← sub_eq_zero, hsub, h_zero]
  let T : Fin 2 → Set Q := fun i => {q | abOf q ∈ O i}
  let S : Fin 2 → Set C := fun i => Subtype.val '' T i
  have hS : ∀ i x, x ∈ S i ↔ ∃ hx : x ∈ Q, abOf ⟨x, hx⟩ ∈ O i := by
    intro i x
    constructor
    · rintro ⟨q, hqT, hq⟩
      rw [← hq]
      exact ⟨q.2, hqT⟩
    · rintro ⟨hx, hxO⟩
      exact ⟨⟨x, hx⟩, hxO, rfl⟩
  have hcardT : ∀ i, Nat.card ↥(T i) =
      Nat.card ↥(O i) * Nat.card ↥(Subgroup.center Q) := by
    intro i
    let c0 : Additive (Abelianization Q) → Q := fun v => Classical.choose (exists_ofMul_of v)
    have c0_spec : ∀ v, abOf (c0 v) = v := fun v => Classical.choose_spec (exists_ofMul_of v)
    let e : ↥(T i) ≃ ↥(O i) × ↥(Subgroup.center Q) :=
      { toFun := fun q =>
          (⟨abOf q.1, q.2⟩,
           ⟨(c0 (abOf q.1))⁻¹ * q.1,
            (h_zero _).mp (by rw [h_mul, h_inv, c0_spec]; abel)⟩)
        invFun := fun p =>
          ⟨c0 (p.1 : Additive (Abelianization Q)) * (p.2 : Q),
           (by
             show abOf (c0 (p.1 : Additive (Abelianization Q)) * (p.2 : Q)) ∈ O i
             have hφ : abOf (c0 (p.1 : Additive (Abelianization Q)) * (p.2 : Q)) =
                 (p.1 : Additive (Abelianization Q)) := by
               rw [h_mul, c0_spec, (h_zero _).mpr p.2.2, add_zero]
             rw [hφ]
             exact p.1.2)⟩
        left_inv := by
          intro q
          apply Subtype.ext
          show c0 (abOf q.1) * ((c0 (abOf q.1))⁻¹ * q.1) = q.1
          group
        right_inv := by
          intro p
          have hφ : abOf (c0 (p.1 : Additive (Abelianization Q)) * (p.2 : Q)) =
              (p.1 : Additive (Abelianization Q)) := by
            rw [h_mul, c0_spec, (h_zero _).mpr p.2.2, add_zero]
          refine Prod.ext ?_ ?_
          · exact Subtype.ext hφ
          · apply Subtype.ext
            show (c0 (abOf (c0 (p.1 : Additive (Abelianization Q)) * (p.2 : Q))))⁻¹ *
                (c0 (p.1 : Additive (Abelianization Q)) * (p.2 : Q)) = (p.2 : Q)
            rw [hφ]
            group }
    rw [Nat.card_congr e, Nat.card_prod]
  have hsubS : ∀ i, S i ⊆ {q | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} := by
    intro i x hx
    obtain ⟨hxQ, hxO⟩ := (hS i x).mp hx
    have hcov := (hcover (abOf ⟨x, hxQ⟩)).mpr ⟨i, hxO⟩
    refine ⟨hxQ, ?_, ?_⟩
    · have h2 : (⟨x, hxQ⟩ : Q) ^ 2 = 1 := (h_qform ⟨x, hxQ⟩).mp hcov.2
      have := congrArg (fun q : Q => (q : C)) h2
      simpa using this
    · intro hxZ
      exact hcov.1 ((h_zero _).mpr ((mem_centerOf_iff ⟨x, hxQ⟩).mp hxZ))
  have hcovS : ∀ x ∈ {q | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q}, ∃ i, x ∈ S i := by
    rintro x ⟨hxQ, hx2, hxZ⟩
    have hφne : abOf ⟨x, hxQ⟩ ≠ 0 := fun h0 =>
      hxZ ((mem_centerOf_iff ⟨x, hxQ⟩).mpr ((h_zero _).mp h0))
    have hφ0 : extraspecialQuadForm hE (abOf ⟨x, hxQ⟩) = 0 :=
      (h_qform ⟨x, hxQ⟩).mpr (by
        apply Subtype.ext
        simpa using hx2)
    obtain ⟨i, hi⟩ := (hcover _).mp ⟨hφne, hφ0⟩
    exact ⟨i, (hS i x).mpr ⟨hxQ, hi⟩⟩
  have hdisjS : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    obtain ⟨hxiQ, hxiO⟩ := (hS i x).mp hxi
    obtain ⟨hxjQ, hxjO⟩ := (hS j x).mp hxj
    have hφeq : abOf (⟨x, hxiQ⟩ : Q) = abOf (⟨x, hxjQ⟩ : Q) :=
      congrArg abOf (Subtype.ext rfl)
    have : abOf (⟨x, hxiQ⟩ : Q) ∈ O j := by rw [hφeq]; exact hxjO
    exact (Set.disjoint_left.mp (hdisj i j hij) hxiO) this
  have horb : ∀ i, IsConjOrbit (⊤ : Subgroup C) (S i) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · intro k _ x hx
      obtain ⟨hxQ, hxO⟩ := (hS i x).mp hx
      have hconj : conjLinEquiv hQn k (abOf ⟨x, hxQ⟩) ∈ O i := hinv i k _ hxO
      rw [h_conj] at hconj
      refine (hS i (k * x * k⁻¹)).mpr ⟨(conjAut hQn k ⟨x, hxQ⟩).2, ?_⟩
      have he : (⟨k * x * k⁻¹, (conjAut hQn k ⟨x, hxQ⟩).2⟩ : Q) =
          conjAut hQn k ⟨x, hxQ⟩ := Subtype.ext (conjAut_apply hQn k ⟨x, hxQ⟩).symm
      rw [he]
      exact hconj
    · obtain ⟨v, hv⟩ := hne i
      obtain ⟨q, hq⟩ := exists_ofMul_of v
      refine ⟨(q : C), (hS i (q : C)).mpr ⟨q.2, ?_⟩⟩
      rw [show abOf q = v from hq]
      exact hv
    · rintro x hx x' hx'
      obtain ⟨hxQ, hxO⟩ := (hS i x).mp hx
      obtain ⟨hx'Q, hx'O⟩ := (hS i x').mp hx'
      obtain ⟨k, hk⟩ := htrans i (abOf ⟨x, hxQ⟩) hxO (abOf ⟨x', hx'Q⟩) hx'O
      rw [h_conj] at hk
      let a : Q := conjAut hQn k ⟨x, hxQ⟩
      let b : Q := ⟨x', hx'Q⟩
      have hab : abOf a = abOf b := hk
      have hzmem : a * b⁻¹ ∈ Subgroup.center Q := (fib a b).mp hab
      have hca : (a : C) = k * x * k⁻¹ := conjAut_apply hQn k ⟨x, hxQ⟩
      by_cases hzc : a * b⁻¹ = 1
      · refine ⟨k, Subgroup.mem_top _, ?_⟩
        have hab_eq : a = b := (mul_inv_eq_one).mp hzc
        calc k * x * k⁻¹ = (a : C) := hca.symm
          _ = (b : C) := congrArg (fun q : Q => (q : C)) hab_eq
          _ = x' := rfl
      · have haQ : a ∉ Subgroup.center Q := by
          intro ha
          have hbne : abOf b ≠ 0 := ((hcover (abOf b)).mpr ⟨i, hx'O⟩).1
          exact hbne (by rw [← hab]; exact (h_zero a).mpr ha)
        obtain ⟨y, hy⟩ : ∃ y : Q, y * a ≠ a * y := by
          by_contra h
          push Not at h
          exact haQ (Subgroup.mem_center_iff.mpr h)
        have hcomm_ne : ⁅y, a⁆ ≠ 1 :=
          fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
        have hcomm_c : ⁅y, a⁆ ∈ Subgroup.center Q := commutatorElement_mem_center hE y a
        have hcomm_eq : ⁅y, a⁆ = a * b⁻¹ :=
          eq_of_mem_center hE hcomm_c hzmem hcomm_ne hzc
        have hya : y * a * y⁻¹ = (a * b⁻¹) * a := by
          rw [commutatorElement_def] at hcomm_eq
          rw [← hcomm_eq]
          group
        have hzsq : (a * b⁻¹) ^ 2 = 1 := sq_eq_one_of_mem_center hE hzmem
        have hza : (a * b⁻¹) * a = b := by
          have h2 : a * b⁻¹ * b = a := by group
          calc (a * b⁻¹) * a
              = (a * b⁻¹) * (a * b⁻¹ * b) := by rw [h2]
            _ = (a * b⁻¹) * (a * b⁻¹) * b := by group
            _ = (a * b⁻¹) ^ 2 * b := by rw [pow_two]
            _ = 1 * b := by rw [hzsq]
            _ = b := one_mul b
        have hyb : y * a * y⁻¹ = b := hya.trans hza
        have hybC : (y : C) * (a : C) * (y : C)⁻¹ = (b : C) := by
          have := congrArg (fun q : Q => (q : C)) hyb
          simpa using this
        refine ⟨(y : C) * k, Subgroup.mem_top _, ?_⟩
        calc ((y : C) * k) * x * ((y : C) * k)⁻¹
            = (y : C) * (a : C) * (y : C)⁻¹ := by rw [hca]; group
          _ = (b : C) := hybC
          _ = x' := rfl
  refine ⟨S, ⟨hsubS, hcovS, hdisjS, horb⟩, ?_⟩
  intro i
  change Nat.card (Subtype.val '' T i) = 2 * Nat.card ↥(O i)
  rw [Nat.card_image_of_injective (f := Subtype.val) Subtype.val_injective (T i), hcardT i,
    hE.2.2.2, Nat.mul_comm]

end CFSG.EvenSporadicStandard.HNRecog.CSide
