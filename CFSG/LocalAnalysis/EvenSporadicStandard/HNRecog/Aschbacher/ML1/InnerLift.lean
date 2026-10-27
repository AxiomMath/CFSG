module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.FreeInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LeCommutator

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.HNRecog.ML1 CFSG.RankThree.Literature.FSmith

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem AschbacherHyp.exists_mul_mem_sq_eq [Finite C] (hC : AschbacherHyp C Q)
    (θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
    (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
      (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)))
    (hθk : ∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q)
    (hσθ : ∀ l : ↥(commutator C), σ (θ l) = conjLinEquiv hQn (l : C))
    (hσi : Function.Injective σ)
    (hirr : ∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
      (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ u ∈ U, σ g u ∈ U) →
        U = ⊥ ∨ U = ⊤)
    {z : C} (hzQ : z ∈ Q)
    (hz : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = z)
    (hne : ∀ l : ↥(commutator C), InnerInv (θ l) → l ^ 2 ≠ 1)
    (l : ↥(commutator C)) (hl : InnerInv (θ l)) :
    ∃ q : C, q ∈ Q ∧ ((l : C) * q) ^ 2 = z := by
  classical
  haveI : Finite Q := hC.plus.finite
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q); infer_instance
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  obtain ⟨a, ha1, ha2, hcases⟩ := hl
  have hθlsq : (θ l) ^ 2 = 1 := by
    rcases hcases with h | h
    · rw [h]; ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha2]
    · rw [h]; ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha2]
  have hθl2 : θ (l ^ 2) = 1 := by rw [map_pow, hθlsq]
  have hl2Q : (l : C) ^ 2 ∈ Q := by
    simpa using (hθk (l ^ 2)).1 hθl2
  let l2 : Q := ⟨(l : C) ^ 2, hl2Q⟩
  set w : Additive (Abelianization Q) := Additive.ofMul (Abelianization.of l2) with hw_def
  set u : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q) := σ (θ l) with hu_def
  have hu : u = conjLinEquiv hQn (l : C) := hu_def.trans (hσθ l)
  have huu : u * u = 1 := by
    have h : u ^ 2 = 1 := by rw [hu_def, ← map_pow, hθlsq, map_one]
    simpa [pow_two] using h
  have hconj : conjAut hQn (l : C) l2 = l2 := by
    refine Subtype.ext ?_
    rw [conjAut_apply]
    show (l : C) * ((l : C) ^ 2) * (l : C)⁻¹ = (l : C) ^ 2
    group
  have huw : u w = w := by
    rw [hu, hw_def, conjLinEquiv_apply, hconj]
  have h8 : Module.finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    rw [hC.plus.finrank_quotient]
  have hfix := exists_eq_add_of_fixed_inner σ hσi h8 hirr ha1 ha2
  obtain ⟨w', hw'⟩ : ∃ w' : Additive (Abelianization Q), w = w' + u w' := by
    rcases hcases with h | h
    · obtain ⟨w', hw'⟩ := hfix.1 w (by rw [← h]; exact huw)
      exact ⟨w', by rw [← h, ← hu_def] at hw'; exact hw'⟩
    · obtain ⟨w', hw'⟩ := hfix.2 w (by rw [← h]; exact huw)
      exact ⟨w', by rw [← h, ← hu_def] at hw'; exact hw'⟩
  obtain ⟨q, hq⟩ := exists_ofMul_of w'
  let lq : C := (l : C) * (q : C)
  have hlq_mem : lq ∈ commutator C :=
    (commutator C).mul_mem l.2 (hC.le_commutator q.2)
  let lq' : ↥(commutator C) := ⟨lq, hlq_mem⟩
  have hθlq : θ lq' = θ l := by
    have heq : lq' = l * ⟨(q : C), hC.le_commutator q.2⟩ := Subtype.ext rfl
    rw [heq, map_mul, (hθk ⟨(q : C), hC.le_commutator q.2⟩).2 q.2, mul_one]
  have hlq_inv : InnerInv (θ lq') := by
    rw [hθlq]; exact ⟨a, ha1, ha2, hcases⟩
  have hlq_ne : lq ^ 2 ≠ 1 := by
    intro h
    apply hne lq' hlq_inv
    apply Subtype.ext
    change lq ^ 2 = (1 : C)
    exact h
  have hlq2Q : lq ^ 2 ∈ Q := by
    have h : θ (lq' ^ 2) = 1 := by rw [map_pow, hθlq, hθlsq]
    have hmem := (hθk (lq' ^ 2)).1 h
    change ((l : C) * (q : C)) ^ 2 ∈ Q
    simpa using hmem
  have hcQ : (l : C)⁻¹ * (q : C) * (l : C) ∈ Q := by
    simpa using hQn.conj_mem (q : C) q.2 (l : C)⁻¹
  let c : Q := ⟨(l : C)⁻¹ * (q : C) * (l : C), hcQ⟩
  have hsq : (⟨lq ^ 2, hlq2Q⟩ : Q) = l2 * c * q := by
    refine Subtype.ext ?_
    show lq ^ 2 = (l : C) ^ 2 * ((l : C)⁻¹ * (q : C) * (l : C)) * (q : C)
    dsimp only [lq]
    rw [pow_two]
    group
  have hc_eq : c = conjAut hQn ((l : C)⁻¹) q := by
    refine Subtype.ext ?_
    rw [conjAut_apply]
    show (l : C)⁻¹ * (q : C) * (l : C) = (l : C)⁻¹ * (q : C) * ((l : C)⁻¹)⁻¹
    group
  have hc_class : Additive.ofMul (Abelianization.of c) = conjLinEquiv hQn ((l : C)⁻¹) w' := by
    rw [hc_eq, ← conjLinEquiv_apply hQn ((l : C)⁻¹) q, hq]
  have hc_class' : Additive.ofMul (Abelianization.of c) = u w' := by
    rw [hc_class, map_inv (conjLinEquiv hQn) (l : C),
      show conjLinEquiv hQn (l : C) = u from hu.symm, inv_eq_of_mul_eq_one_right huu]
  have hclass : Additive.ofMul (Abelianization.of (⟨lq ^ 2, hlq2Q⟩ : Q)) =
      w + (u w' + w') := by
    rw [hsq, ofMul_of_mul, ofMul_of_mul, hc_class', hq, ← hw_def, add_assoc]
  have hself : ∀ x : Additive (Abelianization Q), x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from by decide, zero_smul]
  have hzero : Additive.ofMul (Abelianization.of (⟨lq ^ 2, hlq2Q⟩ : Q)) = 0 := by
    rw [hclass, hw']
    calc (w' + u w') + (u w' + w')
        = (w' + w') + (u w' + u w') := by abel
      _ = 0 := by rw [hself w', hself (u w'), zero_add]
  have hcen : (⟨lq ^ 2, hlq2Q⟩ : Q) ∈ Subgroup.center Q :=
    (ofMul_of_eq_zero_iff hE (⟨lq ^ 2, hlq2Q⟩ : Q)).mp hzero
  have hcomm : ∀ y ∈ Q, lq ^ 2 * y = y * lq ^ 2 := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp hcen ⟨y, hy⟩
    exact (congrArg Subtype.val h).symm
  rcases hz (lq ^ 2) hlq2Q hcomm with h1 | hz_eq
  · exact absurd h1 hlq_ne
  · exact ⟨(q : C), q.2, hz_eq⟩

end CFSG.EvenSporadicStandard.HNRecog
