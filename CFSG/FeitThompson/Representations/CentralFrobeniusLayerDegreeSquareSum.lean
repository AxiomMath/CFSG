module

public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import CFSG.FeitThompson.Representations.FreeCentralSectionTISylowRestriction
public import CFSG.FeitThompson.Representations.KernelLayerDegreeSum
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction Pointwise Subgroup

section Finsets

variable {K : Type*} [Group K] [Finite K]

theorem finite_irrDetect (H : Subgroup K) : (irrDetect ℂ H).Finite := by
  rw [← irrKer_bot]
  exact finite_irrKer H ⊥

theorem coe_irrKerFinset_bot (H : Subgroup K) :
    (irrKerFinset H ⊥ : Set (K → ℂ)) = irrDetect ℂ H := by
  rw [← irrKer_bot]
  ext χ
  simp

theorem sum_sq_degree_irrKerFinset_bot (H : Subgroup K) [H.Normal] :
    ∑ χ ∈ irrKerFinset H ⊥, χ 1 ^ 2 = (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
  rw [sum_sq_degree_irrKer bot_le, Subgroup.relIndex_bot_left]

end Finsets

section Fam

variable {L : Type*} [Group L] [Fintype L]

theorem finite_indFamDetect (K : Subgroup L) (H : Subgroup K) : (indFamDetect K H).Finite := by
  rw [indFamDetect_eq_indFam]
  exact indFam_finite K (finite_irrDetect H)

noncomputable def indFamDetectFinset (K : Subgroup L) (H : Subgroup K) : Finset (L → ℂ) :=
  (finite_indFamDetect K H).toFinset

@[simp] theorem mem_indFamDetectFinset {K : Subgroup L} {H : Subgroup K} {f : L → ℂ} :
    f ∈ indFamDetectFinset K H ↔ f ∈ indFamDetect K H := Set.Finite.mem_toFinset _

@[simp] theorem coe_indFamDetectFinset (K : Subgroup L) (H : Subgroup K) :
    (indFamDetectFinset K H : Set (L → ℂ)) = indFamDetect K H := Set.Finite.coe_toFinset _

theorem indFamDetectFinset_eq_empty_iff {K : Subgroup L} {H : Subgroup K} :
    indFamDetectFinset K H = ∅ ↔ indFamDetect K H = ∅ := by
  rw [← Finset.coe_injective.eq_iff, coe_indFamDetectFinset, Finset.coe_empty]

end Fam

section Free

theorem natCard_orbit_eq_natCard_of_stabilizer_eq_bot {D : Type*} [Group D] {X : Type*}
    [MulAction D X] (hst : ∀ x : X, MulAction.stabilizer D x = ⊥) (x : X) :
    Nat.card (MulAction.orbit D x) = Nat.card D := by
  rw [natCard_orbit_eq_index_stabilizer, hst, Subgroup.index_bot]

variable {L : Type*} [Group L] [Finite L] {P E Z : Subgroup L}

theorem natCard_dvd_sub_one_of_free [Z.Normal]
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) :
    Nat.card E ∣ Nat.card Z - 1 := by
  have hE : E ≤ normalizer (Z : Set L) := by rw [Subgroup.normalizer_eq_top]; exact le_top
  let φ : E →* MulAut Z := (Z.normalizerMonoidHom).comp (Subgroup.inclusion hE)
  have hφ : ∀ u : E, u ≠ 1 → ∀ z : Z, φ u z = z → z = 1 := by
    intro u hu z hz
    have hc : (u : L) * (z : L) * (u : L)⁻¹ = (z : L) := by
      have := congrArg Subtype.val hz
      simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    refine Subtype.ext ?_
    have hz1 : (z : L) = 1 :=
      hfree (u : L) u.2 (by simpa using hu) (z : L) z.2 (mul_inv_eq_iff_eq_mul.1 hc)
    simpa using hz1
  let _ : MulDistribMulAction E Z := MulDistribMulAction.compHom (↥Z) φ
  let S : SubMulAction E Z :=
    { carrier := {1}ᶜ
      smul_mem' := fun u _ hx hx1 => hx (smul_left_cancel u (by rw [hx1, smul_one])) }
  have hst : ∀ x : S, stabilizer E x = ⊥ := by
    intro x
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    by_contra hu1
    exact x.2 (hφ u hu1 x.1 (congrArg Subtype.val (mem_stabilizer_iff.1 hu)))
  have h1 : Nat.card S = Nat.card (Quotient (orbitRel E S)) * Nat.card E := by
    rw [Nat.card_congr (selfEquivOrbitsQuotientProd hst), Nat.card_prod]
  have h2 : Nat.card S = Nat.card Z - 1 := by
    classical
    have : Fintype Z := Fintype.ofFinite _
    have h3 : Nat.card S = Nat.card {x : Z // ¬ x = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    rw [h3, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun x : Z => x = 1)]
    simp
  exact ⟨_, by rw [← h2, h1, Nat.mul_comm]⟩

theorem index_eq_natCard_of_sup_eq_top [P.Normal] (hPE : P ⊔ E = ⊤) (hinf : P ⊓ E = ⊥) :
    P.index = Nat.card E := by
  have hprod : Nat.card ((P : Set L) * (E : Set L)) * Nat.card (P ⊓ E : Subgroup L)
      = Nat.card P * Nat.card E := natCard_mul_mul_natCard_inf P E
  rw [hinf, ← Subgroup.normal_mul P E, hPE] at hprod
  simp only [Subgroup.card_bot, mul_one, Subgroup.coe_top] at hprod
  rw [Nat.card_coe_set_eq, Set.ncard_univ] at hprod
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P)) ?_
  rw [Subgroup.card_mul_index P, ← hprod]

end Free

section Main

variable {L : Type*} [Group L] [Fintype L] {P E Z : Subgroup L} [P.Normal] [Z.Normal]
  (hZP : Z ≤ P) (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
  (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1)

include hZP hZc hPE hfree

theorem indFamDetectFinset_eq_irrKerFinset_bot :
    indFamDetectFinset P (Z.subgroupOf P) = irrKerFinset Z ⊥ := by
  apply Finset.coe_injective
  rw [coe_indFamDetectFinset, coe_irrKerFinset_bot,
    indFamDetect_eq_irrDetect (E := E) hZP hZc hPE hfree]

theorem sum_sq_degree_indFamDetect :
    ∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), χ 1 ^ 2
      = (P.index : ℂ) * (Z.relIndex P : ℂ) * ((Nat.card Z : ℂ) - 1) := by
  rw [indFamDetectFinset_eq_irrKerFinset_bot (E := E) hZP hZc hPE hfree,
    sum_sq_degree_irrKerFinset_bot, ← Subgroup.relIndex_mul_index hZP]
  push_cast
  ring

theorem sum_sq_degree_indFamDetect_ne_zero (hZ : Z ≠ ⊥) :
    ∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), χ 1 ^ 2 ≠ 0 := by
  rw [sum_sq_degree_indFamDetect (E := E) hZP hZc hPE hfree]
  have hP : (P.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hr : (Z.relIndex P : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 ?_
    have : Finite (↥P ⧸ Z.subgroupOf P) := Quotient.finite _
    exact Subgroup.index_ne_zero_of_finite
  have hZ1 : (1 : ℕ) < Nat.card Z := (Z.one_lt_card_iff_ne_bot).2 hZ
  have hZne : ((Nat.card Z : ℂ) - 1) ≠ 0 := by
    have : ((Nat.card Z : ℕ) : ℂ) ≠ 1 := by simpa using (by omega : Nat.card Z ≠ 1)
    simpa [sub_eq_zero] using this
  exact mul_ne_zero (mul_ne_zero hP hr) hZne

theorem indFamDetect_nonempty (hZ : Z ≠ ⊥) : (indFamDetect P (Z.subgroupOf P)).Nonempty := by
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  refine sum_sq_degree_indFamDetect_ne_zero (E := E) hZP hZc hPE hfree hZ ?_
  rw [indFamDetectFinset_eq_empty_iff.2 hc, Finset.sum_empty]

theorem exists_sum_sq_degree_indFamDetect (hinf : P ⊓ E = ⊥) (hZ : Z ≠ ⊥) :
    ∃ t : ℕ, 0 < t ∧ ∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), χ 1 ^ 2
      = (t : ℂ) * ((P.index : ℂ) ^ 2 * (Z.relIndex P : ℂ)) := by
  obtain ⟨t, ht⟩ := natCard_dvd_sub_one_of_free (E := E) hfree
  have hZ1 : 1 < Nat.card Z := (Z.one_lt_card_iff_ne_bot).2 hZ
  have hidx : P.index = Nat.card E := index_eq_natCard_of_sup_eq_top hPE hinf
  refine ⟨t, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at ht; omega
    · exact h0
  · rw [sum_sq_degree_indFamDetect (E := E) hZP hZc hPE hfree]
    have key : ((Nat.card Z : ℂ) - 1) = (P.index : ℂ) * (t : ℂ) := by
      have h2 : ((Nat.card Z - 1 : ℕ) : ℂ) = ((Nat.card E : ℂ) * (t : ℂ)) := by
        rw [ht]; push_cast; ring
      rw [Nat.cast_sub hZ1.le, Nat.cast_one] at h2
      rw [h2, hidx]
    rw [key]
    ring

end Main

namespace IsFreeCentralSection

variable {G : Type*} [Group G] [Finite G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z)

include h

omit [Finite G] in
theorem Z_subgroupOf_le_P_subgroupOf : Z.subgroupOf L ≤ P.subgroupOf L :=
  Subgroup.subgroupOf_mono _ h.Z_le_P

omit [Finite G] in
theorem natCard_Z_subgroupOf : Nat.card (Z.subgroupOf L) = Nat.card Z :=
  Nat.card_congr (subgroupOfEquivOfLe h.Z_le).toEquiv

theorem Z_subgroupOf_ne_bot : Z.subgroupOf L ≠ ⊥ := by
  refine (Subgroup.one_lt_card_iff_ne_bot _).1 ?_
  rw [h.natCard_Z_subgroupOf]
  exact (Subgroup.one_lt_card_iff_ne_bot Z).2 h.Z_ne_bot

omit [Finite G] in
theorem inf_subgroupOf_eq_bot : P.subgroupOf L ⊓ E.subgroupOf L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h1 : ((x : ↥L) : G) ∈ P ⊓ E := ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
  rw [h.inf_eq_bot] at h1
  exact Subtype.ext (Subgroup.mem_bot.1 h1)

section Conclusions

variable [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal] [Fintype ↥L]

theorem sum_sq_degree_indFamDetect_subgroupOf :
    ∑ χ ∈ indFamDetectFinset (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), χ 1 ^ 2
      = (Nat.card E : ℂ) * (Z.relIndex P : ℂ) * ((Nat.card Z : ℂ) - 1) := by
  rw [CFSG.FeitThompson.sum_sq_degree_indFamDetect (E := E.subgroupOf L)
      h.Z_subgroupOf_le_P_subgroupOf h.Z_subgroupOf_le_centralizer h.sup_subgroupOf
      h.free_subgroupOf,
    h.index_subgroupOf_eq, Subgroup.relIndex_subgroupOf h.P_le, h.natCard_Z_subgroupOf]

theorem exists_sum_sq_degree_indFamDetect_subgroupOf :
    ∃ t : ℕ, 0 < t ∧ ∑ χ ∈ indFamDetectFinset (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), χ 1 ^ 2
      = (t : ℂ) * ((Nat.card E : ℂ) ^ 2 * (Z.relIndex P : ℂ)) := by
  obtain ⟨t, ht, hsum⟩ :=
    CFSG.FeitThompson.exists_sum_sq_degree_indFamDetect (E := E.subgroupOf L)
      h.Z_subgroupOf_le_P_subgroupOf h.Z_subgroupOf_le_centralizer h.sup_subgroupOf
      h.free_subgroupOf h.inf_subgroupOf_eq_bot h.Z_subgroupOf_ne_bot
  refine ⟨t, ht, ?_⟩
  rwa [h.index_subgroupOf_eq, Subgroup.relIndex_subgroupOf h.P_le] at hsum

theorem indFamDetect_nonempty_subgroupOf :
    (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))).Nonempty :=
  CFSG.FeitThompson.indFamDetect_nonempty (E := E.subgroupOf L)
    h.Z_subgroupOf_le_P_subgroupOf h.Z_subgroupOf_le_centralizer h.sup_subgroupOf
    h.free_subgroupOf h.Z_subgroupOf_ne_bot

end Conclusions

end IsFreeCentralSection

end CFSG.FeitThompson
