module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedLinear
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.SectionRank.ClassicalEven (rotMatrix rotGL rotGL_pow_three rotGL_commute mul_scalar_ne)

section Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem statedProj_pair_indep {x y : H} {a b c d : ι} (hab : a ≠ b) (hcd : c ≠ d)
    (hx : ((x : GL ι K) : Matrix ι ι K) *ᵥ Pi.single a 1 = Pi.single b 1)
    (hxc : ∀ m : ℕ, (((x : GL ι K) ^ m : GL ι K) : Matrix ι ι K) *ᵥ Pi.single c 1 =
      Pi.single c 1)
    (hy : ((y : GL ι K) : Matrix ι ι K) *ᵥ Pi.single c 1 = Pi.single d 1) (hx3 : x ^ 3 = 1) :
    (QuotientGroup.mk x : StatedProj H) ≠ 1 ∧
      (QuotientGroup.mk y : StatedProj H) ∉ zpowers (QuotientGroup.mk x : StatedProj H) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact mul_scalar_ne (g := 1) hab (by rw [Units.val_one, one_mulVec]) hx h (one_mul _)
  · have hfin : IsOfFinOrder (QuotientGroup.mk x : StatedProj H) :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, by rw [← QuotientGroup.mk_pow, hx3]; rfl⟩
    obtain ⟨m, hm⟩ := (hfin.mem_powers_iff_mem_zpowers).2 h
    change (QuotientGroup.mk x : StatedProj H) ^ m = QuotientGroup.mk y at hm
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hm
    refine mul_scalar_ne (g := (x : GL ι K) ^ m) hcd (hxc m) hy hm ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, mul_inv_cancel_left]

end Pair

section Sp

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spRot (k : Fin r) : StatedSp r K :=
  ⟨rotGL (Sum.inl k) (Sum.inr k), CFSG.HardMathSupport.Timmesfeld.Tables.Census.rotGL_mem_sp k⟩

theorem spRot_pow_three (k : Fin r) : spRot (K := K) k ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow]; exact rotGL_pow_three _ _)

theorem fieldSp_spRot (σ : K ≃+* K) (k : Fin r) : fieldSp r K σ (spRot k) = spRot k :=
  Subtype.ext (Units.ext (rotMatrix_map_ringHom σ.toRingHom (Sum.inl k) (Sum.inr k)))

theorem exists_E9_fixed_fieldAut_sp [Finite K] (hr : 2 ≤ r) (σ : K ≃+* K) :
    ∃ E : Subgroup (StatedProj (StatedSp r K)), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, fieldAut r K σ e = e := by
  set k0 : Fin r := ⟨0, by omega⟩
  set k1 : Fin r := ⟨1, by omega⟩
  have h01 : k0 ≠ k1 := by simp [k0, k1, Fin.ext_iff]
  have hll : (Sum.inl k0 : Fin r ⊕ Fin r) ≠ Sum.inl k1 := by simpa using h01
  have hrr : (Sum.inr k0 : Fin r ⊕ Fin r) ≠ Sum.inr k1 := by simpa using h01
  have hlr : (Sum.inl k0 : Fin r ⊕ Fin r) ≠ Sum.inr k1 := Sum.inl_ne_inr
  have hrl : (Sum.inr k0 : Fin r ⊕ Fin r) ≠ Sum.inl k1 := Sum.inr_ne_inl
  obtain ⟨h1, hz⟩ := statedProj_pair_indep (x := spRot (K := K) k0) (y := spRot k1)
    (a := Sum.inl k0) (b := Sum.inr k0) (c := Sum.inl k1) (d := Sum.inr k1) Sum.inl_ne_inr
    Sum.inl_ne_inr (CFSG.SectionRank.ClassicalEven.rotMatrix_mulVec_left _ _)
    (fun m => by
      rw [Units.val_pow_eq_pow_val]
      exact rotMatrix_pow_mulVec_single_of_ne hll.symm hrl.symm m)
    (CFSG.SectionRank.ClassicalEven.rotMatrix_mulVec_left _ _) (spRot_pow_three k0)
  have h3 : ∀ k : Fin r, proj r K (spRot k) ^ 3 = 1 := fun k => by
    rw [← map_pow, spRot_pow_three, map_one]
  have hc : proj r K (spRot (K := K) k0) * proj r K (spRot k1) =
      proj r K (spRot k1) * proj r K (spRot k0) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (rotGL_commute hll hlr hrl hrr).eq
  obtain ⟨E, hEH, hE, hE9⟩ :=
    exists_E9_le_of_pair (H := CFSG.RankThree.PartOne.CTP.fixedSubgroup (fieldAut r K σ))
      (u := proj r K (spRot k0)) (v := proj r K (spRot k1))
      (by change fieldAut r K σ (proj r K _) = _; rw [fieldAut_proj, fieldSp_spRot])
      (by change fieldAut r K σ (proj r K _) = _; rw [fieldAut_proj, fieldSp_spRot])
      h1 (h3 k0) (h3 k1) hc hz
  exact ⟨E, hE, hE9, fun e he => hEH he⟩

theorem not_mem_range_conjAut_sp [NeZero r] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (StatedProj (StatedSp r K))} (hα3 : α ^ 3 = 1)
    (hαo : α ∉ (MulAut.conj : StatedProj (StatedSp r K) →* MulAut _).range) :
    α ∉ (conjAut r K).range := by
  intro hD
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K))).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  refine hαo (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.mem_of_pow_eq_one_of_relIndex_dvd_two
    (D := spLinearAutGroup r K) ((relIndex_inner_spLinearAutGroup_dvd hp hf hK).trans
      (Nat.gcd_dvd_left 2 _)) Nat.prime_three (by norm_num) ?_ hα3)
  rw [spLinearAutGroup_eq_range]
  exact hD

theorem outerFixesE9_projSp [Finite K] (hr : 2 ≤ r) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : OuterFixesE9 (StatedProj (StatedSp r K)) := by
  haveI : NeZero r := ⟨by omega⟩
  refine outerFixesE9_of_descent fun α hα3 hαo => ?_
  have hD := not_mem_range_conjAut_sp hp hf hK hα3 hαo
  have hdesc : ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : gsp r K,
      α = conjAut r K H * fieldAut r K σ * (conjAut r K H)⁻¹ := by
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
    · by_cases h2 : ringChar K = 2
      · haveI : CharP K 2 := ringChar.of_eq h2
        exact CFSG.RankThree.PartTwo.KFacts.sp4_even_order_three_field_descent α hα3 hD
      · exact CFSG.RankThree.PartTwo.KFacts.psp4_odd_order_three_field_descent h2 α hα3 hD
    · exact CFSG.RankThree.PartTwo.KFacts.symplectic_order_three_field_descent hr3 α hα3 hD
  obtain ⟨σ, -, H, rfl⟩ := hdesc
  exact ⟨conjAut r K H, fieldAut r K σ, rfl, exists_E9_fixed_fieldAut_sp hr σ⟩

end Sp

theorem outerFixedAt_of_psp {d : ValidLieTypeIndex} {r : ℕ} (hr : 2 ≤ r) (q : PrimePower)
    (h : ∀ (G : Type) [Group G], (G ≃* (CFSGIndex.lie d).Group) →
      StatedClassicalModel G .PSp r q.p q.exponent) : OuterFixedAt d := by
  refine outerFixedAt_of_model fun G _ _ e => ?_
  obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := h G e
  exact ⟨_, _, outerFixesE9_projSp hr q.prime_p q.exponent_pos hF, ⟨f⟩⟩

theorem outerFixedAt_B2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) :
    OuterFixedAt ⟨.B 2 q, hv⟩ :=
  outerFixedAt_of_psp le_rfl q fun _ _ e =>
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e

theorem outerFixedAt_C3 (q : PrimePower) (hv : (LieTypeIndex.C 3 q).Valid) :
    OuterFixedAt ⟨.C 3 q, hv⟩ :=
  outerFixedAt_of_psp (by norm_num) q fun _ _ e =>
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC 3 q hv e

theorem outerFixedAt_B3_even (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid)
    (hp : q.p = 2) : OuterFixedAt ⟨.B 3 q, hv⟩ :=
  outerFixedAt_of_psp (by norm_num) q fun _ _ e =>
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp le_rfl e

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
