module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4EightOuterFix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4EightOuterFixAux
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (listVec)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace F4EightOPrimeAux

section Abstract

theorem mem_of_pow_nine_mem {M : Type*} [Group M] {x : M} (hx : Nat.Coprime 3 (orderOf x))
    {P : Subgroup M} (h : x ^ 9 ∈ P) : x ∈ P := by
  have hx9 : Nat.Coprime 9 (orderOf x) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 hx
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0] at hx
    norm_num at hx
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.1 h1]
    exact one_mem _
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hx9 (by omega)
  have e : x = (x ^ 9) ^ m := by
    rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
  rw [e]
  exact pow_mem h m

theorem mul_pow_mul_inv_pow_mem {M : Type*} [Group M] {P : Subgroup M} {t l : M} (hl : l ∈ P)
    (ht : ∀ k : ℕ, t ^ k * l * (t ^ k)⁻¹ ∈ P) : ∀ k : ℕ, (t * l) ^ k * (t ^ k)⁻¹ ∈ P
  | 0 => by simp
  | k + 1 => by
    have e : (t * l) ^ (k + 1) * (t ^ (k + 1))⁻¹ =
        ((t * l) ^ k * (t ^ k)⁻¹) * (t ^ (k + 1) * l * (t ^ (k + 1))⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem (mul_pow_mul_inv_pow_mem hl ht k) (ht (k + 1))

theorem eq_bot_of_normal_coprime_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (N : Subgroup SL(2, K)) (hN : N.Normal)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  classical
  haveI : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcen : ∀ A : SL(2, K), A ∈ Subgroup.center SL(2, K) → A = 1 := by
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      have h : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
    apply Subtype.ext
    rw [← hrA, hr1]
    simp
  let B₀ : SL(2, K) := ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination -h2⟩
  have hB3 : B₀ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
    rw [pow_succ, pow_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2
  have hB1 : B₀ ≠ 1 := by
    intro h
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [B₀] at this
  set π : SL(2, K) →* PSL(2, K) := QuotientGroup.mk' (Subgroup.center SL(2, K)) with hπ
  have hπ1 : ∀ A, π A = 1 → A = 1 := fun A hA => hcen A ((QuotientGroup.eq_one_iff A).1 hA)
  have hmapN : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  haveI := hmapN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · rw [eq_bot_iff]
    intro A hA
    have hA' : π A ∈ N.map π := Subgroup.mem_map_of_mem π hA
    rw [h, Subgroup.mem_bot] at hA'
    exact Subgroup.mem_bot.2 (hπ1 A hA')
  · exfalso
    have hmem : π B₀ ∈ N.map π := h ▸ Subgroup.mem_top _
    obtain ⟨A, hA, hAB⟩ := Subgroup.mem_map.1 hmem
    have h3 : orderOf (π B₀) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, hB3, map_one]
      · intro h1
        exact hB1 (hπ1 B₀ h1)
    have hdvd : orderOf (π B₀) ∣ orderOf A := by
      rw [← hAB]
      exact orderOf_map_dvd π A
    have hA' : orderOf A ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨A, hA⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    rw [h3] at hdvd
    have h33 := Nat.Coprime.eq_one_of_dvd hcop (hdvd.trans hA')
    norm_num at h33

end Abstract

section Leaf

variable {τ : Tag} {k : Type} [Field k]
  {G : Subgroup (ModGL τ k)} [Finite G] {ω : kˣ}

theorem gLAPPrimeCoreOf_leaf9 (hGC : G ≤ adjointGroup τ k) (hG : ∀ x, dV (τ := τ) ω x ∈ G)
    {kb : List (List ℕ)} (hX9 : ∀ g ∈ G, g ∈ torusGroup τ k → g ^ 9 = 1)
    (hcase : (familyKernel (famV (τ := τ) ω kb) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω kb) = {α, -α} ∧
        (∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 ∨ w = rootReflection α) ∧
        (∀ g ∈ G, g ∈ torusGroup τ k ⊔ rootSpan τ k {α, -α} → g ^ 9 ∈ rootSpan τ k {α, -α}) ∧
        ∀ N : Subgroup G, (∀ n ∈ N, (n : ModGL τ k) ∈ rootSpan τ k {α, -α}) →
          (∀ g : G, (g : ModGL τ k) ∈ rootSpan τ k {α, -α} → ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
          Nat.Coprime 3 (Nat.card N) → N = ⊥) :
    GLAPPrimeCoreOf 3 (famCent hG kb) = ⊥ := by
  set C := famCent hG kb
  set O := GLAPPrimeCoreOf 3 C
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_gLAPPrimeCoreOf' Nat.prime_three C
  have hord : ∀ o ∈ O, Nat.Coprime 3 (orderOf (o : ModGL τ k)) := by
    intro o ho
    have h1 : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    have h2 : orderOf (o : ModGL τ k) = orderOf (⟨o, ho⟩ : O) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rw [h2]
    exact hcop.coprime_dvd_right h1
  have hfac := fun {o : G} (ho : o ∈ O) => familyCentralizer_le_mul τ k (famV (τ := τ) ω kb)
    (mem_familyCentralizer_of_mem_famCent hGC hG (gLAPPrimeCoreOf_le_self' C ho))
  rcases hcase with ⟨hK, hW⟩ | ⟨α, hα, hK, hW, hX4, hX5⟩
  · refine eq_bot_iff.2 fun o ho => ?_
    obtain ⟨w, hw, m, hm, he⟩ := hfac ho
    rw [hW w hw, canonicalRep_one, mul_one] at he
    have hmT : m ∈ torusGroup τ k := by
      have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
      rw [hK] at hm'
      have hbot : rootSpan τ k (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by
        simp [rootSpan]
      rwa [hbot, sup_bot_eq] at hm'
    have h9 : (o : ModGL τ k) ^ 9 = 1 := hX9 _ o.2 (he ▸ hmT)
    have h1 := mem_of_pow_nine_mem (hord o ho) (P := ⊥) (by rw [h9]; exact one_mem _)
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  · set Lα := rootSpan τ k {α, -α}
    have hOL : ∀ o ∈ O, (o : ModGL τ k) ∈ Lα := by
      intro o ho
      obtain ⟨w, hw, m, hm, he⟩ := hfac ho
      have hmM : m ∈ torusGroup τ k ⊔ Lα := by
        have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
        rwa [hK] at hm'
      have hoM : (o : ModGL τ k) ∈ torusGroup τ k ⊔ Lα := by
        rw [he]
        rcases hW w hw with rfl | rfl
        · rwa [canonicalRep_one, mul_one]
        · exact mul_mem hmM (canonicalRep_rootReflection_mem hα)
      exact mem_of_pow_nine_mem (hord o ho) (hX4 _ o.2 hoM)
    have hLC : ∀ g : G, (g : ModGL τ k) ∈ Lα → g ∈ C := by
      intro g hg
      have hgF : (g : ModGL τ k) ∈ familyCentralizer τ k (famV (τ := τ) ω kb) := by
        refine familyGroup_le_familyCentralizer (K := k) _ ?_
        change (g : ModGL τ k) ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb))
        rw [hK]
        exact le_sup_right (a := torusGroup τ k) hg
      refine Subgroup.mem_iInf.2 fun j => Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 := (mem_familyCentralizer.1 hgF).2 j
      apply Subtype.ext
      change (g : ModGL τ k) * dV ω (listVec τ.rank (kb.get j)) =
        dV ω (listVec τ.rank (kb.get j)) * g
      have h2 : dV ω (listVec τ.rank (kb.get j)) * g * (dV ω (listVec τ.rank (kb.get j)))⁻¹ =
        (g : ModGL τ k) := h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    exact hX5 O hOL (fun g hg n hn => gLAPPrimeCoreOf_conj_mem' g (hLC g hg) n hn) hcop

end Leaf

section Port

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]
  {w₀ : WeylGroup τ}

theorem pow_nine_of_mem_twModel8
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {g : ModGL τ L}
    (hg : g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3))
    (hgT : g ∈ torusGroup τ L) : g ^ 9 = 1 := by
  obtain ⟨a, rfl, ha⟩ := (mem_twistedTorus_of_neg htorL hw₀
    (fun c => iterateFrobenius_three_apply c)).1 (mem_twistedTorus.2 ⟨hgT, hg.2⟩)
  have h1 : rootDiagUnit τ (a ^ 9) = rootDiagUnit τ a ^ 9 := map_pow (rootDiagUnitHom τ L) a 9
  have h2 : a ^ 9 = 1 := funext fun i => by simpa using ha i
  rw [← h1, h2, rootDiagUnit_one]

theorem exists_twFrob_rootSL2_8 (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ μ : Lˣ, ∀ A : SL2 L,
      canonicalRep (coxeterSystem τ) L w₀ *
          Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootSL2 τ L α A) *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
      rootSL2 τ L α (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 3) A)) := by
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq (canonicalRep_mem_monomialSubgroup L w₀)
    (mapsRootLines_canonicalRep w₀) hα (hw₀ α)
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.KGD.exists_rootSL2_neg_eq (L := L) hα
  refine ⟨a * s, fun A => ?_⟩
  rw [entrywise_rootSL2_of_field, hs, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]

theorem pow_nine_mem_rootSpan8 (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {g : ModGL τ L}
    (hg : g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3))
    (hgTL : g ∈ torusGroup τ L ⊔ rootSpan τ L {α, -α}) : g ^ 9 ∈ rootSpan τ L {α, -α} := by
  obtain ⟨μ, hμ⟩ := exists_twFrob_rootSL2_8 (L := L) hw₀ hα
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  have hTN : torusGroup τ L ≤ Subgroup.normalizer (rootSpan τ L {α, -α} : Set (ModGL τ L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun β hβ => by
      rcases hβ with rfl | rfl
      · exact hα
      · exact IsRoot.neg hα
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hgTL
  obtain ⟨t, ht, l, hl, rfl⟩ := hgTL
  obtain ⟨b, rfl⟩ := torusGroup_le_range_rootDiagUnitHom ht
  obtain ⟨A, rfl⟩ : l ∈ (rootSL2 τ L α).range := hspan ▸ hl
  have hF : canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 3))
        (rootDiagUnit τ b * rootSL2 τ L α A) * (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
      rootDiagUnit τ b * rootSL2 τ L α A := hg.2
  rw [map_mul] at hF
  have e : canonicalRep (coxeterSystem τ) L w₀ *
      (Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootDiagUnit τ b) *
        Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootSL2 τ L α A)) *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
    (canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootDiagUnit τ b) *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹) *
    (canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 3)) (rootSL2 τ L α A) *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹) := by group
  rw [e, twFrob_rootDiagUnit8 hw₀ b, hμ A] at hF
  set B := conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
    (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 3) A) with hB
  have hb9 : rootDiagUnit τ b ^ 9 ∈ rootSpan τ L {α, -α} := by
    have h1 : rootDiagUnit τ b ^ 9 = rootSL2 τ L α B * (rootSL2 τ L α A)⁻¹ := by
      calc rootDiagUnit τ b ^ 9 = rootDiagUnit τ b ^ 8 *
            (rootDiagUnit τ b * rootSL2 τ L α A) * (rootSL2 τ L α A)⁻¹ := by group
        _ = rootDiagUnit τ b ^ 8 * ((rootDiagUnit τ b)⁻¹ ^ 8 * rootSL2 τ L α B) *
            (rootSL2 τ L α A)⁻¹ := by rw [← hF]
        _ = rootSL2 τ L α B * (rootSL2 τ L α A)⁻¹ := by group
    rw [h1, hspan]
    exact mul_mem ⟨B, rfl⟩ (inv_mem ⟨A, rfl⟩)
  have hlL : rootSL2 τ L α A ∈ rootSpan τ L {α, -α} := by
    rw [hspan]
    exact ⟨A, rfl⟩
  have hc : ∀ k : ℕ, rootDiagUnit τ b ^ k * rootSL2 τ L α A * (rootDiagUnit τ b ^ k)⁻¹ ∈
      rootSpan τ L {α, -α} := fun k =>
    (Subgroup.mem_normalizer_iff.1 (hTN (pow_mem ht k)) _).1 hlL
  have h9 := mul_pow_mul_inv_pow_mem hlL hc 9
  have e2 : (rootDiagUnit τ b * rootSL2 τ L α A) ^ 9 =
      ((rootDiagUnit τ b * rootSL2 τ L α A) ^ 9 * (rootDiagUnit τ b ^ 9)⁻¹) *
        rootDiagUnit τ b ^ 9 := by group
  change (rootDiagUnit τ b * rootSL2 τ L α A) ^ 9 ∈ _
  rw [e2]
  exact mul_mem h9 hb9

theorem eq_bot_of_le_rootSpan8 [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    (hK : Nat.card K = 8) (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (N : Subgroup (twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3)))
    (hNL : ∀ m ∈ N, (m : ModGL τ L) ∈ rootSpan τ L {α, -α})
    (hnorm : ∀ g : twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3),
      (g : ModGL τ L) ∈ rootSpan τ L {α, -α} → ∀ m ∈ N, g * m * g⁻¹ ∈ N)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  classical
  haveI : CharP K 2 := (Algebra.charP_iff K L 2).2 inferInstance
  have hFr : ∀ c : L, iterateFrobenius L 2 3 c = c ^ Nat.card K := fun c => by
    rw [hK, iterateFrobenius_three_apply]
  obtain ⟨P, hP, -⟩ := exists_twisted_rootSL2 (τ := τ) (K := K) hFr hα (hw₀ α)
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  set ψ : SL(2, K) →* ModGL τ L :=
    (rootSL2 τ L α).comp ((conjSL P).comp (Matrix.SpecialLinearGroup.map (algebraMap K L)))
    with hψ
  have hψS : ∀ B : SL(2, K), conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) B) ∈
      (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) :=
    fun B => ⟨_, ⟨B, rfl⟩, rfl⟩
  have hψL : ∀ B, ψ B ∈ rootSpan τ L {α, -α} := fun B => by
    rw [hspan]
    exact ⟨_, rfl⟩
  have hψW : ∀ B, ψ B ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3) :=
    fun B => ⟨rootSpan_le_adjointGroup L {α, -α} (hψL B), (hP _).2 (hψS B)⟩
  have hconjinj : Function.Injective (conjSL P) := by
    intro A B h
    have h' := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h'
  have hmapinj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A B h
    apply Subtype.ext
    ext i j
    have h' : algebraMap K L ((A : Matrix (Fin 2) (Fin 2) K) i j) =
        algebraMap K L ((B : Matrix (Fin 2) (Fin 2) K) i j) :=
      congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L) i j) h
    exact (algebraMap K L).injective h'
  have hψinj : Function.Injective ψ :=
    (rootSL2_injective_of_field α).comp (hconjinj.comp hmapinj)
  have hNψ : ∀ m ∈ N, ∃ B, ψ B = (m : ModGL τ L) := by
    intro m hm
    obtain ⟨A, hA⟩ : (m : ModGL τ L) ∈ (rootSL2 τ L α).range := hspan ▸ hNL m hm
    have hAS := (hP A).1 (by rw [hA]; exact m.2.2)
    obtain ⟨_, ⟨B, rfl⟩, hB⟩ := hAS
    exact ⟨B, by rw [← hA, ← hB]; rfl⟩
  set N₁ : Subgroup SL(2, K) :=
    (N.map (twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3)).subtype).comap
      ψ with hN₁
  have hmemN₁ : ∀ m ∈ N, ∀ B, ψ B = (m : ModGL τ L) → B ∈ N₁ := by
    intro m hm B hB
    rw [hN₁, Subgroup.mem_comap, hB]
    exact Subgroup.mem_map_of_mem _ hm
  have hN₁map : N₁.map ψ =
      N.map (twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3)).subtype := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨B, hB⟩ := hNψ m hm
    exact ⟨B, hmemN₁ m hm B hB, hB⟩
  have hcard : Nat.card N₁ = Nat.card N := by
    rw [← Subgroup.card_map_of_injective hψinj, hN₁map,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hN₁n : N₁.Normal := by
    refine ⟨fun b hb B => ?_⟩
    obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hb)
    rw [hN₁, Subgroup.mem_comap]
    refine Subgroup.mem_map.2 ⟨⟨ψ B, hψW B⟩ * m * ⟨ψ B, hψW B⟩⁻¹, hnorm _ (hψL B) m hm, ?_⟩
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hmb]
    rfl
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hcop₁ : Nat.Coprime 3 (Nat.card N₁) := by rw [hcard]; exact hcop
  have hbot := eq_bot_of_normal_coprime_three h4 N₁ hN₁n hcop₁
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨B, hB⟩ := hNψ m hm
  have hBN : B ∈ N₁ := hmemN₁ m hm B hB
  rw [hbot, Subgroup.mem_bot] at hBN
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hB, hBN, map_one]
  rfl

theorem gLAPPrimeCoreOf_centralizer_dV_eight [IsAlgClosed L] {K : Type} [Field K] [Finite K]
    [Algebra K L] (hK : Nat.card K = 8)
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    [Finite (twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3))]
    {ω : Lˣ} (hω : orderOf ω = 3)
    (hG : ∀ x, dV (τ := τ) ω x ∈
      twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3))
    (hcert : Native.hypOK τ = true) {x : Fin τ.rank → ZMod 3} (hx : x ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer {dG hG x}) = ⊥ := by
  have hGC : twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3) ≤
      adjointGroup τ L := inf_le_left
  have hX9 : ∀ g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 3),
      g ∈ torusGroup τ L → g ^ 9 = 1 := fun g hg hgT =>
    pow_nine_of_mem_twModel8 htorL hw₀ hg hgT
  have hleaf : ∀ (kb : List (List ℕ)), (∀ b ∈ kb, b.length = τ.rank) →
      (∀ b ∈ kb, ∀ x ∈ b, x < 3) →
      Native.famOK (Native.gramL τ) (Native.rootsN τ) (Native.simpleL τ)
        ((Native.simpleL τ).map fun e => Native.formB (Native.gramL τ) e e) kb = true →
      GLAPPrimeCoreOf 3 (famCent hG kb) = ⊥ := by
    intro kb hlen hlt hok
    refine gLAPPrimeCoreOf_leaf9 hGC hG hX9 ?_
    rcases famData_of_famOK hω hlen hlt hok with h | ⟨α, hα, hker, hWs⟩
    · exact Or.inl h
    · exact Or.inr ⟨α, hα, hker, hWs, fun g hg hgTL => pow_nine_mem_rootSpan8 hw₀ hα hg hgTL,
        fun N hNL hnorm hcop => eq_bot_of_le_rootSpan8 hK hw₀ hα N hNL hnorm hcop⟩
  have hstd := famData0_of_famOK0 (τ := τ) hω length_of_mem_stdBasis lt_of_mem_stdBasis
    (famOK_std_of_hypOK hcert)
  exact gLAPPrimeCoreOf_centralizer_dG hω hG
    (fun fl hfl => hleaf _ (length_of_mem_kerBasis hfl) lt_of_mem_kerBasis
      (famOK_of_hypOK hcert hfl))
    (gLAPPrimeCoreOf_leaf9 hGC hG hX9 (Or.inl hstd)) hx

end Port

section Main


theorem oPrimeCoreTrivialAt_eight (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) :
    OPrimeCoreTrivialAt 3 ↥(adjointGroup Tag.F4 K) := by
  classical
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  haveI : CharP K 2 := hchar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.F4 K f4Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 3 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_three_apply]; norm_num
  subst hFr2
  set L := AlgebraicClosure K with hL
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set W := twModel n (iterateFrobenius L 2 3) with hW
  haveI : Finite W := finite_twModelF4 K L hFr hg0C hg0
  let e : adjointGroup Tag.F4 K ≃* W := twModelEquivF4 K L hFr hg0C hg0
  have htorL : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit Tag.F4 a ∈ torusGroup Tag.F4 L :=
    rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := L) (N := 3)
    (by rw [hK]; norm_num)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hG : ∀ x, dV (τ := Tag.F4) ω x ∈ W := dV_mem_twModel8 htorL f4Neg_smul hω3
  have hLang : ∀ a : Fin Tag.F4.rank → Lˣ, (∀ i, a i ^ 3 = 1) → ∀ c ∈ toralCentralizer Tag.F4 L a,
      ∃ z ∈ toralCentralizer Tag.F4 L a, z⁻¹ * frobTwistGL Tag.F4 L 2 3 n z = c :=
    fun a ha3 c hc =>
    toral_centralizer_Lang_F4_three 2 L (by norm_num) a ha3 3 (by norm_num)
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq f4Neg_smul ha3) c hc
  have hfus : ∀ s ∈ W, s ^ 3 = 1 → ∃ u ∈ W, ∃ x : Fin Tag.F4.rank → ZMod 3,
      u * s * u⁻¹ = dV ω x := fun s hs hs3 =>
    exists_conj_dV_twModel8 (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_F4) f4Neg_smul hLang hω hs hs3
  have hcert : Native.hypOK Tag.F4 = true := Certificates.certificate13666.1
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  intro s hs3
  have hs3' : s ^ 3 = 1 := by rw [← hs3]; exact pow_orderOf_eq_one s
  have hes3 : ((e s : W) : ModGL Tag.F4 L) ^ 3 = 1 := by
    have h1 : (e s) ^ 3 = 1 := by rw [← map_pow, hs3', map_one]
    have := congrArg (fun m : W => (m : ModGL Tag.F4 L)) h1
    simpa using this
  obtain ⟨u, huW, x, hux⟩ := hfus _ (e s).2 hes3
  set uW : W := ⟨u, huW⟩ with huW'
  set φ : adjointGroup Tag.F4 K ≃* W := e.trans (MulAut.conj uW) with hφ
  have hφs : φ s = dG hG x := by
    apply Subtype.ext
    change u * (e s : ModGL Tag.F4 L) * u⁻¹ = dV ω x
    exact hux
  have hx : x ≠ 0 := by
    rintro rfl
    have h1 : φ s = 1 := by
      rw [hφs]
      exact Subtype.ext (dV_zero ω)
    have h2 : s = 1 := φ.injective (h1.trans (map_one φ).symm)
    rw [h2, orderOf_one] at hs3
    norm_num at hs3
  rw [gLAPPrimeCoreOf_centralizer_eq_bot_iff φ s, hφs]
  exact gLAPPrimeCoreOf_centralizer_dV_eight hK8 htorL f4Neg_smul hω hG hcert hx

end Main

end F4EightOPrimeAux

section Final


theorem f4EightOPrimeCore_holds : F4LocalOneAux.F4EightOPrimeCore :=
  fun K _ _ hK => F4EightOPrimeAux.oPrimeCoreTrivialAt_eight K hK

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
