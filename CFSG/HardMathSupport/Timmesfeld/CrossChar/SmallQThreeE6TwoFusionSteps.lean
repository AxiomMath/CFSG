module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionTables
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionChecksA
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionChecksB
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionChecksC
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionChecksD
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionChecksE

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot

section Steps

variable {K : Type} [Field K] [CharP K 2]

theorem exists_conj_mem_range_psiHom [Finite K] (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {x : adjointGroup .E6 K} (hx3 : x ^ 3 = 1) :
    ∃ c : adjointGroup .E6 K, c * x * c⁻¹ ∈ (psiHom K h2).range := by
  have := Fact.mk Nat.prime_three
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have hC0 : Nat.card (adjointGroup .E6 K) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (adjointGroup .E6 K)).factorization 3 = 6 := by
    have h6 : 3 ^ 6 ∣ Nat.card (adjointGroup .E6 K) := by
      rw [← card_range_psiHom h2]
      exact Subgroup.card_subgroup_dvd_card _
    have h7 := not_pow_seven_dvd_E6_two hK
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hC0] at h6 h7
    omega
  let P : Sylow 3 (adjointGroup .E6 K) :=
    Sylow.ofCard (psiHom K h2).range (by rw [card_range_psiHom h2, hfac])
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine fun g => ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, ← hk, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup .E6 K) Q P
  refine ⟨c, ?_⟩
  have h1 : (MulAut.conj c) x ∈ ((c • Q : Sylow 3 _) : Subgroup (adjointGroup .E6 K)) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (Q : Subgroup _)
      (hQ (Subgroup.mem_zpowers x))
  rw [hc] at h1
  exact h1

theorem exists_conj_rep_of_table (h2 : (2 : K) = 0) {g : G9}
    {table : List ((Fin 4 → ZMod 3) × (ZMod 3 × ZMod 3) × (Fin 4 → ZMod 3))}
    {reps : List (Fin 4 → ZMod 3)} {v : Fin 4 → ZMod 3}
    (h : ∃ e ∈ table, e.1 = v ∧ e.2.2 + actG (gOf e.2.1.1 e.2.1.2) v - actG g e.2.2 ∈ reps) :
    ∃ c : adjointGroup .E6 K, ∃ r ∈ reps,
      c * (torusE6Two h2 (.ofAdd v) * stHom K g) * c⁻¹ = torusE6Two h2 (.ofAdd r) * stHom K g := by
  obtain ⟨e, -, rfl, hr⟩ := h
  exact ⟨torusE6Two h2 (.ofAdd e.2.2) * stHom K (gOf e.2.1.1 e.2.1.2), _, hr,
    conj_torus_stHom h2 g _ e.1 e.2.2⟩

theorem exists_conj_torus_of_rep (h2 : (2 : K) = 0) {g : G9} {reps : List (Fin 4 → ZMod 3)}
    (hreps : ∀ r ∈ reps, ∃ c : adjointGroup .E6 K, ∃ w,
      c * (torusE6Two h2 (.ofAdd r) * stHom K g) * c⁻¹ = torusE6Two h2 (.ofAdd w))
    {v : Fin 4 → ZMod 3} (h : ∃ c : adjointGroup .E6 K, ∃ r ∈ reps,
      c * (torusE6Two h2 (.ofAdd v) * stHom K g) * c⁻¹ = torusE6Two h2 (.ofAdd r) * stHom K g) :
    ∃ c : adjointGroup .E6 K, ∃ w,
      c * (torusE6Two h2 (.ofAdd v) * stHom K g) * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  obtain ⟨c₁, r, hr, hc₁⟩ := h
  obtain ⟨c₂, w, hc₂⟩ := hreps r hr
  refine ⟨c₂ * c₁, w, ?_⟩
  rw [← hc₂, ← hc₁]
  group

theorem reps_T (h2 : (2 : K) = 0) : ∀ r ∈ repsT, ∃ c : adjointGroup .E6 K, ∃ w,
    c * (torusE6Two h2 (.ofAdd r) * stHom K (gOf 0 1)) * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  intro r hr
  simp only [repsT, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 0 1) fuseT0).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 0 1) fuseT1).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 0 1) fuseT2).elim
      fun c hc => ⟨c, _, hc⟩

theorem reps_S (h2 : (2 : K) = 0) : ∀ r ∈ repsS, ∃ c : adjointGroup .E6 K, ∃ w,
    c * (torusE6Two h2 (.ofAdd r) * stHom K (gOf 1 0)) * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  intro r hr
  simp only [repsS, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 0) fuseS0).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 0) fuseS1).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 0) fuseS2).elim
      fun c hc => ⟨c, _, hc⟩

theorem reps_U (h2 : (2 : K) = 0) : ∀ r ∈ repsU, ∃ c : adjointGroup .E6 K, ∃ w,
    c * (torusE6Two h2 (.ofAdd r) * stHom K (gOf 1 1)) * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  intro r hr
  simp only [repsU, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 1) fuseU0).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 1) fuseU1).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 1) fuseU2).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 1) fuseU3).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 1 1) fuseU4).elim
      fun c hc => ⟨c, _, hc⟩

theorem reps_V (h2 : (2 : K) = 0) : ∀ r ∈ repsV, ∃ c : adjointGroup .E6 K, ∃ w,
    c * (torusE6Two h2 (.ofAdd r) * stHom K (gOf 2 1)) * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  intro r hr
  simp only [repsV, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 2 1) fuseV0).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 2 1) fuseV1).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 2 1) fuseV2).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 2 1) fuseV3).elim
      fun c hc => ⟨c, _, hc⟩
  · exact (conj_eq_of_wordsAgree h2 (coe_torus_mul_stHom_eq_wordElt h2 _ 2 1) fuseV4).elim
      fun c hc => ⟨c, _, hc⟩

theorem exists_conj_torus_of_coset (h2 : (2 : K) = 0) {g : G9}
    (hg : g = gOf 0 1 ∨ g = gOf 1 0 ∨ g = gOf 1 1 ∨ g = gOf 2 1) {v : Fin 4 → ZMod 3}
    (hv : normG g v = 0) :
    ∃ c : adjointGroup .E6 K, ∃ w,
      c * (torusE6Two h2 (.ofAdd v) * stHom K g) * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact exists_conj_torus_of_rep h2 (reps_T h2) (exists_conj_rep_of_table h2 (tableT_ok v hv))
  · exact exists_conj_torus_of_rep h2 (reps_S h2) (exists_conj_rep_of_table h2 (tableS_ok v hv))
  · exact exists_conj_torus_of_rep h2 (reps_U h2) (exists_conj_rep_of_table h2 (tableU_ok v hv))
  · exact exists_conj_torus_of_rep h2 (reps_V h2) (exists_conj_rep_of_table h2 (tableV_ok v hv))

theorem normG_eq_zero_of_pow_three (h2 : (2 : K) = 0) {g : G9} {v : Fin 4 → ZMod 3}
    (h : (torusE6Two h2 (.ofAdd v) * stHom K g) ^ 3 = 1) : normG g v = 0 := by
  rw [cube_torus_stHom] at h
  exact congrArg Multiplicative.toAdd (torusE6Two_injective h2 (h.trans (map_one _).symm))

theorem exists_conj_torus_of_psiHom (h2 : (2 : K) = 0) (y : NG)
    (hy : psiHom K h2 y ^ 3 = 1) :
    ∃ c : adjointGroup .E6 K, ∃ w, c * psiHom K h2 y * c⁻¹ = torusE6Two h2 (.ofAdd w) := by
  rw [psiHom_apply] at hy ⊢
  have hyl : y.left = Multiplicative.ofAdd (Multiplicative.toAdd y.left) := rfl
  rw [hyl] at hy ⊢
  by_cases hg : y.right = 1
  · refine ⟨1, Multiplicative.toAdd y.left, ?_⟩
    rw [hg, map_one]
    group
  rcases g9_cases y.right hg with hR | hR
  · exact exists_conj_torus_of_coset h2 hR (normG_eq_zero_of_pow_three h2 hy)
  · have hinv := inv_torus_stHom (K := K) h2 y.right (Multiplicative.toAdd y.left)
    have hy' : (torusE6Two h2 (.ofAdd (-actG y.right⁻¹ (Multiplicative.toAdd y.left))) *
        stHom K y.right⁻¹) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hy, inv_one]
    obtain ⟨c, w, hc⟩ := exists_conj_torus_of_coset h2 hR (normG_eq_zero_of_pow_three h2 hy')
    refine ⟨c, -w, ?_⟩
    rw [← hinv] at hc
    have hw : (torusE6Two h2 (.ofAdd w))⁻¹ = torusE6Two h2 (.ofAdd (-w)) := by
      rw [← map_inv]
      rfl
    rw [← hw, ← hc]
    group

theorem exists_conj_bReps (h2 : (2 : K) = 0) {v : Fin 4 → ZMod 3} (hv : v ≠ 0) :
    ∃ c : adjointGroup .E6 K, ∃ r ∈ bReps,
      c * torusE6Two h2 (.ofAdd v) * c⁻¹ = torusE6Two h2 (.ofAdd r) := by
  obtain ⟨e, -, rfl, hr⟩ := bTable_ok v hv
  obtain ⟨c, hc⟩ := exists_conj_applyMoves (K := K) h2 e.2 e.1
  exact ⟨c, _, hr, hc⟩

theorem torus_single_one (h2 : (2 : K) = 0) (i : Fin 4) :
    torusE6Two h2 (.ofAdd (Pi.single i 1)) = uE6Two (K := K) i := by
  rw [torusE6Two_single_eq_pow, ZMod.val_one, pow_one]

theorem torus_bRep₀ (h2 : (2 : K) = 0) :
    torusE6Two h2 (.ofAdd ![1, 0, 0, 0]) = uE6Two (K := K) 0 := by
  have e : (![1, 0, 0, 0] : Fin 4 → ZMod 3) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  rw [e, torus_single_one]

theorem torus_bRep₁ (h2 : (2 : K) = 0) :
    torusE6Two h2 (.ofAdd ![1, 0, 0, 1]) = uE6Two (K := K) 0 * uE6Two 3 := by
  have e : (Multiplicative.ofAdd ![1, 0, 0, 1] : Multiplicative (Fin 4 → ZMod 3)) =
      .ofAdd (Pi.single 0 1) * .ofAdd (Pi.single 3 1) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  rw [e, map_mul, torus_single_one, torus_single_one]

theorem torus_bRep₂ (h2 : (2 : K) = 0) :
    torusE6Two h2 (.ofAdd ![1, 0, 1, 1]) = uE6Two (K := K) 0 * uE6Two 2 * uE6Two 3 := by
  have e : (Multiplicative.ofAdd ![1, 0, 1, 1] : Multiplicative (Fin 4 → ZMod 3)) =
      .ofAdd (Pi.single 0 1) * .ofAdd (Pi.single 2 1) * .ofAdd (Pi.single 3 1) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  rw [e, map_mul, map_mul, torus_single_one, torus_single_one, torus_single_one]

end Steps

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
