module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcG2F4Dim

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.SignalizerFunctorTheorem.NonLocalExc
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.LieType.Steinberg.Adjoint

theorem repShapeCheck_F4_two : (repsOf .F4).all (repShapeCheck .F4 2) = true := by
  decide +kernel

theorem abs_factor_F4_le_two {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf .F4) :
    ∀ f ∈ r.2.2, 1 ≤ |f.2.2.2| ∧ |f.2.2.2| ≤ 2 := by
  have h := repShapeCheck_F4_two
  rw [List.all_eq_true] at h
  have h' := h r hr
  simp only [repShapeCheck, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Nat.ble_eq] at h'
  obtain ⟨-, hC⟩ := h'
  intro f hf
  obtain ⟨h1, h2⟩ := hC f hf
  rw [Int.abs_eq_natAbs]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩


theorem hasCommFormula_rep_F4_two {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf .F4) :
    (rootOperatorFamily .F4).HasCommFormula 2 ((Tag.rootCertificate .F4).root r.1)
      ((Tag.rootCertificate .F4).root r.2.1) := by
  obtain ⟨-, -, hkeys, -, -⟩ := repShape_spec hr
  have hnd := keys_nodup_of_mem_repsOf hr
  refine ⟨factorConst r.2.2, fun p hp => ?_, commFormula_rep hr⟩
  rw [← hkeys, List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  rw [factorConst_of_mem hnd hf]
  exact abs_factor_F4_le_two hr f hf

theorem hasCommFormula_F4_two {α β : Fin (Tag.rank .F4) → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    (rootOperatorFamily .F4).HasCommFormula 2 α β := by
  obtain ⟨r, hr, w, rfl, rfl⟩ := exists_smul_rep hα hβ hne hne'
  exact (hasCommFormula_rep_F4_two hr).smul w

theorem abs_commConst_F4_le_two {α β : Fin (Tag.rank .F4) → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β) (hp : commPairs .F4 α β = [(1, 1)]) :
    |commConst .F4 α β (1, 1)| ≤ 2 := by
  obtain ⟨C, hC, hF⟩ := hasCommFormula_F4_two hα hβ hne hne'
  have e1 := pinnedX_commFormula_of_commFormula hα hβ hF ℤ 1 1
  have e2 := (commConst_spec hα hβ hne hne').2 ℤ 1 1
  rw [hp] at e1 e2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    one_smul, Int.cast_id] at e1 e2
  have h := pinnedX_injective .F4 ℤ _ (e2.symm.trans e1)
  have hC1 := (hC (1, 1) (by rw [hp]; exact List.mem_singleton_self _)).2
  rw [h]
  simp only [pow_one, abs_mul, abs_pinnedFamilySign, one_mul]
  exact_mod_cast hC1

theorem commConst_F4_cast_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {α β : Fin (Tag.rank .F4) → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β)
    (hne' : α ≠ -β) (hp : commPairs .F4 α β = [(1, 1)]) :
    ((commConst .F4 α β (1, 1) : ℤ) : K) ≠ 0 := by
  have hb := abs_commConst_F4_le_two hα hβ hne hne' hp
  have hl := ((commConst_spec.{0} hα hβ hne hne').1 (1, 1)
    (by rw [hp]; exact List.mem_singleton_self _)).1
  have hcases : commConst .F4 α β (1, 1) = 1 ∨ commConst .F4 α β (1, 1) = -1 ∨
      commConst .F4 α β (1, 1) = 2 ∨ commConst .F4 α β (1, 1) = -2 := by
    rcases abs_cases (commConst .F4 α β (1, 1)) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rcases hcases with h | h | h | h <;> rw [h] <;> simp [h2]

theorem two_pow_le_card_of_adjointF4_odd {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hp2 : p ≠ 2) {L : Subgroup (MulAut W)} (π : ↥L →* AdjointQuotient .F4 K)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * ((Nat.card K - 1) / 2 * Nat.card K ^ 7 / (p - 1))) ≤
      Nat.card W := by
  classical
  have hF := HeisGenFacts.of_codeFacts genCodeFacts_F4
  have h2 : (2 : K) ≠ 0 := by
    have := natCast_ne_zero_of_ne (K := K) (p := p) Nat.prime_two hp2
    simpa using this
  have hC : ∀ β ∈ genS .F4 [34953, 34969, 35481, 35225, 35497, 39321, 39577],
      ((commConst .F4 (decodeVec 44218 - β) β (1, 1) : ℤ) : K) ≠ 0 := fun β hβ =>
    commConst_F4_cast_ne_zero h2 (hF.isRoot_sub β hβ) (hF.isRoot_of_mem β hβ) (hF.sub_ne hβ hβ)
      (ne_neg_of_pos (hF.height_sub_pos hβ) (hF.pos β hβ)) (exists_comm_ss_gen hF hβ)
  have key := two_pow_le_card_of_heisSystem hW hp2 π hπ hker hZ
    (heisSystemGen (K := K) hF hC) (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .F4 K)))
    (by rw [QuotientGroup.ker_mk'])
    (fun c hc => by
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
      have h1 := congrArg (fun x : ↥(adjointGroup .F4 K) => (x : ModGL .F4 K)) hc
      exact pinnedX_injective .F4 K _ (h1.trans (pinnedX_zero .F4 K _).symm))
    ((QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .F4 K))).comp
      (torusA .F4 K (decodeVec 44218)))
    (powMonoidHom 2)
    (fun s c => by
      show QuotientGroup.mk' _ (torusA .F4 K (decodeVec 44218) s) * QuotientGroup.mk' _
        (pinnedA .F4 K (decodeVec 44218) c) *
          (QuotientGroup.mk' _ (torusA .F4 K (decodeVec 44218) s))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg _ (torusA_conj_z_gen hF s c))
    (fun s u => by
      obtain ⟨u', hu'⟩ := torusA_conj_xaProd_gen hF hC s u
      refine ⟨u', ?_⟩
      show QuotientGroup.mk' _ (torusA .F4 K (decodeVec 44218) s) * QuotientGroup.mk' _ _ *
        (QuotientGroup.mk' _ (torusA .F4 K (decodeVec 44218) s))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hu'])
  have hc : (genS .F4 [34953, 34969, 35481, 35225, 35497, 39321, 39577]).card = 7 := by
    decide +kernel
  rwa [card_range_powMonoidHom_two h2, Nat.card_fun, Nat.card_eq_fintype_card
    (α := ↥(genS .F4 [34953, 34969, 35481, 35225, 35497, 39321, 39577])), Fintype.card_coe,
    hc] at key

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
