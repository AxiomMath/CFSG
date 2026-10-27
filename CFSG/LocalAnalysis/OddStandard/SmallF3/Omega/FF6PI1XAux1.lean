module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ffOutFF6PI1X_hat (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) : Equiv.Perm (Fin 5) →* ↥(omegaProj hQ) :=
  MonoidHom.mk' (fun σ => omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩)
    (fun σ τ => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, coe_omegaToProj]
      rw [← map_mul, ffHat_mul])

theorem ffOutFF6PI1X_hat_apply (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5)) :
    ffOutFF6PI1X_hat hQ fr σ =
      omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ := rfl

theorem ffOutFF6PI1X_hat_mem_fix (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) :
    ffOutFF6PI1X_hat hQ fr σ ∈ ffFix hQ h2 (ffTs fr) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  rw [ffFix, mem_fixSub_iff, ffOutFF6PI1X_hat_apply]
  apply ffOmegaToSim_injective hQ
  rw [ff_omegaToSim_act]
  have hcomm := ffTs_comm_normalizer hQ h2 hπ fr
    (ff6p_mem_normalizer_of_N0 hQ hπ fr (g := ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩)
      (ffHat_mem_ffN0p hQ fr σ))
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def ffOutFF6PI1X_sp (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J : Finset (Fin 5)) (hJ : Even J.card) :
    ↥(omegaProj hQ) :=
  omegaToProj hQ ⟨fr.signChange (ffOpt J),
    ffB0p_le_omega hQ fr ((mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJ, rfl⟩)⟩

theorem ffOutFF6PI1X_sp_mem_B1p (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J : Finset (Fin 5)) (hJ : Even J.card) :
    ffOutFF6PI1X_sp hQ fr J hJ ∈ ffB1p hQ fr := by
  refine (mem_ffB1p_iff hQ fr).mpr ⟨J, hJ, ?_⟩
  exact coe_omegaToProj hQ _

theorem ffOutFF6PI1X_sp_proof_irrel (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J : Finset (Fin 5)) (h h' : Even J.card) :
    ffOutFF6PI1X_sp hQ fr J h = ffOutFF6PI1X_sp hQ fr J h' := by
  apply Subtype.ext
  simp only [ffOutFF6PI1X_sp, coe_omegaToProj]

theorem ffOutFF6PI1X_sp_congr (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {J K : Finset (Fin 5)} (h : J = K)
    (hJ : Even J.card) (hK : Even K.card) :
    ffOutFF6PI1X_sp hQ fr J hJ = ffOutFF6PI1X_sp hQ fr K hK := by
  subst h
  exact ffOutFF6PI1X_sp_proof_irrel hQ fr J hJ hK

theorem ffOutFF6PI1X_sp_empty (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (hJ : Even (∅ : Finset (Fin 5)).card) :
    ffOutFF6PI1X_sp hQ fr ∅ hJ = 1 := by
  apply Subtype.ext
  simp only [ffOutFF6PI1X_sp, coe_omegaToProj, ffOpt, Finset.map_empty, fr.signChange_empty,
    map_one, Subgroup.coe_one]

theorem ffOutFF6PI1X_sp_mul (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J K : Finset (Fin 5))
    (hJ : Even J.card) (hK : Even K.card) (hJK : Even (symmDiff J K).card) :
    ffOutFF6PI1X_sp hQ fr J hJ * ffOutFF6PI1X_sp hQ fr K hK =
      ffOutFF6PI1X_sp hQ fr (symmDiff J K) hJK := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ffOutFF6PI1X_sp, coe_omegaToProj, ← map_mul,
    fr.signChange_mul, ffOpt_symmDiff]

theorem ffOutFF6PI1X_sp_mul_self (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J : Finset (Fin 5)) (hJ : Even J.card) :
    ffOutFF6PI1X_sp hQ fr J hJ * ffOutFF6PI1X_sp hQ fr J hJ = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_one, ffOutFF6PI1X_sp, coe_omegaToProj,
    ← map_mul, fr.signChange_mul_self, map_one]

theorem ffOutFF6PI1X_sp_inv (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J : Finset (Fin 5)) (hJ : Even J.card) :
    (ffOutFF6PI1X_sp hQ fr J hJ)⁻¹ = ffOutFF6PI1X_sp hQ fr J hJ :=
  inv_eq_of_mul_eq_one_right (ffOutFF6PI1X_sp_mul_self hQ fr J hJ)

theorem ffOutFF6PI1X_hat_conj_sp (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (J : Finset (Fin 5)) (hJ : Even J.card) (hJ' : Even (ffAct σ J).card) :
    ffOutFF6PI1X_hat hQ fr σ * ffOutFF6PI1X_sp hQ fr J hJ *
      (ffOutFF6PI1X_hat hQ fr σ)⁻¹ =
    ffOutFF6PI1X_sp hQ fr (ffAct σ J) hJ' := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ffOutFF6PI1X_hat_apply, ffOutFF6PI1X_sp,
    coe_omegaToProj, ← map_inv, ← map_mul, ffHat_conj_signChange_ffOpt]

theorem ffOutFF6PI1X_sp_mem_fix (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    (J : Finset (Fin 5)) (hJ : Even J.card) :
    ffOutFF6PI1X_sp hQ fr J hJ ∈ ffFix hQ h2 (ffTs fr) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  rw [ffFix, mem_fixSub_iff]
  apply ffOmegaToSim_injective hQ
  rw [ff_omegaToSim_act]
  have hcomm := ffTs_comm_normalizer hQ h2 hπ fr
    (Subgroup.le_normalizer (ffOutFF6PI1X_sp_mem_B1p hQ fr J hJ))
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem ffOutFF6PI1X_exists_pair :
    ∀ a b : Fin 5, a ≠ b →
      ∃ c d : Fin 5, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  decide

theorem ffOutFF6PI1X_three_cycle_pow :
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      (Equiv.swap a c * Equiv.swap a b) ^ 3 = 1 := by
  decide +kernel

theorem ffOutFF6PI1X_three_cycle_act :
    ∀ a b c d : Fin 5, a ≠ b → a ≠ c → b ≠ c → d ≠ a → d ≠ b → d ≠ c →
      ffAct (Equiv.swap a c * Equiv.swap a b) ({a, d} : Finset (Fin 5)) = {b, d} := by
  decide +kernel

theorem ffOutFF6PI1X_symmDiff_pairs :
    ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
      symmDiff ({a, d} : Finset (Fin 5)) {b, d} = {a, b} := by
  decide +kernel

theorem ffOutFF6PI1X_symmDiff_sdiff (J : Finset (Fin 5)) {a b : Fin 5}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) :
    symmDiff ({a, b} : Finset (Fin 5)) (J \ {a, b}) = J := by
  have hsub : ({a, b} : Finset (Fin 5)) ⊆ J := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  ext x
  rw [Finset.mem_symmDiff, Finset.mem_sdiff]
  constructor
  · rintro (⟨hxA, -⟩ | ⟨⟨hxJ, -⟩, -⟩)
    · exact hsub hxA
    · exact hxJ
  · intro hxJ
    by_cases hxA : x ∈ ({a, b} : Finset (Fin 5))
    · exact Or.inl ⟨hxA, fun h => h.2 hxA⟩
    · exact Or.inr ⟨⟨hxJ, hxA⟩, hxA⟩

theorem ffOutFF6PI1X_weight_two_mem_twoRes (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    {a b : Fin 5} (hab : a ≠ b) (hPair : Even ({a, b} : Finset (Fin 5)).card) :
    ffOutFF6PI1X_sp hQ fr ({a, b} : Finset (Fin 5)) hPair ∈
      twoRes (ffFix hQ h2 (ffTs fr)) := by
  classical
  obtain ⟨c, d, hca, hcb, hda, hdb, hdc⟩ := ffOutFF6PI1X_exists_pair a b hab
  have hac : a ≠ c := fun h => hca h.symm
  have hbc : b ≠ c := fun h => hcb h.symm
  set σ : Equiv.Perm (Fin 5) := Equiv.swap a c * Equiv.swap a b with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ]
    exact ffOutFF6PI1X_three_cycle_pow a b c hab hac hbc
  have hact : ffAct σ ({a, d} : Finset (Fin 5)) = {b, d} := by
    rw [hσ]
    exact ffOutFF6PI1X_three_cycle_act a b c d hab hac hbc hda hdb hdc
  set C : Subgroup ↥(omegaProj hQ) := ffFix hQ h2 (ffTs fr) with hC
  have hgC : ffOutFF6PI1X_hat hQ fr σ ∈ C := ffOutFF6PI1X_hat_mem_fix hQ hdim hsgn h2 fr σ
  have hodd : Odd (orderOf (ffOutFF6PI1X_hat hQ fr σ)) := by
    apply Odd.of_dvd_nat (n := 3) (by norm_num)
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hσ3, map_one])
  have hgS : ffOutFF6PI1X_hat hQ fr σ ∈ twoRes C := Subgroup.subset_closure ⟨hgC, hodd⟩
  have hA : Even ({a, d} : Finset (Fin 5)).card := by
    rw [Finset.card_insert_of_notMem (by simpa using hda.symm), Finset.card_singleton]
    norm_num
  have hB : Even ({b, d} : Finset (Fin 5)).card := by
    rw [Finset.card_insert_of_notMem (by simpa using hdb.symm), Finset.card_singleton]
    norm_num
  have hAct : Even (ffAct σ ({a, d} : Finset (Fin 5))).card := by
    rw [ffAct_card]; exact hA
  have htC : ffOutFF6PI1X_sp hQ fr ({a, d}) hA ∈ C :=
    ffOutFF6PI1X_sp_mem_fix hQ hdim hsgn h2 fr ({a, d}) hA
  have hconjC : ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_hat hQ fr σ *
      (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹ ∈ C :=
    C.mul_mem (C.mul_mem htC hgC) (C.inv_mem htC)
  have hconjOdd : Odd (orderOf (ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_hat hQ fr σ *
      (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹)) := by
    change Odd (orderOf ((MulAut.conj (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)).toMonoidHom
      (ffOutFF6PI1X_hat hQ fr σ)))
    rw [orderOf_injective _ (MulAut.conj _).injective]
    exact hodd
  have hconjS : ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_hat hQ fr σ *
      (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹ ∈ twoRes C :=
    Subgroup.subset_closure ⟨hconjC, hconjOdd⟩
  have hprod : (ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_hat hQ fr σ *
      (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹) * (ffOutFF6PI1X_hat hQ fr σ)⁻¹ ∈ twoRes C :=
    (twoRes C).mul_mem hconjS (Subgroup.inv_mem _ hgS)
  have h1 : ffOutFF6PI1X_hat hQ fr σ * ffOutFF6PI1X_sp hQ fr ({a, d}) hA *
      (ffOutFF6PI1X_hat hQ fr σ)⁻¹ = ffOutFF6PI1X_sp hQ fr ({b, d}) hB :=
    (ffOutFF6PI1X_hat_conj_sp hQ fr σ ({a, d}) hA hAct).trans
      (ffOutFF6PI1X_sp_congr hQ fr hact hAct hB)
  have h2' : ffOutFF6PI1X_hat hQ fr σ * (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹ *
      (ffOutFF6PI1X_hat hQ fr σ)⁻¹ = ffOutFF6PI1X_sp hQ fr ({b, d}) hB := by
    rw [ffOutFF6PI1X_sp_inv hQ fr ({a, d}) hA]
    exact h1
  have hSymm : Even (symmDiff ({a, d} : Finset (Fin 5)) {b, d}).card := by
    rw [ffOutFF6PI1X_symmDiff_pairs a b d hab hda.symm hdb.symm]
    exact hPair
  have hAB : symmDiff ({a, d} : Finset (Fin 5)) {b, d} = {a, b} :=
    ffOutFF6PI1X_symmDiff_pairs a b d hab hda.symm hdb.symm
  have heq : (ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_hat hQ fr σ *
      (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹) * (ffOutFF6PI1X_hat hQ fr σ)⁻¹ =
      ffOutFF6PI1X_sp hQ fr ({a, b}) hPair := by
    calc (ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_hat hQ fr σ *
        (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹) * (ffOutFF6PI1X_hat hQ fr σ)⁻¹
        = ffOutFF6PI1X_sp hQ fr ({a, d}) hA *
          (ffOutFF6PI1X_hat hQ fr σ * (ffOutFF6PI1X_sp hQ fr ({a, d}) hA)⁻¹ *
            (ffOutFF6PI1X_hat hQ fr σ)⁻¹) := by group
      _ = ffOutFF6PI1X_sp hQ fr ({a, d}) hA * ffOutFF6PI1X_sp hQ fr ({b, d}) hB := by
            rw [h2']
      _ = ffOutFF6PI1X_sp hQ fr (symmDiff ({a, d}) {b, d}) hSymm :=
            ffOutFF6PI1X_sp_mul hQ fr ({a, d}) {b, d} hA hB hSymm
      _ = ffOutFF6PI1X_sp hQ fr ({a, b}) hPair :=
            ffOutFF6PI1X_sp_congr hQ fr hAB hSymm hPair
  rwa [heq] at hprod

theorem ffOutFF6PI1X_even_sp_mem (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    (J : Finset (Fin 5)) (hJ : Even J.card) :
    ffOutFF6PI1X_sp hQ fr J hJ ∈ twoRes (ffFix hQ h2 (ffTs fr)) := by
  classical
  have main : ∀ n, ∀ (J : Finset (Fin 5)), J.card = n → ∀ hJ : Even J.card,
      ffOutFF6PI1X_sp hQ fr J hJ ∈ twoRes (ffFix hQ h2 (ffTs fr)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro J hJn hJ
      by_cases h0 : J.card = 0
      · have hJ0 : J = ∅ := Finset.card_eq_zero.mp h0
        subst hJ0
        rw [ffOutFF6PI1X_sp_empty]
        exact (twoRes _).one_mem
      · have hge2 : 2 ≤ J.card := by
          rcases hJ with ⟨k, hk⟩
          omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        have hpos_erase : 0 < (J.erase a).card := by
          rw [Finset.card_erase_of_mem ha]; omega
        obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos_erase
        have hbJ : b ∈ J := Finset.mem_of_mem_erase hb
        have hba : b ≠ a := Finset.ne_of_mem_erase hb
        have hab : a ≠ b := hba.symm
        set K : Finset (Fin 5) := J \ ({a, b} : Finset (Fin 5)) with hK
        have hKcard : K.card = J.card - 2 := by
          have hsub : ({a, b} : Finset (Fin 5)) ⊆ J := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact ha
            · exact hbJ
          rw [hK, Finset.card_sdiff_of_subset hsub,
            Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
        have hKeven : Even K.card := by
          rcases hJ with ⟨k, hk⟩
          refine ⟨k - 1, ?_⟩
          rw [hKcard]; omega
        have hKlt : K.card < J.card := by rw [hKcard]; omega
        have ihK : ffOutFF6PI1X_sp hQ fr K hKeven ∈ twoRes (ffFix hQ h2 (ffTs fr)) :=
          ih K.card (by omega) K rfl hKeven
        have hpair : Even ({a, b} : Finset (Fin 5)).card := by
          rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
          norm_num
        have hw2 := ffOutFF6PI1X_weight_two_mem_twoRes hQ hdim hsgn h2 fr hab hpair
        have hJeq : symmDiff ({a, b} : Finset (Fin 5)) K = J := by
          rw [hK]
          exact ffOutFF6PI1X_symmDiff_sdiff J ha hbJ hab
        have hSymm : Even (symmDiff ({a, b} : Finset (Fin 5)) K).card := by
          rw [hJeq]; exact hJ
        have hsplit : ffOutFF6PI1X_sp hQ fr J hJ =
            ffOutFF6PI1X_sp hQ fr ({a, b}) hpair * ffOutFF6PI1X_sp hQ fr K hKeven := by
          rw [ffOutFF6PI1X_sp_congr hQ fr hJeq.symm hJ hSymm,
            ← ffOutFF6PI1X_sp_mul hQ fr ({a, b}) K hpair hKeven hSymm]
        rw [hsplit]
        exact (twoRes _).mul_mem hw2 ihK
  exact main J.card J rfl hJ

end CFSG.OddStandard.SmallF3.Omega
