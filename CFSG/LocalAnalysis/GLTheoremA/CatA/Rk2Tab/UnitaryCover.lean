module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCoverUni
public import CFSG.RankThree.CentralLift.ClassicalCoverTools
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint


private theorem exceptionalOrders_PSU_eq_one_of_two_le_f {d f : ℕ} (hf : 2 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU d 2 f = (1, 1) := by
  by_cases hd4 : d = 4
  · subst hd4
    have hf1 : f ≠ 1 := by omega
    simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hf1]
  · by_cases hd6 : d = 6
    · subst hd6
      have hf1 : f ≠ 1 := by omega
      simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hf1]
    · simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hd4, hd6]

theorem exists_mulEquiv_quot_of_odd_center {S₀ K : Type} [Group S₀] [Finite S₀] [Group K]
    [Finite K] (hS₀ : Group.IsPerfect S₀) (hK : Group.IsPerfect K) (D : Subgroup S₀)
    [D.Normal] (hD : D ≤ Subgroup.center S₀) (ρ : K →* S₀ ⧸ D)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center K) {k : ℕ}
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (S₀ ⧸ D)) =
      Nat.card D * 2 ^ k)
    (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ (C : Subgroup S₀) (_ : C.Normal), C ≤ D ∧ Nonempty (K ≃* (S₀ ⧸ C)) := by
  classical
  have hcop : Nat.Coprime (Nat.card ρ.ker) (2 ^ k) := by
    rw [hker]
    exact (Odd.coprime_two_right hodd).pow_right k
  have hk₀ : (QuotientGroup.mk' D).ker ≤ Subgroup.center S₀ := by
    rwa [QuotientGroup.ker_mk']
  obtain ⟨α, -, hαc⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ACore.exists_lift_of_coprime_card hS₀ hK
      (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D) hk₀ ρ hρ hker.le hcop
      (by rw [QuotientGroup.ker_mk']; exact hcard)
  obtain ⟨-, hker_le, -, ⟨e, -⟩, -⟩ :=
    CFSG.RankThree.CentralLift.cover_map_of_comp_eq (QuotientGroup.mk'_surjective D)
      hker.le hαc
  refine ⟨α.ker, inferInstance, ?_, ⟨e.symm⟩⟩
  rwa [QuotientGroup.ker_mk'] at hker_le

theorem exists_mulEquiv_statedSU_quot_of_isLabel (hG : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .twA) (hn : 2 ≤ lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (C : Subgroup (StatedSU (lab.rank + 1) (2 ^ lab.n) F)) (_ : C.Normal),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧
      C ≤ Subgroup.center (StatedSU (lab.rank + 1) (2 ^ lab.n) F) ∧
      Nonempty (K ≃* (StatedSU (lab.rank + 1) (2 ^ lab.n) F ⧸ C)) := by
  classical
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag hn
  subst htag
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (ℓ + 1) 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.statedClassicalModel (by decide : StatedLieTag.PSU ∈ classicalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hFcard
  have hperfK : Group.IsPerfect K := Group.isPerfect_def.mpr hQ.1
  have hℓ : 2 ≤ ℓ := hlab.2.1
  have hd3 : 3 ≤ ℓ + 1 := by omega
  have hne : (ℓ + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hperfSU : Group.IsPerfect (StatedSU (ℓ + 1) (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard hd3 hne
  set D : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F) :=
    (StatedScalars (Fin (ℓ + 1)) F).subgroupOf (StatedSU (ℓ + 1) (2 ^ n) F) with hDdef
  have hDcen : D ≤ Subgroup.center (StatedSU (ℓ + 1) (2 ^ n) F) :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  let ρ : K →* StatedProj (StatedSU (ℓ + 1) (2 ^ n) F) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']
  have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 n = (1, 1) :=
    exceptionalOrders_PSU_eq_one_of_two_le_f hn
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    have hdvd : Nat.card (Subgroup.center K) ∣ Nat.gcd (ℓ + 1) (2 ^ n + 1) :=
      rk2_card_center_dvd_twA hK hex
    have hq : Odd (2 ^ n + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ]
      exact ⟨2 ^ k, by ring⟩
    exact Odd.of_dvd_nat hq (hdvd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨k, hMk⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ACore.card_hopfMultiplier_psu_char_two hG
      (l := ℓ) (f := n) (q := 2 ^ n) rfl hFcard hM'.admissible
  obtain ⟨C, hCn, hCD, ⟨e⟩⟩ :=
    exists_mulEquiv_quot_of_odd_center hperfSU hperfK D hDcen ρ hρ hρk hMk hodd
  exact ⟨F, hFld, hFin, inferInstance, C, hCn, hFcard, hCD.trans hDcen, ⟨e⟩⟩

theorem rk2_split_up_twA (hG : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .twA) (hn : 2 ≤ lab.n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ 2 ^ lab.n + 1)
    (hSU : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f d : ℕ),
      Nat.card F = (2 ^ f) ^ 2 → 3 ≤ d → r ∣ 2 ^ f + 1 →
        ∀ (C : Subgroup (StatedSU d (2 ^ f) F)) [C.Normal],
          C ≤ Subgroup.center (StatedSU d (2 ^ f) F) →
            CFSG.Open.twoLocalPrimeRank r (StatedSU d (2 ^ f) F ⧸ C) ≤ d - 2) :
    CFSG.Open.twoLocalPrimeRank r K ≤ lab.rank - 1 := by
  classical
  obtain ⟨-, hlab, -⟩ := rk2_model_of_isLabel hK
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag
  subst htag
  have hℓ : 2 ≤ ℓ := hlab.2.1
  obtain ⟨F, hFld, hFin, hChar, C, hCn, hFcard, hCcen, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSU_quot_of_isLabel hG hK (by rfl) (by simpa using hn)
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : CharP F 2 := hChar
  haveI : C.Normal := hCn
  have hb : CFSG.Open.twoLocalPrimeRank r (StatedSU (ℓ + 1) (2 ^ n) F ⧸ C) ≤ ℓ - 1 := by
    have h := hSU F n (ℓ + 1) hFcard (by omega) (by simpa using hrq) C hCcen
    have hd : (ℓ + 1) - 2 = ℓ - 1 := by omega
    rwa [hd] at h
  have he : CFSG.Open.twoLocalPrimeRank r (StatedSU (ℓ + 1) (2 ^ n) F ⧸ C) =
      CFSG.Open.twoLocalPrimeRank r K :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hr.one_lt e
  rwa [he] at hb

end CFSG.LocalAnalysis.GLTheoremA
