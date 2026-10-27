module

public import CFSG.ClassicalInvolution.Q3.TL4MF165ABal
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF165A

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance.StrongBalance CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped commutatorElement MatrixGroups

theorem pow_three_of_mem_center_sl3 {F : Type} [Field F] {z : SL(3, F)}
    (hz : z ∈ Subgroup.center SL(3, F)) : z ^ 3 = 1 := by
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hzr, ← map_pow, hr, map_one]
  rfl

theorem pow_three_of_mem_center_unitarySU {F : Type} [Field F] [Finite F] {p e : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ e) ^ 2) (hq : p ^ e ≠ 2)
    {z : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p e) 3}
    (hz : z ∈ Subgroup.center (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p e) 3)) :
    z ^ 3 = 1 := by
  set E := Unitary.equivStatedSU (p := p) (f := e) hF 3 with hE
  have hz' : E z ∈ Subgroup.center (StatedSU 3 (p ^ e) F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [(Unitary.isQuasisimple_statedSU_of_card hF le_rfl (by simp [hq])).2] at hz'
  have hsc : ((E z : StatedSU 3 (p ^ e) F) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F :=
    Subgroup.mem_subgroupOf.mp hz'
  have hdet := Unitary.det_eq_one_of_mem_statedSU (E z).2
  have h3 : ((E z : StatedSU 3 (p ^ e) F) : GL (Fin 3) F) ^ 3 = 1 := by
    obtain ⟨u, hu⟩ := hsc
    rw [← hu] at hdet ⊢
    have hu3 : u ^ 3 = 1 := by
      have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).det = (u : F) ^ 3 := by
        simp [Matrix.GeneralLinearGroup.scalar]
      rw [h1] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    rw [← map_pow, hu3, map_one]
  have h4 : E (z ^ 3) = 1 := by
    apply Subtype.ext
    rw [map_pow, SubgroupClass.coe_pow, h3]
    rfl
  exact (map_eq_one_iff E E.injective).mp h4

theorem statedLieAdmissible_three {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : StatedLieAdmissible t 3 p f := by
  have hq2 : p ^ f ≠ 2 := fun h => by
    have := (hp.odd_of_ne_two hp2).pow (n := f)
    rw [h] at this
    exact absurd this (by decide)
  rcases ht with rfl | rfl
  · exact ⟨hp, hf, show 2 ≤ 3 ∧ (3, p ^ f) ≠ (2, 2) ∧ (3, p ^ f) ≠ (2, 3) from
      ⟨by norm_num, by simp, by simp⟩⟩
  · exact ⟨hp, hf, show 3 ≤ 3 ∧ (3, p ^ f) ≠ (3, 2) from ⟨le_rfl, by simp [hq2]⟩⟩

theorem center_pow_three_psl {p e : ℕ} (hp : p.Prime) :
    ∀ z ∈ Subgroup.center (modelUniv .PSL 3 p e hp).K, z ^ 3 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact fun z hz => pow_three_of_mem_center_sl3 (F := GaloisField p e) hz

theorem center_pow_three_psu {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hq : p ^ e ≠ 2) :
    ∀ z ∈ Subgroup.center (modelUniv .PSU 3 p e hp).K, z ^ 3 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e he
  have hU : modelUniv .PSU 3 p e hp =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) 3,
        Unitary.rootDatum hF 3⟩ := by
    simp only [modelUniv, CFSG.LieType.Universal.lieUniversal, he, ↓reduceDIte]
  rw [hU]
  exact fun z hz => pow_three_of_mem_center_unitarySU hF hq hz

theorem center_eq_bot_of_lieModel
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hl : CFSG.Blueprint.LieModel L t 3 p f) : Subgroup.center L = ⊥ := by
  have hFT : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  have hadm := statedLieAdmissible_three ht hp hp2 hf
  obtain ⟨ψ₀, hsurj, -⟩ := Upgrade.lieModelCentralCover t 3 p f hp hp2 hFT hadm L hl
  have hKp : Group.IsPerfect (modelUniv t 3 p f hp).K :=
    ⟨(ModelFacts.modelClauseZero t 3 p f hp hFT hadm).1.1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    have hcomm : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      have ha : a ∈ Subgroup.center L := h ▸ Subgroup.mem_top a
      rw [Subgroup.mem_bot, commutatorElement_def, ← Subgroup.mem_center_iff.mp ha b]
      group
    have hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
      have h1 := congrArg (Subgroup.map ψ₀) hKp.commutator_eq_top
      rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ₀ hsurj]
        at h1
    exact bot_ne_top (hcomm.symm.trans hperf)

theorem alphaOf_eq_bot_of_lieModel
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hl : CFSG.Blueprint.LieModel L t 3 p f) {𝒳 : Subgroup (MulAut L)}
    (hinn : innSubgroup L ≤ 𝒳) {A : Subgroup ↥𝒳}
    (hAinn : ∀ a ∈ A, ((a : ↥𝒳) : MulAut L) ∈ innSubgroup L) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card ↥A = 4) : alphaOf A = ⊥ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h5
    · exact h
  have hq2 : p ^ f ≠ 2 := by omega
  have hFT : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  have hadm := statedLieAdmissible_three ht hp hp2 hf
  obtain ⟨ψ₀, hsurj, hker⟩ := Upgrade.lieModelCentralCover t 3 p f hp hp2 hFT hadm L hl
  have hZ := center_eq_bot_of_lieModel ht hp hp2 hf hl
  have : Finite (MulAut L) := Finite.of_injective (fun β : MulAut L => (β : L → L))
    fun β γ h => MulEquiv.ext (congrFun h)
  rcases ht with rfl | rfl
  · exact alphaOf_eq_bot_of_strongConclusion hZ hsurj hker (center_pow_three_psl hp) hinn
      hAinn hA2 fun ψ hk hn hfa htor =>
        Linear.strongLocalTwoBalanceToralOn_PSL_odd 3 p f hp ⟨1, rfl⟩ hFT hadm hp2 h5 ↥𝒳 ψ
          hk hn A hcard hA2 hfa htor.toralAction
  · exact alphaOf_eq_bot_of_strongConclusion hZ hsurj hker (center_pow_three_psu hp hf hq2) hinn
      hAinn hA2 fun ψ hk hn hfa htor =>
        Unitary.strongLocalTwoBalanceToralPowOn_PSU_two 3 p f hp trivial hFT hadm hp2 h5 ↥𝒳 ψ
          hk hn A hcard hA2 hfa htor

end CFSG.ClassicalInvolution.Q3.TL4.MF165A
