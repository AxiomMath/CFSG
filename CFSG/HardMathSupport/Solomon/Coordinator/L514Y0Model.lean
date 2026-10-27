module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514Y0Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.L514Y0K
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KFixIso

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.IVK CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem l514y0_nu_of_models {S Y P : Type*} [Group S] [Group Y] [Group P]
    (hZ : Subgroup.center Y = ⊥) (e : (Y ⧸ Subgroup.center Y) ≃* P)
    (eta : (S ⧸ Subgroup.center S) ≃* P) (α : MulAut Y) (αS : MulAut S) (ψ : MulAut P)
    (hψ : MulAut.congr e (centerDescend Y α) = ψ)
    (hηψ : MulAut.congr eta (centerDescend S αS) = ψ) :
    ∃ ν : S →* Y, Function.Surjective ν ∧ ν.ker = Subgroup.center S ∧
      ∀ s, ν (αS s) = α (ν s) := by
  let eY : Y ≃* P := (barEquivBot hZ).symm.trans e
  have hY : ∀ y, eY (α y) = ψ (eY y) := by
    intro y
    have h1 : (barEquivBot hZ).symm y = (y : Y ⧸ Subgroup.center Y) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    have h2 : (barEquivBot hZ).symm (α y) = (α y : Y ⧸ Subgroup.center Y) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [eY, MulEquiv.trans_apply, h1, h2]
    rw [← hψ]
    simp [MulAut.congr_apply, centerDescend_mk]
  let π : S →* P := (eta : _ →* P).comp (QuotientGroup.mk' (Subgroup.center S))
  refine ⟨eY.symm.toMonoidHom.comp π, ?_, ?_, ?_⟩
  · exact eY.symm.surjective.comp (eta.surjective.comp (QuotientGroup.mk'_surjective _))
  · ext s
    rw [MonoidHom.mem_ker]
    show eY.symm (eta (QuotientGroup.mk' (Subgroup.center S) s)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff s
  · intro s
    show eY.symm (eta (QuotientGroup.mk' (Subgroup.center S) (αS s))) =
      α (eY.symm (eta (QuotientGroup.mk' (Subgroup.center S) s)))
    have h3 : eta (QuotientGroup.mk' (Subgroup.center S) (αS s)) =
        ψ (eta (QuotientGroup.mk' (Subgroup.center S) s)) := by
      rw [← hηψ]
      simp [MulAut.congr_apply, centerDescend_mk]
    rw [h3]
    apply eY.injective
    rw [MulEquiv.apply_symm_apply, hY, MulEquiv.apply_symm_apply]

theorem l514y0_isL3Raw {Y : Type*} [Group Y] {r : ℕ} (h : IsL3Eps r Y) : IsL3Raw r Y := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem l514y0_center_bot {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) {r : ℕ}
    (hr : IsL3Eps r Y) : Subgroup.center Y = ⊥ := by
  rcases l3_std hY (l514y0_isL3Raw hr) with ⟨F, _, _, e, hZ⟩ | ⟨p, f, F, _, hF, hq, e, hZ⟩ <;>
    exact hZ

theorem l514y0_psl {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {r : ℕ}
    (hr : IsL3Eps r Y)
    (hZ : Subgroup.center Y = ⊥) {α : MulAut Y} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hf : IsFieldAutPSL3 α) :
    ∃ y : Y, y ^ 3 = 1 ∧ y ≠ 1 ∧ α y = y ∧ ∃ r0 : ℕ, r = r0 ^ 3 ∧ ∃ L : Subgroup Y,
      (∀ J : Subgroup Y, GLAPComponent 3 (fixedSub α ⊓ Subgroup.centralizer {y}) J ↔ J = L) ∧
        IsTypeL2 r0 (barOf 3 L) := by
  obtain ⟨F, _, _, e, σ, hψ⟩ := l3bf_cases_psl hf
  let eY : Y ≃* projectiveSL 3 F := (barEquivBot hZ).symm.trans e
  have h2 : IsPSLn 3 (Nat.card F) Y :=
    ⟨F, inferInstance, inferInstance, rfl, ⟨eY.trans (psiO F).symm⟩⟩
  have hrL3 := l514y0_isL3Raw hr
  have hrF : r = Nat.card F := (inputL3iso_holds Y r (Nat.card F) hrL3 (Or.inl h2)).1
  have hr3 : r % 3 = 1 := by
    rcases hr with ⟨h3, -⟩ | ⟨-, hpsu⟩
    · exact h3
    · exact absurd ⟨h2, hpsu⟩ (inputL3iso_holds Y (Nat.card F) r (Or.inl h2) (Or.inr hpsu)).2
  have := Finite.of_injective _ (MulEquiv.injective eY)
  obtain ⟨p, f, hK⟩ := exists_piField_true F
  have hpf : p ^ f = r := by
    have := hK.card
    rw [piCard, Bool.cond_true] at this
    rw [hrF, this]
  have hq : ModThree true (p ^ f) := by
    change p ^ f % 3 = 1
    rw [hpf]; exact hr3
  have hψ3 : (fieldAut 3 F σ) ^ 3 = 1 := by
    rw [← hψ, ← map_pow, ← map_pow, hα3, map_one, map_one]
  have hψ1 : fieldAut 3 F σ ≠ 1 := by
    intro h
    apply hα1
    apply eq_one_of_centerDescend_eq_one hY
    apply (MulAut.congr e).injective
    rw [hψ, h, map_one]
  have hσ := kfix_orderOf_eq_three hψ3 hψ1
  obtain ⟨d⟩ := exists_frobData hK hσ
  obtain ⟨ν, hν, hker, hαν⟩ := l514y0_nu_of_models hZ e (etaTrue (p ^ f) F) α (frobSL hK σ)
    (fieldAut 3 F σ) hψ (congr_etaTrue_frob hK σ)
  obtain ⟨y, hy3, hy1, hy, r0, hr0, L, hL, hLt⟩ :=
    l514y0_cover ν hker hq d (fun h => absurd h (by simp)) hν hαν
  exact ⟨y, hy3, hy1, hy, r0, by rw [← hpf]; exact hr0, L, hL, hLt⟩

theorem l514y0_psu {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {r : ℕ}
    (hr : IsL3Eps r Y) (hr8 : r ≠ 8) (hZ : Subgroup.center Y = ⊥) {α : MulAut Y}
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hf : IsFieldAutPSU3 α) :
    ∃ y : Y, y ^ 3 = 1 ∧ y ≠ 1 ∧ α y = y ∧ ∃ r0 : ℕ, r = r0 ^ 3 ∧ ∃ L : Subgroup Y,
      (∀ J : Subgroup Y, GLAPComponent 3 (fixedSub α ⊓ Subgroup.centralizer {y}) J ↔ J = L) ∧
        IsTypeL2 r0 (barOf 3 L) := by
  have hα : orderOf α = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hα3 hα1
  obtain ⟨p, f, f₀, K, _, hK, e, σ, hσ, hff, h₀, hψ⟩ := l3bf_cases_psu hY hα hf
  have := hK.finite
  have hKc : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  let eY : Y ≃* unitaryPSU hK 3 := (barEquivBot hZ).symm.trans e
  have h2 : IsPSUn 3 (p ^ f) Y := ⟨K, inferInstance, inferInstance, hKc, ⟨eY.trans (psuO hK)⟩⟩
  have hrL3 := l514y0_isL3Raw hr
  have hrF : r = p ^ f ∧ ¬ (IsPSLn 3 r Y ∧ IsPSUn 3 (p ^ f) Y) :=
    inputL3iso_holds Y r (p ^ f) hrL3 (Or.inr h2)
  have hr3 : r % 3 = 2 := by
    rcases hr with ⟨-, h⟩ | ⟨h3, -⟩
    · exact absurd ⟨h, h2⟩ hrF.2
    · exact h3
  have hPi : PiField false p f K :=
    ⟨hK.prime, hK.one_le, by rw [piCard, Bool.cond_false]; exact hKc⟩
  have hq : ModThree false (p ^ f) := by
    change p ^ f % 3 = 2
    rw [← hrF.1]; exact hr3
  obtain ⟨d⟩ := exists_frobData hPi hσ
  have hpow : p ^ f = (p ^ d.f₀) ^ 3 := d.pow_eq
  have hq2 : 2 < p ^ f := by
    have h2' : 2 ≤ p ^ d.f₀ := by
      have := Nat.one_lt_pow (Nat.pos_iff_ne_zero.1 d.hP.one_le) d.hP.prime.one_lt
      omega
    rw [hpow]
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ (p ^ d.f₀) ^ 3 := Nat.pow_le_pow_left h2' 3
  obtain ⟨ν, hν, hker, hαν⟩ := l514y0_nu_of_models hZ e (etaFalse hPi hq2) α (frobSL hPi σ)
    (psuField hK σ) hψ (congr_eta_false_frob hPi hq2 σ)
  obtain ⟨y, hy3, hy1, hy, r0, hr0, L, hL, hLt⟩ :=
    l514y0_cover ν hker hq d (fun _ h => hr8 (by rw [hrF.1, hpow, h]; norm_num)) hν hαν
  exact ⟨y, hy3, hy1, hy, r0, by rw [hrF.1]; exact hr0, L, hL, hLt⟩

theorem y0Level_holds : Y0Level := by
  intro Y _ _ hY r hr hr8 α hα3 hα1 hfld
  have hZ := l514y0_center_bot hY hr
  rcases hfld with h1 | hpsl | hpsu
  · exact absurd h1 hα1
  · exact l514y0_psl hY hr hZ hα3 hα1 hpsl
  · exact l514y0_psu hY hr hr8 hZ hα3 hα1 hpsu

theorem inputL3y0_holds : InputL3y0 innAutDerivedVocab := inputL3y0_of_ylevel y0Level_holds

end CFSG.HardMathSupport.Solomon.Coordinator
