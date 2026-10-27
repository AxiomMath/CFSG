module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict
public import CFSG.RankThree.PartOne.KFR4.Row4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDSel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Orth

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.SD CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
open scoped commutatorElement

@[expose] def FamSelOrth : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate →
      (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
      (p = 3 → 4 ≤ Nat.card K) →
      FamSel p ↥(orthDerived Q)
        (fun φ => φ ∈ Set.range (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)))

theorem sdo_stated_plus {T : Type} [Group T] (h : catalogIs T t263GOrth) :
    ∃ (r f : ℕ), 4 ≤ r ∧ StatedClassicalModel T .POmegaPlus r 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [t263GOrth, onLie] at hi
  | alternating n hn => simp [t263GOrth, onLie] at hi
  | sporadic s => simp [t263GOrth, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | D r q =>
      have hq : q.p = 2 := by simpa [t263GOrth, onLie] using hi
      have hLM := CFSG.Models.lieModel_D r q hv e
      have hr : 4 ≤ r := hLM.1.2.2
      rcases hLM.2 with hSC | ⟨h0, -⟩
      · exact ⟨r, q.exponent, hr, by rw [hq] at hSC; exact hSC⟩
      · omega
    | _ => simp [t263GOrth, onLie] at hi

theorem sdo_stated_minus {T : Type} [Group T] (h : catalogIs T t263GTwOrth) :
    ∃ (r f : ℕ), 4 ≤ r ∧ StatedClassicalModel T .POmegaMinus r 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [t263GTwOrth, onLie] at hi
  | alternating n hn => simp [t263GTwOrth, onLie] at hi
  | sporadic s => simp [t263GTwOrth, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedD r q =>
      have hq : q.p = 2 := by simpa [t263GTwOrth, onLie] using hi
      have hLM := CFSG.Models.lieModel_twistedD r q hv e
      have hr : 4 ≤ r := hLM.1.2.2
      rcases hLM.2 with hSC | ⟨h0, -⟩
      · exact ⟨r, q.exponent, hr, by rw [hq] at hSC; exact hSC⟩
      · omega
    | _ => simp [t263GTwOrth, onLie] at hi

theorem sdo_recipe_plus {lab : LargeEvenLabel} {r f : ℕ} (hr : 4 ≤ r)
    (hc : canonLabel lab = ⟨.D, r, f⟩) :
    lab.n = f ∧ ∀ Q : LargeEvenRawCont,
      LargeEvenRawDatum lab Q ↔ LargeEvenRecipeOmegaPlus r (2 ^ f) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case D =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · simp [canonLabel, h3] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨rfl, fun Q => by simp [LargeEvenRawDatum, h3]⟩
  case twD =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · by_cases h2 : rank = 2
      · simp [canonLabel, h2] at hc
      · simp [canonLabel, h3, h2] at hc
  all_goals simp [canonLabel] at hc

theorem sdo_recipe_minus {lab : LargeEvenLabel} {r f : ℕ} (hr : 4 ≤ r)
    (hc : canonLabel lab = ⟨.twD, r, f⟩) :
    lab.n = f ∧ ∀ Q : LargeEvenRawCont,
      LargeEvenRawDatum lab Q ↔ LargeEvenRecipeOmegaMinus (r - 1) (2 ^ f) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case D =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · simp [canonLabel, h3] at hc
  case twD =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · by_cases h2 : rank = 2
      · simp [canonLabel, h2] at hc
      · simp [canonLabel, h3, h2] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨rfl, fun Q => by simp [LargeEvenRawDatum, h3, h2]⟩
  all_goals simp [canonLabel] at hc

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem sdo_kd264Rho_congr {S B : Subgroup Ω} (hBN : B ≤ Subgroup.normalizer (S : Set Ω)) {P : Type} [Group P]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) (b : ↥B) :
    kd264Rho hBN θ b = MulAut.congr θ (kd264Rho hBN (MulEquiv.refl _) b) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨s, rfl⟩ := sdσ_surjective θ y
  have h1 := sd_rho_apply hBN θ b s
  have h2 := sd_rho_apply hBN (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)) b s
  rw [h1, MulAut.congr_apply]
  have h3 : (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)).symm.trans θ = θ := rfl
  show _ = θ ((kd264Rho hBN (MulEquiv.refl _) b) (θ.symm (θ (QuotientGroup.mk s))))
  rw [MulEquiv.symm_apply_apply]
  have h4 : (kd264Rho hBN (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)) b) (QuotientGroup.mk s) =
      QuotientGroup.mk (CFSG.normalizerConjAutOfMem S B hBN b s) := h2
  rw [h4]
  rfl

theorem sdo_congr_conj {P P' : Type} [Group P] [Group P'] (e : P ≃* P') (g : P) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  apply MulEquiv.ext
  intro y
  rw [MulAut.congr_apply]
  simp [MulAut.conj_apply]

theorem sdo_rho_inner {S B : Subgroup Ω} (hBN : B ≤ Subgroup.normalizer (S : Set Ω)) {R : Type} [Group R]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) (b : ↥B) (r : R)
    (hφ : LargeEvenInduces θ (fun s s' : ↥S => (s' : Ω) = (b : Ω) * s * (b : Ω)⁻¹) (MulAut.conj r)) :
    kd264Rho hBN (MulEquiv.refl _) b = MulAut.conj (θ.symm r) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 := sd_rho_apply hBN (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)) b s
  have h2 := hφ s (CFSG.normalizerConjAutOfMem S B hBN b s) (sd_conj_coe hBN b s)
  rw [MulAut.conj_apply] at h2
  have h3 : (kd264Rho hBN (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)) b) (QuotientGroup.mk s) =
      QuotientGroup.mk (CFSG.normalizerConjAutOfMem S B hBN b s) := h1
  rw [h3, MulAut.conj_apply]
  apply θ.injective
  rw [← h2, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]

theorem sdFamModel_orth (hOLD : Y10GFldOrth.OrthLabelDict) (hF : FamSelOrth) :
    SDFamModel t263GOrth := by
  intro p hp hp2 Ω _ _ S B B₀ hSn hSq hSp hSc hQ hF2 hBel hB₀B hInn
  obtain ⟨lab, hΛ, hraw⟩ := sd_marking_on_S hSp hInn
  have hlab : HasLabel ↥S (fun l : GLALabel => l = lab) :=
    ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨r, f, hr, hM⟩ := sdo_stated_plus hQ
  have hc := (hOLD ↥S lab r f hlab).1 hM
  obtain ⟨hnf, hiff⟩ := sdo_recipe_plus hr hc
  obtain ⟨Km, instF, instFin, hKm, hs, hna, θm, hindb⟩ := (hiff _).1 hraw
  obtain ⟨hadm, K, instK, instKfin, hcard, ⟨e⟩⟩ := hM
  haveI : CharP K 2 := Y10GField.charP_two_of_card_pow hcard
  haveI : NeZero r := ⟨by omega⟩
  have hQnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
  have hdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [two_mul]
  have hT := exists_threeSingular_of_dim (CFSG.LieType.Universal.Spin.quadPlus r K) hQnd (m := r) hr hdim
  have hK3 : p = 3 → 4 ≤ Nat.card K := by
    intro h3
    by_contra hlt
    push Not at hlt
    rw [hcard] at hlt
    have hf1 : 1 ≤ f := hadm.2.1
    have hf : f = 1 := by
      by_contra hne
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hF2 h3 ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, by show lab.n = 1; rw [hnf, hf]⟩) hraw⟩
  have hFam := hF p hp hp2 K (Fin r ⊕ Fin r → K) (CFSG.LieType.Universal.Spin.quadPlus r K) hQnd hT hK3
  let θ : ↥S ⧸ Subgroup.center ↥S ≃* ↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus r K)) :=
    (e.trans (statedProjOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadPlus (n := r) (K := K)))).trans
      (KFR4.orthDerivedEquivProj hQnd).symm
  refine ⟨↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus r K)), inferInstance, inferInstance, θ,
    fun φ => φ ∈ Set.range (MulAut.conj : ↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus r K)) →*
      MulAut ↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus r K))), ?_, hFam⟩
  intro b hb
  obtain ⟨φ, ⟨rm, hrm⟩, hφ⟩ := hindb (b : Ω) hb
  subst hrm
  rw [sdo_kd264Rho_congr (sd_hBN hSn B) θ b, sdo_rho_inner (sd_hBN hSn B) θm b rm hφ, sdo_congr_conj]
  exact ⟨_, rfl⟩

theorem sdFamModel_twOrth (hOLD : Y10GFldOrth.OrthLabelDict) (hF : FamSelOrth) :
    SDFamModel t263GTwOrth := by
  intro p hp hp2 Ω _ _ S B B₀ hSn hSq hSp hSc hQ hF2 hBel hB₀B hInn
  obtain ⟨lab, hΛ, hraw⟩ := sd_marking_on_S hSp hInn
  have hlab : HasLabel ↥S (fun l : GLALabel => l = lab) :=
    ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨r, f, hr, hM⟩ := sdo_stated_minus hQ
  have hc := (hOLD ↥S lab r f hlab).2 hM
  obtain ⟨hnf, hiff⟩ := sdo_recipe_minus hr hc
  obtain ⟨Km, instF, instFin, hKm, bm, cm, hirrm, hs, hna, θm, hindb⟩ := (hiff _).1 hraw
  obtain ⟨hadm, K, instK, instKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hM
  haveI : CharP K 2 := Y10GField.charP_two_of_card_pow hcard
  have hQnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite r K hirr
  have hdim : Module.finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  have hT := exists_threeSingular_of_dim (CFSG.LieType.Universal.Spin.quadMinus r K b c) hQnd (m := r) hr hdim
  have hK3 : p = 3 → 4 ≤ Nat.card K := by
    intro h3
    by_contra hlt
    push Not at hlt
    rw [hcard] at hlt
    have hf1 : 1 ≤ f := hadm.2.1
    have hf : f = 1 := by
      by_contra hne
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hF2 h3 ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, by show lab.n = 1; rw [hnf, hf]⟩) hraw⟩
  have hFam := hF p hp hp2 K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K)
    (CFSG.LieType.Universal.Spin.quadMinus r K b c) hQnd hT hK3
  haveI : Nontrivial (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := inferInstance
  let θ : ↥S ⧸ Subgroup.center ↥S ≃* ↥(orthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c)) :=
    (e.trans (statedProjOrthEquiv (CFSG.LieType.Universal.Spin.coe_quadMinus r K b c))).trans
      (KFR4.orthDerivedEquivProj hQnd).symm
  refine ⟨↥(orthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c)), inferInstance, inferInstance, θ,
    fun φ => φ ∈ Set.range (MulAut.conj : ↥(orthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c)) →*
      MulAut ↥(orthDerived (CFSG.LieType.Universal.Spin.quadMinus r K b c))), ?_, hFam⟩
  intro b' hb'
  obtain ⟨φ, ⟨rm, hrm⟩, hφ⟩ := hindb (b' : Ω) hb'
  subst hrm
  rw [sdo_kd264Rho_congr (sd_hBN hSn B) θ b', sdo_rho_inner (sd_hBN hSn B) θm b' rm hφ, sdo_congr_conj]
  exact ⟨_, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Orth

end
