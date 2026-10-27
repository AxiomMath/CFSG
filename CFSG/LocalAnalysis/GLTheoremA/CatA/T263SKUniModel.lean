module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKUniMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDSel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniAux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.GLTheoremA.T263
  CFSG.LocalAnalysis.GLTheoremA.T263.SD CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU mem_heldGU)

open scoped commutatorElement

section Equiv

variable {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

theorem map_statedScalars_eq_normOneScalars (hd : 1 ≤ d) :
    ((StatedScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ n) K)).map
        (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h d)).toMonoidHom =
      normOneScalars h (gramSU h (idGram K d)) d := by
  have hU := unitaryScalars_eq h hd
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ unitaryScalars h d := by
      rw [hU]
      exact hy
    obtain ⟨c, hcN, hcn, hyc⟩ := mem_unitaryScalars.1 hy'
    exact ⟨c, hcN, hcn, hyc⟩
  · rintro ⟨c, hcN, hcn, hz⟩
    refine ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h d)).symm z, ?_, MulEquiv.apply_symm_apply _ _⟩
    have h1 : (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h d)).symm z ∈ unitaryScalars h d :=
      mem_unitaryScalars.2 ⟨c, hcN, hcn, hz⟩
    rw [hU] at h1
    exact h1

@[expose] noncomputable def psuEquivPrimeForm (hd : 1 ≤ d) :
    StatedProj (StatedSU d (2 ^ n) K) ≃* primeFormP h (idGram K d) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h d))
    (map_statedScalars_eq_normOneScalars h hd)

theorem psuEquivPrimeForm_mk (hd : 1 ≤ d) (g : ↥(StatedSU d (2 ^ n) K)) :
    psuEquivPrimeForm h hd (QuotientGroup.mk g) =
      ((⟨(g : GL (Fin d) K), (unitarySU_eq_gramSU h d).le g.2⟩ : ↥(gramSU h (idGram K d))) :
        primeFormP h (idGram K d)) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem psuEquivPrimeForm_symm_mk (hd : 1 ≤ d) (g : ↥(gramSU h (idGram K d))) :
    (psuEquivPrimeForm h hd).symm (g : primeFormP h (idGram K d)) =
      QuotientGroup.mk (⟨(g : GL (Fin d) K), (unitarySU_eq_gramSU h d).ge g.2⟩ : ↥(StatedSU d (2 ^ n) K)) := by
  rw [MulEquiv.symm_apply_eq, psuEquivPrimeForm_mk]

theorem psuEquivPrimeForm_conj (hd : 1 ≤ d) {A : primeFormUnitary h (idGram K d)}
    {φ : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hA : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
      φ (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (x : primeFormP h (idGram K d)) :
    psuEquivPrimeForm h hd (φ ((psuEquivPrimeForm h hd).symm x)) = primeFormConjHom h (idGram K d) A x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [psuEquivPrimeForm_symm_mk, primeFormConjHom_mk]
  have hmem : A * (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ ∈ StatedSU d (2 ^ n) K :=
    (unitarySU_eq_gramSU h d).ge (conj_mem_gramSU h (idGram K d) A.2 g.2)
  have h1 := hA ⟨(g : GL (Fin d) K), (unitarySU_eq_gramSU h d).ge g.2⟩
    ⟨A * (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹, hmem⟩ rfl
  have h2 : φ (QuotientGroup.mk (⟨(g : GL (Fin d) K), (unitarySU_eq_gramSU h d).ge g.2⟩ :
      ↥(StatedSU d (2 ^ n) K))) =
      QuotientGroup.mk (⟨A * (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹, hmem⟩ : ↥(StatedSU d (2 ^ n) K)) := h1
  rw [h2, psuEquivPrimeForm_mk]

theorem psuEquivPrimeForm_apply_conj (hd : 1 ≤ d) {A : primeFormUnitary h (idGram K d)}
    {φ : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hA : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
      φ (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (y : StatedProj (StatedSU d (2 ^ n) K)) :
    psuEquivPrimeForm h hd (φ y) = primeFormConjHom h (idGram K d) A (psuEquivPrimeForm h hd y) :=
  calc psuEquivPrimeForm h hd (φ y)
      = psuEquivPrimeForm h hd (φ ((psuEquivPrimeForm h hd).symm (psuEquivPrimeForm h hd y))) := by
        rw [MulEquiv.symm_apply_apply]
    _ = primeFormConjHom h (idGram K d) A (psuEquivPrimeForm h hd y) := psuEquivPrimeForm_conj h hd hA _

end Equiv

theorem uniRecipe_labN {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) (hfam : FamUni lab) :
    ∃ d : ℕ, 3 ≤ d ∧ 1 ≤ lab.n ∧
      ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔ LargeEvenRecipeUnitary d (2 ^ lab.n) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hT⟩ := hΛ
  dsimp only at hn
  rcases hfam with h | ⟨h, hr⟩
  · subst h
    dsimp only [LargeEvenInLambda2] at hT
    exact ⟨rank + 1, by omega, hn, fun Q => Iff.rfl⟩
  · subst h
    dsimp only at hr
    subst hr
    exact ⟨4, by norm_num, hn, fun Q => by simp [LargeEvenRawDatum]⟩

section Certs


theorem sd_uni_model {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B₀ : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hQ : catalogIs (↥S ⧸ Subgroup.center ↥S) t263GUni)
    (hInn : InnDiagOn p B₀ S) :
    ∃ (m d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 m K)
      (θ : ↥S ⧸ Subgroup.center ↥S ≃* primeFormP h (idGram K d)),
      3 ≤ d ∧ (m = 1 → GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) ∧
      ∀ b ∈ B₀, ∃ A : primeFormUnitary h (idGram K d),
        LargeEvenInduces θ (fun s s' : ↥S => (s' : Ω) = b * s * b⁻¹) (primeFormConjHom h (idGram K d) A) := by
  classical
  obtain ⟨lab, hΛ, hraw⟩ := sd_marking_on_S hSp hInn
  have hlab : HasLabel ↥S (fun l : GLALabel => l = lab) :=
    ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨i, hi, hie⟩ := hQ
  obtain ⟨a, m, E, hEf, hEfin, ha, hE, hnq, ⟨e⟩⟩ :=
    exists_psu_of_l154Uni (T := ↥S ⧸ Subgroup.center ↥S) ⟨i, hi.1, hie⟩
  obtain ⟨τ', hτ'm, hτ'⟩ := exists_frob_equiv hE
  obtain ⟨ψ'⟩ := nonempty_quot_heldSU_equiv_statedProj uniScalar_holds τ' hτ' hτ'm hE ha hnq
  have hcanon : canonLabel lab = ⟨.twA, a - 1, m⟩ :=
    canonLabel_uni_holds τ' hτ' hτ'm hE ha hlab (e.trans ψ'.symm)
  obtain ⟨d, hd, hn1, hiff⟩ := uniRecipe_labN hΛ (famUni_of_canon hcanon)
  obtain ⟨K, instF, instFin, hK, hs, hna, θ, hindb⟩ := (hiff _).1 hraw
  obtain ⟨τ, hτq, hτ⟩ := exists_frob_equiv hK
  let h : UnitaryFieldData 2 lab.n K := UnitaryFieldData.mk Nat.prime_two hn1 (by rw [hK, ← pow_mul, mul_comm])
  have hd1 : 1 ≤ d := by omega
  refine ⟨lab.n, d, K, instF, instFin, h, θ.trans (psuEquivPrimeForm h hd1), hd, fun h1 => ?_,
    fun b hb => ?_⟩
  · exact ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, h1⟩) hraw⟩
  · obtain ⟨φ, ⟨A₀, hA₀, hAconj⟩, hφ⟩ := hindb b hb
    obtain ⟨A, hA, hAeq⟩ := exists_heldGU_of_GUSet hτq hK hτ A₀ hA₀
    have hAU : A ∈ primeFormUnitary h (idGram K d) := by
      rw [mem_primeFormUnitary]
      simp only [idGram, Units.val_one, Matrix.mul_one]
      have hbar : (⇑h.bar : K → K) = ⇑τ := funext fun c => by rw [UnitaryFieldData.bar_apply, hτq]
      rw [hbar]
      exact mem_heldGU.1 hA
    refine ⟨⟨A, hAU⟩, fun l l' hll' => ?_⟩
    have h3 := psuEquivPrimeForm_apply_conj h hd1 (A := ⟨A, hAU⟩) (φ := φ)
      (fun g g' hg' => hAconj g g' (hg'.trans (hAeq _))) (θ (QuotientGroup.mk l))
    exact h3.symm.trans (congrArg (psuEquivPrimeForm h hd1) (hφ l l' hll'))

theorem sdFamModel_uni : SDFamModel t263GUni := by
  intro p hp hp2 Ω _ _ S B B₀ hSn hSq hSp hSc hQ hF2 hBel hB₀B hInn
  obtain ⟨m, d, K, instF, instFin, h, θ, hd, hm1, hind⟩ := sd_uni_model hSp hSq hQ hInn
  have hK : p = 3 → 4 ≤ 2 ^ m := by
    intro h3
    by_contra hlt
    push Not at hlt
    have hm : m = 1 := by
      have h1 := h.one_le
      by_contra hne
      have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hF2 h3 (hm1 hm)
  refine ⟨primeFormP h (idGram K d), inferInstance, inferInstance, θ,
    fun φ => φ ∈ primeFormD h (idGram K d), ?_, famSel_unitary h hd hp hp2 hK⟩
  intro b hb
  obtain ⟨A, hA⟩ := hind (b : Ω) hb
  refine ⟨A, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := sdσ_surjective θ x
  rw [sd_rho_apply (sd_hBN hSn B) θ b s]
  exact hA s (CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) b s) (sd_conj_coe (sd_hBN hSn B) b s)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
