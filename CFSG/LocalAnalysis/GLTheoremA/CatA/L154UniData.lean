module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniAux
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniSig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinMark CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniTw
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniSig
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU mem_heldGU)

open scoped commutatorElement

section Certs


theorem uni_marking_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} (hQ : catalogIs (PSimple p S) l154Uni)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (n d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
      (θ : PSimple p S ≃* StatedProj (StatedSU d (2 ^ n) K)) (A B : GL (Fin d) K) (σ : K ≃+* K)
      (φx ψ : MulAut (StatedProj (StatedSU d (2 ^ n) K))),
      3 ≤ d ∧ 1 ≤ n ∧ (d, 2 ^ n) ≠ (3, 2) ∧ Nat.card K = (2 ^ n) ^ 2 ∧ (∀ x, τ x = x ^ 2 ^ n) ∧
      A ∈ heldGU d K τ hτ ∧
      (∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
        φx (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g') ∧
      (∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = B * glMap σ (g : GL (Fin d) K) * B⁻¹ →
        ψ (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g') ∧
      (∀ g ∈ StatedSU d (2 ^ n) K, B * glMap σ g * B⁻¹ ∈ StatedSU d (2 ^ n) K) ∧
      σ ≠ 1 ∧ (∃ c : K, τ c = c ∧ σ c ≠ c) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S y) ψ := by
  classical
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  have h1 := CFSG.LocalAnalysis.GLTheoremA.MI.marking_transport (indRel p S x) hdiag hF.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h1
  have hlab : HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨a, m, E, hEf, hEfin, ha, hE, hnq, ⟨e⟩⟩ := exists_psu_of_l154Uni hQ
  obtain ⟨τ', hτ'm, hτ'⟩ := exists_frob_equiv hE
  obtain ⟨ψ'⟩ := nonempty_quot_heldSU_equiv_statedProj uniScalar_holds τ' hτ' hτ'm hE ha hnq
  have hcanon : canonLabel lab = ⟨.twA, a - 1, m⟩ :=
    canonLabel_uni_holds τ' hτ' hτ'm hE ha hlab (e.trans ψ'.symm)
  have hfam := famUni_of_canon hcanon
  obtain ⟨d, m0, hd, hm0, hdq, hiff⟩ := famUni_recipe hΛ hfam
  obtain ⟨K, instF, instFin, hK, hs, hna, θ, ⟨hlt, f, hf, u, hu, hord, hindy⟩, φx, hφx, hindx⟩ :=
    (hiff _).1 hraw
  obtain ⟨τ, hτq, hτ⟩ := exists_frob_equiv hK
  have hdq' : (d, 2 ^ m0) ≠ (3, 2) := fun hc => hdq ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  obtain ⟨σ, hfσ⟩ := hf
  obtain ⟨U₀, hU₀, hUconj⟩ := hu
  obtain ⟨A₀, hA₀, hAconj⟩ := hφx
  obtain ⟨U, hU, hUeq⟩ := exists_heldGU_of_GUSet hτq hK hτ U₀ hU₀
  obtain ⟨A, hA, hAeq⟩ := exists_heldGU_of_GUSet hτq hK hτ A₀ hA₀
  have hUconj' : ∀ h h' : ↥(StatedSU d (2 ^ m0) K), (h' : GL (Fin d) K) = U * (h : GL (Fin d) K) * U⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ m0) K) h) = LargeEvenProjMk (StatedSU d (2 ^ m0) K) h' :=
    fun h h' hh' => hUconj h h' (hh'.trans (hUeq _))
  have hAconj' : ∀ h h' : ↥(StatedSU d (2 ^ m0) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φx (LargeEvenProjMk (StatedSU d (2 ^ m0) K) h) = LargeEvenProjMk (StatedSU d (2 ^ m0) K) h' :=
    fun h h' hh' => hAconj h h' (hh'.trans (hAeq _))
  have hσSU : ∀ g ∈ StatedSU d (2 ^ m0) K, glMap σ g ∈ StatedSU d (2 ^ m0) K :=
    fun g hg => glMap_mem_statedSU hτ hτq σ hg
  have hUnorm : ∀ g ∈ StatedSU d (2 ^ m0) K, U⁻¹ * g * U ∈ StatedSU d (2 ^ m0) K := by
    intro g hg
    have := conj_mem_statedSU hτ hτq (inv_mem hU) hg
    simpa using this
  have hBeq : ∀ g : GL (Fin d) K, (U * glMap σ U⁻¹) * glMap σ g * (U * glMap σ U⁻¹)⁻¹ =
      U * glMap σ (U⁻¹ * g * U) * U⁻¹ := by
    intro g
    rw [map_mul, map_mul, map_inv]
    group
  have hBmem : ∀ g ∈ StatedSU d (2 ^ m0) K, (U * glMap σ U⁻¹) * glMap σ g * (U * glMap σ U⁻¹)⁻¹ ∈
      StatedSU d (2 ^ m0) K := by
    intro g hg
    rw [hBeq]
    exact conj_mem_statedSU hτ hτq hU (hσSU _ (hUnorm g hg))
  have hψ : ∀ g g' : ↥(StatedSU d (2 ^ m0) K),
      (g' : GL (Fin d) K) = (U * glMap σ U⁻¹) * glMap σ (g : GL (Fin d) K) * (U * glMap σ U⁻¹)⁻¹ →
      (u * f * u⁻¹) (LargeEvenProjMk (StatedSU d (2 ^ m0) K) g) =
        LargeEvenProjMk (StatedSU d (2 ^ m0) K) g' := by
    intro g g' hg'
    have hg1 : U⁻¹ * (g : GL (Fin d) K) * U ∈ StatedSU d (2 ^ m0) K := hUnorm _ g.2
    have hg2 : glMap σ (U⁻¹ * (g : GL (Fin d) K) * U) ∈ StatedSU d (2 ^ m0) K := hσSU _ hg1
    have h1 : u⁻¹ (LargeEvenProjMk (StatedSU d (2 ^ m0) K) g) =
        LargeEvenProjMk (StatedSU d (2 ^ m0) K) ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩ := by
      have h0 := hUconj' ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩ g (by simp [mul_assoc])
      have h00 : (MulEquiv.symm u) (u (LargeEvenProjMk (StatedSU d (2 ^ m0) K)
          ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩)) =
          LargeEvenProjMk (StatedSU d (2 ^ m0) K) ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩ :=
        MulEquiv.symm_apply_apply u _
      rw [h0] at h00
      exact h00
    have h2 : f (LargeEvenProjMk (StatedSU d (2 ^ m0) K) ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩) =
        LargeEvenProjMk (StatedSU d (2 ^ m0) K) ⟨glMap σ (U⁻¹ * (g : GL (Fin d) K) * U), hg2⟩ :=
      hfσ _ _ (coe_glMap σ _)
    have h3 : u (LargeEvenProjMk (StatedSU d (2 ^ m0) K)
        ⟨glMap σ (U⁻¹ * (g : GL (Fin d) K) * U), hg2⟩) = LargeEvenProjMk (StatedSU d (2 ^ m0) K) g' := by
      refine hUconj' _ g' ?_
      rw [hg', hBeq]
    show u (f (u⁻¹ (LargeEvenProjMk (StatedSU d (2 ^ m0) K) g))) = _
    rw [h1, h2, h3]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    subst hσ1
    have hf1 : f = 1 := MulEquiv.ext (fld_fix_of_one_uni f hfσ)
    rw [hf1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hpowf : f ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one f
  have hgraph : ∀ h h' : ↥(StatedSU d (2 ^ m0) K), (h' : GL (Fin d) K) =
      (1 : GL (Fin d) K) * glMap σ (h : GL (Fin d) K) * (1 : GL (Fin d) K)⁻¹ →
      f (LargeEvenProjMk (StatedSU d (2 ^ m0) K) h) = LargeEvenProjMk (StatedSU d (2 ^ m0) K) h' := by
    intro h h' hh'
    refine hfσ h h' ?_
    show ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ
    rw [hh', one_mul, inv_one, mul_one, coe_glMap]
  have hσp : σ ^ p = 1 :=
    uniSigmaPowOne_holds K m0 d τ hτ hτq hK hd hdq' 1 (one_mem _) σ p hp hp2 f hgraph hpowf
  obtain ⟨c, hc1, hc2⟩ := l154_exists_moved_of_odd τ σ hτ
    (fun c => by rw [hτq, hτq, map_pow]) (hp.odd_of_ne_two hp2) hσp hσ1
  exact ⟨m0, d, K, instF, instFin, τ, hτ, θ, A, U * glMap σ U⁻¹, σ, φx, u * f * u⁻¹, hd, hm0, hdq', hK,
    hτq, hA, hAconj', hψ, hBmem, hσ1, ⟨c, hc1, hc2⟩, hindx, hindy⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X
