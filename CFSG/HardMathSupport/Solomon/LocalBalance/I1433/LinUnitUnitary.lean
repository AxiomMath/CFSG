module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinearAut
import CFSG.RankThree.PartOne.KC.UnitaryRigidityBlock
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
import CFSG.RankThree.PartOne.KC.UnitaryGoodSetting

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open Polynomial Matrix CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.LinearCore
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks

namespace UnitaryCore

variable {n : ℕ} {k : Type} [Field k] [Finite k]

theorem eq_X_sub_C_of_acts_as_scalar {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {b : k[X]}
    (hb : b ∈ primaryFactors (glA A : Module.End k (Fin n → k))) {μ : k}
    (hμ : ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) b,
      (glA A : Module.End k (Fin n → k)) v = μ • v) : b = X - C μ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hb)
  have heig : Module.End.HasEigenvector (glA A : Module.End k (Fin n → k)) μ v :=
    Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hμ v hv), hv0⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := b) heig
  rw [mem_primaryComponent.mp hv] at h1
  have h2 : b.eval μ = 0 := by
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact h
    · exact absurd h hv0
  have h3 : X - C μ ∣ b := dvd_iff_isRoot.2 h2
  have hirr := irreducible_of_mem_primaryFactors hb
  have hass : Associated (X - C μ) b :=
    (irreducible_X_sub_C μ).associated_of_dvd hirr h3
  exact (eq_of_monic_of_associated (monic_X_sub_C μ) (monic_of_mem_primaryFactors hb) hass).symm


theorem commute_of_eq_mul_scalar {n : ℕ} {K : Type} [Field K] [Finite K] {A B : GL (Fin n) K}
    {g : LinearMap.GeneralLinearGroup K (Fin n → K)} {c' : Kˣ}
    (hAeq : glA A = g * glA (Matrix.GeneralLinearGroup.scalar (Fin n) c'))
    (hg : glA B * g = g * glA B) : B * A = A * B := by
  apply Matrix.GeneralLinearGroup.toLin.injective
  have hS : glA (Matrix.GeneralLinearGroup.scalar (Fin n) c') * glA B =
      glA B * glA (Matrix.GeneralLinearGroup.scalar (Fin n) c') := by
    rw [← glA_mul, ← glA_mul, Matrix.GeneralLinearGroup.scalar_commute]
  show glA (B * A) = glA (A * B)
  rw [glA_mul, glA_mul, hAeq, ← mul_assoc, hg, mul_assoc, mul_assoc, hS]


section Unitary

variable {n : ℕ} {K : Type} [Field K] {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) [Finite K]

theorem unitaryCentralizer_glA {A B : GL (Fin n) K} (hAU : A ∈ primeFormUnitary h (idGram K n))
    (hBU : B ∈ primeFormUnitary h (idGram K n)) (hBA : B * A = A * B) :
    glA B ∈ unitaryCentralizer (idForm h n) (glA A) := by
  refine mem_unitaryCentralizer.mpr ⟨?_, ?_⟩
  · exact (toLin_mem_sesqUnitaryGroup_iff B).mpr hBU
  · exact (mem_gl_centralizer.mp (mem_gl_centralizer_glA hBA))

theorem commutator_acts_trivially_good {A Ba Bb : GL (Fin n) K}
    (hAU : A ∈ primeFormUnitary h (idGram K n))
    (hBaU : Ba ∈ primeFormUnitary h (idGram K n)) (hBbU : Bb ∈ primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA A))
    (hcomm : A = Ba * Bb * Ba⁻¹ * Bb⁻¹) (hBa : Ba * A = A * Ba) (hBb : Bb * A = A * Bb)
    {j : K[X]} (hj : j ∈ primaryFactors (glA A : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (glA A) ⟨j, hj⟩)
    (hFa : ∀ g ∈ specialBlock (idForm h n) (glA A) j, glA Ba * g = g * glA Ba)
    (hFb : ∀ g ∈ specialBlock (idForm h n) (glA A) j, glA Bb * g = g * glA Bb) :
    ∀ v ∈ primaryComponent (glA A : Module.End K (Fin n → K)) j,
      (glA A : Module.End K (Fin n → K)) v = v := by
  have hq2 := two_le_pow_of h
  have hfac := specialBlockFacts_of_good H hq2 ⟨j, hj⟩ hgood
  obtain ⟨ca, hca⟩ := hfac.scalar (glA Ba) (unitaryCentralizer_glA h hAU hBaU hBa)
    (fun _ g hg => (commute_iff_eq _ _).2 (hFa g hg))
  obtain ⟨cb, hcb⟩ := hfac.scalar (glA Bb) (unitaryCentralizer_glA h hAU hBbU hBb)
    (fun _ g hg => (commute_iff_eq _ _).2 (hFb g hg))
  exact commutator_acts_trivially_of_scalars hcomm hBa hBb ca cb hca hcb

theorem acts_as_scalar_of_mem_X_sub_C {A : GL (Fin n) K} {μ : K} {v : Fin n → K}
    (hv : v ∈ primaryComponent (glA A : Module.End K (Fin n → K)) (X - C μ)) :
    (glA A : Module.End K (Fin n → K)) v = μ • v := by
  rw [mem_primaryComponent] at hv
  simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv
  exact sub_eq_zero.1 hv

theorem unitary_matrix_core (hℓ3 : ℓ ≠ 3) {A Ba Bb : GL (Fin n) K}
    (hAU : A ∈ primeFormUnitary h (idGram K n))
    (hBaU : Ba ∈ primeFormUnitary h (idGram K n)) (hBbU : Bb ∈ primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA A))
    (hdetA : (A : Matrix (Fin n) (Fin n) K).det = 1)
    (hcomm : A = Ba * Bb * Ba⁻¹ * Bb⁻¹)
    (hA1 : ∀ c' : Kˣ, A ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c')
    {a : K[X]} (ha : a ∈ primaryFactors (glA A : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (glA A) ⟨a, ha⟩)
    (hFa : ∀ g ∈ specialBlock (idForm h n) (glA A) a, glA Ba * g = g * glA Ba)
    (hFb : ∀ g ∈ specialBlock (idForm h n) (glA A) a, glA Bb * g = g * glA Bb)
    (hA : ∃ g ∈ specialBlock (idForm h n) (glA A) a, ∃ c' : Kˣ,
      glA A = g * glA (Matrix.GeneralLinearGroup.scalar (Fin n) c'))
    (hQ : ∀ (j : K[X]) (hj : j ∈ primaryFactors (glA A : Module.End K (Fin n → K))), j ≠ a →
      IsGoodBlock h (glA A) ⟨j, hj⟩ → glA A ∈ specialBlock (idForm h n) (glA A) j →
      (∀ g ∈ specialBlock (idForm h n) (glA A) j, glA Ba * g = g * glA Ba) ∧
      (∀ g ∈ specialBlock (idForm h n) (glA A) j, glA Bb * g = g * glA Bb)) :
    ℓ ^ f = 2 ∧ 4 ≤ primaryMultiplicity (glA A : Module.End K (Fin n → K)) a ∧
      dualPoly h.bar a = a ∧ a.natDegree = 1 ∧
      ∃ j ∈ primaryFactors (glA A : Module.End K (Fin n → K)), j ≠ a := by
  classical
  have hq2 := two_le_pow_of h
  have hsq := H.squarefree
  obtain ⟨g₀, hg₀, c', hAeq⟩ := hA
  have hBa : Ba * A = A * Ba := commute_of_eq_mul_scalar hAeq (hFa g₀ hg₀)
  have hBb : Bb * A = A * Bb := commute_of_eq_mul_scalar hAeq (hFb g₀ hg₀)
  have hAa := commutator_acts_trivially_good h hAU hBaU hBbU H hcomm hBa hBb ha hgood hFa hFb
  have ha1 : a = X - C 1 := eq_X_sub_C_of_acts_as_scalar hsq ha (μ := 1)
    (fun v hv => by rw [one_smul]; exact hAa v hv)
  have hselfa : dualPoly h.bar a = a := by rw [ha1]; exact dualPoly_X_sub_C_one _
  have hnda : a.natDegree = 1 := by rw [ha1]; exact natDegree_X_sub_C 1
  have hAj : ∀ j ∈ primaryFactors (glA A : Module.End K (Fin n → K)), j ≠ a →
      ∀ v ∈ primaryComponent (glA A : Module.End K (Fin n → K)) j,
        (glA A : Module.End K (Fin n → K)) v = (c' : K) • v := by
    intro j hj hja v hv
    obtain ⟨hs, -, -⟩ := mem_specialBlock.mp hg₀
    have h1 : (g₀ : Module.End K (Fin n → K)) v = v :=
      hs.2 j hj (by simp [hselfa, hja]) v hv
    have e : (glA A : Module.End K (Fin n → K)) v =
        (g₀ : Module.End K (Fin n → K)) ((c' : K) • v) := by
      conv_lhs => rw [hAeq]
      simp only [Units.val_mul, Module.End.mul_apply]
      congr 1
      ext i
      simp [glA, Matrix.GeneralLinearGroup.scalar]
    rw [e, map_smul, h1]
  obtain ⟨j₀, hj₀, hj₀a⟩ : ∃ j ∈ primaryFactors (glA A : Module.End K (Fin n → K)), j ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hA1 1
    rw [map_one]
    refine eq_one_of_acts_trivially hsq (fun j hj v hv => ?_)
    rw [hcon j hj] at hv
    exact hAa v hv
  have hσ1 : (c' : K) ≠ 1 := by
    intro hc1
    apply hA1 1
    rw [map_one]
    refine eq_one_of_acts_trivially hsq (fun j hj v hv => ?_)
    by_cases hja : j = a
    · subst hja; exact hAa v hv
    · rw [hAj j hj hja v hv, hc1, one_smul]
  have hj₀eq : j₀ = X - C (c' : K) :=
    eq_X_sub_C_of_acts_as_scalar hsq hj₀ (fun v hv => hAj j₀ hj₀ hj₀a v hv)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot hsq hj₀)
  have hcontra : (∀ v ∈ primaryComponent (glA A : Module.End K (Fin n → K)) j₀,
      (glA A : Module.End K (Fin n → K)) v = v) → False := by
    intro hid
    have h1 := hid v₀ hv₀
    rw [hAj j₀ hj₀ hj₀a v₀ hv₀] at h1
    have h2 : ((c' : K) - 1) • v₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact hσ1 (sub_eq_zero.1 h)
    · exact hv₀ne h
  have hbar0 : h.bar (c' : K) ≠ 0 := by
    simpa using c'.ne_zero
  have hdmem := dualPoly_mem_primaryFactors H hj₀
  have hdeq : dualPoly h.bar j₀ = X - C (h.bar (c' : K))⁻¹ := by
    rw [hj₀eq]; exact KCUnitaryBlock.dualPoly_X_sub_C hbar0
  have hμ : h.bar (c' : K) * (c' : K) = 1 := by
    obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hsq hdmem)
    have hw' : w ∈ primaryComponent (glA A : Module.End K (Fin n → K))
        (X - C (h.bar (c' : K))⁻¹) := by rw [← hdeq]; exact hw
    have h1 := acts_as_scalar_of_mem_X_sub_C hw'
    by_cases hda : dualPoly h.bar j₀ = a
    · exfalso
      rw [hda] at hw
      have h2 := hAa w hw
      rw [h1] at h2
      have h3 : ((h.bar (c' : K))⁻¹ - 1) • w = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      rcases smul_eq_zero.1 h3 with h4 | h4
      · have h5 : (h.bar (c' : K))⁻¹ = 1 := sub_eq_zero.1 h4
        have h6 : h.bar (c' : K) = 1 := by simpa using h5
        apply hσ1
        have h7 : h.bar (c' : K) = h.bar 1 := by rw [h6, map_one]
        exact h.bar.injective h7
      · exact hwne h4
    · have h2 := hAj _ hdmem hda w hw
      rw [h1] at h2
      have h3 : ((h.bar (c' : K))⁻¹ - (c' : K)) • w = 0 := by rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.1 h3 with h4 | h4
      · have h5 : (h.bar (c' : K))⁻¹ = (c' : K) := sub_eq_zero.1 h4
        have h6 : h.bar (c' : K) * (h.bar (c' : K))⁻¹ = 1 := mul_inv_cancel₀ hbar0
        rw [h5] at h6
        exact h6
      · exact absurd h4 hwne
  have hselfj : dualPoly h.bar j₀ = j₀ := by
    have : (h.bar (c' : K))⁻¹ = (c' : K) := inv_eq_of_mul_eq_one_right hμ
    rw [hdeq, this, hj₀eq]
  have hndj : j₀.natDegree = 1 := by rw [hj₀eq]; exact natDegree_X_sub_C _
  have hm1 : 1 ≤ primaryMultiplicity (glA A : Module.End K (Fin n → K)) j₀ := by
    have : Fact (Irreducible j₀) := ⟨irreducible_of_mem_primaryFactors hj₀⟩
    haveI : Nontrivial (primaryComponent (glA A : Module.End K (Fin n → K)) j₀) :=
      Submodule.nontrivial_iff_ne_bot.2 (primaryComponent_ne_bot hsq hj₀)
    exact Module.finrank_pos
  by_cases hm : primaryMultiplicity (glA A : Module.End K (Fin n → K)) j₀ ≤ 1
  · exact (hcontra (commutator_acts_trivially_of_mult_le_one hj₀ hcomm hBa hBb hm)).elim
  push Not at hm
  by_cases hgood2 : IsGoodBlock h (glA A) ⟨j₀, hj₀⟩
  · exfalso
    have hgA : glA A ∈ sesqUnitaryGroup (idForm h n) :=
      (toLin_mem_sesqUnitaryGroup_iff A).mpr hAU
    have hdet : LinearMap.det (glA A : Module.End K (Fin n → K)) = 1 := by
      have : (glA A : Module.End K (Fin n → K)) = Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) :=
        rfl
      rw [this, LinearMap.det_toLin']
      exact hdetA
    have hall : ∀ b ∈ primaryFactors (glA A : Module.End K (Fin n → K)), b = a ∨ b = j₀ := by
      intro b hb
      by_cases hba : b = a
      · exact Or.inl hba
      · exact Or.inr ((eq_X_sub_C_of_acts_as_scalar hsq hb (hAj b hb hba)).trans hj₀eq.symm)
    have hpf : primaryFactors (glA A : Module.End K (Fin n → K)) = {a, j₀} := by
      ext b
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hall b, fun hb => hb.elim (fun hb => hb ▸ ha) (fun hb => hb ▸ hj₀)⟩
    have hid : ∀ v : Fin n → K,
        (∀ w ∈ primaryComponent (glA A : Module.End K (Fin n → K)) (X - C (c' : K)),
          idForm h n w v = 0) → (glA A : Module.End K (Fin n → K)) v = v := by
      intro v hv
      rw [← hj₀eq] at hv
      have hu : primaryProjection (glA A : Module.End K (Fin n → K)) j₀ v ∈
          primaryComponent (glA A : Module.End K (Fin n → K)) j₀ := primaryProjection_mem hsq hj₀ v
      have hva : primaryProjection (glA A : Module.End K (Fin n → K)) a v ∈
          primaryComponent (glA A : Module.End K (Fin n → K)) a := primaryProjection_mem hsq ha v
      have hsum : v = primaryProjection (glA A : Module.End K (Fin n → K)) a v +
          primaryProjection (glA A : Module.End K (Fin n → K)) j₀ v := by
        have := LinearMap.congr_fun (sum_primaryProjection hsq) v
        rw [LinearMap.sum_apply, hpf, Finset.sum_pair hj₀a.symm] at this
        simpa using this.symm
      have hperp : ∀ w ∈ primaryComponent (glA A : Module.End K (Fin n → K)) j₀,
          idForm h n w (primaryProjection (glA A : Module.End K (Fin n → K)) j₀ v) = 0 := by
        intro w hw
        have h1 : idForm h n w v = 0 := hv w hw
        have h2 : idForm h n w (primaryProjection (glA A : Module.End K (Fin n → K)) a v) = 0 :=
          orthogonal_of_ne_dualPoly H hj₀ ha (by rw [hselfj]; exact hj₀a.symm) hw hva
        rw [hsum, map_add, h2, zero_add] at h1
        exact h1
      have hu0 : primaryProjection (glA A : Module.End K (Fin n → K)) j₀ v = 0 :=
        eq_zero_of_perfect_right H hj₀ hj₀ hselfj.symm hu hperp
      rw [hu0, add_zero] at hsum
      rw [hsum]
      exact hAa _ hva
    have hmem : glA A ∈ specialBlock (idForm h n) (glA A) j₀ := by
      rw [hj₀eq]
      exact KCUnitaryBlock.mem_specialBlock_of_degree_one H hμ (hj₀eq ▸ hj₀) hgA (Commute.refl _)
        hid hdet
    obtain ⟨hQa, hQb⟩ := hQ j₀ hj₀ hj₀a hgood2 hmem
    exact hcontra (commutator_acts_trivially_good h hAU hBaU hBbU H hcomm hBa hBb hj₀ hgood2 hQa
      hQb)
  · have hex : (primaryMultiplicity (glA A : Module.End K (Fin n → K)) j₀,
        ℓ ^ (f * j₀.natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
      by_contra hnot
      exact hgood2 ⟨hm, fun _ => hnot⟩
    rw [hndj, mul_one] at hex
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hex
    have hℓf2 : ℓ ^ f = 2 := by
      rcases hex with ⟨-, h2⟩ | ⟨-, h3⟩ | ⟨-, h2⟩
      · exact h2
      · exfalso
        have : ℓ ∣ 3 := h3 ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
        exact hℓ3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 this)
      · exact h2
    refine ⟨hℓf2, ?_, hselfa, hnda, j₀, hj₀, hj₀a⟩
    obtain ⟨hma2, hma⟩ := hgood
    have h4 := hma hselfa
    simp only [hnda, mul_one, hℓf2, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
      not_or, and_true] at h4
    change 2 ≤ primaryMultiplicity (glA A : Module.End K (Fin n → K)) a at hma2
    omega

end Unitary


end UnitaryCore

namespace UnitaryGlue

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) [Finite K]

@[expose] noncomputable def specialSU (A : GL (Fin n) K) (j : K[X]) :
    Subgroup (gramSU h (idGram K n)) :=
  (specialBlock (idForm h n) (glA A) j).comap (toLinSU h n)

theorem mem_specialSU {A : GL (Fin n) K} {j : K[X]} {g : gramSU h (idGram K n)} :
    g ∈ specialSU h A j ↔ toLinSU h n g ∈ specialBlock (idForm h n) (glA A) j := Iff.rfl

theorem specialBlock_le_range_toLinSU {A : GL (Fin n) K}
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA A)) {j : K[X]}
    (hj : j ∈ primaryFactors (glA A : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (glA A) ⟨j, hj⟩) :
    specialBlock (idForm h n) (glA A) j ≤ (toLinSU h n).range := fun g hg =>
  mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H (two_le_pow_of h) ⟨j, hj⟩
    hgood hg)

theorem map_specialSU {A : GL (Fin n) K}
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA A)) {j : K[X]}
    (hj : j ∈ primaryFactors (glA A : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (glA A) ⟨j, hj⟩) :
    (specialSU h A j).map (toLinSU h n) = specialBlock (idForm h n) (glA A) j :=
  Subgroup.map_comap_eq_self (specialBlock_le_range_toLinSU h H hj hgood)

theorem isQuasisimple_specialSU {A : GL (Fin n) K}
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA A)) {j : K[X]}
    (hj : j ∈ primaryFactors (glA A : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (glA A) ⟨j, hj⟩) : CFSG.IsQuasisimple (specialSU h A j) := by
  have hQ := (specialBlockFacts_of_good H (two_le_pow_of h) ⟨j, hj⟩ hgood).quasisimple hgood.1
  let e : ↥(specialSU h A j) ≃* ↥(specialBlock (idForm h n) (glA A) j) :=
    (Subgroup.equivMapOfInjective (specialSU h A j) (toLinSU h n) toLinSU_injective).trans
      (MulEquiv.subgroupCongr (map_specialSU h H hj hgood))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ

theorem specialSU_le_fixSubgroup (A : primeFormUnitary h (idGram K n)) (j : K[X]) :
    specialSU h (A : GL (Fin n) K) j ≤ fixSubgroup (primeFormConjSU h (idGram K n) A) := fun g hg =>
  (mem_fixSubgroup_primeFormConjSU_iff A rfl g).mpr
    (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2

theorem conj_mem_specialSU (A : primeFormUnitary h (idGram K n)) (j : K[X])
    {c g : gramSU h (idGram K n)} (hc : c ∈ fixSubgroup (primeFormConjSU h (idGram K n) A))
    (hg : g ∈ specialSU h (A : GL (Fin n) K) j) :
    c * g * c⁻¹ ∈ specialSU h (A : GL (Fin n) K) j := by
  have hcU := toLinSU_mem_unitaryCentralizer A rfl hc
  have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
  rw [mem_specialSU, map_mul, map_mul, map_inv]
  exact this


theorem commute_of_fixes_proj_unitary (F : Subgroup (gramSU h (idGram K n))) (hF : ⁅F, F⁆ = F)
    (B : primeFormUnitary h (idGram K n))
    (hfix : ∀ f ∈ F, primeFormConjHom h (idGram K n) B (f : primeFormP h (idGram K n)) =
      (f : primeFormP h (idGram K n))) :
    ∀ f ∈ F, (B : GL (Fin n) K) * (f : GL (Fin n) K) = (f : GL (Fin n) K) * (B : GL (Fin n) K) := by
  have h1 := eq_of_perfect_of_central F hF (primeFormConjSU h (idGram K n) B) (fun f hf => by
    have h0 := hfix f hf
    rw [primeFormConjHom_mk] at h0
    have h0' : ((primeFormConjSU h (idGram K n) B f : gramSU h (idGram K n)) :
        primeFormP h (idGram K n)) = (f : primeFormP h (idGram K n)) := h0
    have h2 : ((f⁻¹ * primeFormConjSU h (idGram K n) B f : gramSU h (idGram K n)) :
        primeFormP h (idGram K n)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h0', inv_mul_cancel]
    exact normOneScalars_le_center h _ n ((QuotientGroup.eq_one_iff _).1 h2))
  intro f hf
  have h4 := congrArg Subtype.val (h1 f hf)
  change (B : GL (Fin n) K) * f * (B : GL (Fin n) K)⁻¹ = f at h4
  calc (B : GL (Fin n) K) * f = ((B : GL (Fin n) K) * f * (B : GL (Fin n) K)⁻¹) * B := by group
    _ = f * B := by rw [h4]


theorem glaPComponent_map_specialSU {A : primeFormUnitary h (idGram K n)}
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA (A : GL (Fin n) K))) {j : K[X]}
    (hj : j ∈ primaryFactors (glA (A : GL (Fin n) K) : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (glA (A : GL (Fin n) K)) ⟨j, hj⟩) {t : gramSU h (idGram K n)}
    (htA : (t : GL (Fin n) K) = (A : GL (Fin n) K))
    (hmem : glA (A : GL (Fin n) K) ∈ specialBlock (idForm h n) (glA (A : GL (Fin n) K)) j)
    (hx3 : orderOf (t : primeFormP h (idGram K n)) = 3) :
    GLAPComponent 3 (fixSubgroup (primeFormConjHom h (idGram K n) A))
      ((specialSU h (A : GL (Fin n) K) j).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) := by
  classical
  haveI := h.finite
  have hker : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
      Subgroup.center (gramSU h (idGram K n)) := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hcomp := isComponentOf_map_fixSubgroup_aux
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _)
    hker (primeFormConjSU h (idGram K n) A) (primeFormConjHom h (idGram K n) A)
    (fun g => (primeFormConjHom_mk h (idGram K n) A g).symm)
    (specialSU_le_fixSubgroup h A j) (fun c hc g hg => conj_mem_specialSU h A j hc hg)
    (isQuasisimple_specialSU h H hj hgood)
  have htF : t ∈ specialSU h (A : GL (Fin n) K) j := by
    rw [mem_specialSU]
    have : toLinSU h n t = glA (t : GL (Fin n) K) := toLinSU_apply t
    rw [this, htA]
    exact hmem
  have h3 : 3 ∣ Nat.card ((specialSU h (A : GL (Fin n) K) j).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) := by
    have hxF : (t : primeFormP h (idGram K n)) ∈ (specialSU h (A : GL (Fin n) K) j).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := ⟨t, htF, rfl⟩
    have := orderOf_dvd_natCard (⟨_, hxF⟩ : ↥((specialSU h (A : GL (Fin n) K) j).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))))
    rwa [Subgroup.orderOf_mk, hx3] at this
  exact i253_glaPComponent_of_subnormal hcomp.1 hcomp.2.1 hcomp.2.2 h3


theorem eighty_one_dvd_prod {m : ℕ} (hm : 4 ≤ m) :
    (81 : ℤ) ∣ ∏ i ∈ Finset.Icc 2 m, ((2 : ℤ) ^ i - (-1) ^ i) := by
  have h1 : ∏ i ∈ Finset.Icc 2 4, ((2 : ℤ) ^ i - (-1) ^ i) = 405 := by
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide]
    simp [Finset.prod_insert]
  have h2 := Finset.prod_dvd_prod_of_subset (Finset.Icc 2 4) (Finset.Icc 2 m)
    (fun i => ((2 : ℤ) ^ i - (-1) ^ i)) (Finset.Icc_subset_Icc_right hm)
  rw [h1] at h2
  exact (show (81 : ℤ) ∣ 405 by norm_num).trans h2


theorem eighty_one_dvd_card_specialBlock {A : GL (Fin n) K}
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA A)) {jb : K[X]}
    (hjb : jb ∈ primaryFactors (glA A : Module.End K (Fin n → K))) (hℓf : ℓ ^ f = 2)
    (hm4 : 4 ≤ primaryMultiplicity (glA A : Module.End K (Fin n → K)) jb)
    (hself : dualPoly h.bar jb = jb) (hnd : jb.natDegree = 1) :
    81 ∣ Nat.card ↥(specialBlock (idForm h n) (glA A) jb) := by
  have : Fact (Irreducible jb) := ⟨irreducible_of_mem_primaryFactors hjb⟩
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ := nonempty_specialBlock_mulEquiv_sesqSU (a := ⟨jb, hjb⟩) hself
    (selfDualPrimaryBlock H ⟨jb, hjb⟩ hself)
  have hord := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := primaryMultiplicity (glA A : Module.End K (Fin n → K)) jb) rfl (by omega)).2.1
  set Q : ℕ := ℓ ^ (f * (↑(⟨jb, hjb⟩ : primaryFactors (glA A : Module.End K (Fin n → K))) :
    K[X]).natDegree) with hQdef
  have hQ2 : Q = 2 := by
    have : (↑(⟨jb, hjb⟩ : primaryFactors (glA A : Module.End K (Fin n → K))) : K[X]).natDegree =
        1 := hnd
    rw [hQdef, this, mul_one, hℓf]
  rw [hQ2] at hord
  have h81 : (81 : ℤ) ∣ (Nat.card ↥(sesqSpecialUnitaryGroup Hf) : ℤ) := by
    rw [hord]
    exact Dvd.dvd.mul_left (eighty_one_dvd_prod hm4) _
  rw [Nat.card_congr e.toEquiv]
  exact_mod_cast h81


end UnitaryGlue

open UnitaryCore UnitaryGlue in
theorem unitary_core {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hℓ : ℓ ≠ 3)
    (hZ : Subgroup.center (primeFormP h (idGram K n)) = ⊥)
    {a b : MulAut (primeFormP h (idGram K n))} {x : primeFormP h (idGram K n)}
    {J : Subgroup (primeFormP h (idGram K n))} (c : CoreCfg a b x J) : False := by
  classical
  haveI := h.finite
  obtain ⟨Ba, hBa⟩ := exists_primeFormConjHom_of_mem_commutator h hn hq c.a_mem
  obtain ⟨Bb, hBb⟩ := exists_primeFormConjHom_of_mem_commutator h hn hq c.b_mem
  set A : primeFormUnitary h (idGram K n) := Ba * Bb * Ba⁻¹ * Bb⁻¹ with hAdef
  have hdetA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det (A : GL (Fin n) K) = 1 := by
      rw [hAdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      have := commutatorElement_eq_one_iff_mul_comm.2
        (mul_comm (Matrix.GeneralLinearGroup.det (Ba : GL (Fin n) K))
          (Matrix.GeneralLinearGroup.det (Bb : GL (Fin n) K)))
      rwa [commutatorElement_def] at this
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa using h2
  set t : gramSU h (idGram K n) := ⟨(A : GL (Fin n) K), (mem_gramSU_iff_unitary h).2 ⟨A.2, hdetA⟩⟩
    with ht
  have hconjt :
      primeFormConjHom h (idGram K n) A = MulAut.conj (t : primeFormP h (idGram K n)) := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk, MulAut.conj_apply]
    rfl
  have hconjA : primeFormConjHom h (idGram K n) A = MulAut.conj x := by
    rw [hAdef, map_mul, map_mul, map_mul, map_inv, map_inv, ← hBa, ← hBb]
    exact c.comm
  have hxt : x = (t : primeFormP h (idGram K n)) :=
    conj_injective_of_center_bot hZ (hconjA.symm.trans hconjt)
  have hx3 : x ^ 3 = 1 := c.order ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    have := c.order
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨c₃, -, -, hc₃⟩ : (t ^ 3) ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    have h1 : ((t ^ 3 : gramSU h (idGram K n)) : primeFormP h (idGram K n)) = 1 := by
      rw [QuotientGroup.mk_pow, ← hxt, hx3]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hA3 : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c₃ := by
    have : ((t ^ 3 : gramSU h (idGram K n)) : GL (Fin n) K) = (A : GL (Fin n) K) ^ 3 := rfl
    rw [← this]; exact hc₃
  have H := primaryData_toLin' h A.2 Nat.prime_three (Ne.symm hℓ) hA3
  have hsq := H.squarefree
  have hA1 : ∀ c' : Kˣ, (A : GL (Fin n) K) ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c' := by
    intro c' hc'
    apply hx1
    apply conj_injective_of_center_bot hZ
    rw [← hconjA, map_one]
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    show (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
    rw [hc', (commute_scalar c' (g : GL (Fin n) K)).eq.symm, mul_inv_cancel_right]
  have hfix : fixSubgroup (primeFormConjHom h (idGram K n) A) =
      Subgroup.centralizer ({x} : Set _) := by
    rw [hconjA]; exact fixSubgroup_conj_eq x
  have hJc : GLAPComponent 3 (fixSubgroup (primeFormConjHom h (idGram K n) A)) J := by
    rw [hfix]; exact c.comp
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJc
  have hlayer := LieSemisimple.perfectInLayer_primeFormConjHom h Nat.prime_three (Ne.symm hℓ) A hA3
    J hJc.1 hperf
  obtain ⟨hJcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJc hlayer
  obtain ⟨⟨⟨jb, hjb⟩, hgood⟩, hJeq⟩ :=
    exists_good_block_of_component (two_le_pow_of h) A rfl H J hJcomp
  have hFq := isQuasisimple_specialSU h H hjb hgood
  have hFperf : ⁅specialSU h (A : GL (Fin n) K) jb, specialSU h (A : GL (Fin n) K) jb⁆ =
      specialSU h (A : GL (Fin n) K) jb := Subgroup.isPerfect_iff.1 hFq.1
  have hfixJ : ∀ f ∈ specialSU h (A : GL (Fin n) K) jb,
      a (f : primeFormP h (idGram K n)) = (f : primeFormP h (idGram K n)) ∧
      b (f : primeFormP h (idGram K n)) = (f : primeFormP h (idGram K n)) := fun f hf =>
    c.centralizes J (hfix ▸ hJc) _ (hJeq ▸ ⟨f, hf, rfl⟩)
  have hcommSB : ∀ {j : K[X]} (hj : j ∈ primaryFactors (glA (A : GL (Fin n) K) :
        Module.End K (Fin n → K))) (hg : IsGoodBlock h (glA (A : GL (Fin n) K)) ⟨j, hj⟩)
      {B : GL (Fin n) K},
      (∀ f ∈ specialSU h (A : GL (Fin n) K) j, B * (f : GL (Fin n) K) = (f : GL (Fin n) K) * B) →
      ∀ g ∈ specialBlock (idForm h n) (glA (A : GL (Fin n) K)) j, glA B * g = g * glA B := by
    intro j hj hg B hB g hgS
    obtain ⟨f, rfl⟩ := specialBlock_le_range_toLinSU h H hj hg hgS
    have hf : f ∈ specialSU h (A : GL (Fin n) K) j := hgS
    rw [toLinSU_apply, ← glA_mul, ← glA_mul, hB f hf]
  have hFa := hcommSB hjb hgood (B := (Ba : GL (Fin n) K))
    (commute_of_fixes_proj_unitary h _ hFperf Ba (fun f hf => by rw [← hBa]; exact (hfixJ f hf).1))
  have hFb := hcommSB hjb hgood (B := (Bb : GL (Fin n) K))
    (commute_of_fixes_proj_unitary h _ hFperf Bb (fun f hf => by rw [← hBb]; exact (hfixJ f hf).2))
  have hA : ∃ g ∈ specialBlock (idForm h n) (glA (A : GL (Fin n) K)) jb, ∃ c' : Kˣ,
      glA (A : GL (Fin n) K) = g * glA (Matrix.GeneralLinearGroup.scalar (Fin n) c') := by
    have hxJ : x ∈ (specialSU h (A : GL (Fin n) K) jb).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := hJeq ▸ c.mem
    obtain ⟨f, hf, hfx⟩ := hxJ
    obtain ⟨c'', -, -, hc''⟩ : f⁻¹ * t ∈ normOneScalars h (gramSU h (idGram K n)) n :=
      QuotientGroup.eq.1 (hfx.trans hxt)
    refine ⟨toLinSU h n f, hf, c'', ?_⟩
    have h1 : (A : GL (Fin n) K) = (f : GL (Fin n) K) *
        Matrix.GeneralLinearGroup.scalar (Fin n) c'' := by
      have : ((f⁻¹ * t : gramSU h (idGram K n)) : GL (Fin n) K) = (f : GL (Fin n) K)⁻¹ * t := rfl
      rw [this] at hc''
      rw [← hc'', mul_inv_cancel_left]
    rw [h1, glA_mul]
    rfl
  have hQ : ∀ (j : K[X]) (hj : j ∈ primaryFactors (glA (A : GL (Fin n) K) :
        Module.End K (Fin n → K))), j ≠ jb →
      IsGoodBlock h (glA (A : GL (Fin n) K)) ⟨j, hj⟩ →
      glA (A : GL (Fin n) K) ∈ specialBlock (idForm h n) (glA (A : GL (Fin n) K)) j →
      (∀ g ∈ specialBlock (idForm h n) (glA (A : GL (Fin n) K)) j,
        glA (Ba : GL (Fin n) K) * g = g * glA (Ba : GL (Fin n) K)) ∧
      (∀ g ∈ specialBlock (idForm h n) (glA (A : GL (Fin n) K)) j,
        glA (Bb : GL (Fin n) K) * g = g * glA (Bb : GL (Fin n) K)) := by
    intro j hj hjb' hjg hmem
    have hx3' : orderOf (t : primeFormP h (idGram K n)) = 3 := hxt ▸ c.order
    have hcomp := glaPComponent_map_specialSU h H hj hjg (t := t) rfl hmem hx3'
    rw [hfix] at hcomp
    have hFjq := isQuasisimple_specialSU h H hj hjg
    have hFjperf : ⁅specialSU h (A : GL (Fin n) K) j, specialSU h (A : GL (Fin n) K) j⁆ =
        specialSU h (A : GL (Fin n) K) j := Subgroup.isPerfect_iff.1 hFjq.1
    have hfixj : ∀ f ∈ specialSU h (A : GL (Fin n) K) j,
        a (f : primeFormP h (idGram K n)) = (f : primeFormP h (idGram K n)) ∧
        b (f : primeFormP h (idGram K n)) = (f : primeFormP h (idGram K n)) := fun f hf =>
      c.centralizes _ hcomp _ ⟨f, hf, rfl⟩
    exact ⟨hcommSB hj hjg (commute_of_fixes_proj_unitary h _ hFjperf Ba
        (fun f hf => by rw [← hBa]; exact (hfixj f hf).1)),
      hcommSB hj hjg (commute_of_fixes_proj_unitary h _ hFjperf Bb
        (fun f hf => by rw [← hBb]; exact (hfixj f hf).2))⟩
  have hcommGL : (A : GL (Fin n) K) = (Ba : GL (Fin n) K) * (Bb : GL (Fin n) K) *
      (Ba : GL (Fin n) K)⁻¹ * (Bb : GL (Fin n) K)⁻¹ := rfl
  obtain ⟨hℓf, hm4, hselfjb, hndjb, j₀, hj₀, hj₀a⟩ := unitary_matrix_core h hℓ A.2 Ba.2 Bb.2 H hdetA
    hcommGL hA1 hjb hgood hFa hFb hA hQ
  have h81 := eighty_one_dvd_card_specialBlock h H hjb hℓf hm4 hselfjb hndjb
  have hcardF : Nat.card ↥(specialSU h (A : GL (Fin n) K) jb) =
      Nat.card ↥(specialBlock (idForm h n) (glA (A : GL (Fin n) K)) jb) := by
    rw [← map_specialSU h H hjb hgood]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ (toLinSU h n) toLinSU_injective).toEquiv
  have hinj : ∀ g ∈ specialSU h (A : GL (Fin n) K) jb,
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) g = 1 → g = 1 := by
    intro g hg hg1
    obtain ⟨c₀, -, -, hc₀⟩ : g ∈ normOneScalars h (gramSU h (idGram K n)) n :=
      (QuotientGroup.eq_one_iff g).1 hg1
    obtain ⟨hs, -, -⟩ := mem_specialBlock.mp (mem_specialSU h |>.1 hg)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hsq hj₀)
    have h1 : ((toLinSU h n g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = v :=
      hs.2 j₀ hj₀ (by simp [hselfjb, hj₀a]) v hv
    have h2 : ((toLinSU h n g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = (c₀ : K) • v := by
      rw [toLinSU_apply, hc₀]
      ext i
      simp [Matrix.GeneralLinearGroup.scalar]
    have h3 : ((c₀ : K) - 1) • v = 0 := by rw [sub_smul, ← h2, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · have : c₀ = 1 := Units.ext (sub_eq_zero.1 h4)
      apply Subtype.ext
      rw [hc₀, this, map_one]
      rfl
    · exact absurd h4 hv0
  have hcardJ : Nat.card J = Nat.card ↥(specialSU h (A : GL (Fin n) K) jb) := by
    rw [hJeq]
    exact Transport.card_map_of_injOn (Transport.injOn_of_ker hinj)
  have h81J : 3 ^ 4 ∣ Nat.card J := by
    rw [hcardJ, hcardF]
    simpa using h81
  have hJpos : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJpos).1 h81J
  have hord := c.ord
  omega


end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
