module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthCases
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSetup
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Core

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Qf : QuadraticForm F V}

theorem perfectInLayer_congr_of_conj {G T : Type*} [Group G] [Group T] (φ : G ≃* T) {a : G}
    (h : PerfectInLayer (MulAut.conj a)) : PerfectInLayer (MulAut.congr φ (MulAut.conj a)) := by
  refine perfectInLayer_of_congr φ.symm _ ?_
  have : MulAut.congr φ.symm (MulAut.congr φ (MulAut.conj a)) = MulAut.conj a := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [this]
  exact h

theorem orth_core (hQ : (QuadraticMap.polarBilin Qf).Nondegenerate)
    (hT : ∃ U : Submodule F V, finrank F U = 3 ∧ ∀ u ∈ U, Qf u = 0) (hℓ5 : ringChar F ≠ 5)
    (hN7 : 7 ≤ finrank F V) {K : Type} [Group K] [Finite K] (φ : K ≃* ProjOrthDerived Qf)
    {P : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K} (D : I1434.Data K P x J₁ J₂)
    (hlayer : PerfectInLayer (MulAut.conj x)) :
    ∃ xl : ↥(orthDerived Qf), QuotientGroup.mk xl = φ x ∧ Nat.card F = 2 ∧ finrank F V = 12 ∧
      finrank F (fixedSpace (xl : V ≃ₗ[F] V)) = 4 := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hpℓ : (5 : ℕ) ≠ ringChar F := fun h => hℓ5 h.symm
  have ha5 : (φ x) ^ 5 = 1 := by rw [← map_pow, D.pow_five, map_one]
  have ha1 : φ x ≠ 1 := fun h => D.ne_one (φ.injective (h.trans (map_one φ).symm))
  obtain ⟨xl, Rep, hxl, Cset, hmk, hRep, hcomp, htype⟩ :=
    exists_components_named Nat.prime_five (by decide) hQ hT hpℓ (φ x) ha5 ha1
  refine ⟨xl, hmk, ?_⟩
  have hno4 : ∀ E : Subgroup (V ≃ₗ[F] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Qf →
      IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 4 :=
    fun E hEO hE hcard => false_of_elemAbelian_five_pow_four hQ hT φ D.rank hEO hE hcard
  have hlayerT := perfectInLayer_congr_of_conj φ hlayer
  obtain ⟨hc₁, h₁⟩ := five_component_data φ hlayerT D.five.comp₁ D.five.quot₁
  obtain ⟨hc₂, h₂⟩ := five_component_data φ hlayerT D.five.comp₂ D.five.quot₂
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.congr φ (MulAut.conj x)) =
      Subgroup.centralizer ({φ x} : Set (ProjOrthDerived Qf)) := by
    rw [congr_conj_eq]
    ext g
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hfix] at hc₁ hc₂
  have hne : J₁.map (φ : K →* ProjOrthDerived Qf) ≠ J₂.map (φ : K →* ProjOrthDerived Qf) :=
    fun h => D.five.ne (Subgroup.map_injective φ.injective h)
  rcases hcomp _ hc₁ with ⟨a₁, hR₁, hne₁, hq₁, hJ₁⟩ | hCs₁ <;>
    rcases hcomp _ hc₂ with ⟨a₂, hR₂, hne₂, hq₂, hJ₂⟩ | hCs₂
  · exfalso
    have hne' : a₁ ≠ a₂ := fun h => hne (by rw [hJ₁, hJ₂, h])
    exact false_of_two_blocks hxl hRep hℓ5 hno4 hR₁ hR₂ hne' hne₁ hne₂ hq₁ hq₂
      (by rw [← hJ₁]; exact h₁) (by rw [← hJ₂]; exact h₂)
  · exact block_fixed_outcome hQ hxl hRep hℓ5 hno4 hN7 hR₁ hne₁ hq₁ (by rw [← hJ₁]; exact h₁)
      htype hCs₂ h₂
  · exact block_fixed_outcome hQ hxl hRep hℓ5 hno4 hN7 hR₂ hne₂ hq₂ (by rw [← hJ₂]; exact h₂)
      htype hCs₁ h₁
  · exfalso
    obtain ⟨-, -, hC⟩ := fixed_component_cases hQ hxl hRep hℓ5 hno4 hN7 htype hCs₁ h₁
    rw [hC, Set.mem_singleton_iff] at hCs₁ hCs₂
    exact hne (hCs₁.trans hCs₂.symm)

end Core

section Model

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q₀ : (ι → F) → F} {Qf : QuadraticForm F (ι → F)}

theorem core_model (hcoe : ⇑Qf = Q₀) (hQ : (QuadraticMap.polarBilin Qf).Nondegenerate)
    (hT : ∃ U : Submodule F (ι → F), finrank F U = 3 ∧ ∀ u ∈ U, Qf u = 0)
    (hℓ5 : ringChar F ≠ 5) (hN7 : 7 ≤ Fintype.card ι) {K : Type} [Group K] [Finite K]
    (eK : K ≃* StatedProj (StatedOmega Q₀)) {P : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K}
    (D : I1434.Data K P x J₁ J₂) (hlayer : PerfectInLayer (MulAut.conj x)) :
    Nat.card F = 2 ∧ Fintype.card ι = 12 ∧ ∃ e' : K ≃* StatedOmega Q₀, e' x ≠ 1 ∧
      (e' x) ^ 5 = 1 ∧ finrank F (LinearMap.ker (Matrix.toLin'
        ((((e' x : StatedOmega Q₀) : GL ι F) : Matrix ι ι F) - 1))) = 4 := by
  classical
  have hdim : finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  set φ : K ≃* ProjOrthDerived Qf := eK.trans (projOrthEquiv hcoe) with hφ
  obtain ⟨xl, hmk, hF2, hι, hfixd⟩ := orth_core hQ hT hℓ5 (by rw [hdim]; exact hN7) φ D hlayer
  refine ⟨hF2, by rw [← hdim]; exact hι, ?_⟩
  haveI := charP_two_of_card_two hF2
  haveI : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  set ρ : ↥(orthDerived Qf) →* ProjOrthDerived Qf :=
    QuotientGroup.mk' ((scalars F (ι → F)).subgroupOf (orthDerived Qf)) with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    exact Subtype.ext (CFSG.RankThree.PartOne.eq_one_of_mem_scalars_of_mem_orthDerived hQ w.2 hw)
  let ρe : ↥(orthDerived Qf) ≃* ProjOrthDerived Qf :=
    MulEquiv.ofBijective ρ ⟨hρinj, QuotientGroup.mk'_surjective _⟩
  let ωe := omegaOrthEquiv hcoe
  let e' : K ≃* StatedOmega Q₀ := φ.trans (ρe.symm.trans ωe.symm)
  refine ⟨e', fun h => D.ne_one (e'.injective (h.trans (map_one e').symm)), by
    rw [← map_pow, D.pow_five, map_one], ?_⟩
  have h1 : ωe (e' x) = xl := by
    show ωe (ωe.symm (ρe.symm (φ x))) = xl
    rw [MulEquiv.apply_symm_apply]
    exact (MulEquiv.symm_apply_eq ρe).2 hmk.symm
  have h2 : toLinEquiv ι F ((e' x : StatedOmega Q₀) : GL ι F) = (xl : (ι → F) ≃ₗ[F] (ι → F)) := by
    rw [← h1]
    exact (coe_omegaOrthEquiv hcoe (e' x)).symm
  have h3 : LinearMap.ker (Matrix.toLin' ((((e' x : StatedOmega Q₀) : GL ι F) :
      Matrix ι ι F) - 1)) = fixedSpace (xl : (ι → F) ≃ₗ[F] (ι → F)) := by
    ext v
    rw [LinearMap.mem_ker, mem_fixedSpace, ← h2, toLinEquiv_apply, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [h3]
  exact hfixd

end Model

section Tags

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

theorem prime_pow_eq_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h : ℓ ^ f = 2) :
    ℓ = 2 ∧ f = 1 := by
  have h1 : ℓ ∣ 2 := by
    rw [← h]
    exact dvd_pow_self ℓ (by omega)
  have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1
  subst hℓ2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (by simpa using h)⟩

theorem i1434Cl_POmega {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hm : StatedClassicalModel K t n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂) :
    t = .POmegaMinus ∧ ℓ = 2 ∧ f = 1 ∧ n = 6 ∧
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (b c : F),
      Fintype.card F = 2 ∧ (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (e : K ≃* StatedOmega (StatedQuadMinus 6 F b c))
        (A : StatedOmega (StatedQuadMinus 6 F b c)),
        e x = A ∧ A ^ 5 = 1 ∧ A ≠ 1 ∧
        Module.finrank F (LinearMap.ker (Matrix.toLin'
          (((A : GL (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2)
              (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2) F) - 1))) =
          4 := by
  classical
  have hm0 := hm
  have hlayer : PerfectInLayer (MulAut.conj x) :=
    LieSemisimple.perfectInLayer_conj_omega ht hm Nat.prime_five (by decide) (Ne.symm hℓ) x
      D.pow_five
  rcases ht with rfl | rfl | rfl
  ·
    exfalso
    obtain ⟨hadm, F, hF, hFfin, hcard, ⟨eK⟩⟩ := hm
    have h3 : 3 ≤ n ∧ ℓ ≠ 2 := hadm.2.2
    have hring : ringChar F = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    have h2 : (2 : F) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (by rw [hring]; exact hadm.1), hring]
      exact h3.2
    obtain ⟨hQ, hT⟩ := regular_quadOdd (K := F) (n := n) h2 h3.1
    have hcardι : Fintype.card (Fin n ⊕ Fin n ⊕ Unit) = 2 * n + 1 := by
      simp [Fintype.card_sum]
      ring
    obtain ⟨-, hι, -⟩ := core_model (CFSG.LieType.Universal.Spin.coe_quadOdd n F) hQ hT
      (by rw [hring]; exact hℓ) (by rw [hcardι]; omega) eK D hlayer
    omega
  ·
    exfalso
    obtain ⟨hadm, F, hF, hFfin, hcard, ⟨eK⟩⟩ := hm
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar F = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := regular_quadPlus (K := F) (n := n) (by omega)
    have hcardι : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
      simp [Fintype.card_sum]
      ring
    obtain ⟨hF2, hι, -⟩ := core_model
      (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := F)) hQ hT
      (by rw [hring]; exact hℓ) (by rw [hcardι]; omega) eK D hlayer
    obtain ⟨rfl, rfl⟩ := prime_pow_eq_two hadm.1 hadm.2.1 (hcard.symm.trans hF2)
    have hn6 : n = 6 := by omega
    subst hn6
    have hord := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hm0
    have h125 : 5 ^ 3 ∣ Nat.card K := by
      obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5)
        (Q : Subgroup K)
      rw [D.rank] at hEcard
      rw [← hEcard]
      exact Subgroup.card_subgroup_dvd_card E
    rw [hord] at h125
    exact absurd h125 (by
      change ¬ 5 ^ 3 ∣ CFSG.Open.ordD 6 (2 ^ 1)
      decide +kernel)
  ·
    obtain ⟨hadm, F, hF, hFfin, hcard, b, c, hirr, ⟨eK⟩⟩ := hm
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar F = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := regular_quadMinus (K := F) (n := n) h4 hirr
    have hcardι : Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = 2 * n := by
      simp [Fintype.card_sum]
      omega
    obtain ⟨hF2, hι, e', hne, h5, hker⟩ := core_model
      (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c) hQ hT
      (by rw [hring]; exact hℓ) (by rw [hcardι]; omega) eK D hlayer
    obtain ⟨rfl, rfl⟩ := prime_pow_eq_two hadm.1 hadm.2.1 (hcard.symm.trans hF2)
    have hn6 : n = 6 := by omega
    subst hn6
    letI : Fintype F := Fintype.ofFinite F
    refine ⟨rfl, rfl, rfl, rfl, F, hF, this, Classical.decEq F, b, c, ?_, hirr,
      e', e' x, rfl, h5, hne, hker⟩
    rw [Fintype.card_eq_nat_card]
    exact hF2

end Tags

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
