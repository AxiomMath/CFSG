module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsOrthAux.Fixed
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Component
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.RankThree.Classical2 (ProjOrthDerived)
open CFSG.ComponentClassification.CatLeaf (lieModel_odd_card_ne_L34 LieOrderFormulasInput)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)

namespace SsOrth

theorem mem_classicalTags_of_omega {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    t ∈ CFSG.Blueprint.classicalTags := by
  rcases ht with rfl | rfl | rfl <;> decide

theorem exists_projOrth_model {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
        (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
        Nat.card K = ℓ ^ f ∧ Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h3 : 3 ≤ n ∧ ℓ ≠ 2 := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two
        (by rw [hring]; exact hadm.1), hring]
      exact h3.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := n) h2 h3.1
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadOdd n K))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
      (by omega)
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) h4 hirr
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard,
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))⟩⟩

section TLevel

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem noL34Layer_conj_projOrth (hO : LieOrderFormulasInput)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hnot : ¬ IsLThreeFour (ProjOrthDerived Q)) {b : ProjOrthDerived Q} (hb : b ^ 3 = 1)
    (hPIL : PerfectInLayer (MulAut.conj b)) : NoL34Layer (MulAut.conj b) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  by_cases hb1 : b = 1
  · subst hb1
    obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    have hfix : fixSubgroup (MulAut.conj (1 : ProjOrthDerived Q)) = ⊤ := by
      ext g
      simp [mem_fixSubgroup, MulAut.conj_apply]
    exact noL34Layer_of_fixed_equiv _ ((MulEquiv.subgroupCongr hfix).trans Subgroup.topEquiv)
      hsimple hnonab hnot
  · have hord : orderOf b = 3 := orderOf_eq_prime hb hb1
    refine noL34Layer_of_components hPIL fun J hJ hJ34 => ?_
    have hJ' : CFSG.Open.IsComponentOf J
        (Subgroup.centralizer ({b} : Set (ProjOrthDerived Q))) := by
      rw [← fixSubgroup_conj_eq_centralizer]
      exact hJ
    obtain ⟨τ, n', f', hadm, hmodel⟩ :=
      oddLie_component_projOrth hQ hT hℓ (by omega) (by omega) hf hK hord hJ'
    exact lieModel_odd_card_ne_L34 hO (by omega) hadm hmodel (card_eq_of_isLThreeFour hJ34)

theorem noL34Layer_of_projOrth_equiv (hO : LieOrderFormulasInput)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {G : Type} [Group G]
    [Finite G] (ε : G ≃* ProjOrthDerived Q) (hnot : ¬ IsLThreeFour G) {a : G} (ha : a ^ 3 = 1)
    (hPIL : PerfectInLayer (MulAut.conj a)) : NoL34Layer (MulAut.conj a) := by
  have : Finite (ProjOrthDerived Q) := Finite.of_equiv G ε.toEquiv
  refine noL34Layer_congr ε ?_
  have hc : MulAut.congr ε (MulAut.conj a) = MulAut.conj (ε a) := by
    ext y
    simp [MulAut.conj_apply]
  rw [hc]
  have hb : (ε a) ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  have hPIL' : PerfectInLayer (MulAut.conj (ε a)) := by
    refine perfectInLayer_of_congr ε.symm (MulAut.conj (ε a)) ?_
    have : MulAut.congr ε.symm (MulAut.conj (ε a)) = MulAut.conj a := by
      ext y
      simp [MulAut.conj_apply]
    rw [this]
    exact hPIL
  exact noL34Layer_conj_projOrth hO hQ hT hℓ hℓ5 hf hK
    (fun h => hnot (IsLThreeFour.of_mulEquiv ε.symm h)) hb hPIL'

end TLevel

end SsOrth

theorem noL34Layer_conj_omega (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hℓ5 : 5 ≤ ℓ) (a : G) (ha : a ^ 3 = 1) :
    NoL34Layer (MulAut.conj a) := by
  have hadm := hG.1
  have hm : LieModel G t n ℓ f :=
    (lieModel_classical_iff (SsOrth.mem_classicalTags_of_omega ht)).mpr hG
  have hnot : ¬ IsLThreeFour G := not_isLThreeFour_of_lieModel_odd hO (by omega) hm
  have hPIL := perfectInLayer_conj_omega ht hG Nat.prime_three (by norm_num) (by omega) a ha
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hK, ⟨ε⟩⟩ := SsOrth.exists_projOrth_model ht hG
  exact SsOrth.noL34Layer_of_projOrth_equiv hO hQ hT hadm.1 hℓ5 hadm.2.1 hK ε hnot ha hPIL

theorem noL34Layer_of_inner_omega (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hℓ5 : 5 ≤ ℓ) {ψ : MulAut G}
    (hψ : ψ ^ 3 = 1) (hin : ∃ a : G, MulAut.conj a = ψ) : NoL34Layer ψ := by
  obtain ⟨a, rfl⟩ := hin
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hK, ⟨ε⟩⟩ := SsOrth.exists_projOrth_model ht hG
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  haveI : IsSimpleGroup G := ε.isSimpleGroup
  have hnabG : ∃ c d : G, c * d ≠ d * c := by
    obtain ⟨c, d, hcd⟩ := hnonab
    exact ⟨ε.symm c, ε.symm d, fun h' => hcd (ε.symm.injective (by rw [map_mul, map_mul]; exact h'))⟩
  have hZ : Subgroup.center G = ⊥ := up34_center_eq_bot_of_simple hnabG
  have ha3 : a ^ 3 = 1 := by
    have h1 : MulAut.conj (a ^ 3) = 1 := by rw [map_pow]; exact hψ
    have hcen : a ^ 3 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := DFunLike.congr_fun h1 g
      rw [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.1 hg).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  exact noL34Layer_conj_omega hO ht hG hℓ5 a ha3

theorem noL34InnAt_orthOdd (hO : LieOrderFormulasInput) : NoL34InnAt FamOrthOdd := by
  intro P _ _ t n p f _ _ hF hp5 hm ψ hψ3 hψ
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaOdd n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨a, ha⟩ := hψ
  exact noL34Layer_of_inner_omega hO (Or.inl rfl) hC hp5 hψ3 ⟨a, ha⟩

theorem noL34InnAt_orthPlus (hO : LieOrderFormulasInput) : NoL34InnAt FamOrthPlus := by
  intro P _ _ t n p f _ _ hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, -⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨a, ha⟩ := hψ
  exact noL34Layer_of_inner_omega hO (Or.inr (Or.inl rfl)) hC hp5 hψ3 ⟨a, ha⟩

theorem noL34InnAt_orthMinus (hO : LieOrderFormulasInput) : NoL34InnAt FamOrthMinus := by
  intro P _ _ t n p f _ _ hF hp5 hm ψ hψ3 hψ
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaMinus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨a, ha⟩ := hψ
  exact noL34Layer_of_inner_omega hO (Or.inr (Or.inr rfl)) hC hp5 hψ3 ⟨a, ha⟩

theorem noL34InnAt_d4 (hO : LieOrderFormulasInput) : NoL34InnAt FamD4 := by
  intro P _ _ t n p f _ _ hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, -⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨a, ha⟩ := hψ
  exact noL34Layer_of_inner_omega hO (Or.inr (Or.inl rfl)) hC hp5 hψ3 ⟨a, ha⟩

end CFSG.HardMathSupport.Dickson.Sec6
