module

public import CFSG.CharacterTheory.Semidihedral.FourPointCentralizer
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.OddCoreFreeGL2Recognition
public import CFSG.CharacterTheory.Semidihedral.Local.InvolutionCentralizerAlternatives

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.ReducedQuotients CFSG.Semidihedral.FourPointQuotient
open CFSG.Semidihedral.FourPointCentralizer

theorem ambientZ_centralizer_eq_zpowers {G : Type*} [Group G] (t : G) :
    CentralQuotients.ambientZ (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({t} : Set G)) (Local.self_mem_center_centralizer t) =
      Subgroup.zpowers ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :=
  rfl

theorem four_point_reduced_centralizer_GL2_quotient {G : Type*} [Group G] [Finite G]
    (hG : ∀ L : Subgroup G, L.index ≠ 2) (n : ℕ) (hn : 4 ≤ n) (S₀ : Sylow 2 G)
    (f₀ : SemidihedralGroup n ≃* S₀) (t : G) (ht : orderOf t = 2)
    (φ : (Subgroup.centralizer ({t} : Set G) ⧸
      (CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ⊔
        CentralQuotients.ambientZ (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
          Subgroup.centralizer ({t} : Set G)) (Local.self_mem_center_centralizer t))) ≃*
      Equiv.Perm (Fin 4)) :
    n = 4 ∧ (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∧
    ∃ π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3),
      Function.Surjective π ∧ π.ker = CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ∧
      Odd (Nat.card π.ker) ∧ π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1 := by
  have hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
    intro u v hu hv
    exact (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG u hu).1.trans
      (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG v hv).1.symm
  obtain ⟨⟨S, f, hz⟩, hall⟩ := involution_centralizer_four_point_linear_two_model n hn S₀ f₀ hG t ht
  obtain ⟨-, -, hdata⟩ := hall S f hz
  subst hz
  obtain ⟨hn4, -, θ, hθ, -⟩ := hdata ⟨φ⟩
  let π : Subgroup.centralizer ({centeredInvolution n S f} : Set G) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 2 (involutionCentralizer n S f)))
  have hker : π.ker =
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({centeredInvolution n S f} : Set G)) := by
    ext x
    exact (MulEquiv.map_eq_one_iff θ).trans
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 (involutionCentralizer n S f)) x)
  refine ⟨hn4, hinv, π, θ.surjective.comp (QuotientGroup.mk'_surjective
    (CFSG.pPrimeCore 2 (Subgroup.centralizer ({centeredInvolution n S f} : Set G)))), hker, ?_,
    ?_⟩
  · rw [hker]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))
  · change θ (coreInvolution n S f) = -1
    apply Units.ext
    rw [hθ, Units.val_neg, Units.val_one]
    rfl

theorem four_point_reduced_centralizer_branch_classification
    {G : Type} [Group G] [Finite G]
    (hG : ∀ L : Subgroup G, L.index ≠ 2)
    (hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K = ⊥)
    (n : ℕ) (hn : 4 ≤ n) (S₀ : Sylow 2 G) (f₀ : SemidihedralGroup n ≃* S₀)
    (t : G) (ht : orderOf t = 2)
    (φ : (Subgroup.centralizer ({t} : Set G) ⧸
      (CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ⊔
        CentralQuotients.ambientZ (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
          Subgroup.centralizer ({t} : Set G)) (Local.self_mem_center_centralizer t))) ≃*
      Equiv.Perm (Fin 4)) :
    n = 4 ∧ CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) = ⊥ ∧
      Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)) ∧
      commutator G = ⊤ ∧
      Xor (Nat.card G = 5616 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1)
        (Nat.card G = 7920 ∧ Nonempty (G ≃* CFSG.Open.StatedM11) ∧
          Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11)) := by
  obtain ⟨hn4, hinv, π, hπ, hker, hN, hπt⟩ :=
    four_point_reduced_centralizer_GL2_quotient hG n hn S₀ f₀ t ht φ
  obtain ⟨hbot, hbij, hperf, hxor⟩ :=
    odd_core_free_GL2_centralizer_quotient_recognition hodd hinv t ht π hπ hN hπt
  exact ⟨hn4, hker.symm.trans hbot, ⟨MulEquiv.ofBijective π hbij⟩, hperf, hxor⟩

end CFSG.Semidihedral.GL2Recognition
