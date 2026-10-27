module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FUntw
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6JBoundTw
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldTorus
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.YS04E6F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (twExtHom twExtHom_apply twExt twIncl twDiag
  twExtHom_injective twExtHom_mem_diagJ twJ mem_twJ_iff)


variable {K : Type} [Field K] (σ : K ≃+* K)

theorem rootDiagUnit_compatDiag_mem (hσσ : ∀ c, σ (σ c) = c)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hC : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      adjointGroup TwistTag.E6.tag K) :
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      twistedE6RootGroup K σ := by
  have hσσ' : ∀ c, σ.toRingHom (σ.toRingHom c) = c := hσσ
  have h1 : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).2
      ⟨hC, twistHom_rootDiagUnit (compatDiag_perm u)⟩
  rw [SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 hσσ'] at h1
  exact h1

theorem mem_inner_of_diag_mem (hσσ : ∀ c, σ (σ c) = c) (g : twistedE6RootGroup K σ)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hC : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      adjointGroup TwistTag.E6.tag K) :
    MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ twistedE6Inn K σ := by
  have hd := rootDiagUnit_compatDiag_mem σ hσσ u hC
  have h1 : compatDiagAutHom TwistTag.E6 K σ.toRingHom u =
      MulAut.conj (⟨_, hd⟩ : twistedE6RootGroup K σ) :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.conj_eq_compatDiagAutHom σ rfl).symm
  rw [h1, ← map_mul]
  exact ⟨g * ⟨_, hd⟩, rfl⟩

theorem rootDiag_of_conj_eq (h : twistedE6RootGroup K σ)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hh : MulAut.conj h = compatDiagAutHom TwistTag.E6 K σ.toRingHom v) :
    (h : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v) := by
  obtain ⟨w, hw⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_eq_rootDiagUnit_compatDiag
    σ.surjective (hh ▸ CFSG.HardMathSupport.Timmesfeld.Tables.T1b.compatDiagAutHom_mem_stabilizer v)
  have h1 := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.conj_eq_compatDiagAutHom σ hw
  have hwv : w = v := compatDiagAutHom_injective (h1.symm.trans hh)
  rw [hw, hwv]

variable [Finite K]

theorem eq_of_comm_tw (η : K ≃+* K) {g : twistedE6RootGroup K σ}
    {u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (hcomm : (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) * fieldActor σ η =
      fieldActor σ η * (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u)) :
    Units.map (entrywiseHom η.toRingHom) (g : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit TwistTag.E6.tag
        (compatDiag TwistTag.E6 σ.toRingHom u *
          (twU η (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) := by
  set F := fieldActor σ η with hF
  set u' := orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ η) u with hu'
  have hFu : F * compatDiagAutHom TwistTag.E6 K σ.toRingHom u =
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u' * F := fieldActor_mul_compatDiagAutHom σ η u
  have h2 : (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) * F =
      (MulAut.conj (F g) * compatDiagAutHom TwistTag.E6 K σ.toRingHom u') * F := by
    calc (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) * F
        = F * (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) := hcomm
      _ = (F * MulAut.conj g) * compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
            rw [mul_assoc]
      _ = (MulAut.conj (F g) * F) * compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
            rw [mulAut_mul_conj]
      _ = MulAut.conj (F g) * (F * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) := by
            rw [mul_assoc]
      _ = MulAut.conj (F g) * (compatDiagAutHom TwistTag.E6 K σ.toRingHom u' * F) := by
            rw [hFu]
      _ = (MulAut.conj (F g) * compatDiagAutHom TwistTag.E6 K σ.toRingHom u') * F := by
            rw [mul_assoc]
  have h1 := mul_right_cancel h2
  have h3 : MulAut.conj (g⁻¹ * F g) =
      compatDiagAutHom TwistTag.E6 K σ.toRingHom (u * u'⁻¹) := by
    have h4 : MulAut.conj (F g) = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom u')⁻¹ := eq_mul_inv_of_mul_eq h1.symm
    rw [map_mul, map_inv, h4, map_mul, map_inv]
    group
  have h6 := rootDiag_of_conj_eq σ _ _ h3
  have h7 : compatDiag TwistTag.E6 σ.toRingHom (u * u'⁻¹) =
      compatDiag TwistTag.E6 σ.toRingHom u * (twU η (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ := by
    have h8 : compatDiag TwistTag.E6 σ.toRingHom (u * u'⁻¹) *
        compatDiag TwistTag.E6 σ.toRingHom u' = compatDiag TwistTag.E6 σ.toRingHom u := by
      rw [← compatDiag_mul, inv_mul_cancel_right]
    have h9 : compatDiag TwistTag.E6 σ.toRingHom u' =
        twU η (compatDiag TwistTag.E6 σ.toRingHom u) :=
      compatDiag_orbitUnitsMap (ringEquiv_comm_of_finite σ η) u
    rw [h9] at h8
    exact eq_mul_inv_of_mul_eq h8
  rw [h7, Subgroup.coe_mul, Subgroup.coe_inv] at h6
  exact eq_mul_of_inv_mul_eq h6

theorem meets_inner_E6_tw {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : 3 ∣ ℓ ^ f + 1)
    (D : Subgroup (MulAut (twistedE6RootGroup K σ))) (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 9) : ∃ x ∈ D ⊓ twistedE6Inn K σ, x ≠ 1 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hex, ⟨Θ, hΘ, -, hΘker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hKℓ : Nat.card K = ℓ ^ (f * 2) := by rw [hK, ← pow_mul]
  obtain ⟨hcardAut, hcyc⟩ := card_ringAut_and_isCyclic hℓ K hKℓ
  haveI : IsCyclic (RingAut K) := hcyc
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hℓ hf K hK
    have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
    rw [hσσ'] at hord
    rw [← pow_orderOf_eq_one σ, hord]
    rfl
  have hσσ : ∀ c, σ (σ c) = c :=
    SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  have h3K : 3 ∣ Nat.card K - 1 := by
    have hq : ℓ ^ f % 3 = 2 := by omega
    have h1 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    rw [hK]
    omega
  refine meets_inner_of_data (twistedE6Inn K σ) Θ ?_ ?_ ?_ D hD hc
  · intro F hF
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_le_three_of_elemAbelian_cyclic F hF
  · intro E hEker hE hEI
    have hEJ : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := hΘker ▸ hEker
    set E₁ : Subgroup (twJ σ) := E.subgroupOf (twJ σ) with hE₁
    set E' : Subgroup (MulAut (adjointGroup Tag.E6 K)) := E₁.map (twExtHom σ) with hE'
    have hcard : Nat.card E' = Nat.card E := by
      rw [hE', Subgroup.card_map_of_injective (twExtHom_injective σ), hE₁]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
    rw [← hcard]
    refine card_le_three_of_inndiag E' ?_ ?_
    · rintro _ ⟨α, hαE₁, rfl⟩
      obtain ⟨g, u, hαgu⟩ := (mem_twJ_iff σ).1 α.2
      exact ⟨twIncl σ g, twDiag σ u, twExtHom_apply σ α hαgu⟩
    · rw [eq_bot_iff]
      rintro _ ⟨⟨α, hαE₁, rfl⟩, h, hh⟩
      obtain ⟨g, u, hαgu⟩ := (mem_twJ_iff σ).1 α.2
      have hy := twExtHom_apply σ α hαgu
      rw [hy] at hh
      simp only [twExt] at hh
      have h1 : rootDiagAutHom Tag.E6 K (twDiag σ u) =
          MulAut.conj ((twIncl σ g)⁻¹ * h) := by
        rw [map_mul, map_inv, hh]
        group
      have h2 := conj_eq_rootDiagAut ((twIncl σ g)⁻¹ * h) (twDiag σ u) h1.symm
      have hdC : rootDiagUnit Tag.E6 (twDiag σ u) ∈ adjointGroup Tag.E6 K :=
        h2 ▸ ((twIncl σ g)⁻¹ * h).2
      have hαI : (α : MulAut (twistedE6RootGroup K σ)) ∈ twistedE6Inn K σ := by
        rw [hαgu]
        exact mem_inner_of_diag_mem σ hσσ g u hdC
      have hαE : (α : MulAut (twistedE6RootGroup K σ)) ∈ E := hαE₁
      have : (α : MulAut (twistedE6RootGroup K σ)) ∈ E ⊓ twistedE6Inn K σ := ⟨hαE, hαI⟩
      rw [hEI, Subgroup.mem_bot] at this
      have hα1 : α = 1 := Subtype.ext this
      rw [hα1, map_one]
      exact Subgroup.one_mem _
  · intro α hα3 hΘα
    obtain ⟨d, hfd, hd1, r, s, T, ε, hT, hε, hαrs, ψ, hψ1, hψ2⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K
        (by rw [hK, ← pow_mul, mul_comm]) σ hσ Θ hΘ Nat.prime_three (by norm_num) α hα3 hΘα
    refine ⟨ψ, fun δ hδ hcomm => ?_⟩
    rw [hψ2] at hcomm
    set η := Θ α with hη
    have hη3 : η ^ 3 = 1 := by rw [hη, ← map_pow, hα3, map_one]
    have hηord : orderOf η = 3 := orderOf_eq_prime hη3 hΘα
    have hT' := exists_cube_of_fixed η hηord h3K
    have hδJ : δ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := hΘker ▸ hδ
    obtain ⟨g, u, hδ'⟩ := (mem_twJ_iff σ).1 hδJ
    rw [hδ'] at hcomm
    have hmat := eq_of_comm_tw σ η hcomm
    have hdC := rootDiagUnit_mem_adjointGroup_of_twist η (hcube_E6 η hT')
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedE6RootGroup_le σ g.2) _ hmat
    rw [hδ']
    exact mem_inner_of_diag_mem σ hσσ g u hdC

end CFSG.LocalAnalysis.GLTheoremA.YS04E6F
