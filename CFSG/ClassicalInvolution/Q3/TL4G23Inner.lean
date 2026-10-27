module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut
import CFSG.ClassicalInvolution.Q3.Q3ExcToral
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLang
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral
import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.ModelFacts


theorem oddCoreIn_centralizer_adjoint_three {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK3 : Nat.card K = 3) {z : ↥(adjointGroup τ K)} (hz2 : z * z = 1) :
    oddCoreIn (Subgroup.centralizer ({z} : Set ↥(adjointGroup τ K))) = ⊥ := by
  have hodd : Odd (Nat.card K) := by rw [hK3]; decide
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨g, b, hb, hgz⟩ := exists_conj_eq_rootDiagUnit_of_involution hτ hodd z hz2
  refine oddCoreIn_centralizer_eq_bot_of_mulEquiv
    (MulAut.conj g : ↥(adjointGroup τ K) ≃* ↥(adjointGroup τ K)) z ?_
  have hz' : ((MulAut.conj g) z : ↥(adjointGroup τ K)) = g * z * g⁻¹ := rfl
  rw [hz']
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b (g * z * g⁻¹) hgz
  have hXC := toralCentralizer_le_adjointGroup (K := K) (τ := τ) b
  set O := oddCoreIn (Subgroup.centralizer ({g * z * g⁻¹} : Set ↥(adjointGroup τ K)))
  have hN := exc3_oddNormal_eq_bot hK3 hb
    (N := O.map (adjointGroup τ K).subtype) (by
      rintro _ ⟨x, hx, rfl⟩
      have := hCz ▸ oddCoreIn_le _ hx
      exact Subgroup.mem_subgroupOf.1 this) (by
      rintro x hxX _ ⟨n, hn, rfl⟩
      have hxC : (⟨x, hXC hxX⟩ : ↥(adjointGroup τ K)) ∈
          Subgroup.centralizer ({g * z * g⁻¹} : Set ↥(adjointGroup τ K)) := by
        rw [hCz]
        exact Subgroup.mem_subgroupOf.2 hxX
      exact ⟨⟨x, hXC hxX⟩ * n * ⟨x, hXC hxX⟩⁻¹, conj_mem_oddCoreIn hxC hn, rfl⟩) (by
      rw [Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective]
      exact odd_card_oddCoreIn _)
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (adjointGroup τ K).subtype_injective).mp hN

theorem mem_innSubgroup_of_odd_orderOf_g2_three {K : Type} [Field K] [Finite K]
    (hK3 : Nat.card K = 3) (α : MulAut ↥(adjointGroup .G2 K)) (hα : Odd (orderOf α)) :
    α ∈ innSubgroup ↥(adjointGroup .G2 K) := by
  have hchar3 : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three le_rfl (by rw [hK3]; norm_num)
  have hchar : CharP K LieType.Ree.ReeTag.G2.prime := hchar3
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form (f := 1) le_rfl K
    (by rw [hK3]; norm_num)
  have h1 : orderOf (Θ α) ∣ orderOf α := orderOf_map_dvd Θ α
  have h2 : orderOf (Θ α) ∣ 2 := by
    have := orderOf_dvd_natCard (Θ α)
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at this
  have h3 : orderOf (Θ α) = 1 := by
    have h4 : orderOf (Θ α) ∣ Nat.gcd (orderOf α) 2 := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hα), Nat.dvd_one] at h4
  have h5 : α ∈ Θ.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h3)
  exact (SetLike.ext_iff.mp hker α).mp h5

theorem autOddFreeInner_of_lieModel_g2_three {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (h : CFSG.Blueprint.LieModel L .G2 0 3 1) : AutOddFreeInner L := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h.chevalleyExceptionalModel (by decide)
  have hK3 : Nat.card K = 3 := by simpa using hcard
  let e' : L ≃* ↥(adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans QuotientGroup.quotientBot)
  have hZ : Subgroup.center L = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective _ (f := e'.toMonoidHom) e'.injective).mp ?_
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.map_center_eq, center_adjointGroup_eq_bot]
  have hO : ∀ x : L, orderOf x = 2 → CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥ := by
    intro x hx
    have hx2 : e' x * e' x = 1 := by
      rw [← map_mul, mul_self_eq_one_of_orderOf_eq_two' hx, map_one]
    rw [involutionOddCore_eq_oddCoreIn]
    exact oddCoreIn_centralizer_eq_bot_of_mulEquiv e' x
      (oddCoreIn_centralizer_adjoint_three (Or.inl rfl) hK3 hx2)
  have hodd : ∀ α : MulAut L, Odd (orderOf α) → α ∈ innSubgroup L := by
    intro α hα
    set φ : MulAut L ≃* MulAut ↥(adjointGroup .G2 K) := MulAut.congr e' with hφ
    have h1 : Odd (orderOf (φ α)) := by rwa [MulEquiv.orderOf_eq]
    obtain ⟨c, hc⟩ := mem_innSubgroup_of_odd_orderOf_g2_three hK3 (φ α) h1
    refine ⟨e'.symm c, φ.injective ?_⟩
    rw [← hc]
    ext y
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  exact autOddFreeInner_of_oddCoreFree hZ hO hodd

end CFSG.ClassicalInvolution.Q3.TL4
