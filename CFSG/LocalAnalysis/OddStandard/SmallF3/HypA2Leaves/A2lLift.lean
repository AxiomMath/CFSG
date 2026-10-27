module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lDatum
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLiftSL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypUDiag
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Lift

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.OddStandard.SmallF3.HypA2 (NoncentralDatum diagonalTransfer_typU)

theorem a2l_conj_involutive {G : Type*} [Group G] {t : G} (h : t * t = 1) (x : G) :
    MulAut.conj t (MulAut.conj t x) = x := by
  have h1 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, h, inv_one]
  rw [MulAut.conj_apply, MulAut.conj_apply]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [h, h1, one_mul, mul_one]

theorem a2l_isSLTwoOver_quotient {A : Type} [Group A] {q₀ : ℕ} (hodd : Odd q₀) (h5 : 5 ≤ q₀)
    (h : HarrisLit.IsSLTwoOver q₀ A) :
    HarrisLit.IsSLTwoOver q₀ (A ⧸ pPrimeCore 2 A) := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff q₀).1 (HypA2.isPrimePow_of_isSLTwoOver h)
  subst hpk
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (Even.pow_of_ne_zero even_two hk.ne')
  obtain ⟨F, i1, i2, hF, ⟨e⟩⟩ := h
  haveI := Fintype.finite i2
  haveI : Finite A := Finite.of_equiv _ e.toEquiv.symm
  have hO : pPrimeCore 2 A = ⊥ :=
    (HarrisLit.Lemma47.sl2_facts hp hp2 hk h5 ⟨F, i1, i2, hF, ⟨e⟩⟩).2.2.2
  exact ⟨F, i1, i2, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩⟩

theorem a2l_noncentralDatum_of_quotient (hGA : TBLit.GriessMultipliersOdd)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) {K : Type} [Group K] [Finite K]
    (h2 : IsPGroup 2 ↥(center K)) (hX : a2lDatum (K ⧸ center K)) : NoncentralDatum K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q₀, T', N', z', hodd, h5, hz', hz'N, hNT, hTC, hTc, hN, hTU⟩ := hX
  let π : K →* K ⧸ center K := QuotientGroup.mk' (center K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ center K := by rw [QuotientGroup.ker_mk']
  have h2k : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact h2
  obtain ⟨N₁, hN₁, hN₁map, hN₁comm, hinj⟩ := a2l_lift_sl2 hGA π hπ hker h2k hodd h5 N' hN
  obtain ⟨z, hzN₁, hzπ⟩ : ∃ z ∈ N₁, π z = z' := by
    have : z' ∈ N₁.map π := by rw [hN₁map]; exact hz'N
    obtain ⟨z, hz, hz1⟩ := this
    exact ⟨z, hz, hz1⟩
  have hz'sq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz', pow_two] at this
  have hzsq : z * z = 1 := by
    have h1 : z * z ∈ N₁ := N₁.mul_mem hzN₁ hzN₁
    refine hinj _ h1 ?_
    rw [map_mul, hzπ, hz'sq]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one] at hzπ
    rw [← hzπ, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
  have hznc : z ∉ center K := by
    intro hzc
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).2 hzc
    rw [hzπ] at h1
    rw [h1, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  have hcomm : ∀ x, π (MulAut.conj z x) = MulAut.conj z' (π x) := fun x => by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hzπ]
  obtain ⟨-, -, -, hlift, -⟩ :=
    LocalAnalysis.ComponentInitial.full_central_kernel_involution_fixed_component_correspondence
      hπ hker (a2l_conj_involutive hzsq) (a2l_conj_involutive hz'sq) hcomm
  have hTc' : CFSG.Assembly.IsComponentOf T' (fixedSubgroup (MulAut.conj z')) := by
    rw [CFSG.Sporadic.HeldB.fixedSubgroup_conj]
    exact hTc
  obtain ⟨-, hQc, hQmap, hQfix, -, -, ⟨eQ⟩⟩ := hlift T' hTc'
  set T : Subgroup K := ⁅T'.comap π, T'.comap π⁆ with hT
  have hTle : T ≤ centralizer ({z} : Set K) := fun x hx => by
    rw [← CFSG.Sporadic.HeldB.fixedSubgroup_conj]
    exact hQfix x hx
  have hTcomp : CFSG.Assembly.IsComponentOf T (centralizer ({z} : Set K)) := by
    rw [← CFSG.Sporadic.HeldB.fixedSubgroup_conj]
    exact hQc
  have hN₁T : N₁ ≤ T := by
    have h1 : N₁ ≤ T'.comap π := fun x hx => by
      have : π x ∈ N₁.map π := Subgroup.mem_map_of_mem π hx
      rw [hN₁map] at this
      exact hNT this
    calc N₁ = ⁅N₁, N₁⁆ := hN₁comm.symm
      _ ≤ ⁅T'.comap π, T'.comap π⁆ := Subgroup.commutator_mono h1 h1
  have hzT : z ∈ T := hN₁T hzN₁
  have hPC := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
    ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hTle).mp hTcomp)
  refine ⟨q₀, T, N₁, z, hodd, h5, hz2, hznc, hzN₁, hN₁T, hTle, hPC, hN₁, ?_⟩
  have hqT' : CFSG.IsQuasisimple ↥T' :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1 hTc.2.2
  have hqT : CFSG.IsQuasisimple ↥T := (AssemblyBPredicates.isQuasisimple_iff_native _).1 hQc.2.2
  have h2T' : 2 ∣ Nat.card ↥T' := by
    have := orderOf_dvd_natCard (⟨z', hNT hz'N⟩ : ↥T')
    rwa [Subgroup.orderOf_mk, hz'] at this
  have h2T : 2 ∣ Nat.card ↥T := by
    have := orderOf_dvd_natCard (⟨z, hzT⟩ : ↥T)
    rwa [Subgroup.orderOf_mk, hz2] at this
  obtain ⟨hT2', hOT'⟩ := HarrisLit.P1.isTwoQuasisimple_of_isQuasisimple hqT' h2T'
  obtain ⟨hT2, hOT⟩ := HarrisLit.P1.isTwoQuasisimple_of_isQuasisimple hqT h2T
  have hZ' := CatLeaf.fusionZStar_eq_center_of_quasisimple hqT' hOT'
  have hZ := CatLeaf.fusionZStar_eq_center_of_quasisimple hqT hOT
  have hcc : (⟨z, hzT⟩ : ↥T) ∈ center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hTle y.2))
  have hNcomm : ⁅N₁.subgroupOf T, N₁.subgroupOf T⁆ = N₁.subgroupOf T := by
    apply Subgroup.map_injective T.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hN₁T, hN₁comm]
  have hNSL : HarrisLit.IsSLTwoOver q₀ ↥(N₁.subgroupOf T) :=
    HypA2.isSLTwoOver_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hN₁T).symm hN₁
  exact diagonalTransfer_typU hGA hSchur q₀ ↥T' ↥T hT2' hT2 hTU
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ').trans
      (eQ.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))⟩
    (N₁.subgroupOf T) hNcomm (a2l_isSLTwoOver_quotient hodd h5 hNSL) ⟨z, hzT⟩
    (by rw [Subgroup.orderOf_mk]; exact hz2) (Subgroup.mem_subgroupOf.2 hzN₁)
    (fun y _ => Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_center_iff.1 hcc y)))
    (by rw [hZ]; exact hcc)

end CFSG.OddStandard.SmallF3.HypA2Leaves
