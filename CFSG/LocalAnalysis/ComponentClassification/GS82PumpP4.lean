module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP4Cover

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem mTypeOfSLTwoSection_holds :
    MTypeOfSLTwoSection := by
  intro J _ _ hJ p hp hp2 hS N q₀ hq₀ h5 hN c hc hcN hcZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcc : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  refine .inl ⟨hJ, hS, ?_, fun n r hn hr hm => ?_⟩
  ·
    have h1 : orderOf (⟨c, hcZ⟩ : ↥(Open.fusionZStar J)) ∣ Nat.card ↥(Open.fusionZStar J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hc] at h1
    exact even_iff_two_dvd.mpr h1
  set O := pPrimeCore 2 J with hO
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hZ : Open.fusionZStar J = (center (J ⧸ O)).comap (QuotientGroup.mk' O) := by
    ext x
    rw [GSThmB.OddQuot.mem_fusionZStar_iff, mem_comap, mem_center_iff]
    constructor
    · intro h q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective O q
      have h1 := (QuotientGroup.eq_one_iff _).mpr (h m)
      rw [← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    · intro h m
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact (h _).symm
  have hZcard : Nat.card ↥(Open.fusionZStar J) = Nat.card O * Nat.card ↥(center (J ⧸ O)) := by
    rw [hZ, P4.card_comap_of_surjective _ (QuotientGroup.mk'_surjective O), QuotientGroup.ker_mk']
  set Y := J ⧸ O with hYdef
  have hY : IsQuasisimple Y := hJ.2
  have h2 : IsPGroup 2 ↥(center Y) := by
    intro x
    obtain ⟨k, hk⟩ := UnbalancedGS.SwappedCentralProduct.pow_two_pow_eq_one_of_mem_center
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := J) 2) x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  let ψ : J →* Y ⧸ center Y := (QuotientGroup.mk' (center Y)).comp (QuotientGroup.mk' O)
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hψk : Open.fusionZStar J = ψ.ker := by
    rw [hZ]
    change _ = ((QuotientGroup.mk' (center Y)).comp (QuotientGroup.mk' O)).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : Y ⧸ center Y ≃* J ⧸ Open.fusionZStar J := (QuotientGroup.liftEquiv _ hψ hψk).symm
  have hm' : Blueprint.LieModel (Y ⧸ center Y) .PSL (2 * n) p r ∨
      Blueprint.LieModel (Y ⧸ center Y) .PSU (2 * n) p r :=
    hm.imp (GSThmB.OddQuot.lieModel_of_equiv e.symm) (GSThmB.OddQuot.lieModel_of_equiv e.symm)
  set A := N.map (QuotientGroup.mk' O) with hA
  have hAsl : HarrisLit.IsSLTwoOver q₀ (↥A ⧸ pPrimeCore 2 ↥A) := by
    have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' O).ker := by
      rw [QuotientGroup.ker_mk']
      exact fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
    obtain ⟨eA⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
      ((QuotientGroup.mk' O).subgroupMap N) ((QuotientGroup.mk' O).subgroupMap_surjective N)
      (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap _ hker N)
    obtain ⟨F, i₁, i₂, hF, ⟨eF⟩⟩ := hN
    exact ⟨F, i₁, i₂, hF, ⟨eA.symm.trans eF⟩⟩
  set cb := QuotientGroup.mk' O c with hcb
  have hcbA : cb ∈ A := mem_map_of_mem _ hcN
  have hcbZ : cb ∈ center Y := by
    have h1 := hcZ
    rw [hZ, mem_comap] at h1
    exact h1
  have hcbb : cb * cb = 1 := by rw [hcb, ← map_mul, hcc, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h
    have hcO : c ∈ O := (QuotientGroup.eq_one_iff c).mp h
    have h1 := P4.eq_one_of_pow_two_pow_eq_one hOodd hcO 1 (by rw [pow_one, sq, hcc])
    rw [h1, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have h2n : 2 * n ≠ 0 := by omega
  have : NeZero (2 * n) := ⟨h2n⟩
  suffices H : ∃ (K : Type) (_ : Field K) (_ : Finite K) (H : Subgroup (GL (Fin (2 * n)) K))
      (π : ↥H →* Y), Function.Surjective π ∧
      (∀ g, g ∈ (StatedScalars (Fin (2 * n)) K).subgroupOf H ↔ π g ∈ center Y) ∧
      ordProj[2] (Nat.card ↥((StatedScalars (Fin (2 * n)) K).subgroupOf H)) =
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y))) by
    obtain ⟨K, _, _, H, π, hπ, hπN, hord⟩ := H
    have hZY := P4.card_center_eq_of_scalar_cover h2 π hπ hπN hq₀ h5 hAsl hcbA hcbZ hcbb hcb1
    rw [hZcard, Nat.mul_comm (Nat.card ↥O), P4.ordProj_two_mul_odd Nat.card_pos.ne' hOodd,
      ← Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
      ← hord, ← hZY]
    obtain ⟨a, ha⟩ := h2.exists_card_eq
    rw [ha]
    exact P4.ordProj_two_pow a
  rcases hm' with hmL | hmU
  · obtain ⟨K, _, _, π, hπ, hπN, hord⟩ :=
      P4.exists_psl_cover hY h2 hp2 (hmL.statedClassicalModel_of_ne_zero h2n)
    exact ⟨K, inferInstance, inferInstance, _, π, hπ, hπN, hord⟩
  · obtain ⟨K, _, _, π, hπ, hπN, hord⟩ :=
      P4.exists_psu_cover hY h2 hp2 (even_two_mul n) (hmU.statedClassicalModel_of_ne_zero h2n)
    exact ⟨K, inferInstance, inferInstance, _, π, hπ, hπN, hord⟩

end CFSG.ComponentClassification.GS82PumpInputs
