module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Tools
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

namespace Sp

variable {K : Type} [Field K] [Finite K]

theorem sp_facts {m : ℕ} (hm : 1 ≤ m) (hK : 5 ≤ Nat.card K) (hodd : Odd (Nat.card K)) :
    IsQuasisimple (StatedSp m K) ∧ center (StatedSp m K) = SymplecticHigher.spScalars m K ∧
      Nat.card (SymplecticHigher.spScalars m K) = 2 ∧ pPrimeCore 2 (StatedSp m K) = ⊥ := by
  have hK4 : 4 ≤ Nat.card K := by omega
  have hs : IsSimpleGroup (StatedProj (StatedSp m K)) :=
    ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m hm (Or.inl (Or.inr hK4))
  have hperf : Group.IsPerfect (StatedSp m K) :=
    LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp m K hK4
  have hcard : Nat.card (SymplecticHigher.spScalars m K) = 2 := by
    rw [card_spScalars_eq_gcd K hm]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have hZ : center (StatedSp m K) = SymplecticHigher.spScalars m K := by
    refine le_antisymm (fun z hz => ?_) SymplecticHigher.spScalars_le_center
    have hperf' : Group.IsPerfect (StatedProj (StatedSp m K)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (SymplecticHigher.spScalars m K))
        (QuotientGroup.mk'_surjective _)
    have hZP : center (StatedProj (StatedSp m K)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (StatedProj (StatedSp m K))) with
        h | h
      · exact h
      · exact absurd (Subgroup.center_eq_top_iff.mp h) (Group.IsPerfect.not_isMulCommutative _)
    have hzc : QuotientGroup.mk' (SymplecticHigher.spScalars m K) z ∈
        center (StatedProj (StatedSp m K)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz g₀]
    rw [hZP, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzc
    exact hzc
  have hq : IsQuasisimple (StatedSp m K) := by
    have : IsSimpleGroup (StatedSp m K ⧸ center (StatedSp m K)) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).isSimpleGroup
    have : Group.IsPerfect (StatedSp m K ⧸ center (StatedSp m K)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center (StatedSp m K)))
        (QuotientGroup.mk'_surjective _)
    refine ⟨hperf, inferInstance, ?_⟩
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨h⟩⟩
  refine ⟨hq, hZ, hcard, pPrimeCore_eq_bot_of_isQuasisimple hq ?_ ?_⟩
  · rw [hZ]
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  · exact hcard ▸ Subgroup.card_subgroup_dvd_card (SymplecticHigher.spScalars m K)

variable {n : ℕ}

omit [Finite K] in
theorem conj_mem_complGroup {i c x : StatedSp n K} (hc : c * i = i * c)
    (hx : x ∈ complGroup i) : c * x * c⁻¹ ∈ complGroup i := by
  have hc' : c⁻¹ * i = i * c⁻¹ := (Commute.inv_left (show Commute c i from hc)).eq
  intro v hv
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mem_complGroup.1 hx _ (mulVec_mem_minusSpace hc' hv), Matrix.mulVec_mulVec, ← map_mul,
    mul_inv_cancel, map_one, Matrix.one_mulVec]

omit [Finite K] in
theorem normal_complGroup (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)} {i : StatedSp n K}
    (h : IsLongRootSp2 L i) :
    complGroup i ≤ centralizer {i} ∧ ((complGroup i).subgroupOf (centralizer {i})).Normal := by
  have hle : complGroup i ≤ centralizer {i} := by
    rw [h.centralizer_eq h2]
    exact le_sup_right
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc => ?_⟩
  have hc' : c * i = i * c := mem_centralizer_singleton_iff.mp hc
  have hc'' : c⁻¹ * i = i * c⁻¹ := (Commute.inv_left (show Commute c i from hc')).eq
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_complGroup hc', fun hx => ?_⟩
  have h1 := conj_mem_complGroup hc'' hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h1

omit [Finite K] in
theorem mat_eq_scalar {s : StatedSp n K} {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c = (s : GL (Fin n ⊕ Fin n) K)) :
    mat n K s = Matrix.scalar (Fin n ⊕ Fin n) (c : K) := by
  rw [mat_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar]

theorem concl_statedSp {m p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {s : StatedSp (m + 1) K}
    (hs : s ∈ SymplecticHigher.spScalars (m + 1) K) (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    Concl p f (StatedSp (m + 1) K) s := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h => by rw [h, pow_zero] at h5; omega
  obtain ⟨hqU, hZU, -, -⟩ := sp_facts (K := K) (m := m + 1) (by omega) h5K hodd
  set u := longInv K (m + 1) 0 with hu
  have hL : IsLongRootSp2 (longRootSp2 K (m + 1) 0) u := isLongRootSp2_standard 0
  have hcl := hL.isClassicalSL2 h2
  obtain ⟨c, hc⟩ := hs
  have hsmat := mat_eq_scalar hc
  have hc2 : (c : K) * c = 1 := by
    have h1 := congrArg (mat (m + 1) K) hs2
    rw [map_mul, map_one, hsmat] at h1
    have h3 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.scalar_apply] using h3
  have hc1 : (c : K) ≠ 1 := fun h => hs1 (mat_injective (by rw [hsmat, h, map_one, map_one]))
  have hcm : (c : K) = -1 := (mul_self_eq_one_iff.mp hc2).resolve_left hc1
  have hsm : mat (m + 1) K s = -1 := by rw [hsmat, hcm, map_neg, map_one]
  have huZ : u ∉ center (StatedSp (m + 1) K) := by
    rw [hZU]
    rintro ⟨d, hd⟩
    have hdm := mat_eq_scalar hd
    set k₁ : Fin (m + 1) := ⟨1, by omega⟩
    have hk₁ : k₁ ≠ 0 := fun h => absurd (congrArg Fin.val h) (by simp [k₁])
    have e0 : mat (m + 1) K u (Sum.inl 0) (Sum.inl 0) = -1 := by
      rw [hu, mat_longInv, Matrix.diagonal_apply_eq, ite_eq_left (inl_mem_coords 0)]
    have e1 : mat (m + 1) K u (Sum.inl k₁) (Sum.inl k₁) = 1 := by
      rw [hu, mat_longInv, Matrix.diagonal_apply_eq, ite_eq_right]
      intro h
      rcases mem_coords.1 h with h' | h'
      · exact hk₁ (Sum.inl_injective h')
      · exact Sum.inl_ne_inr h'
    have e2 : mat (m + 1) K u (Sum.inl 0) (Sum.inl 0) =
        mat (m + 1) K u (Sum.inl k₁) (Sum.inl k₁) := by
      rw [hdm]
      simp [Matrix.scalar_apply]
    rw [e0, e1] at e2
    exact h2 (by linear_combination -e2)
  obtain ⟨eL⟩ := hcl.nonempty_mulEquiv
  have hsL : IsSLTwoOver (p ^ f) (longRootSp2 K (m + 1) 0) := by
    have := Fintype.ofFinite K
    exact ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK], ⟨eL⟩⟩
  obtain ⟨hqL, hOL⟩ := isQuasisimple_of_isSLTwoOver hp hp2 h5 hsL
  obtain ⟨eC⟩ := nonempty_mulEquiv_complGroup_longInv h2 (0 : Fin (m + 1))
  obtain ⟨hqm, hZm, -, hOm⟩ := sp_facts (K := K) hm h5K hodd
  have hqC : IsQuasisimple (complGroup u) := LocalCores.isQuasisimple_of_mulEquiv eC hqm
  have hOC : pPrimeCore 2 (complGroup u) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eC, hOm, Subgroup.map_bot]
  obtain ⟨hCle, hCn⟩ := normal_complGroup h2 hL
  have hsu : s * u ∈ complGroup u := by
    intro v hv
    rw [map_mul, ← Matrix.mulVec_mulVec, mem_minusSpace.1 hv, hsm, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_neg]
  have hlieC : ∃ (τ' : StatedLieTag) (n' : ℕ),
      Blueprint.LieModel (↥(complGroup u) ⧸ Open.fusionZStar ↥(complGroup u)) τ' n' p f := by
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · obtain rfl : m = 1 := by omega
      have := Fintype.ofFinite K
      refine ⟨.PSL, 2, lieModel_psl_of_isSLTwoOver hp hp2 h5 ⟨K, inferInstance, inferInstance,
        by rw [← Nat.card_eq_fintype_card, hK],
        ⟨eC.symm.trans (longBlockEquivOne (K := K)).symm⟩⟩⟩
    · have hZC : (SymplecticHigher.spScalars m K).map eC.toMonoidHom =
          Open.fusionZStar ↥(complGroup u) := by
        rw [Frame.fusionZStar_eq_center hOC, ← hZm]
        exact Subgroup.map_center_eq eC
      refine ⟨.PSp, m, Or.inl ⟨by decide, ⟨hp, hf, hm2, ?_⟩, K, inferInstance, inferInstance, hK,
        ⟨(QuotientGroup.congr _ _ eC hZC).symm⟩⟩⟩
      intro h
      simp only [Prod.mk.injEq] at h
      omega
  refine ⟨u, hcl.orderOf_eq_two, not_mem_fusionZStar hqU (orderOf_eq_prime (by rw [sq, hs2]) hs1)
    huZ, longRootSp2 K (m + 1) 0, complGroup u,
    isTwoComponentIn_of_normal hcl.le_centralizer (hL.normal_subgroupOf_centralizer h2) hqL hOL,
    isTwoComponentIn_of_normal hCle hCn hqC hOC, fun h => ?_, hcl.mem,
    isSLTwoOver_quot hp hp2 h5 hsL, hlieC, .inr hsu⟩
  have h1 : u = 1 := Subgroup.disjoint_def.1 (hL.disjoint_complGroup h2) hcl.mem (h ▸ hcl.mem)
  have h3 := hcl.orderOf_eq_two
  rw [h1, orderOf_one] at h3
  exact absurd h3 (by norm_num)

end Sp

theorem rowSp : RowSp := by
  intro Y _ _ hq hZ p hp hp2 τ n f hτ hlie h5 hpsl hc t ht htZ
  subst hτ
  rcases hlie with ⟨-, ⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hZne : center Y ≠ ⊥ := fun h => ht1 (by rw [h, mem_bot] at htZ; exact htZ)
  have hβ2 : Nat.card (QuotientGroup.mk' (SymplecticHigher.spScalars (m + 1) K)).ker = 2 := by
    rw [QuotientGroup.ker_mk']
    exact (Sp.sp_facts (K := K) (m := m + 1) (by omega) h5K hodd).2.2.1
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_card_ker_two (QuotientGroup.mk'_surjective _) hβ2
    (fun E _ _ π hπ hcen _ => LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central
      (by omega) h5K hπ hcen) hq hZ hZne e
  rw [QuotientGroup.ker_mk'] at hα
  have htα : t ∈ (SymplecticHigher.spScalars (m + 1) K).map α.toMonoidHom := hα ▸ htZ
  obtain ⟨s, hs, rfl⟩ := htα
  have hs1 : s ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have hs2 : s * s = 1 := by
    apply α.injective
    rw [map_mul, map_one, ← sq]
    rw [← ht]
    exact pow_orderOf_eq_one _
  have hkα : ¬ 2 ∣ Nat.card α.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr α.injective, Subgroup.card_bot]
    norm_num
  exact Concl.map (φ := α.toMonoidHom) α.surjective hkα
    (Sp.concl_statedSp hp hp2 (by omega) hK h5 hs hs1 hs2)

end CFSG.ComponentClassification.HarrisLit.T1.P54
