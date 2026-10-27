module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Sp
public import CFSG.RankThree.PerfectCover.HopfCentralCovers
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Spin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank Blueprint.Multiplier
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

theorem inf_center_eq_bot_of_equiv_sl2 {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {G : Type*} [Group G] {J : Subgroup G} (e : ↥J ≃* SL(2, F))
    {u : G} (huJ : u ∈ J) (hu2 : orderOf u = 2) (huZ : u ∉ center G) : J ⊓ center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_inf] at hx
  obtain ⟨hxJ, hxZ⟩ := hx
  have hc : e ⟨x, hxJ⟩ ∈ center SL(2, F) := by
    rw [← Subgroup.map_center_eq e]
    refine mem_map_of_mem _ ?_
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hxZ g)
  have hue : e ⟨u, huJ⟩ = -1 := (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd _).mp
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2])
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hc with h1 | h1
  · have h3 : (⟨x, hxJ⟩ : J) = 1 := e.injective (by rw [h1, map_one])
    exact mem_bot.mpr (congrArg Subtype.val h3)
  · have h3 : (⟨x, hxJ⟩ : J) = ⟨u, huJ⟩ := e.injective (by rw [h1, hue])
    have h4 : x = u := congrArg Subtype.val h3
    exact absurd (h4 ▸ hxZ) huZ

namespace Sp

variable {K : Type} [Field K] [Finite K]

theorem sp_facts_three {m : ℕ} (hm : 2 ≤ m) (hK3 : Nat.card K = 3) :
    IsQuasisimple (StatedSp m K) ∧ center (StatedSp m K) = SymplecticHigher.spScalars m K ∧
      Nat.card (SymplecticHigher.spScalars m K) = 2 := by
  have hs : IsSimpleGroup (StatedProj (StatedSp m K)) :=
    ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m (by omega)
      (Or.inr (Or.inl ⟨hK3, hm⟩))
  have hperf : Group.IsPerfect (StatedSp m K) :=
    ClassicalGroups.Symplectic.isPerfect_statedSp m K (Or.inr (Or.inl ⟨hK3, hm⟩))
  have hcard : Nat.card (SymplecticHigher.spScalars m K) = 2 := by
    rw [card_spScalars_eq_gcd K (by omega), hK3]
    rfl
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
  exact ⟨hq, hZ, hcard⟩

theorem rawF3_sp (hK3 : Nat.card K = 3) {m : ℕ} (hm : 1 ≤ m) {s : StatedSp (m + 1) K}
    (hs : s ∈ SymplecticHigher.spScalars (m + 1) K) (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    RawF3 (StatedSp (m + 1) K) s := by
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨hqU, hZU, -⟩ := sp_facts_three (K := K) (m := m + 1) (by omega) hK3
  set u := longInv K (m + 1) 0 with hu
  have hL : IsLongRootSp2 (longRootSp2 K (m + 1) 0) u := isLongRootSp2_standard 0
  have hcl := hL.isClassicalSL2 h2
  obtain ⟨c, hc⟩ := hs
  have hsmat := Sp.mat_eq_scalar hc
  have hc2 : (c : K) * c = 1 := by
    have h1 := congrArg (mat (m + 1) K) hs2
    rw [map_mul, map_one, hsmat] at h1
    have h3 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.scalar_apply] using h3
  have hc1 : (c : K) ≠ 1 := fun h => hs1 (mat_injective (by rw [hsmat, h, map_one, map_one]))
  have hcm : (c : K) = -1 := (mul_self_eq_one_iff.mp hc2).resolve_left hc1
  have hsm : mat (m + 1) K s = -1 := by rw [hsmat, hcm, map_neg, map_one]
  have hsZ : s ∈ center (StatedSp (m + 1) K) := by
    rw [hZU]
    exact ⟨c, hc⟩
  have huZ : u ∉ center (StatedSp (m + 1) K) := by
    rw [hZU]
    rintro ⟨d, hd⟩
    have hdm := Sp.mat_eq_scalar hd
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
  obtain ⟨eK⟩ := nonempty_sl2_equiv_zmod_three hK3
  obtain ⟨eL⟩ := hcl.nonempty_mulEquiv
  have hJ₁Z := inf_center_eq_bot_of_equiv_sl2 hodd eL hcl.mem hcl.orderOf_eq_two huZ
  obtain ⟨eC⟩ := nonempty_mulEquiv_complGroup_longInv h2 (0 : Fin (m + 1))
  obtain ⟨hCle, hCn⟩ := Sp.normal_complGroup h2 hL
  have hsu : s * u ∈ complGroup u := by
    intro v hv
    rw [map_mul, ← Matrix.mulVec_mulVec, mem_minusSpace.1 hv, hsm, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_neg]
  refine ⟨u, hcl.orderOf_eq_two, huZ, longRootSp2 K (m + 1) 0, complGroup u, hcl.le_centralizer,
    (hL.normal_subgroupOf_centralizer h2).isSubnormal, hcl.mem, hJ₁Z, ⟨eL.trans eK⟩, ?_,
    .inr hsu⟩
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    obtain rfl : m = 1 := by omega
    let eJ : ↥(complGroup u) ≃* SL(2, K) := eC.symm.trans (longBlockEquivOne (K := K)).symm
    have hsu2 : orderOf (s * u) = 2 := by
      have hcomm : s * u = u * s := (mem_center_iff.mp hsZ u).symm
      have hs2' : orderOf s = 2 := orderOf_eq_prime (by rw [sq, hs2]) hs1
      exact T1.F3.orderOf_mul_of_commute hs2' hcl.orderOf_eq_two hcomm
        (fun h => huZ (h ▸ hsZ))
    have hsuZ : s * u ∉ center (StatedSp (1 + 1) K) := fun h => huZ (by
      have h1 : u = s⁻¹ * (s * u) := by group
      rw [h1]
      exact mul_mem (inv_mem hsZ) h)
    exact .inr ⟨hCle, hCn.isSubnormal, inf_center_eq_bot_of_equiv_sl2 hodd eJ hsu hsu2 hsuZ,
      ⟨eJ.trans eK⟩⟩
  ·
    obtain ⟨hqm, hZm, -⟩ := sp_facts_three (K := K) (m := m) hm2 hK3
    have hqC : IsQuasisimple (complGroup u) := LocalCores.isQuasisimple_of_mulEquiv eC hqm
    have h2C : 2 ∣ Nat.card (complGroup u) := by
      have hsu2 : orderOf (s * u) = 2 := by
        have hcomm : s * u = u * s := (mem_center_iff.mp hsZ u).symm
        have hs2' : orderOf s = 2 := orderOf_eq_prime (by rw [sq, hs2]) hs1
        exact T1.F3.orderOf_mul_of_commute hs2' hcl.orderOf_eq_two hcomm
          (fun h => huZ (h ▸ hsZ))
      have h1 := orderOf_dvd_natCard (⟨s * u, hsu⟩ : complGroup u)
      rwa [Subgroup.orderOf_mk, hsu2] at h1
    have hZC : (SymplecticHigher.spScalars m K).map eC.toMonoidHom = center ↥(complGroup u) := by
      rw [← hZm]
      exact Subgroup.map_center_eq eC
    have hlie : Blueprint.LieModel (↥(complGroup u) ⧸ center ↥(complGroup u)) .PSp m 3 1 := by
      refine Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, hm2, ?_⟩, K, inferInstance,
        inferInstance, by rw [hK3, pow_one], ⟨(QuotientGroup.congr _ _ eC hZC).symm⟩⟩
      intro h
      simp only [Prod.mk.injEq] at h
      omega
    exact .inl ⟨⟨hCle, hCn.isSubnormal, SL.isTwoQuasisimple_of_isQuasisimple hqC h2C⟩, hqC,
      ⟨.PSp, m, hlie⟩⟩

end Sp

theorem rowSpThree (hG : GriessNativeTable) : RowSpThree := by
  intro Y _ _ hq hZ τ n hτ hlie hc t ht htZ
  subst hτ
  have hlie0 := hlie
  rcases hlie with ⟨-, ⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hqS, hZS, hcS⟩ := Sp.sp_facts_three (K := K) (m := m + 1) (by omega) hK3
  obtain ⟨-, ⟨eM⟩⟩ := hG _ .PSp (m + 1) 3 1 hlie0
  have hMcard : Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y)) = 2 := by
    rw [Nat.card_congr eM.toEquiv, card_generic_prod_exceptional]
    have hex : exceptionalOrders .PSp (m + 1) 3 1 = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    rw [hex]
    simp [genericOrders]
  have : Finite (Open.griessHopfMultiplier (Y ⧸ center Y)) := Nat.finite_of_card_ne_zero (by
    rw [hMcard]
    norm_num)
  have : Group.IsPerfect Y := hq.1
  have hdvd := Subgroup.card_dvd_of_surjective
    (RankThree.PerfectCover.hopfMultiplierToKer_surjective (QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' (center Y)).le)
  rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    QuotientGroup.ker_mk', hMcard] at hdvd
  have h2Z : 2 ∣ Nat.card (center Y) := by
    have h := orderOf_dvd_natCard (⟨t, htZ⟩ : center Y)
    rwa [Subgroup.orderOf_mk, ht] at h
  have hZY : Nat.card (center Y) = 2 := Nat.dvd_antisymm hdvd h2Z
  have hSyl : ∀ S : Sylow 2 (Open.griessHopfMultiplier (Y ⧸ center Y)), Nat.card S = 2 := by
    intro S
    rw [Sylow.card_eq_multiplicity, hMcard, Nat.prime_two.factorization_self, pow_one]
  have hSZ : Nat.card (center (StatedSp (m + 1) K)) = 2 := by rw [hZS, hcS]
  obtain ⟨α⟩ := (RankThree.PerfectCover.hopf_central_cover_consequences (Y ⧸ center Y)).2 hSyl
    (StatedSp (m + 1) K) Y hqS hq hSZ hZY
    ⟨(QuotientGroup.quotientMulEquivOfEq hZS).trans e.symm⟩ ⟨MulEquiv.refl _⟩
  have htZ' : α.symm t ∈ center (StatedSp (m + 1) K) := by
    rw [← Subgroup.map_center_eq α.symm]
    exact mem_map_of_mem _ htZ
  have hs1 : α.symm t ≠ 1 := fun h => by
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hs2 : α.symm t * α.symm t = 1 := by
    rw [← map_mul, ← sq, ← ht, pow_orderOf_eq_one, map_one]
  have hα : (α : StatedSp (m + 1) K →* Y).ker ≤ center (StatedSp (m + 1) K) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr α.injective]
    exact bot_le
  have h := (Sp.rawF3_sp hK3 (by omega) (hZS ▸ htZ') hs1 hs2).concl3 hqS α.surjective hα
    (by simpa using ht) htZ'
  simpa using h

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
