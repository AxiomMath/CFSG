module

public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTwoOne

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem stronglyEmbedded_index_odd {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : fusionStronglyEmbedded M) : Odd M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 (even_iff_two_dvd.mp hM.2.1)
  have hwtwo : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_orderOf_two hw
  obtain ⟨D, hD⟩ := hwtwo.exists_le_sylow
  let T : Subgroup X := (D : Subgroup M).map M.subtype
  have hwT : (w : X) ∈ T := ⟨w, hD (Subgroup.mem_zpowers w), rfl⟩
  have hTM : T ≤ M := Subgroup.map_subtype_le _
  have hN : Subgroup.normalizer (T : Set X) ≤ M := by
    intro n hn
    by_contra hnM
    have hodd := hM.2.2 n hnM
    have hwI : (w : X) ∈ M ⊓ M.map (MulAut.conj n⁻¹).toMonoidHom := by
      refine ⟨w.property, ?_⟩
      refine ⟨n * w * n⁻¹, hTM ((Subgroup.mem_normalizer_iff.mp hn w).mp hwT), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    have hworder : orderOf (⟨w, hwI⟩ : ↥(M ⊓ M.map (MulAut.conj n⁻¹).toMonoidHom)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact (Subgroup.orderOf_coe w).trans hw
    exact (hodd.not_two_dvd_nat) (hworder ▸ orderOf_dvd_natCard _)
  obtain ⟨P0, hP0⟩ := CFSG.BenderSuzuki.exists_sylow_map_eq_of_normalizer_le D hN
  have hP0M : (P0 : Subgroup X) ≤ M := by rw [hP0]; exact hTM
  have hndvd := Sylow.not_dvd_index P0
  have hdvd : M.index ∣ (P0 : Subgroup X).index := Subgroup.index_dvd_of_le hP0M
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hndvd (h.trans hdvd))

theorem exists_fixed_of_involutive_odd_card {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ a, f (f a) = a) (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  classical
  let := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Function.End α := f
  have hF : F ^ 2 ^ 1 = 1 := by
    funext a
    exact hf a
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hF
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hodd
  have hpos : 0 < Fintype.card (Function.fixedPoints F) := by
    by_contra h
    have h0 : Fintype.card (Function.fixedPoints F) = 0 := by omega
    rw [h0] at hmod
    simp only [Nat.ModEq, Nat.zero_mod] at hmod
    omega
  obtain ⟨⟨a, ha⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨a, ha⟩

theorem productUniqueContainment_of_pointHullStrongSplit [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h3 : PointHullStrongSplit H z) :
    ProductUniqueContainment H z := by
  intro t ht hzt hne g
  have hzH := mem_of_unique huniq
  have htH : t ∈ H := centralizer_le_of_unique huniq
    (Subgroup.mem_centralizer_singleton_iff.mpr hzt.eq.symm)
  have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have htt := class_mul_self hz ht
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
  refine ⟨fun hmem => ?_, fun hg => H.mul_mem (H.mul_mem (H.inv_mem hg)
    (H.mul_mem hzH htH)) hg⟩
  let L := involutionPointHull z
  have hzL : z ∈ L := Subgroup.subset_closure (distinguished_mem_pointClass z)
  have htL : t ∈ L := Subgroup.subset_closure ht
  rcases h3 with hrank | ⟨u, -, -, -, -, hse, hcls⟩
  · exfalso
    have h2 := CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions L
      ⟨z, hzL⟩ ⟨t, htL⟩ ((Subgroup.orderOf_mk z hzL).trans hz)
      ((Subgroup.orderOf_mk t htL).trans (class_orderOf hz ht))
      (fun h => hne (congrArg Subtype.val h).symm) (Subtype.ext hzt.eq)
    exact absurd hrank (not_le.mpr h2)
  · let L' : Subgroup G := ⁅L, L⁆
    have hLnormal : L.Normal := minimalLocalFailure_hull_normal z
    have hL'normal : L'.Normal := inferInstance
    have hmulL' : ∀ s ∈ involutionPointClass z, z * s ∈ L' := by
      intro s hs
      have h1 := hcls z (distinguished_mem_pointClass z)
      have h2 := hcls s hs
      have hmem := L'.mul_mem (L'.inv_mem h1) h2
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, hzinv] using hmem
    let base : G ⧸ H := QuotientGroup.mk 1
    let Δ : Set (G ⧸ H) := MulAction.orbit L' base
    have hstab : MulAction.stabilizer L' base = H.subgroupOf L' := by
      ext ℓ
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      exact class_mem_iff_fixes_base.symm
    have hΔodd : Odd (Nat.card Δ) := by
      have h := MulAction.index_stabilizer L' base
      rw [hstab, ← Nat.card_coe_set_eq] at h
      exact h ▸ stronglyEmbedded_index_odd hse
    let s : G := g * z * g⁻¹
    have hs : s ∈ involutionPointClass z := by
      simpa only [inv_inv] using class_conj_mem (distinguished_mem_pointClass z) g⁻¹
    have hss := class_mul_self hz hs
    have hsΔ : ∀ ω ∈ Δ, s • ω ∈ Δ := by
      rintro ω ⟨ℓ, rfl⟩
      have hzs := hmulL' s hs
      have hmem : z * ((z * s) * (ℓ : G)) * z⁻¹ ∈ L' :=
        hL'normal.conj_mem _ (L'.mul_mem hzs ℓ.property) z
      refine ⟨⟨_, hmem⟩, ?_⟩
      have hzbase : z⁻¹ • base = base := by
        rw [← class_mem_iff_fixes_base]
        exact H.inv_mem hzH
      change (z * ((z * s) * (ℓ : G)) * z⁻¹) • base = s • ((ℓ : G) • base)
      rw [mul_smul, hzbase, ← mul_smul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hzz, one_mul]
    let f : Δ → Δ := fun ω => ⟨s • ω.1, hsΔ ω.1 ω.2⟩
    have hf : ∀ ω, f (f ω) = ω := by
      intro ω
      apply Subtype.ext
      change s • s • ω.1 = ω.1
      rw [← mul_smul, hss, one_smul]
    obtain ⟨ω, hω⟩ := exists_fixed_of_involutive_odd_card f hf hΔodd
    have hsω : s • ω.1 = ω.1 := congrArg Subtype.val hω
    have hωg : ω.1 = QuotientGroup.mk g := by
      have h := (conj_smul_eq_iff_eq huniq g⁻¹ ω.1).mp (by simpa only [inv_inv] using hsω)
      rw [h, inv_inv, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    obtain ⟨ℓ, hℓ⟩ := ω.2
    change (ℓ : G) • base = ω.1 at hℓ
    rw [hωg] at hℓ
    have hfix : (z * t) • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g :=
      (smul_mk_eq_mk_iff _ _).mpr hmem
    rw [← hℓ, ← mul_smul, ← inv_smul_eq_iff, ← mul_smul] at hfix
    have hconjH : (ℓ : G)⁻¹ * ((z * t) * (ℓ : G)) ∈ H := class_mem_iff_fixes_base.mpr hfix
    let M : Subgroup L' := H.subgroupOf L'
    have hℓM : ℓ ∈ M := by
      by_contra hℓM
      have hℓinv : ℓ⁻¹ ∉ M := fun h => hℓM (by simpa only [inv_inv] using M.inv_mem h)
      have hodd := hse.2.2 ℓ⁻¹ hℓinv
      let y : L' := ⟨z * t, hmulL' t ht⟩
      have hyI : y ∈ M ⊓ M.map (MulAut.conj ℓ⁻¹⁻¹).toMonoidHom := by
        refine ⟨H.mul_mem hzH htH, ℓ⁻¹ * y * ℓ, ?_, ?_⟩
        · change (ℓ : G)⁻¹ * (z * t) * (ℓ : G) ∈ H
          simpa only [mul_assoc] using hconjH
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          group
      have hyorder : orderOf (⟨y, hyI⟩ : ↥(M ⊓ M.map (MulAut.conj ℓ⁻¹⁻¹).toMonoidHom)) = 2 := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
        exact orderOf_mul_of_commute hzz htt hzt hne
      exact hodd.not_two_dvd_nat (hyorder ▸ orderOf_dvd_natCard _)
    have hℓH : (ℓ : G) ∈ H := hℓM
    have hbase : (ℓ : G) • base = base := class_mem_iff_fixes_base.mp hℓH
    rw [hbase] at hℓ
    exact (mk_eq_base_iff g).mp hℓ.symm

end CFSG.ComponentClassification.AschbacherStrongEmbedding
