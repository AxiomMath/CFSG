module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingNormSplit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G} {z : G}

theorem class_mem_hull_class (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    (hH : H ≠ ⊤) {t : G} (ht : t ∈ involutionPointClass z) :
    (⟨t, Subgroup.subset_closure ht⟩ : involutionPointHull z) ∈
      involutionPointClass (⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩ :
        involutionPointHull z) := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    exact hH (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
  have hx' : g⁻¹ * z * g ∈ involutionPointClass z := class_conj_mem
    (distinguished_mem_pointClass z) g
  have hx'base : (g⁻¹ * z * g) • (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk 1 :=
    fun h => hg ((conj_mem_iff huniq g).mp (class_mem_iff_fixes_base.mpr h))
  obtain ⟨y, hy, rfl⟩ := class_conj_in_closure hz huniq h1 (le_refl _)
    (distinguished_mem_pointClass z) hx' hx'base ht
  exact ⟨⟨y, hy⟩, rfl⟩

theorem hull_internal_eq_top (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    (hH : H ≠ ⊤) :
    involutionPointHull (⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩ :
      involutionPointHull z) = ⊤ := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    exact hH (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
  have hx' : g⁻¹ * z * g ∈ involutionPointClass z := class_conj_mem
    (distinguished_mem_pointClass z) g
  have hx'base : (g⁻¹ * z * g) • (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk 1 :=
    fun h => hg ((conj_mem_iff huniq g).mp (class_mem_iff_fixes_base.mpr h))
  exact hull_closure_eq_top hz huniq h1 (le_refl _) (distinguished_mem_pointClass z) hx' hx'base

theorem pointHullStrongSplit_of_normSplit (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    (hH : H ≠ ⊤)
    (hO : CFSG.oddCore (involutionPointHull z) ≤ H.subgroupOf (involutionPointHull z))
    (hN : NormSplit (involutionPointHull z ⧸ CFSG.oddCore (involutionPointHull z))
      ((H.subgroupOf (involutionPointHull z)).map
        (QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z))))
      (QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z))
        ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩)) :
    PointHullStrongSplit H z := by
  unfold PointHullStrongSplit
  let L := involutionPointHull z
  let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
  let q := QuotientGroup.mk' (CFSG.oddCore L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = CFSG.oddCore L := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card q.ker) := by
    rw [hker]
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hkerH : q.ker ≤ H.subgroupOf L := by
    rw [hker]
    exact hO
  rcases hN with hrank | ⟨ub, hub2, hubc, hubinf, hubsup, hse, hcls⟩
  · exact Or.inl (twoRank_le_one_of_odd_kernel q hodd hrank)
  obtain ⟨u, hu2, hqu⟩ : ∃ u : L, u ^ 2 = 1 ∧ q u = ub := by
    by_cases hub1 : ub = 1
    · exact ⟨1, one_pow 2, by rw [map_one, hub1]⟩
    · obtain ⟨u, huI, hqu⟩ :=
        CFSG.ProperTwoGeneratedCore.involution_lift_of_odd_kernel q hodd ⟨hub1, hub2⟩ (hq ub)
      exact ⟨u, huI.sq_eq_one, hqu⟩
  have hqu' : QuotientGroup.mk' (CFSG.oddCore L) u = ub := hqu
  let K : Subgroup L := commutator L
  let Kb : Subgroup (L ⧸ CFSG.oddCore L) := commutator _
  have hKmap : K.map q = Kb := by
    change (commutator L).map q = commutator _
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hq, commutator_def]
  refine Or.inr ⟨u, hu2, hqu' ▸ hubc, hqu' ▸ hubinf, hqu' ▸ hubsup, ?_, ?_⟩
  · let φ : K →* Kb := (q.comp K.subtype).codRestrict Kb
      (fun k => hKmap ▸ ⟨k, k.property, rfl⟩)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      rw [← hKmap] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact ⟨⟨k, hk⟩, rfl⟩
    have hφker : Odd (Nat.card φ.ker) := by
      have hle : φ.ker.map K.subtype ≤ q.ker := by
        rintro x ⟨k, hk, rfl⟩
        exact congrArg Subtype.val hk
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective K.subtype_injective] at hdvd
      exact hodd.of_dvd_nat hdvd
    let MK : Subgroup K := (H.subgroupOf L).subgroupOf K
    have hφkerM : φ.ker ≤ MK := fun k hk => hkerH (congrArg Subtype.val hk)
    have hMKmap : MK.map φ = ((H.subgroupOf L).map q).subgroupOf Kb := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
      · intro hy
        obtain ⟨k, rfl⟩ := hφ y
        exact ⟨k, (mem_map_iff_of_ker_le q hkerH k).mp hy, rfl⟩
    have hseK : fusionStronglyEmbedded MK :=
      stronglyEmbedded_of_map_odd_kernel φ hφ hφker hφkerM (hMKmap ▸ hse)
    let L' : Subgroup G := ⁅L, L⁆
    have hKG : K.map L.subtype = L' := Subgroup.map_subtype_commutator L
    let e : K ≃* L' :=
      (K.equivMapOfInjective L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hKG)
    have hecoe : ∀ k : K, ((e k : L') : G) = ((k : L) : G) := fun _ => rfl
    have hmap : MK.map e.toMonoidHom = H.subgroupOf L' := by
      ext w
      constructor
      · rintro ⟨k, hk, rfl⟩
        change ((e k : L') : G) ∈ H
        rw [hecoe]
        exact hk
      · intro hw
        refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
        change (((e.symm w : K) : L) : G) ∈ H
        rw [← hecoe, e.apply_symm_apply]
        exact hw
    have h := hseK.map_mulEquiv e
    rwa [hmap] at h
  · intro t ht
    have htL := class_mem_hull_class hz huniq h1 hH ht
    have hqt : q ⟨t, Subgroup.subset_closure ht⟩ ∈ involutionPointClass (q zL) := by
      obtain ⟨y, hy⟩ := htL
      refine ⟨q y, ?_⟩
      change (q y)⁻¹ * q zL * q y = _
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg q hy
    have hmem := hcls _ hqt
    rw [← hqu, ← map_inv, ← map_mul] at hmem
    have hmem' : q (u⁻¹ * ⟨t, Subgroup.subset_closure ht⟩) ∈ Kb := hmem
    rw [← hKmap] at hmem'
    obtain ⟨k, hk, hkeq⟩ := hmem'
    have hker' : k⁻¹ * (u⁻¹ * ⟨t, Subgroup.subset_closure ht⟩) ∈ q.ker := by
      change q (k⁻¹ * (u⁻¹ * ⟨t, Subgroup.subset_closure ht⟩)) = 1
      rw [map_mul, map_inv, hkeq, inv_mul_cancel]
    have hoddord : Odd (orderOf (k⁻¹ * (u⁻¹ * ⟨t, Subgroup.subset_closure ht⟩))) := by
      apply hodd.of_dvd_nat
      rw [← Subgroup.orderOf_mk _ hker']
      exact orderOf_dvd_natCard _
    have hgen : Subgroup.closure (involutionPointClass zL) = ⊤ :=
      hull_internal_eq_top hz huniq h1 hH
    have hzL2 : orderOf zL = 2 := (Subgroup.orderOf_mk z _).trans hz
    have hS : ∀ s ∈ involutionPointClass zL, s ^ 2 = 1 := fun s hs =>
      (class_orderOf hzL2 hs) ▸ pow_orderOf_eq_one s
    have hcomm := mem_commutator_of_odd_order hgen hS hoddord
    have hfinal : u⁻¹ * ⟨t, Subgroup.subset_closure ht⟩ ∈ commutator L := by
      have hprod := (commutator L).mul_mem hk hcomm
      rwa [mul_inv_cancel_left] at hprod
    have hG := Subgroup.mem_map_of_mem L.subtype hfinal
    rw [Subgroup.map_subtype_commutator] at hG
    exact hG

end CFSG.ComponentClassification.AschbacherStrongEmbedding
