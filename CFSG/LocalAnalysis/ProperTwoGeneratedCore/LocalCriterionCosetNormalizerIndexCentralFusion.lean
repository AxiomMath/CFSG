module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexSylowNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe v

variable {G : Type v} [Group G]

theorem subgroup_normalizer_le_class_intersection_normalizer (u : G) (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (involutionPointClass u ∩ (T : Set G)) := by
  intro n hn
  change ∀ x : G, x ∈ involutionPointClass u ∩ (T : Set G) ↔
    n * x * n⁻¹ ∈ involutionPointClass u ∩ (T : Set G)
  intro x
  constructor
  · rintro ⟨hxclass, hxT⟩
    exact ⟨by simpa only [rightConjugateElem, inv_inv] using
      pointClass_right_conjugate_mem hxclass n⁻¹,
      (Subgroup.mem_normalizer_iff.mp hn x).mp hxT⟩
  · rintro ⟨hxclass, hxT⟩
    exact ⟨by simpa only [rightConjugateElem, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using pointClass_right_conjugate_mem hxclass n,
      (Subgroup.mem_normalizer_iff.mp hn x).mpr hxT⟩

theorem central_class_representative_in_every_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] (S Q : Sylow p G) (z : G)
    (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    ∃ w : G, ∃ hw : w ∈ (Q : Subgroup G),
      (⟨w, hw⟩ : (Q : Subgroup G)) ∈ Subgroup.center (Q : Subgroup G) ∧
        w ∈ involutionPointClass z := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S Q
  let w : G := g * z * g⁻¹
  have hw : w ∈ (g • S : Sylow p G) := ⟨z, hzS, rfl⟩
  have hwcenter : (⟨w, hw⟩ : (g • S : Sylow p G)) ∈
      Subgroup.center (g • S : Sylow p G) := by
    apply Subgroup.mem_center_iff.mpr
    rintro ⟨t, ht⟩
    obtain ⟨x, hx, rfl⟩ := ht
    apply Subtype.ext
    have hxz : x * z = z * x :=
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter) ⟨x, hx⟩)
    change (g * x * g⁻¹) * (g * z * g⁻¹) =
      (g * z * g⁻¹) * (g * x * g⁻¹)
    simpa only [mul_assoc, inv_mul_cancel_left] using
      congrArg (fun y : G => g * y * g⁻¹) hxz
  exact ⟨w, hw, hwcenter, g⁻¹, by simp only [rightConjugateElem, inv_inv, w]⟩

theorem coset_normalizer_moves_of_central_sylow_fusion [Finite G]
    (U : Subgroup G) (u z : G) (hz : IsInvolution z)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hclasses : ∀ w : G, w ∈ involutionPointClass z → w ∉ involutionPointClass u)
    (hpartition : ∀ x : G,
      x ∈ (T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype → IsInvolution x →
      x ∈ U ∨ x ∈ (fun v : G => u * v) '' (U : Set G))
    (hDelta : involutionPointClass u ∩
      (((T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G) =
      (fun v : G => u * v) '' (U : Set G)) :
    ∃ n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
      rightConjugateElem u (n : G) ≠ u := by
  classical
  let M := Subgroup.centralizer ({u} : Set G)
  let A : Subgroup G := (T : Subgroup M).map M.subtype
  let Delta : Set G := (fun v : G => u * v) '' (U : Set G)
  let N := Subgroup.normalizer Delta
  have hDelta' : involutionPointClass u ∩ (A : Set G) = Delta := hDelta
  by_contra hmove
  have hfix : ∀ n : G, n ∈ N → rightConjugateElem u n = u := by
    intro n hn
    by_contra hne
    exact hmove ⟨⟨n, hn⟩, hne⟩
  have hNM : N ≤ M := by
    intro n hn
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have heq := congrArg (fun x : G => n * x) (hfix n hn)
    have heq' : u * n = n * u := by
      simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left] using heq
    exact heq'.symm
  have hAN : Subgroup.normalizer (A : Set G) ≤ N := by
    change Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer Delta
    rw [← hDelta']
    exact subgroup_normalizer_le_class_intersection_normalizer u A
  obtain ⟨Q, hQ⟩ := supplied_sylow_ambient_of_entire_normalizer_le M T (hAN.trans hNM)
  obtain ⟨w, hwQ, hwcenter, hwclass⟩ :=
    central_class_representative_in_every_sylow S Q z hzS hzcenter
  have hwA : w ∈ A := by
    change w ∈ (T : Subgroup M).map M.subtype
    rw [← hQ]
    exact hwQ
  have hwinvolution : IsInvolution w := by
    obtain ⟨g, rfl⟩ := hwclass
    exact isInvolution_rightConjugateElem hz
  have hwU : w ∈ U := (hpartition w hwA hwinvolution).resolve_right (by
    intro hwDelta
    have hwclassu : w ∈ involutionPointClass u := (hDelta.symm ▸ hwDelta).1
    exact hclasses w hwclass hwclassu)
  have hAM : A ≤ M := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have huC : u ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    have htA : t ∈ A := by
      change t ∈ (T : Subgroup M).map M.subtype
      rw [← hQ]
      exact ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAM htA)
  have hwC : w ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hwcenter) ⟨t, ht⟩)
  have huwDelta : u * w ∈ Delta := ⟨w, hwU, rfl⟩
  have huwclass : u * w ∈ involutionPointClass u := (hDelta'.symm ▸ huwDelta).1
  obtain ⟨g, hg⟩ := huwclass
  change rightConjugateElem u g = u * w at hg
  have hgC : g⁻¹ * u * g ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
    change rightConjugateElem u g ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G)
    rw [hg]
    exact (Subgroup.centralizer ((Q : Subgroup G) : Set G)).mul_mem huC hwC
  obtain ⟨n, hnQ, hconj⟩ := Q.conj_eq_normalizer_conj_of_mem_centralizer u g huC hgC
  have hnN : n ∈ N := by
    apply hAN
    change n ∈ Subgroup.normalizer (((T : Subgroup M).map M.subtype : Subgroup G) : Set G)
    rw [← hQ]
    exact hnQ
  have hvalue : rightConjugateElem u n = u * w := hconj.symm.trans hg
  have heq : u * w = u * 1 := hvalue.symm.trans ((hfix n hnN).trans (mul_one u).symm)
  exact hwinvolution.ne_one (mul_left_cancel heq)

theorem full_conjugation_transitivity_of_move_and_stabilizer
    (Delta : Set G) (u : G) (hu : u ∈ Delta)
    (hmove : ∃ n : Subgroup.normalizer Delta, rightConjugateElem u (n : G) ≠ u)
    (hstab : ∀ s : G, s ∈ Delta → s ≠ u → ∀ t : G, t ∈ Delta → t ≠ u →
      ∃ a : (Subgroup.normalizer Delta ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t) :
    ∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t := by
  classical
  obtain ⟨m, hm⟩ := hmove
  have hbase : ∀ t : G, t ∈ Delta →
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem u (n : G) = t := by
    intro t ht
    by_cases htu : t = u
    · exact ⟨1, by simp [rightConjugateElem, htu]⟩
    · have hmDelta : rightConjugateElem u (m : G) ∈ Delta := by
        have hn := (Subgroup.normalizer Delta).inv_mem m.property
        simpa only [rightConjugateElem, inv_inv] using
          (show ∀ x : G, x ∈ Delta ↔ (m : G)⁻¹ * x * ((m : G)⁻¹)⁻¹ ∈ Delta from hn) u |>.mp hu
      obtain ⟨a, ha⟩ := hstab _ hmDelta hm t ht htu
      refine ⟨m * ⟨(a : G), a.property.1⟩, ?_⟩
      simpa only [rightConjugateElem, Subgroup.coe_mul, mul_inv_rev, mul_assoc] using ha
  intro s hs t ht
  obtain ⟨a, ha⟩ := hbase s hs
  obtain ⟨b, hb⟩ := hbase t ht
  refine ⟨a⁻¹ * b, ?_⟩
  rw [← ha]
  simpa only [rightConjugateElem, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
    inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] using hb

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
