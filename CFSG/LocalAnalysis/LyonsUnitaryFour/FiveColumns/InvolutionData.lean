module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.InvolutionCount
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.CentralizerNorm

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

theorem mem_four_of_card {Z : Subgroup G} (hZ : Nat.card Z = 4) {z w : G} (hz : z ∈ Z)
    (hw : w ∈ Z) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : w ≠ z) (hzz : z * z = 1) :
    ∀ v ∈ Z, v = 1 ∨ v = z ∨ v = w ∨ v = z * w := by
  intro v hv
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hzw1 : z * w ≠ 1 := fun h => hzw (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hzz])
  have hzw2 : z * w ≠ z := fun h => hw1 (by simpa using congrArg (z⁻¹ * ·) h)
  have hzw3 : z * w ≠ w := fun h => hz1 (by simpa using congrArg (· * w⁻¹) h)
  have hsub : ({1, z, w, z * w, v} : Finset G) ⊆ (Z : Set G).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hz
    · exact hw
    · exact Z.mul_mem hz hw
    · exact hv
  have hcard := Finset.card_le_card hsub
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at hcard
  change _ ≤ Nat.card Z at hcard
  rw [hZ] at hcard
  have h5 : ({1, z, w, z * w, v} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (Ne.symm h4)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzw3.symm, fun h => h3 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzw.symm, hzw2.symm, fun h => h2 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz1.symm, hw1.symm, hzw1.symm, fun h => h1 h.symm⟩
  omega

omit [Fintype G] in
theorem mem_centralizer_zpowers_iff {z g : G} :
    g ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G) ↔ z * g = g * z := by
  constructor
  · intro h
    exact Subgroup.mem_centralizer_iff.mp h z (Subgroup.mem_zpowers z)
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left h k)).eq

theorem lyons_involution_counts (S : Sylow 2 G) (Z : Subgroup G) (hZS : Z ≤ (S : Subgroup G))
    (hsq : ∀ x ∈ (S : Subgroup G), x * x = 1 ↔ x ∈ Z) (hZcard : Nat.card Z = 4)
    (hall : ∀ t u : G, orderOf t = 2 → orderOf u = 2 → IsConj t u)
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) {L : Type*} [Group L]
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G))
    (hcentral : ∀ v (hv : v ∈ Z), π ⟨v, hSC (hZS hv)⟩ ∈ Subgroup.center L)
    (hinj : ∀ v (hv : v ∈ Z) v' (hv' : v' ∈ Z),
      π ⟨v, hSC (hZS hv)⟩ = π ⟨v', hSC (hZS hv')⟩ → v = v')
    {w : G} (hwZ : w ∈ Z) (hw1 : w ≠ 1) (hwz : w ≠ z) :
    (∀ g, ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = g).card : ℂ) ≠ 0 →
      g = π (centralizerSelf z) ∨ g = π ⟨w, hSC (hZS hwZ)⟩ ∨
        g = π (centralizerSelf z) * π ⟨w, hSC (hZS hwZ)⟩) ∧
    ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z)).card : ℂ) = 1 ∧
    ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π ⟨w, hSC (hZS hwZ)⟩).card : ℂ) *
      Nat.card (Subgroup.centralizer (Z : Set G)) =
      Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) ∧
    ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z) * π ⟨w, hSC (hZS hwZ)⟩).card : ℂ) *
      Nat.card (Subgroup.centralizer (Z : Set G)) =
      Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) := by
  have hsqZ : ∀ v ∈ Z, v * v = 1 := fun v hv => (hsq v (hZS hv)).mpr hv
  have hinvZ : ∀ x ∈ (S : Subgroup G), x * x = 1 → x ∈ Z := fun x hx hxx => (hsq x hx).mp hxx
  have hzz : z * z = 1 := hsqZ z hzZ
  have horder : ∀ v ∈ Z, v ≠ 1 → orderOf v = 2 := fun v hv hv1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hsqZ v hv) hv1
  have hconj : ∀ v ∈ Z, v ≠ 1 → IsConj v z := fun v hv hv1 =>
    hall v z (horder v hv hv1) (horder z hzZ hz1)
  have hfour := mem_four_of_card hZcard hzZ hwZ hz1 hw1 hwz hzz
  have hzwZ : z * w ∈ Z := Z.mul_mem hzZ hwZ
  have hzw1 : z * w ≠ 1 := fun h => hwz (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hzz])
  have hcnt := fun v (hv : v ∈ Z) (hv1 : v ≠ 1) =>
    card_isConj_image_mul_card_centralizer S hinvZ hSC hZS π hcentral hinj hzz hconj hv hv1
  refine ⟨fun g hg => ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨x, hx⟩ : ∃ x, x ∈ (Finset.univ.filter fun x :
        Subgroup.centralizer (Subgroup.zpowers z : Set G) => IsConj (x : G) z ∧ π x = g) := by
      by_contra hnone
      push Not at hnone
      apply hg
      rw [Finset.eq_empty_of_forall_notMem hnone, Finset.card_empty, Nat.cast_zero]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxz, rfl⟩ := hx
    obtain ⟨c, hc⟩ := exists_conj_mem_of_isConj_involution S hinvZ hSC hzz x hxz
    have hu : π (c * x * c⁻¹) ∈ Subgroup.center L := hcentral _ hc
    have hπx : π x = π (c * x * c⁻¹) := by
      have h1 : π x = (π c)⁻¹ * π (c * x * c⁻¹) * π c := by
        rw [map_mul, map_mul, map_inv]; group
      rw [h1, mul_assoc, ← Subgroup.mem_center_iff.mp hu (π c), ← mul_assoc, inv_mul_cancel,
        one_mul]
    have hu1 : ((c * x * c⁻¹ : Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G) ≠ 1 := by
      intro h1
      have hxe : x = 1 := by
        have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        rw [h2, show c * x * c⁻¹ = 1 from Subtype.ext h1]; group
      rw [hxe, Subgroup.coe_one] at hxz
      exact hz1 (isConj_one_right.mp hxz)
    rcases hfour _ hc with h | h | h | h
    · exact absurd h hu1
    · left
      rw [hπx]
      congr 1
      exact Subtype.ext h
    · right; left
      rw [hπx]
      congr 1
      exact Subtype.ext h
    · right; right
      rw [hπx, ← map_mul]
      congr 1
      exact Subtype.ext h
  ·
    have h := hcnt z hzZ hz1
    rw [card_centralizer_subgroup_eq] at h
    have hinf : Subgroup.centralizer (Subgroup.zpowers z : Set G) ⊓
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      apply inf_of_le_left
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_centralizer_zpowers_iff.mp hg).symm
    rw [hinf] at h
    have hpos : 0 < Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) := Nat.card_pos
    have h1 := Nat.eq_of_mul_eq_mul_right hpos (h.trans (one_mul _).symm)
    exact_mod_cast h1
  ·
    have h := hcnt w hwZ hw1
    rw [card_centralizer_subgroup_eq] at h
    have hinf : Subgroup.centralizer (Subgroup.zpowers z : Set G) ⊓
        Subgroup.centralizer ({w} : Set G) = Subgroup.centralizer (Z : Set G) := by
      ext g
      rw [Subgroup.mem_inf, mem_centralizer_zpowers_iff, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hgz, hgw⟩ v hv
        rcases hfour v hv with rfl | rfl | rfl | rfl
        · rw [one_mul, mul_one]
        · exact hgz
        · exact hgw.symm
        · rw [mul_assoc, ← hgw, ← mul_assoc, hgz, mul_assoc]
      · intro h
        exact ⟨h z hzZ, (h w hwZ).symm⟩
    rw [hinf] at h
    exact_mod_cast h
  ·
    have h := hcnt (z * w) hzwZ hzw1
    rw [card_centralizer_subgroup_eq] at h
    have hinf : Subgroup.centralizer (Subgroup.zpowers z : Set G) ⊓
        Subgroup.centralizer ({z * w} : Set G) = Subgroup.centralizer (Z : Set G) := by
      ext g
      rw [Subgroup.mem_inf, mem_centralizer_zpowers_iff, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hgz, hgzw⟩ v hv
        have hgw : g * w = w * g := by
          have h1 : z * (g * w) = z * (w * g) := by
            calc z * (g * w) = (z * g) * w := (mul_assoc _ _ _).symm
              _ = (g * z) * w := by rw [hgz]
              _ = g * (z * w) := mul_assoc _ _ _
              _ = (z * w) * g := hgzw
              _ = z * (w * g) := mul_assoc _ _ _
          exact mul_left_cancel h1
        rcases hfour v hv with rfl | rfl | rfl | rfl
        · rw [one_mul, mul_one]
        · exact hgz
        · exact hgw.symm
        · exact hgzw.symm
      · intro h
        exact ⟨h z hzZ, (h (z * w) hzwZ).symm⟩
    rw [hinf] at h
    have hmul : π (centralizerSelf z) * π ⟨w, hSC (hZS hwZ)⟩ = π ⟨z * w, hSC (hZS hzwZ)⟩ := by
      rw [← map_mul]; rfl
    rw [hmul]
    exact_mod_cast h

end CFSG.LyonsUnitaryFour
