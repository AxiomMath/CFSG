module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Dictionary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private lemma Gxy_le_Gx_left (x y : G) : Gxy x y ≤ Gx x :=
  fun _ hg => (mem_Gxy.mp hg).1

private lemma Gxy_le_Gx_right (x y : G) : Gxy x y ≤ Gx y :=
  fun _ hg => (mem_Gxy.mp hg).2

private lemma Gxy_le_Gx_mul (x y : G) : Gxy x y ≤ Gx (x * y) := by
  intro g hg
  obtain ⟨hx, hy⟩ := mem_Gxy.mp hg
  rw [mem_Gx] at hx hy ⊢
  calc (x * y) * g = x * (y * g) := mul_assoc x y g
    _ = x * (g * y) := by rw [hy]
    _ = (x * g) * y := (mul_assoc x g y).symm
    _ = (g * x) * y := by rw [hx]
    _ = g * (x * y) := mul_assoc g x y

private lemma commute_of_le_Gx {K H : Subgroup G} (hKH : K ≤ H) {v : G} (hv : H ≤ Gx v) :
    ∀ x ∈ K, x * v = v * x :=
  fun x hx => (mem_Gx.mp (hv (hKH hx))).symm

private lemma coe_mulEquiv_ne_of_comm {K : Subgroup G}
    (φ : alternatingGroup (Fin 8) ≃* ↥K) {t : alternatingGroup (Fin 8)} (ht1 : t ≠ 1) {v : G}
    (hcomm : ∀ x ∈ K, x * v = v * x) : (φ t : G) ≠ v := by
  intro hv
  apply ht1
  apply eq_one_of_forall_commute
  intro s
  apply φ.injective
  apply Subtype.ext
  rw [map_mul, map_mul]
  change (φ s : G) * (φ t : G) = (φ t : G) * (φ s : G)
  rw [hv]
  exact hcomm (φ s : G) (φ s).2

theorem fig8a_of_fusion2 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hA8 : A8Shapes a z) :
    ∀ b ∈ orb2A a a, ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a b)),
      ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2} →
        IsConj a (φ t : G) ∧ IsConj z (a * φ t) ∧ IsConj z (b * φ t) ∧
          IsConj z (a * b * φ t) := by
  intro b hb φ t ht
  simp only [orb2A, Set.mem_setOf_eq] at hb
  obtain ⟨hba, hab⟩ := hb
  have hKle : derivedOf (Gxy a b) ≤ Gx a := le_trans (derivedOf_le _) (Gxy_le_Gx_left a b)
  have hra : IsConj a (φ t : G) := hA8.shape_2211 (derivedOf (Gxy a b)) hKle φ t ht
  have hrK : (φ t : G) ∈ derivedOf (Gxy a b) := (φ t).2
  have ht1 : t ≠ 1 := (sq_eq_one_of_cycleType_two_two ht).2
  have hcomm_a : ∀ x ∈ derivedOf (Gxy a b), x * a = a * x :=
    commute_of_le_Gx (derivedOf_le _) (Gxy_le_Gx_left a b)
  have hcomm_b : ∀ x ∈ derivedOf (Gxy a b), x * b = b * x :=
    commute_of_le_Gx (derivedOf_le _) (Gxy_le_Gx_right a b)
  have hcomm_ab : ∀ x ∈ derivedOf (Gxy a b), x * (a * b) = (a * b) * x :=
    commute_of_le_Gx (derivedOf_le _) (Gxy_le_Gx_mul a b)
  refine ⟨hra, ?_, ?_, ?_⟩
  · exact isConj_z_mul_of_isConj_a hI h hF1 hF2 (IsConj.refl a)
      (derivedOf_mono (Gxy_le_Gx_left a b) hrK) (coe_mulEquiv_ne_of_comm φ ht1 hcomm_a) hra
  · exact isConj_z_mul_of_isConj_a hI h hF1 hF2 hba
      (derivedOf_mono (Gxy_le_Gx_right a b) hrK) (coe_mulEquiv_ne_of_comm φ ht1 hcomm_b) hra
  · exact isConj_z_mul_of_isConj_a hI h hF1 hF2 hab
      (derivedOf_mono (Gxy_le_Gx_mul a b) hrK) (coe_mulEquiv_ne_of_comm φ ht1 hcomm_ab) hra

theorem fig8b_of_fusion2 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hA8 : A8Shapes a z) :
    ∀ b ∈ orb2A a a, ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a b)),
      ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
        IsConj z (φ t : G) ∧ IsConj a (a * φ t) ∧ IsConj a (b * φ t) ∧
          IsConj a (a * b * φ t) := by
  intro b hb φ t ht
  simp only [orb2A, Set.mem_setOf_eq] at hb
  obtain ⟨hba, hab⟩ := hb
  have hKle : derivedOf (Gxy a b) ≤ Gx a := le_trans (derivedOf_le _) (Gxy_le_Gx_left a b)
  have hrz : IsConj z (φ t : G) := hA8.shape_2222 (derivedOf (Gxy a b)) hKle φ t ht
  have hrK : (φ t : G) ∈ derivedOf (Gxy a b) := (φ t).2
  refine ⟨hrz, ?_, ?_, ?_⟩
  · exact isConj_a_mul_of_isConj_z hI h hF1 hF2 (IsConj.refl a)
      (derivedOf_mono (Gxy_le_Gx_left a b) hrK) hrz
  · exact isConj_a_mul_of_isConj_z hI h hF1 hF2 hba
      (derivedOf_mono (Gxy_le_Gx_right a b) hrK) hrz
  · exact isConj_a_mul_of_isConj_z hI h hF1 hF2 hab
      (derivedOf_mono (Gxy_le_Gx_mul a b) hrK) hrz

end CFSG.EvenSporadicStandard.HNRecog.Section3
