module

public import CFSG.ClassicalInvolution.Q3.Q3TLOut
public import CFSG.ClassicalInvolution.Q3.Q3TLPerm
public import CFSG.ClassicalInvolution.Q3.Q3TIRed

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.ClassicalInvolution
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open scoped MatrixGroups Pointwise

theorem sl2Three_exists_quaternion : ∃ i j : SL(2, ZMod 3),
    i ^ 2 = -1 ∧ j ^ 2 = -1 ∧ (i * j) ^ 2 = -1 := by
  decide

theorem sl2Three_neg_one_pow_odd {n : ℕ} (hn : Odd n) : (-1 : SL(2, ZMod 3)) ^ n ≠ 1 := by
  rw [hn.neg_one_pow]
  decide

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem smul_pointFamily_of_pow_four (hz : IsClassicalMember3 L z) {T : Subgroup Y} [T.Normal]
    (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))) {u : Y}
    (hu : u ∈ L) (hu4 : u ^ 4 = 1) :
    MulAut.congr e (MulAut.conjNormal u : MulAut T) •
        statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) =
      statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) := by
  classical
  set F := statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) with hF
  set O := MulAction.orbit
    (MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))))) F with hO
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by rw [natCard_galoisField_three, pow_one]
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))))
      .POmegaPlus 4 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, GaloisField 3 1, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  have hncard : O.ncard ≤ 3 :=
    ((orthogonal_geometry_plus_point_family_orbit hT hK (MulEquiv.refl _)).2.2.1 rfl).2
  have : Fintype O := Fintype.ofFinite O
  have hcard : Fintype.card O ≤ 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hncard
  let ρ : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))) →*
      Equiv.Perm O := MulAction.toPermHom _ O
  let φ : L →* Equiv.Perm O :=
    ρ.comp ((MulAut.congr e).toMonoidHom.comp ((MulAut.conjNormal).comp L.subtype))
  have hsign : Equiv.Perm.sign (φ ⟨u, hu⟩) = 1 :=
    hom_eq_one_of_sq hz (Equiv.Perm.sign.comp φ) (fun m => Int.units_sq m) ⟨u, hu⟩
  have h4 : φ ⟨u, hu⟩ ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨u, hu⟩ : L) ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hu4)
    rw [this, map_one]
  have h1 := perm_eq_one_of_sign_of_pow_four hcard hsign h4
  have h2 := congrArg (fun σ : Equiv.Perm O => σ ⟨F, MulAction.mem_orbit_self F⟩) h1
  have h3 := congrArg Subtype.val h2
  exact h3

omit [Finite Y] in
theorem mem_of_congr_mem_inner {T : Subgroup Y} [T.Normal]
    (hCT : Subgroup.centralizer (T : Set Y) = ⊥) {P : Type*} [Group P] (e : T ≃* P) {w : Y}
    (h : MulAut.congr e (MulAut.conjNormal w : MulAut T) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner P) : w ∈ T := by
  obtain ⟨p, hp⟩ := h
  have h1 : (MulAut.conjNormal w : MulAut T) = MulAut.conj (e.symm p) := by
    apply (MulAut.congr e).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hp.symm
  rw [eq_of_conjNormal_eq_conj hCT h1]
  exact (e.symm p).2

theorem eq_one_of_two_pow_of_mem_oddCore (hz : IsClassicalMember3 L z) {w : L} {k : ℕ}
    (hk : orderOf w ∣ 2 ^ k) (hw : w ∈ CFSG.Open.classicalInvolutionOddCore L) : w = 1 := by
  have hodd := hz.odd_orderOf_of_mem_oddCore hw
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj, Nat.odd_iff, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by norm_num)

theorem mem_of_socle_d4 (hz : IsClassicalMember3 L z) {T : Subgroup Y} [T.Normal]
    (hCT : Subgroup.centralizer (T : Set Y) = ⊥)
    (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))) : z ∈ T := by
  by_contra hzT
  obtain ⟨ψ, hψs, hψk⟩ := hz.exists_hom
  obtain ⟨i, j, hi, hj, hij⟩ := sl2Three_exists_quaternion
  have hneg : (-1 : SL(2, ZMod 3)) ^ 2 = 1 := by decide
  have h4 : ∀ s : SL(2, ZMod 3), s ^ 2 = -1 → s ^ 4 = 1 := fun s hs => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs, hneg]
  obtain ⟨u, ⟨a, ha⟩, hu⟩ := exists_two_pow_lift ψ hψs (h4 i hi)
  obtain ⟨v, ⟨b, hb⟩, hv⟩ := exists_two_pow_lift ψ hψs (h4 j hj)
  have hfour : ∀ w : L, ∀ k, orderOf w = 2 ^ k → ψ w ^ 4 = 1 → w ^ 4 = 1 := by
    intro w k hk h
    refine eq_one_of_two_pow_of_mem_oddCore hz (k := k) ?_ ((hψk _).mp (by rw [map_pow]; exact h))
    rw [← hk]
    exact orderOf_pow_dvd 4
  have hu4 : ((u : Y)) ^ 4 = 1 := by
    have := hfour u a ha (by rw [hu]; exact h4 i hi)
    rw [← SubgroupClass.coe_pow, this, OneMemClass.coe_one]
  have hv4 : ((v : Y)) ^ 4 = 1 := by
    have := hfour v b hb (by rw [hv]; exact h4 j hj)
    rw [← SubgroupClass.coe_pow, this, OneMemClass.coe_one]
  have hFu := smul_pointFamily_of_pow_four hz e u.2 hu4
  have hFv := smul_pointFamily_of_pow_four hz e v.2 hv4
  have hodd : Odd (Nat.card ↥(L ⊓ T)) := odd_card_inf_of_not_mem hz hzT
  have hkey : ∀ w : L, ψ w = -1 → (w : Y) ∉ T := by
    intro w hw hwT
    have h1 : orderOf (⟨w, w.2, hwT⟩ : ↥(L ⊓ T)) ∣ Nat.card ↥(L ⊓ T) :=
      orderOf_dvd_natCard _
    have h0 : orderOf (⟨w, w.2, hwT⟩ : ↥(L ⊓ T)) = orderOf w := by
      rw [← Subgroup.orderOf_coe (⟨w, w.2, hwT⟩ : ↥(L ⊓ T)), ← Subgroup.orderOf_coe w]
    have h2 : Odd (orderOf w) := hodd.of_dvd_nat (h0 ▸ h1)
    apply sl2Three_neg_one_pow_odd h2
    rw [← hw, ← map_pow, pow_orderOf_eq_one, map_one]
  rcases sq_mem_inner_or_of_smul_pointFamily _ _ hFu hFv with h | h | h
  · rw [← map_pow, ← map_pow] at h
    exact hkey (u ^ 2) (by rw [map_pow, hu, hi]) (by
      rw [SubgroupClass.coe_pow]; exact mem_of_congr_mem_inner hCT e h)
  · rw [← map_pow, ← map_pow] at h
    exact hkey (v ^ 2) (by rw [map_pow, hv, hj]) (by
      rw [SubgroupClass.coe_pow]; exact mem_of_congr_mem_inner hCT e h)
  · rw [← map_mul, ← map_mul, ← map_pow, ← map_pow] at h
    exact hkey ((u * v) ^ 2) (by rw [map_pow, map_mul, hu, hv, hij]) (by
      rw [SubgroupClass.coe_pow, Subgroup.coe_mul]; exact mem_of_congr_mem_inner hCT e h)

end CFSG.ClassicalInvolution.Q3.Q3T
