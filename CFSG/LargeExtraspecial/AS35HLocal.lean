module

public import CFSG.LargeExtraspecial.AS35HCoprime
public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS35EResid

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Asc77

variable {G : Type} [Group G]

theorem conjIn_eq_of_mem {z e : G} {H : Subgroup G} (he : e ∈ conjIn z H) :
    conjIn e H = conjIn z H := by
  obtain ⟨g, hg, rfl⟩ := he
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, H.mul_mem hh hg, by group⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g⁻¹, H.mul_mem hh (H.inv_mem hg), by group⟩

theorem conjIn_map_conj (z c : G) (H : Subgroup G) :
    conjIn z (H.map (MulAut.conj c).toMonoidHom) =
      (fun p => c * p * c⁻¹) '' conjIn (c⁻¹ * z * c) H := by
  ext p
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨h * (c⁻¹ * z * c) * h⁻¹, ⟨h, hh, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨c * h * c⁻¹, ⟨h, hh, rfl⟩, ?_⟩
    group

end Asc77

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

omit S in
theorem mem_Qa_iff_inv_conj_mem (S : Setting G) {k y : G} :
    y ∈ S.Qa k ↔ k⁻¹ * y * k ∈ S.QG := by
  rw [Qa_eq_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [mul_assoc] using hq
  · intro h
    exact ⟨k⁻¹ * y * k, h, by simp [mul_assoc]⟩

variable [Finite G]

theorem HAt_inv_eq_map (k : G) :
    S.HAt k⁻¹ = (S.HAt k).map (MulAut.conj k⁻¹).toMonoidHom := by
  rw [HAt, HAt, Subgroup.map_sup, ← Qa_eq_map, ← Qa_mul, inv_mul_cancel, Qa_one, sup_comm]

theorem zConj_HAt_inv {k : G} (he : k * S.z * k⁻¹ ∈ S.zConj (S.HAt k)) :
    S.zConj (S.HAt k⁻¹) = (fun p => k⁻¹ * p * k) '' S.zConj (S.HAt k) := by
  rw [zConj, HAt_inv_eq_map, Asc77.conjIn_map_conj, inv_inv, Asc77.conjIn_eq_of_mem he]

theorem cl_conj_mul_eq {e q : G} (heM : e ∈ S.M) (hee : e * e = 1) (hq : q ∈ S.QG) :
    q * e * q⁻¹ * e ∈ S.QG ∧ S.cl (q * e * q⁻¹ * e) = S.rhoL heM (S.cl q) - S.cl q := by
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have h1 : q * e * q⁻¹ * e = q * (e * q⁻¹ * e⁻¹) := by rw [heinv]; group
  have h2 : e * q⁻¹ * e⁻¹ ∈ S.QG := S.conj_mem_QG heM (S.QG.inv_mem hq)
  rw [h1]
  refine ⟨S.QG.mul_mem hq h2, ?_⟩
  rw [S.cl_mul hq h2, ← S.rhoL_cl heM (S.QG.inv_mem hq), S.cl_inv hq, sub_eq_add_vec (ZMod 2),
    add_comm]

theorem rhoL_comm_of_commute {e y : G} (heM : e ∈ S.M) (hyM : y ∈ S.M) (hye : y * e = e * y)
    (v : S.Qt) : S.rhoL heM (S.rhoL hyM v) = S.rhoL hyM (S.rhoL heM v) := by
  obtain ⟨w, hw, rfl⟩ := S.exists_cl v
  rw [S.rhoL_cl hyM hw, S.rhoL_cl heM (S.conj_mem_QG hyM hw), S.rhoL_cl heM hw,
    S.rhoL_cl hyM (S.conj_mem_QG heM hw)]
  congr 1
  calc e * (y * w * y⁻¹) * e⁻¹ = (e * y) * w * (e * y)⁻¹ := by group
    _ = (y * e) * w * (y * e)⁻¹ := by rw [hye]
    _ = y * (e * w * e⁻¹) * y⁻¹ := by group

theorem exists_conj_eq_of_fix (hS : S.SixHyp) {e k : G} (he : e ∈ S.DSet)
    (hk : k * S.z * k⁻¹ = e) (heM : e ∈ S.M) {y : G} (hyM : y ∈ S.M) (hy3 : y ^ 3 = 1)
    (hye : y * e = e * y) (hfix : commSpace (S.rhoL heM) ≤ fixSpace (S.rhoL hyM)) {p : G}
    (hp : p ∈ S.zConj (S.HAt k)) (hpz : p ≠ S.z) :
    ∃ q ∈ S.QG ⊓ centralizer ({y} : Set G), q * e * q⁻¹ = p := by
  classical
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hee : e * e = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet he.1)
  have hdim : finrank (ZMod 2) (commSpace (S.rhoL heM)) = 2 :=
    (S.fiveOne_two hS.sixFour hS.weak he heM).1.2.2.2.1
  have heH := S.mem_zConj_of_mem_ESet he.1 hk
  have h5 := (S.isHStar_of_mem_ESet he.1 hk).2
  set O := S.zConj (S.HAt k) \ {S.z} with hO
  set A := (fun q => q * e * q⁻¹) ''
    ((S.QG ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) with hA
  have hAO : A ⊆ O := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨Asc77.conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa k) (mem_inf.mp hq).1) heH, ?_⟩
    intro h
    have h' : q * e * q⁻¹ = S.z := h
    apply S.ne_z_of_mem_ESet he.1
    have hqM := S.QG_le_M (mem_inf.mp hq).1
    calc e = q⁻¹ * (q * e * q⁻¹) * q := by group
      _ = q⁻¹ * S.z * q⁻¹⁻¹ := by rw [h', inv_inv]
      _ = S.z := S.conj_z_of_mem_M (S.M.inv_mem hqM)
  have hcardO : O.ncard = 4 := by
    rw [hO, Set.ncard_sdiff_singleton_of_mem (Asc77.self_mem_conjIn _ _), h5]
  have himage : (fun p => S.cl (p * e)) '' A = (commSpace (S.rhoL heM) : Set S.Qt) := by
    ext v
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      change S.cl (q * e * q⁻¹ * e) ∈ commSpace (S.rhoL heM)
      rw [(S.cl_conj_mul_eq heM hee (mem_inf.mp hq).1).2]
      exact sub_mem_commSpace _ _
    · intro hv
      obtain ⟨c, hc, hcv⟩ := S.commSpace_eq_image_fixSpace_of_pow_three hyM hy3
        (S.rhoL_comm_of_commute heM hyM hye) hfix hv
      rw [← S.cqxSub_eq_fixSpace_of_pow_three hyM hy3] at hc
      obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hc
      exact ⟨q * e * q⁻¹, ⟨q, hq, rfl⟩, by
        change S.cl (q * e * q⁻¹ * e) = v
        rw [(S.cl_conj_mul_eq heM hee hqQ).2, hcv]⟩
  have hcardA : 4 ≤ A.ncard := by
    have h1 := Set.ncard_image_le (f := fun p => S.cl (p * e)) (s := A) (Set.toFinite A)
    rw [himage, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, S.card_submodule, hdim] at h1
    norm_num at h1
    exact h1
  have hAeq : A = O := Set.eq_of_subset_of_ncard_le hAO (by omega) (Set.toFinite O)
  have hpO : p ∈ A := hAeq ▸ (⟨hp, hpz⟩ : p ∈ O)
  obtain ⟨q, hq, rfl⟩ := hpO
  exact ⟨q, hq, rfl⟩

theorem exists_conj_eq_of_mem_zConj (hS : S.SixHyp) {e k : G} (he : e ∈ S.DSet)
    (hk : k * S.z * k⁻¹ = e) {p : G} (hp : p ∈ S.zConj (S.HAt k)) (hpz : p ≠ S.z) :
    ∃ q ∈ S.QG, q * e * q⁻¹ = p := by
  have heM := S.mem_M_of_mem_ESet hS.sixFour he.1
  have h1M : (1 : G) ∈ S.M := S.M.one_mem
  have hfix : commSpace (S.rhoL heM) ≤ fixSpace (S.rhoL h1M) := by
    intro v _
    obtain ⟨w, hw, rfl⟩ := S.exists_cl v
    rw [mem_fixSpace, S.rhoL_cl h1M hw]
    congr 1
    group
  obtain ⟨q, hq, hqp⟩ := S.exists_conj_eq_of_fix hS he hk heM h1M (one_pow 3)
    (by rw [one_mul, mul_one]) hfix hp hpz
  exact ⟨q, (mem_inf.mp hq).1, hqp⟩

theorem mul_mem_QG_of_mem_zConj (hS : S.SixHyp) {e k : G} (he : e ∈ S.DSet)
    (hk : k * S.z * k⁻¹ = e) (heM : e ∈ S.M) {p : G} (hp : p ∈ S.zConj (S.HAt k))
    (hpz : p ≠ S.z) : p * e ∈ S.QG ∧ S.cl (p * e) ∈ commSpace (S.rhoL heM) := by
  have hee : e * e = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet he.1)
  obtain ⟨q, hq, rfl⟩ := S.exists_conj_eq_of_mem_zConj hS he hk hp hpz
  obtain ⟨h1, h2⟩ := S.cl_conj_mul_eq heM hee hq
  exact ⟨h1, h2 ▸ sub_mem_commSpace _ _⟩

theorem mul_z_mem_Qa_of_mem_zConj (hS : S.SixHyp) {e k : G} (he : e ∈ S.DSet)
    (hk : k * S.z * k⁻¹ = e) {p : G} (hp : p ∈ S.zConj (S.HAt k)) (hpe : p ≠ e) :
    p * S.z ∈ S.Qa k := by
  have hS4 := hS.sixFour
  have he' : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.DSet := by
    rw [inv_inv]
    exact S.mem_DAt.mp (S.z_mem_DAt hS4 he hk)
  have heH : k * S.z * k⁻¹ ∈ S.zConj (S.HAt k) := hk ▸ S.mem_zConj_of_mem_ESet he.1 hk
  have hp' : k⁻¹ * p * k ∈ S.zConj (S.HAt k⁻¹) := by
    rw [S.zConj_HAt_inv heH]
    exact ⟨p, hp, rfl⟩
  have hp'z : k⁻¹ * p * k ≠ S.z := by
    intro h
    apply hpe
    rw [← hk]
    calc p = k * (k⁻¹ * p * k) * k⁻¹ := by group
      _ = k * S.z * k⁻¹ := by rw [h]
  have he'M := S.mem_M_of_mem_ESet hS4 he'.1
  have h1 := (S.mul_mem_QG_of_mem_zConj hS he' rfl he'M hp' hp'z).1
  rw [S.mem_Qa_iff_inv_conj_mem]
  rwa [show k⁻¹ * (p * S.z) * k = k⁻¹ * p * k * (k⁻¹ * S.z * k⁻¹⁻¹) by group]

theorem mul_mem_QG_inf_Qa (hS : S.SixHyp) {e k : G} (he : e ∈ S.DSet)
    (hk : k * S.z * k⁻¹ = e) (heM : e ∈ S.M) {p p' : G} (hp : p ∈ S.zConj (S.HAt k))
    (hp' : p' ∈ S.zConj (S.HAt k)) (hpz : p ≠ S.z) (hpe : p ≠ e) (hp'z : p' ≠ S.z)
    (hp'e : p' ≠ e) (hne : p ≠ p') :
    p * p' ∈ S.QG ⊓ S.Qa k ∧ S.cl (p * p') ∈ commSpace (S.rhoL heM) ∧ S.cl (p * p') ≠ 0 := by
  have hS4 := hS.sixFour
  have hpD := S.zConj_diff_subset_DSet hS4 he hk hp hpz
  have hpp : p * p = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet hpD.1)
  have hp'D := S.zConj_diff_subset_DSet hS4 he hk hp' hp'z
  have hp'p' : p' * p' = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet hp'D.1)
  have hee : e * e = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet he.1)
  obtain ⟨h1, h1c⟩ := S.mul_mem_QG_of_mem_zConj hS he hk heM hp hpz
  obtain ⟨h2, h2c⟩ := S.mul_mem_QG_of_mem_zConj hS he hk heM hp' hp'z
  have h3 := S.mul_z_mem_Qa_of_mem_zConj hS he hk hp hpe
  have h4 := S.mul_z_mem_Qa_of_mem_zConj hS he hk hp' hp'e
  have hp'inv : p'⁻¹ = p' := inv_eq_of_mul_eq_one_right hp'p'
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hpp'1 : p * p' = p * e * (p' * e)⁻¹ := by
    rw [mul_inv_rev, heinv, hp'inv]
    calc p * p' = p * (e * e) * p' := by rw [hee, mul_one]
      _ = p * e * (e * p') := by group
  have hpp'2 : p * p' = p * S.z * (p' * S.z)⁻¹ := by
    rw [mul_inv_rev, S.z_inv, hp'inv]
    calc p * p' = p * (S.z * S.z) * p' := by rw [S.z_mul_z, mul_one]
      _ = p * S.z * (S.z * p') := by group
  have hQ : p * p' ∈ S.QG := hpp'1 ▸ S.QG.mul_mem h1 (S.QG.inv_mem h2)
  refine ⟨mem_inf.mpr ⟨hQ, hpp'2 ▸ (S.Qa k).mul_mem h3 ((S.Qa k).inv_mem h4)⟩, ?_, ?_⟩
  · rw [hpp'1, S.cl_mul h1 (S.QG.inv_mem h2), S.cl_inv h2]
    exact Submodule.add_mem _ h1c h2c
  · intro h0
    rcases (S.cl_eq_zero_iff hQ).mp h0 with h5 | h5
    · apply hne
      calc p = p * p' * p'⁻¹ := by group
        _ = p' := by rw [h5, one_mul, hp'inv]
    · apply hpD.2
      have hpM := S.mem_M_of_mem_ESet hS4 hpD.1
      have h6 : p' = S.z * p := by
        calc p' = p⁻¹ * (p * p') := by group
          _ = p * S.z := by rw [h5, inv_eq_of_mul_eq_one_right hpp]
          _ = S.z * p := (S.mem_M_iff.mp hpM)
      rw [← h6]
      exact S.isConj_of_mem_ESet hp'D.1

end Setting

end CFSG.LargeExtraspecial
