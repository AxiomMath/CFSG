module

public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs

public section

namespace CFSG.CGT.T75A

open CFSG.Open

section Uniqueness

variable {D : Type*} [Group D]

theorem mem_normalizer_of_commute {q k : ℕ} (hB : fusionBenderBorel D q k) (S : Sylow 2 D) {x : D}
    (hxS : x ∈ (S : Subgroup D)) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) {c : D} (hc : c * x = x * c) :
    c ∈ Subgroup.normalizer ((S : Subgroup D) : Set D) := by
  by_contra hcn
  obtain ⟨hSE, -⟩ := hB S
  have hodd := hSE.2.2 c hcn
  have hxM : x ∈ Subgroup.normalizer ((S : Subgroup D) : Set D) := Subgroup.le_normalizer hxS
  have hxM' : x ∈ (Subgroup.normalizer ((S : Subgroup D) : Set D)).map
      (MulAut.conj c⁻¹).toMonoidHom := by
    refine ⟨x, hxM, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.normalizer ((S : Subgroup D) : Set D) ⊓
      (Subgroup.normalizer ((S : Subgroup D) : Set D)).map (MulAut.conj c⁻¹).toMonoidHom) := by
    have hxI : x ∈ Subgroup.normalizer ((S : Subgroup D) : Set D) ⊓
        (Subgroup.normalizer ((S : Subgroup D) : Set D)).map (MulAut.conj c⁻¹).toMonoidHom :=
      ⟨hxM, hxM'⟩
    have h := orderOf_dvd_natCard (⟨x, hxI⟩ : ↥(Subgroup.normalizer ((S : Subgroup D) : Set D) ⊓
      (Subgroup.normalizer ((S : Subgroup D) : Set D)).map (MulAut.conj c⁻¹).toMonoidHom))
    have h2 : orderOf (⟨x, hxI⟩ : ↥(Subgroup.normalizer ((S : Subgroup D) : Set D) ⊓
        (Subgroup.normalizer ((S : Subgroup D) : Set D)).map (MulAut.conj c⁻¹).toMonoidHom)) =
        2 := by
      exact (Subgroup.orderOf_coe _).symm.trans hord
    rwa [h2] at h
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem sylow_eq_of_center_eq {q k : ℕ} (hq : 2 ≤ q) (hB : fusionBenderBorel D q k)
    {S S' : Sylow 2 D}
    (h : (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype =
      (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype) : S' = S := by
  obtain ⟨-, -, hZ2, hZcard, -⟩ := hB S
  have hfin : Finite ↥(Subgroup.center (S : Subgroup D)) :=
    Nat.finite_of_card_ne_zero (by rw [hZcard]; omega)
  have hnt : Nontrivial ↥(Subgroup.center (S : Subgroup D)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hZcard]; omega)
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center (S : Subgroup D)))
  have hxS : ((z : (S : Subgroup D)) : D) ∈ (S : Subgroup D) := (z : (S : Subgroup D)).2
  have hx1 : ((z : (S : Subgroup D)) : D) ≠ 1 := fun hz => hz1 (Subtype.ext (Subtype.ext hz))
  have hx2 : ((z : (S : Subgroup D)) : D) ^ 2 = 1 := congrArg Subtype.val (hZ2 z z.2)
  have hxT : ((z : (S : Subgroup D)) : D) ∈
      (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype := by
    rw [← h]
    exact ⟨z, z.2, rfl⟩
  obtain ⟨w, hw, hwx⟩ := hxT
  have hle : (S' : Subgroup D) ≤ Subgroup.normalizer ((S : Subgroup D) : Set D) := by
    intro s hs
    refine mem_normalizer_of_commute hB S hxS hx1 hx2 ?_
    have hcomm := Subgroup.mem_center_iff.1 hw ⟨s, hs⟩
    have := congrArg Subtype.val hcomm
    change s * ((w : (S' : Subgroup D)) : D) = ((w : (S' : Subgroup D)) : D) * s at this
    rw [← hwx]
    exact this
  have hsub : (S' : Subgroup D) ≤ (S : Subgroup D) := by
    have h1 : (S' : Subgroup D) ⊓ Subgroup.normalizer ((S : Subgroup D) : Set D) =
        (S' : Subgroup D) ⊓ (S : Subgroup D) := IsPGroup.inf_normalizer_sylow S'.2 S
    rw [inf_eq_left.2 hle] at h1
    exact inf_eq_left.1 h1.symm
  exact Sylow.ext (S'.3 S.2 hsub).symm

end Uniqueness

end CFSG.CGT.T75A
