module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem m6z_sq_sq_eq_one_of_q8_lifts {G : Type} [Group G] {p q r : G}
    (hp : ∀ y, p * y = y * p) (hpp : p * p = 1)
    (hb : r * r = q * q ∨ r * r = p * (q * q))
    (hc : r * q = q⁻¹ * r ∨ r * q = p * (q⁻¹ * r)) : (q * q) * (q * q) = 1 := by
  obtain ⟨z1, hz1, hqr⟩ : ∃ z1 : G, (∀ y, z1 * y = y * z1) ∧ q * q = (r * r) * z1 := by
    rcases hb with h | h
    · exact ⟨1, fun y => by simp, by rw [mul_one, h]⟩
    · refine ⟨p, hp, ?_⟩
      calc q * q = (p * p) * (q * q) := by rw [hpp, one_mul]
        _ = p * (p * (q * q)) := mul_assoc _ _ _
        _ = p * ((q * q) * p) := by rw [hp (q * q)]
        _ = (p * (q * q)) * p := (mul_assoc _ _ _).symm
        _ = (r * r) * p := by rw [h]
  obtain ⟨z2, hz2, hz2sq, hrq⟩ :
      ∃ z2 : G, (∀ y, z2 * y = y * z2) ∧ z2 * z2 = 1 ∧ r * q * r⁻¹ = q⁻¹ * z2 := by
    rcases hc with h | h
    · exact ⟨1, fun y => by simp, mul_one 1, by rw [h]; group⟩
    · refine ⟨p, hp, hpp, ?_⟩
      calc r * q * r⁻¹ = p * (q⁻¹ * r) * r⁻¹ := by rw [h]
        _ = p * q⁻¹ := by group
        _ = q⁻¹ * p := hp q⁻¹
  have hconj : r * (q * q) * r⁻¹ = q * q := by
    calc r * (q * q) * r⁻¹
        = r * ((r * r) * z1) * r⁻¹ := by rw [← hqr]
      _ = (r * (r * r) * r⁻¹) * (r * z1 * r⁻¹) := by group
      _ = r * r * z1 := by
            rw [show r * (r * r) * r⁻¹ = r * r from by group,
                show r * z1 * r⁻¹ = z1 from by rw [← hz1 r]; group]
      _ = q * q := hqr.symm
  have hconj2 : r * (q * q) * r⁻¹ = (q * q)⁻¹ * (z2 * z2) := by
    have hsq : r * (q * q) * r⁻¹ = (q⁻¹ * z2) * (q⁻¹ * z2) := by
      calc r * (q * q) * r⁻¹
          = (r * q * r⁻¹) * (r * q * r⁻¹) := by group
        _ = (q⁻¹ * z2) * (q⁻¹ * z2) := by rw [hrq]
    rw [hsq]
    calc (q⁻¹ * z2) * (q⁻¹ * z2)
        = q⁻¹ * (z2 * q⁻¹) * z2 := by group
      _ = q⁻¹ * (q⁻¹ * z2) * z2 := by rw [hz2 q⁻¹]
      _ = (q * q)⁻¹ * (z2 * z2) := by group
  have hseq : q * q = (q * q)⁻¹ := by
    have h := hconj.symm.trans hconj2
    rw [hz2sq, mul_one] at h
    exact h
  exact (mul_eq_one_iff_eq_inv).mpr hseq

theorem m6z_exists_q8_lift (hQ : Q.Nondegenerate) {f : QuaternionGroup 2 →* omegaProj hQ}
    (hf : Function.Injective f) :
    ∃ q r : omegaGroup hQ, omegaToProj hQ (q * q) = f (QuaternionGroup.a 2) ∧
      ((q : OGroup Q) * q) * ((q : OGroup Q) * q) = 1 ∧ (q : OGroup Q) * q ≠ 1 ∧
      (q : OGroup Q) * q ≠ piOrth Q ∧
      ((r : OGroup Q) * r = (q : OGroup Q) * q ∨
        (r : OGroup Q) * r = piOrth Q * ((q : OGroup Q) * q)) ∧
      ((r : OGroup Q) * q = (q : OGroup Q)⁻¹ * r ∨
        (r : OGroup Q) * q = piOrth Q * ((q : OGroup Q)⁻¹ * r)) := by
  have ha2ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel
  have ha2 : f (QuaternionGroup.a 2) ≠ 1 := fun h => ha2ne (hf (by rw [h, map_one]))
  obtain ⟨q, hq⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.a 1))
  obtain ⟨r, hr⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.xa 0))
  obtain ⟨hρqq, hb, hc⟩ := q8_lift_relations hQ hq hr
  have hyy : ((q : OGroup Q) * (q : OGroup Q)) * ((q : OGroup Q) * (q : OGroup Q)) = 1 :=
    m6z_sq_sq_eq_one_of_q8_lifts (G := OGroup Q) (p := piOrth Q) (q := (q : OGroup Q))
      (r := (r : OGroup Q)) (fun y => (mul_piOrth_comm y).symm) piOrth_mul_self hb hc
  have hy1 : (q : OGroup Q) * (q : OGroup Q) ≠ 1 := fun h =>
    ha2 (hρqq.symm.trans ((omegaToProj_eq_one_iff hQ (q * q)).mpr (Or.inl h)))
  have hyπ : (q : OGroup Q) * (q : OGroup Q) ≠ piOrth Q := fun h =>
    ha2 (hρqq.symm.trans ((omegaToProj_eq_one_iff hQ (q * q)).mpr (Or.inr h)))
  exact ⟨q, r, hρqq, hyy, hy1, hyπ, hb, hc⟩

end CFSG.OddStandard.SmallF3.Omega
