module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sq_sq_eq_one_of_q8_lifts {G : Type} [Group G] {p q r : G}
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

theorem oddCore_centralizer_quaternion_omegaProj (hQ : Q.Nondegenerate)
    (f : QuaternionGroup 2 →* omegaProj hQ) :
    oddCore ↥(Subgroup.centralizer ({f (QuaternionGroup.a 2)} : Set (omegaProj hQ))) = ⊥ := by
  obtain ⟨q, hq⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.a 1))
  obtain ⟨r, hr⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.xa 0))
  obtain ⟨hρqq, hb, hc⟩ := q8_lift_relations hQ hq hr
  have hyy : ((q : OGroup Q) * (q : OGroup Q)) * ((q : OGroup Q) * (q : OGroup Q)) = 1 :=
    sq_sq_eq_one_of_q8_lifts (G := OGroup Q) (p := piOrth Q) (q := (q : OGroup Q))
      (r := (r : OGroup Q)) (fun y => (mul_piOrth_comm y).symm) piOrth_mul_self hb hc
  have hτ : toProj Q ((q : OGroup Q) * (q : OGroup Q)) ∈ omegaProj hQ :=
    (omegaToProj hQ (q * q)).2
  have hy : (⟨toProj Q ((q : OGroup Q) * (q : OGroup Q)), hτ⟩ : omegaProj hQ) =
      f (QuaternionGroup.a 2) := by
    rw [← hρqq]
    rfl
  rw [← hy]
  exact oddCore_centralizer_omegaProj_eq_bot hQ hyy hτ

theorem oddCore_centralizer_quaternion_of_isOmegaStar {Y : Type} [Group Y] {n : ℕ} {ε : ℤˣ}
    (hY : IsOmegaStar Y n ε) (f : QuaternionGroup 2 →* Y) :
    oddCore ↥(Subgroup.centralizer ({f (QuaternionGroup.a 2)} : Set Y)) = ⊥ := by
  obtain ⟨V, i1, i2, i3, Q, hQ, -, -, ⟨e⟩⟩ := hY
  letI := i1
  letI := i2
  letI := i3
  exact oddCore_centralizer_eq_bot_of_mulEquiv e
    (oddCore_centralizer_quaternion_omegaProj hQ (e.toMonoidHom.comp f))

theorem oddCore_centralizer_quaternion_of_smallF3OmegaQuotient {Y : Type} [Group Y]
    (hY : SmallF3OmegaQuotient Y) (f : QuaternionGroup 2 →* Y) :
    oddCore ↥(Subgroup.centralizer ({f (QuaternionGroup.a 2)} : Set Y)) = ⊥ := by
  rcases hY with h | h | h | h | h | h
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_psp h) f
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_psl h) f
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_psu h) f
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_odd h) f
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_plus h) f
  · exact oddCore_centralizer_quaternion_of_isOmegaStar (isOmegaStar_of_lieModel_minus h) f

end CFSG.OddStandard.SmallF3.Omega
