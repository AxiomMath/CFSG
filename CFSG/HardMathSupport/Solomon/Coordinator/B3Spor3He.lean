module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.Sporadic.HeldB.CertPBridge
public import Certificates.Certificate13515
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3
  CFSG.Sporadic.HeldB

theorem map_conj_centralizer_inf_pow {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    {X k : Equiv.Perm (Fin n)} (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2) :
    (Subgroup.centralizer {X} ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer {k * X ^ e * k⁻¹} ⊓ P := by
  have hXe : (X ^ e) ^ e = X := by
    rcases he with rfl | rfl
    · simp
    · calc (X ^ 2) ^ 2 = X ^ 3 * X := by group
        _ = X := by rw [hX3, one_mul]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
    have hz : z * X ^ e = X ^ e * z := (Commute.pow_right (show Commute z X from hzc) e).eq
    refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
    calc k * z * k⁻¹ * (k * X ^ e * k⁻¹) = k * (z * X ^ e) * k⁻¹ := by group
      _ = k * (X ^ e * z) * k⁻¹ := by rw [hz]
      _ = k * X ^ e * k⁻¹ * (k * z * k⁻¹) := by group
  · rintro ⟨hyc, hyP⟩
    refine ⟨k⁻¹ * y * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hyP) hk⟩, by group⟩
    have h1 : k⁻¹ * y * k * X ^ e = X ^ e * (k⁻¹ * y * k) := by
      calc k⁻¹ * y * k * X ^ e = k⁻¹ * (y * (k * X ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * X ^ e * k⁻¹) * y) * k := by rw [hyc]
        _ = X ^ e * (k⁻¹ * y * k) := by group
    have h3 := Commute.pow_right (show Commute (k⁻¹ * y * k) (X ^ e) from h1) e
    rw [hXe] at h3
    exact h3.eq

theorem he3_card {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heP)
    (hxo : orderOf x = 3) :
    Nat.card ↥(Subgroup.centralizer {x} ⊓ heP) = 7560 ∨
      Nat.card ↥(Subgroup.centralizer {x} ⊓ heP) = 504 := by
  have hP := Certificates.certificate13515
  obtain ⟨c, hc, k, hk, e, he, rfl⟩ := hP.1 x hx hxo
  have hX3 := (hP.2.1 c hc).2.1 ▸ pow_orderOf_eq_one (CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[c]!)
  rw [← map_conj_centralizer_inf_pow hX3 hk he,
    Subgroup.card_map_of_injective (MulAut.conj k).injective]
  interval_cases c
  · exact Or.inl hP.2.2.1
  · exact Or.inr hP.2.2.2.1

theorem he3_core {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heP)
    (hxo : orderOf x = 3) :
    CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer {x} ⊓ heP) = ⊥ := by
  have hP := Certificates.certificate13515
  obtain ⟨c, hc, k, hk, e, he, rfl⟩ := hP.1 x hx hxo
  have hX3 := (hP.2.1 c hc).2.1 ▸ pow_orderOf_eq_one (CFSG.Monster.B.Co2.permOfArr 8330 heS3CaseX[c]!)
  rw [← map_conj_centralizer_inf_pow hX3 hk he, ← map_glaPPrimeCoreOf_of_injective 3 _
    (MulAut.conj k).injective, (hP.2.1 c hc).2.2, Subgroup.map_bot]

theorem b3Phi_he :
    ∀ x : ↥heP, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) := by
  apply b3Phi_centralizer_of_perm
  exact fun x hx hxo => b3Phi_of_oPrime (he3_core hx hxo)

theorem b3SporPair_He_three
    (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .He 3 :=
  let e : CFSG.Blueprint.NativeSporadic.He ≃* ↥heP := heEquivP
  b3SporPair_of_model hOut ↥heP ⟨e.symm.trans (hbr .He).some⟩ b3Phi_he

end CFSG.HardMathSupport.Solomon.Coordinator
