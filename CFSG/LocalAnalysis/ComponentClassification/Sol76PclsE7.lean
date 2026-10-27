module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsLinear
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.Isogeny.E7

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.CurtisTits

variable {Q : Type} [Group Q] [Finite Q]

theorem minTorus_e7_not_mem_center
    {K : Type} [Field K]
    {u : Fin (Tag.rank .E7) → Kˣ} (hu : u ⟨0, by decide⟩ ≠ 1 ∨ u ⟨2, by decide⟩ ≠ 1) :
    minTorus e7Data_valid K u ∉ center ↥(e7Data_valid.minGroup K) := by
  rw [minTorus_mem_center_iff]
  intro hc
  have h0 := eq_zpow_of_mem_centerChars e7C_spec hc ⟨0, by decide⟩
  have h2 := eq_zpow_of_mem_centerChars e7C_spec hc ⟨2, by decide⟩
  have e0 : e7c ⟨0, by decide⟩ = 0 := by decide
  have e2 : e7c ⟨2, by decide⟩ = 0 := by decide
  rw [e0, zpow_zero] at h0
  rw [e2, zpow_zero] at h2
  exact hu.elim (· h0) (· h2)

theorem three_le_pRank_of_E7
    (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) {K : Type}
    [Field K] [Finite K] (hK : ringChar K ≠ 2) (e : Q ⧸ center Q ≃* AdjointQuotient .E7 K) :
    3 ≤ CFSG.pRank 2 Q := by
  set πQ := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQs : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerQ := ker_quotientMap e
  have h2Q : IsPGroup 2 πQ.ker := hkerQ ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  set πG : ↥(e7Data_valid.minGroup K) →* AdjointQuotient .E7 K :=
    (QuotientGroup.mk' _).comp (e7Isogeny K) with hπG
  have hπG1 : ∀ x, πG x = 1 → x ∈ center ↥(e7Data_valid.minGroup K) := by
    intro x hx
    have hx' : e7Isogeny K x ∈ center ↥(adjointGroup .E7 K) := (QuotientGroup.eq_one_iff _).mp hx
    rw [center_adjointGroup_eq_bot, mem_bot] at hx'
    exact ker_le_center_of_isQuasisimple (isQuasisimple_e7 K) (exists_e7Isogeny_ne_one K) hx'
  have : Finite ↥(e7Data_valid.minGroup K) := by
    have : Finite (Module.End K (Fin e7Data.d →₀ K)) := Module.finite_of_finite K
    infer_instance
  obtain ⟨σ, hσ, -, -⟩ := LieType.Steinberg.e7_central_two_extension_splitting hK
    (pullbackFst_surjective (πG := πG) hπQs) (pullbackFst_ker_le_center hkerQ.le)
    (isPGroup_pullbackFst_ker h2Q)
  obtain ⟨τ, hτ⟩ := exists_lift_of_section hσ
  have hn1 : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using congrArg Units.val h)
  set i0 : Fin (Tag.rank .E7) := ⟨0, by decide⟩
  set i2 : Fin (Tag.rank .E7) := ⟨2, by decide⟩
  have h02 : i0 ≠ i2 := by decide
  set T := minTorus e7Data_valid K with hT
  have hsq : ∀ i : Fin (Tag.rank .E7), T (Pi.mulSingle i (-1)) * T (Pi.mulSingle i (-1)) = 1 :=
    fun i => by rw [← map_mul, ← Pi.mulSingle_mul, neg_one_mul, neg_neg, Pi.mulSingle_one,
      map_one]
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  refine three_le_pRank_of_four_group hτ (hsq i0) (hsq i2)
    (by rw [← map_mul, mul_comm, map_mul]) (fun h => ?_) (fun h => ?_) (fun h => ?_) hzZ hzz hz1
    (by rw [← MonoidHom.mem_ker, hkerQ]; exact hzZ)
  · exact minTorus_e7_not_mem_center (Or.inl (by rw [Pi.mulSingle_eq_same]; exact hn1))
      (hπG1 _ h)
  · exact minTorus_e7_not_mem_center (Or.inr (by rw [Pi.mulSingle_eq_same]; exact hn1))
      (hπG1 _ h)
  · rw [← map_mul] at h
    refine minTorus_e7_not_mem_center (Or.inl ?_) (hπG1 _ h)
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h02, mul_one]
    exact hn1

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
