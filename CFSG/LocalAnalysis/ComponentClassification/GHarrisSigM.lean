module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigV
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisP312

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

theorem SCert.SE.predE_of_predV {s : SE} (h : SE.predV s) : SE.predE s :=
  ⟨by rw [h.1]; decide, h.2.2.1, h.2.2.2⟩

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem exists_OM_conj_of_piM {m : G} (hm : m ∈ D.M) {e₀ : SE}
    (he : D.toMb.toG e₀ = D.piM ⟨m, hm⟩ * D.toMb.t * (D.piM ⟨m, hm⟩)⁻¹) :
    ∃ o ∈ D.OM, o * D.toG e₀ * o⁻¹ = m * D.t * m⁻¹ ∧ e₀ * e₀ = 1 := by
  have htM : D.t ∈ D.M := D.S_le_M (D.toG_mem _)
  set u : ↥D.M := ⟨m, hm⟩ * ⟨D.t, htM⟩ * ⟨m, hm⟩⁻¹ with hu
  set v : ↥D.M := ⟨D.toG e₀, D.S_le_M (D.toG_mem _)⟩ with hv
  have huv : D.piM u = D.piM v := by
    rw [hu, map_mul, map_mul, map_inv]
    exact he.symm
  have hu2 : u * u = 1 := by
    rw [hu, show (⟨m, hm⟩ : ↥D.M) * ⟨D.t, htM⟩ * (⟨m, hm⟩ : ↥D.M)⁻¹ *
      ((⟨m, hm⟩ : ↥D.M) * ⟨D.t, htM⟩ * (⟨m, hm⟩ : ↥D.M)⁻¹) =
      (⟨m, hm⟩ : ↥D.M) * (⟨D.t, htM⟩ * ⟨D.t, htM⟩) * (⟨m, hm⟩ : ↥D.M)⁻¹ by group,
      show (⟨D.t, htM⟩ : ↥D.M) * ⟨D.t, htM⟩ = 1 from Subtype.ext D.t_mul_t, mul_one,
      mul_inv_cancel]
  have he2 : e₀ * e₀ = 1 := by
    apply D.toMb.toG_injective
    rw [map_mul, map_one, he, show D.piM ⟨m, hm⟩ * D.toMb.t * (D.piM ⟨m, hm⟩)⁻¹ = D.piM u by
      rw [hu, map_mul, map_mul, map_inv]; rfl, ← map_mul, hu2, map_one]
  have hv2 : v * v = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, he2, map_one]; rfl)
  obtain ⟨o, hoO, ho⟩ := D.exists_conj_OM hu2 hv2 huv
  refine ⟨o, ⟨o, hoO, rfl⟩, ?_, he2⟩
  have h := congrArg Subtype.val ho
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu, hv] at h
  calc (o : G) * D.toG e₀ * (o : G)⁻¹
      = (o : G) * ((o : G)⁻¹ * (m * D.t * m⁻¹) * o) * (o : G)⁻¹ := by rw [h]
    _ = m * D.t * m⁻¹ := by group

omit [Finite G]
  in
theorem toG_ne_of_conj_t {m o : G} (hm : m ∈ D.M) (ho : o ∈ D.M) {e₀ : SE}
    (h : o * D.toG e₀ * o⁻¹ = m * D.t * m⁻¹) : e₀ ≠ 1 ∧ e₀ ≠ SE.gen 0 := by
  constructor
  · rintro rfl
    rw [map_one, mul_one, mul_inv_cancel] at h
    exact D.t_ne_one (by
      calc D.t = m⁻¹ * (m * D.t * m⁻¹) * m := by group
        _ = 1 := by rw [← h]; group)
  · rintro rfl
    have hz := D.z_comm_of_mem_M (inv_mem ho)
    rw [inv_inv] at hz
    change o * D.z * o⁻¹ = m * D.t * m⁻¹ at h
    rw [hz] at h
    exact D.z_ne_t (by
      have hz' := D.z_comm_of_mem_M hm
      calc D.z = m⁻¹ * D.z * m := hz'.symm
        _ = m⁻¹ * (m * D.t * m⁻¹) * m := by rw [h]
        _ = D.t := by group)

theorem M_le_H_B (hC : GorensteinHaradaThmCInput) (hB : D.caseB) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) : D.M ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨-, hEt, hFt, -⟩ := D.toMb.prop38B_of hC D.pPrimeCore_Mb D.z_comm_Mb hB
  have hEn := D.toMb.E_normal_of D.pPrimeCore_Mb D.z_comm_Mb hEt
  have hFn := D.toMb.F_normal_of D.pPrimeCore_Mb D.z_comm_Mb hFt
  refine D.M_le_H_of hC h10 h20 fun m hm => ?_
  have htE : D.toMb.t ∈ D.toMb.E := D.toMb.toG_mem_E_iff.mpr (by decide)
  have htF : D.toMb.t ∈ D.toMb.F := D.toMb.toG_mem_F_iff.mpr (by decide)
  obtain ⟨e₀, he₀E, he₀⟩ := hEn.conj_mem _ htE (D.piM ⟨m, hm⟩)
  obtain ⟨f₀, hf₀F, hf₀⟩ := hFn.conj_mem _ htF (D.piM ⟨m, hm⟩)
  have hef : e₀ = f₀ := D.toMb.toG_injective (he₀.trans hf₀.symm)
  subst hef
  obtain ⟨o, ho, hoe, he2⟩ := D.exists_OM_conj_of_piM hm he₀
  obtain ⟨he1, hez⟩ := D.toG_ne_of_conj_t hm (D.OM_le_M ho) hoe
  have hV : SE.predV e₀ := SE.predV_of_E_F e₀ he₀E hf₀F he2
  have he : D.toG e₀ * D.toG e₀ = 1 := by rw [← map_mul, he2, map_one]
  have hze : D.z * D.toG e₀ = D.toG e₀ * D.z := by
    rw [← map_mul, ← map_mul, show SE.gen 0 * e₀ = e₀ * SE.gen 0 from
      (SE.mul_gen0_comm e₀).symm]
  refine ⟨o, ho, D.toG e₀, he, hze, hoe, (D.sigW_V_eq hC h10 h20
    (klein_le D.z_mem_V ((D.toG_mem_V_iff).mpr hV)) ?_).symm⟩
  exact (card_klein D.z_mul_z D.z_ne_one (fun h => he1 (D.toG_eq_one_iff.mp h))
    (fun h => hez (D.toG_injective h))).ge

theorem conj_z_of_mem_E_A (hC : GorensteinHaradaThmCInput) (hA : ¬ D.caseB) (h10 : D.FusN 1 0)
    {ℓ : G} (hℓ : ℓ ∈ D.E) (hℓ2 : ℓ * ℓ = 1) (hℓ1 : ℓ ≠ 1) : ∃ g : G, g⁻¹ * D.z * g = ℓ := by
  by_cases hℓz : ℓ = D.z
  · exact ⟨1, by rw [hℓz]; group⟩
  obtain ⟨m', -, hm'⟩ := D.conj_t_of_mem_E_A hC hA hℓ hℓ2 hℓ1 hℓz
  obtain ⟨g₁, hg₁⟩ := h10
  rw [show SE.invRep (Fin.ofNat 9 0) = SE.gen 0 by decide,
    show Fin.ofNat 9 1 = 1 by decide] at hg₁
  have hg₁' : g₁⁻¹ * D.t * g₁ = D.z := hg₁
  refine ⟨g₁⁻¹ * m', ?_⟩
  rw [← hm', ← hg₁']
  group

theorem M_le_H_A (hC : GorensteinHaradaThmCInput) (hA : ¬ D.caseB) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) : D.M ≤ normalizer (sigW D.V : Set G) := by
  have hEn := D.toMb.E_normal_Y hC D.pPrimeCore_Mb D.z_comm_Mb
  refine D.M_le_H_of hC h10 h20 fun m hm => ?_
  have htE : D.toMb.t ∈ D.toMb.E := D.toMb.toG_mem_E_iff.mpr (by decide)
  obtain ⟨e₀, he₀E, he₀⟩ := hEn.conj_mem _ htE (D.piM ⟨m, hm⟩)
  obtain ⟨o, ho, hoe, he2⟩ := D.exists_OM_conj_of_piM hm he₀
  obtain ⟨he1, hez⟩ := D.toG_ne_of_conj_t hm (D.OM_le_M ho) hoe
  have he : D.toG e₀ * D.toG e₀ = 1 := by rw [← map_mul, he2, map_one]
  have hze : D.z * D.toG e₀ = D.toG e₀ * D.z := by
    rw [← map_mul, ← map_mul, show SE.gen 0 * e₀ = e₀ * SE.gen 0 from
      (SE.mul_gen0_comm e₀).symm]
  have hcard : 4 ≤ Nat.card (klein D.z (D.toG e₀) he hze) :=
    (card_klein D.z_mul_z D.z_ne_one (fun h => he1 (D.toG_eq_one_iff.mp h))
      (fun h => hez (D.toG_injective h))).ge
  refine ⟨o, ho, D.toG e₀, he, hze, hoe, ?_⟩
  rcases SE.partner_V e₀ he₀E he2 he1 hez with hV | ⟨w₀, hw₀, hw1, hwz, hew, hne, hnez⟩
  · exact (D.sigW_V_eq hC h10 h20 (klein_le D.z_mem_V ((D.toG_mem_V_iff).mpr hV)) hcard).symm
  · have hwV : D.toG w₀ ∈ D.V := (D.toG_mem_V_iff).mpr (SE.predV_of_mem_Vlist w₀ hw₀)
    have hw : D.toG w₀ * D.toG w₀ = 1 := by
      rw [← map_mul, SE.sq_of_mem_Vlist w₀ hw₀, map_one]
    have hzw : D.z * D.toG w₀ = D.toG w₀ * D.z := by
      rw [← map_mul, ← map_mul, show SE.gen 0 * w₀ = w₀ * SE.gen 0 from
        (SE.mul_gen0_comm w₀).symm]
    have hwe : D.toG w₀ * D.toG e₀ = D.toG e₀ * D.toG w₀ := by
      rw [← map_mul, ← map_mul, hew]
    set L := e8 D.z (D.toG w₀) (D.toG e₀) hw hzw he hze hwe with hL
    have heK : D.toG e₀ ∉ klein D.z (D.toG w₀) hw hzw := by
      intro h
      rcases (mem_extInv.mp h) with h | h
      · rcases eq_one_or_of_mem_zpowers D.z_mul_z h with h | h
        · exact he1 (D.toG_eq_one_iff.mp h)
        · exact hez (D.toG_injective h)
      · rcases eq_one_or_of_mem_zpowers D.z_mul_z h with h | h
        · exact hne (D.toG_injective (by
            calc D.toG e₀ = D.toG e₀ * D.toG w₀ * D.toG w₀ := by rw [mul_assoc, hw, mul_one]
              _ = D.toG w₀ := by rw [h, one_mul]))
        · exact hnez (D.toG_injective (by
            rw [map_mul]
            calc D.toG e₀ = D.toG e₀ * D.toG w₀ * D.toG w₀ := by rw [mul_assoc, hw, mul_one]
              _ = D.z * D.toG w₀ := by rw [h]))
    have hL8 : 8 ≤ Nat.card L :=
      (card_e8 D.z_mul_z D.z_ne_one (fun h => hw1 (D.toG_eq_one_iff.mp h))
        (fun h => hwz (D.toG_injective h)) heK).ge
    have hLE : L ≤ D.E := e8_le D.z_mem_E
      ((D.toG_mem_E_iff).mpr (SE.predE_of_predV (SE.predV_of_mem_Vlist w₀ hw₀)))
      ((D.toG_mem_E_iff).mpr he₀E)
    have hLab : IsElemAbelian 2 L := isElemAbelian_e8 D.z_mul_z
    have hLch : CharTwoAt L := charTwoAt_of_conj (D.isCharacteristicP_Mb hC) fun ℓ hℓ hℓ1 =>
      D.conj_z_of_mem_E_A hC hA h10 (hLE hℓ) (by rw [← pow_two]; exact hLab.2 ℓ hℓ) hℓ1
    have h1 := sigW_eq_sigW4 hLab hL8 hLch (klein_le (klein_le_e8 mem_klein_left)
      mem_e8_right) hcard
    have h2 := sigW_eq_sigW4 hLab hL8 hLch klein_le_e8
      (card_klein (hb := hw) (hab := hzw) D.z_mul_z D.z_ne_one
        (fun h => hw1 (D.toG_eq_one_iff.mp h)) (fun h => hwz (D.toG_injective h))).ge
    rw [← h1, h2, ← D.sigW_V_eq hC h10 h20 (klein_le D.z_mem_V hwV)
      (card_klein D.z_mul_z D.z_ne_one (fun h => hw1 (D.toG_eq_one_iff.mp h))
        (fun h => hwz (D.toG_injective h))).ge]

theorem M_le_H (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) :
    D.M ≤ normalizer (sigW D.V : Set G) := by
  by_cases hB : D.caseB
  · exact D.M_le_H_B hC hB h10 h20
  · exact D.M_le_H_A hC hB h10 h20

end GHSylow

end CFSG.ComponentClassification.GHarris
