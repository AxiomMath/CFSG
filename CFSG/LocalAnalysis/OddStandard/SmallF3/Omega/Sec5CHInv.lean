module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CHFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CHMeet
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CKPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClassModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec5c_inv_class_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {ζ : OGroup Q} (hζ2 : ζ * ζ = 1) (hζ : invType ζ = (4, 1))
    {u : OGroup Q}
    (hu : u ∈ twoRes (omegaGroup hQ ⊓ Subgroup.centralizer ({ζ} : Set (OGroup Q))))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huζ : u ≠ ζ) :
    ∃ c ∈ omegaGroup hQ, c * u * c⁻¹ = piOrth Q * ζ := by
  let D : Om6Par Q ζ := Om6Par.mk' hQ hdim hsgn hζ2 hζ
  obtain ⟨w, hw, hw2, hwt⟩ := sec5c_frame_witness hQ hdim hsgn hζ2 hζ
  have hwd : invDim w = 2 := congrArg Prod.fst hwt
  have hw1 : w ≠ 1 := fun h => by
    have h0 := (invDim_eq_zero_iff hw2).mpr h
    omega
  have hwζ : w ≠ ζ := fun h => by
    have h4 : invDim ζ = 4 := congrArg Prod.fst hζ
    rw [h] at hwd
    omega
  have hLR : D.L ⊔ D.R =
      twoRes (omegaGroup hQ ⊓ Subgroup.centralizer ({ζ} : Set (OGroup Q))) := D.twoRes_eq
  have hP := D.sec5Pair
  obtain ⟨y, hy, hyu⟩ := sec5b513_trans (Classical.choice hP.iso₁) (Classical.choice hP.iso₂)
    hP.comm hP.z_mem₁ hP.z_mem₂ hP.z_sq hP.z_ne (by rw [hLR]; exact hu) hu2 hu1 huζ
    (by rw [hLR]; exact hw) hw2 hw1 hwζ
  have hgΩ : y⁻¹ ∈ omegaGroup hQ :=
    inv_mem (Subgroup.mem_inf.mp (D.le_omega_cent hy)).1
  have hgu : y⁻¹ * u * y⁻¹⁻¹ = w := by rw [inv_inv]; exact hyu
  have hπζ2 : (piOrth Q * ζ) * (piOrth Q * ζ) = 1 := by
    calc piOrth Q * ζ * (piOrth Q * ζ) = piOrth Q * (ζ * piOrth Q) * ζ := by group
      _ = piOrth Q * (piOrth Q * ζ) * ζ := by rw [mul_piOrth_comm ζ]
      _ = (piOrth Q * piOrth Q) * (ζ * ζ) := by group
      _ = 1 := by rw [piOrth_mul_self, hζ2, mul_one]
  have hty : invType w = invType (piOrth Q * ζ) := by
    rw [ff6m_invType_piOrth_mul hQ hdim hsgn hζ2 hζ, hwt]
    exact Prod.ext rfl (by decide)
  obtain ⟨c₂, hc₂, hc₂w⟩ := exists_mem_omegaGroup_conj hQ (by omega) hw2 hπζ2 hty
  refine ⟨c₂ * y⁻¹, mul_mem hc₂ hgΩ, ?_⟩
  calc c₂ * y⁻¹ * u * (c₂ * y⁻¹)⁻¹ = c₂ * (y⁻¹ * u * y⁻¹⁻¹) * c₂⁻¹ := by group
    _ = piOrth Q * ζ := by rw [hgu, hc₂w]

theorem asc82Fact512H_inv_class_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ t : G, orderOf t = 2 → centerIn L = zpowers t → ∀ z : G, IsI4PlusIn L z →
        ∀ u ∈ twoRes (L ⊓ centralizer ({z} : Set G)), orderOf u = 2 → u ≠ z →
          u ∈ conjClassIn L (t * z) := by
  intro G _ _ L hL t ht2 hct z hz u hu hu2 huz
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ, hinj, hsurj⟩ :=
    sec5c_cover_iso hS hL (sec5c_oddCoreIn_bot hL ht2 hct)
  haveI : Finite (OGroup Q) := sec5c_finite_ogroup
  have hΦ := sec5cdPhi_injective hinj
  have hzL : z ∈ L := sec5c_mem_of_isI4PlusIn hz
  obtain ⟨hztt, hzt4⟩ := sec5c_z_model hL hφ hz hzL
  let D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩) :=
    Om6Par.mk' hQ hφ.finrank_eq hφ.quadSign_eq hztt hzt4
  have huL : u ∈ L := sec5cd_twoRes_le inf_le_left hu
  let uL : ↥L := ⟨u, huL⟩
  have hu' : sec5cdPhi φ uL ∈ D.L ⊔ D.R :=
    (sec5cd_mem_twoRes_iff_sup hinj hsurj hzL D uL).mp hu
  have huu : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hu2' : sec5cdPhi φ uL * sec5cdPhi φ uL = 1 := by
    rw [← map_mul, show uL * uL = 1 from Subtype.ext huu, map_one]
  have hu1' : sec5cdPhi φ uL ≠ 1 := by
    intro h
    have h1 : uL = 1 := hΦ (h.trans (map_one _).symm)
    have h2 : u = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hu2
    omega
  have huζ' : sec5cdPhi φ uL ≠ sec5cdPhi φ ⟨z, hzL⟩ := fun h => huz (congrArg Subtype.val (hΦ h))
  have hu'' : sec5cdPhi φ uL ∈ twoRes (omegaGroup hQ ⊓
      Subgroup.centralizer ({sec5cdPhi φ ⟨z, hzL⟩} : Set (OGroup Q))) := by
    rw [← D.twoRes_eq]
    exact hu'
  obtain ⟨c, hcΩ, hc⟩ := sec5c_inv_class_model hQ hφ.finrank_eq hφ.quadSign_eq hztt hzt4 hu''
    hu2' hu1' huζ'
  have htc : t ∈ centerIn L := hct ▸ Subgroup.mem_zpowers t
  have htL : t ∈ L := by
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp htc
    exact hx ▸ x.2
  have hπ : sec5cdPhi φ ⟨t, htL⟩ = piOrth Q := hφ.map_central hL htc ht2 htL
  obtain ⟨c', hc'⟩ := hsurj ⟨c, hcΩ⟩
  have hc'val : sec5cdPhi φ c' = c := congrArg Subtype.val hc'
  have h5 : sec5cdPhi φ (c' * uL * c'⁻¹) = sec5cdPhi φ (⟨t, htL⟩ * ⟨z, hzL⟩) := by
    simp only [map_mul, map_inv, hc'val]
    rw [hc, hπ]
  have h6 : (c' : G) * u * (c' : G)⁻¹ = t * z := congrArg Subtype.val (hΦ h5)
  refine ⟨((c'⁻¹ : ↥L) : G), (c'⁻¹ : ↥L).2, ?_⟩
  rw [← h6, Subgroup.coe_inv]
  group

theorem asc82Fact512H_of (hS : Asc82SchurU43) : Asc82Fact512H :=
  ⟨asc82Fact512H_inv_class_of hS, asc82Fact512H_meet_holds⟩

end CFSG.OddStandard.SmallF3.Omega
