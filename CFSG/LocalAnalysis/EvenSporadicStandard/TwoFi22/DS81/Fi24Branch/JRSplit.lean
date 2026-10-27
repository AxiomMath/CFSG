module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.JRBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.GenericSplit

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure RSplit (t z : G) : Prop where
  card_R : Nat.card ↥(Rg t z) = 2 ^ 13
  R_inf_K : Rg t z ⊓ Kg t z = OKg t z
  R_normal : ∀ j ∈ Jg t z, ∀ r ∈ Rg t z, j * r * j⁻¹ ∈ Rg t z
  cent_RK : ∀ r ∈ Rg t z, ∀ k ∈ Kg t z, r * k * r⁻¹ * k⁻¹ ∈ OKg t z
  quot : ∃ (X : Type) (_ : Group X) (π : ↥(Jg t z) →* X), Function.Surjective π ∧
    π.ker = (Rg t z).subgroupOf (Jg t z) ∧ IsU42Two X

@[expose] def C1g {t z : G} (hJ : JBasic t z) : Subgroup G where
  carrier := {j | j ∈ Jg t z ∧ ∀ k ∈ Kg t z, j * k * j⁻¹ * k⁻¹ ∈ OKg t z}
  one_mem' := ⟨(Jg t z).one_mem, fun k _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxJ, hx⟩ ⟨hyJ, hy⟩
    refine ⟨(Jg t z).mul_mem hxJ hyJ, fun k hk => ?_⟩
    have h1 : x * y * k * (x * y)⁻¹ * k⁻¹ =
        (x * (y * k * y⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹) := by group
    rw [h1]
    exact (OKg t z).mul_mem (hJ.conj_OK x hxJ _ (hy k hk)) (hx k hk)
  inv_mem' := by
    rintro x ⟨hxJ, hx⟩
    refine ⟨(Jg t z).inv_mem hxJ, fun k hk => ?_⟩
    have h1 : x⁻¹ * k * (x⁻¹)⁻¹ * k⁻¹ =
        (x⁻¹ * (x * k * x⁻¹ * k⁻¹) * x)⁻¹ := by group
    rw [h1]
    exact (OKg t z).inv_mem (by
      simpa using hJ.conj_OK x⁻¹ ((Jg t z).inv_mem hxJ) (x * k * x⁻¹ * k⁻¹) (hx k hk))

theorem rSplit {t z : G} (hJ : JBasic t z) (hKD : KData t z) (hU : U42Facts) : RSplit t z := by
  obtain ⟨X, hXgrp, π, hπ, hker, hXU⟩ := hKD.quot
  letI : Group X := hXgrp
  obtain ⟨hsplit1, hsplit2⟩ := split_of_complete (J := Jg t z) (K := Kg t z) (O := OKg t z)
    (Kg_le_Jg t z) (OKg_le_Kg t z) hJ.conj_K hJ.conj_OK π hπ hker
    (hU.center_bot X hXU) (hU.complete X hXU)
  have hKJn : ((Kg t z).subgroupOf (Jg t z)).Normal :=
    (Subgroup.normal_subgroupOf_iff (Kg_le_Jg t z)).mpr
      (fun h k hh hk => hJ.conj_K k hk h hh)
  haveI := hKJn
  have hRJn : ((Rg t z).subgroupOf (Jg t z)).Normal := TwoB.normal_subgroupOf_O2In (Jg t z)
  haveI := hRJn
  have hOnK : ((OKg t z).subgroupOf (Kg t z)).Normal := TwoB.normal_subgroupOf_O2In (Kg t z)
  have hO_le_C1 : OKg t z ≤ C1g hJ := by
    intro o ho
    refine ⟨Kg_le_Jg t z (OKg_le_Kg t z ho), fun k hk => ?_⟩
    have hko : k * o * k⁻¹ ∈ OKg t z := by
      have h := hOnK.conj_mem (⟨o, OKg_le_Kg t z ho⟩ : ↥(Kg t z))
        (by rw [Subgroup.mem_subgroupOf]; exact ho) ⟨k, hk⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa only [OKg, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h
    have e : o * k * o⁻¹ * k⁻¹ = o * (k * o * k⁻¹)⁻¹ := by group
    rw [e]
    exact (OKg t z).mul_mem ho ((OKg t z).inv_mem hko)
  have hC1K_eq_O : C1g hJ ⊓ Kg t z = OKg t z := by
    refine le_antisymm ?_ (le_inf hO_le_C1 (OKg_le_Kg t z))
    rintro x ⟨hxC1, hxK⟩
    exact hsplit2 x hxK hxC1.2
  have hdecomp : ∀ j ∈ Jg t z, ∃ k ∈ Kg t z, ∃ c ∈ C1g hJ, j = k * c := by
    intro j hj
    obtain ⟨k, hk, hc⟩ := hsplit1 j hj
    exact ⟨k, hk, k⁻¹ * j, ⟨(Jg t z).mul_mem ((Jg t z).inv_mem (Kg_le_Jg t z hk)) hj, hc⟩,
      by group⟩
  have hC1_card : Nat.card ↥(C1g hJ) = 2 ^ 13 := by
    have hmap_top : ((C1g hJ).subgroupOf (Jg t z)).map
        (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z))) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, c, hc, hxc⟩ := hdecomp x x.2
      refine Subgroup.mem_map.mpr ⟨⟨c, hc.1⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
      have hx : x = (⟨k, Kg_le_Jg t z hk⟩ : ↥(Jg t z)) * ⟨c, hc.1⟩ := Subtype.ext hxc
      have hk1 : (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z)))
          ⟨k, Kg_le_Jg t z hk⟩ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
        exact hk
      change (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z))) ⟨c, hc.1⟩ =
        (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z))) x
      rw [hx, map_mul, hk1, one_mul]
    have hrel2 : ((Kg t z).subgroupOf (Jg t z)).relIndex
        ((C1g hJ).subgroupOf (Jg t z)) = 2 := by
      rw [← QuotientGroup.ker_mk' ((Kg t z).subgroupOf (Jg t z)), Subgroup.relIndex_ker,
        hmap_top, Subgroup.card_top, ← Subgroup.index_eq_card]
      simpa only [Subgroup.relIndex] using hJ.relIndex_KJ
    have hinf : (OKg t z).relIndex (C1g hJ) = (Kg t z).relIndex (C1g hJ) := by
      rw [← hC1K_eq_O]
      exact Subgroup.inf_relIndex_left (C1g hJ) (Kg t z)
    have hsub : ((Kg t z).subgroupOf (Jg t z)).relIndex ((C1g hJ).subgroupOf (Jg t z)) =
        (Kg t z).relIndex (C1g hJ) :=
      Subgroup.relIndex_subgroupOf (H := Kg t z) (K := C1g hJ) (L := Jg t z)
        (fun c hc => hc.1)
    have hrel : (OKg t z).relIndex (C1g hJ) = 2 := hinf.trans (hsub.symm.trans hrel2)
    have hmul := Subgroup.relIndex_mul_card (H := OKg t z) (K := C1g hJ)
    rw [inf_of_le_left hO_le_C1, hrel, hKD.card_OK] at hmul
    rw [← hmul]
    norm_num
  have hC1_normal : ∀ j ∈ Jg t z, ∀ c ∈ C1g hJ, j * c * j⁻¹ ∈ C1g hJ := by
    intro j hj c hc
    refine ⟨(Jg t z).mul_mem ((Jg t z).mul_mem hj hc.1) ((Jg t z).inv_mem hj), fun k hk => ?_⟩
    have hk' : j⁻¹ * k * j ∈ Kg t z := by
      simpa using hJ.conj_K j⁻¹ ((Jg t z).inv_mem hj) k hk
    have hmem := hJ.conj_OK j hj (c * (j⁻¹ * k * j) * c⁻¹ * (j⁻¹ * k * j)⁻¹) (hc.2 _ hk')
    have e : (j * c * j⁻¹) * k * (j * c * j⁻¹)⁻¹ * k⁻¹
        = j * (c * (j⁻¹ * k * j) * c⁻¹ * (j⁻¹ * k * j)⁻¹) * j⁻¹ := by group
    rw [e]
    exact hmem
  have hC1_le_J : C1g hJ ≤ Jg t z := fun c hc => hc.1
  haveI hC1n : ((C1g hJ).subgroupOf (Jg t z)).Normal :=
    (Subgroup.normal_subgroupOf_iff hC1_le_J).mpr (fun h k hh hk => hC1_normal k hk h hh)
  have hC1_pgroup : IsPGroup 2 (C1g hJ) := IsPGroup.of_card hC1_card
  have hC1_le_R : C1g hJ ≤ Rg t z := TwoB.le_O2In hC1_le_J hC1n hC1_pgroup
  have hR_normal : ∀ j ∈ Jg t z, ∀ r ∈ Rg t z, j * r * j⁻¹ ∈ Rg t z := by
    intro j hj r hr
    have h := (TwoB.normal_subgroupOf_O2In (Jg t z)).conj_mem
      (⟨r, TwoB.O2In_le (Jg t z) hr⟩ : ↥(Jg t z))
      (by rw [Subgroup.mem_subgroupOf]; exact hr) ⟨j, hj⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa only [Rg, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h
  have hRK_le_O : Rg t z ⊓ Kg t z ≤ OKg t z := by
    refine TwoB.le_O2In inf_le_right ?_ ((TwoB.isPGroup_O2In (Jg t z)).to_le inf_le_left)
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun h k hh hk => ?_
    exact ⟨hR_normal k (Kg_le_Jg t z hk) h hh.1,
      (Kg t z).mul_mem ((Kg t z).mul_mem hk hh.2) ((Kg t z).inv_mem hk)⟩
  have hrel_RK : ((Rg t z) ⊓ (Kg t z)).relIndex (Rg t z) ≤ 2 := by
    have h1 : ((Rg t z) ⊓ (Kg t z)).relIndex (Rg t z) =
        ((Kg t z).subgroupOf (Jg t z)).relIndex ((Rg t z).subgroupOf (Jg t z)) := by
      rw [← Subgroup.relIndex_subgroupOf (Rg_le_Jg t z) (H := (Rg t z) ⊓ (Kg t z))]
      have heq : ((Rg t z) ⊓ (Kg t z)).subgroupOf (Jg t z) =
          ((Kg t z).subgroupOf (Jg t z)) ⊓ ((Rg t z).subgroupOf (Jg t z)) := by
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      rw [heq]
      exact Subgroup.inf_relIndex_right ((Kg t z).subgroupOf (Jg t z))
        ((Rg t z).subgroupOf (Jg t z))
    rw [h1]
    calc ((Kg t z).subgroupOf (Jg t z)).relIndex ((Rg t z).subgroupOf (Jg t z))
        = (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z))).ker.relIndex
            ((Rg t z).subgroupOf (Jg t z)) := by
          rw [QuotientGroup.ker_mk']
      _ = Nat.card (((Rg t z).subgroupOf (Jg t z)).map
            (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z)))) :=
          Subgroup.relIndex_ker ((Rg t z).subgroupOf (Jg t z))
            (QuotientGroup.mk' ((Kg t z).subgroupOf (Jg t z)))
      _ ≤ Nat.card (↥(Jg t z) ⧸ (Kg t z).subgroupOf (Jg t z)) :=
          Subgroup.card_le_card_group _
      _ = ((Kg t z).subgroupOf (Jg t z)).index := (Subgroup.index_eq_card _).symm
      _ = 2 := by simpa only [Subgroup.relIndex] using hJ.relIndex_KJ
  have hcard_R_le : Nat.card ↥(Rg t z) ≤ 2 ^ 13 := by
    have hmul : ((Rg t z) ⊓ (Kg t z)).relIndex (Rg t z) *
        Nat.card ↥((Rg t z) ⊓ (Kg t z)) = Nat.card ↥(Rg t z) := by
      have h := Subgroup.relIndex_mul_card (H := (Rg t z) ⊓ (Kg t z)) (K := (Rg t z))
      simpa [inf_of_le_left inf_le_left] using h
    have hcard_RK : Nat.card ↥((Rg t z) ⊓ (Kg t z)) ≤ 2 ^ 12 := by
      calc Nat.card ↥((Rg t z) ⊓ (Kg t z)) ≤ Nat.card ↥(OKg t z) :=
            Subgroup.card_le_of_le hRK_le_O
        _ = 2 ^ 12 := hKD.card_OK
    calc Nat.card ↥(Rg t z)
        = ((Rg t z) ⊓ (Kg t z)).relIndex (Rg t z) *
            Nat.card ↥((Rg t z) ⊓ (Kg t z)) := hmul.symm
      _ ≤ 2 * 2 ^ 12 := Nat.mul_le_mul hrel_RK hcard_RK
      _ = 2 ^ 13 := by norm_num
  have hR_eq_C1 : Rg t z = C1g hJ :=
    (Subgroup.eq_of_le_of_card_ge hC1_le_R (by rw [hC1_card]; exact hcard_R_le)).symm
  have hKR : ∀ j ∈ Jg t z, ∃ k ∈ Kg t z, ∃ r ∈ Rg t z, j = k * r := by
    intro j hj
    obtain ⟨k, hk, c, hc, hjc⟩ := hdecomp j hj
    exact ⟨k, hk, c, hR_eq_C1.symm ▸ hc, hjc⟩
  let incl : ↥(Kg t z) →* ↥(Jg t z) :=
    { toFun := fun k => ⟨(k : G), Kg_le_Jg t z k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψ : ↥(Kg t z) →* (↥(Jg t z) ⧸ (Rg t z).subgroupOf (Jg t z)) :=
    (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z))).comp incl
  have hψ_surj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, r, hr, hxkr⟩ := hKR x x.2
    refine ⟨⟨k, hk⟩, ?_⟩
    have hx : x = (⟨k, Kg_le_Jg t z hk⟩ : ↥(Jg t z)) * ⟨r, Rg_le_Jg t z hr⟩ := Subtype.ext hxkr
    have hr1 : (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z)))
        ⟨r, Rg_le_Jg t z hr⟩ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      exact hr
    change (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z)))
        (⟨k, Kg_le_Jg t z hk⟩ : ↥(Jg t z))
      = (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z))) x
    rw [hx, map_mul, hr1, mul_one]
  have hψ_ker : ψ.ker = (OKg t z).subgroupOf (Kg t z) := by
    ext k
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z))) (incl k) = 1 ↔
      k ∈ (OKg t z).subgroupOf (Kg t z)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hk : (incl k : ↥(Jg t z)) = ⟨(k : G), Kg_le_Jg t z k.2⟩ := rfl
    rw [hk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [hR_eq_C1, ← hC1K_eq_O, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, k.2⟩, fun h => h.1⟩
  let eπ : (↥(Kg t z) ⧸ π.ker) ≃* X := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let eψ : (↥(Kg t z) ⧸ ψ.ker) ≃*
      (↥(Jg t z) ⧸ (Rg t z).subgroupOf (Jg t z)) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj
  let e : X ≃* (↥(Jg t z) ⧸ (Rg t z).subgroupOf (Jg t z)) :=
    eπ.symm.trans ((QuotientGroup.quotientMulEquivOfEq (hψ_ker.trans hker.symm)).symm.trans eψ)
  let π' : ↥(Jg t z) →* X :=
    (e.symm).toMonoidHom.comp (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z)))
  have hπ'_surj : Function.Surjective π' := by
    rintro x
    obtain ⟨q, rfl⟩ := (e.symm).toEquiv.surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((Rg t z).subgroupOf (Jg t z)) q
    exact ⟨y, rfl⟩
  have hπ'_ker : π'.ker = (Rg t z).subgroupOf (Jg t z) := by
    show ((e.symm).toMonoidHom.comp
      (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z)))).ker = _
    rw [MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk' ((Rg t z).subgroupOf (Jg t z))) ((e.symm).toMonoidHom)
      ((e.symm).injective), QuotientGroup.ker_mk']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hR_eq_C1, hC1_card]
  · rw [hR_eq_C1]; exact hC1K_eq_O
  · exact hR_normal
  · intro r hr k hk
    rw [hR_eq_C1] at hr
    exact hr.2 k hk
  · exact ⟨X, hXgrp, π', hπ'_surj, hπ'_ker, hXU⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
