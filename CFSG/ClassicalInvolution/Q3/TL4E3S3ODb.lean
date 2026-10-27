module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OGen
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E3S3O

variable {Y : Type} [Group Y] [Finite Y]

noncomputable abbrev coreD (Rd L : Subgroup Y) (a : Y) : Subgroup Y :=
  ⨆ M ∈ {M | M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L ∧
    XMem (CoreAssembly.conjClass (tightCore Rd)) a M}, coreAt a M

omit [Finite Y] in
theorem coreD_le_layerY (Rd L : Subgroup Y) (a : Y) :
    coreD Rd L a ≤ layerY (CoreAssembly.conjClass (tightCore Rd)) a :=
  iSup₂_le fun _ hM => coreAt_le_layerY hM.2

omit [Finite Y] in
theorem mk_mem_imgD {Rd L : Subgroup Y} {a d : Y} (hd : d ∈ coreD Rd L a) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass
      (tightCore Rd)) a)) ⟨d, coreD_le_layerY Rd L a hd⟩ ∈ imgD Rd L a := by
  have key : coreD Rd L a ≤ ((imgD Rd L a).comap (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) a)))).map
        (layerY (CoreAssembly.conjClass (tightCore Rd)) a).subtype := by
    refine iSup₂_le fun M hM => fun x hx => ?_
    have hxY := coreAt_le_layerY hM.2 hx
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    exact le_iSup₂ (f := fun M (_ : M ∈ {M | M ∈ omegaNbr (CoreAssembly.conjClass
      (tightCore Rd)) L ∧ XMem (CoreAssembly.conjClass (tightCore Rd)) a M}) =>
        secImg (CoreAssembly.conjClass (tightCore Rd)) a M) M hM
      ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨y, hy, hyd⟩ := key hd
  have e : y = ⟨d, coreD_le_layerY Rd L a hd⟩ := Subtype.ext hyd
  rw [← e]
  exact hy

omit [Finite Y] in
theorem imgD_le_map (Rd L : Subgroup Y) (a : Y) :
    imgD Rd L a ≤ ((coreD Rd L a).subgroupOf (layerY (CoreAssembly.conjClass (tightCore Rd)) a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) a))) := by
  refine iSup₂_le fun M hM => ?_
  show (((coreAt a M).subgroupOf (layerY (CoreAssembly.conjClass (tightCore Rd)) a)).map _) ≤ _
  refine Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ?_
  exact le_iSup₂ (f := fun M (_ : M ∈ {M | M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L ∧
    XMem (CoreAssembly.conjClass (tightCore Rd)) a M}) => coreAt a M) M hM
      (Subgroup.mem_subgroupOf.mp hx)

section Cit3


variable {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y} {u : Y}
  {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y}

theorem Ctx.nonempty_mulEquiv_imgD (h : Ctx n R S t J u L Rd Sd S' R' T W)
    (hLie : LieModel ↥(imgD Rd L (u * t)) .PSU 3 3 1 ∨ LieModel ↥(imgD Rd L (u * t)) .PSL 3 3 1) :
    Nonempty (↥(imgD Rd L (u * t)) ≃*
      ↥(coreD Rd L (u * t)) ⧸ classicalInvolutionOddCore ↥(coreD Rd L (u * t))) := by
  classical
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  have hDY := coreD_le_layerY Rd L (u * t)
  set π := QuotientGroup.mk' (classicalInvolutionOddCore
    ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t))) with hπ
  let f₁ : ↥(coreD Rd L (u * t)) →* ↥(imgD Rd L (u * t)) :=
    (π.comp (Subgroup.inclusion hDY)).codRestrict _ fun d => mk_mem_imgD d.2
  have hf₁ : Function.Surjective f₁ := by
    intro y
    obtain ⟨y₀, hy₀, hy₀y⟩ := imgD_le_map Rd L (u * t) y.2
    refine ⟨⟨y₀, Subgroup.mem_subgroupOf.mp hy₀⟩, Subtype.ext ?_⟩
    exact hy₀y
  have hk₁ : Odd (Nat.card f₁.ker) := by
    have hmap : f₁.ker.map (Subgroup.inclusion hDY) ≤
        classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t)) := by
      rintro _ ⟨d, hd, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hd)
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDY)]
    exact odd_natCard_oddCore_layerY.of_dvd_nat (Subgroup.card_dvd_of_le hmap)
  have hsimp : IsSimpleGroup ↥(imgD Rd L (u * t)) := by
    rcases hLie with h' | h'
    · exact isSimpleGroup_of_lieModel (Or.inr rfl) h'
    · exact isSimpleGroup_of_lieModel (Or.inl rfl) h'
  have hO : classicalInvolutionOddCore ↥(imgD Rd L (u * t)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (classicalInvolutionOddCore ↥(imgD Rd L (u * t))) with hb | ht
    · exact hb
    · exfalso
      have hub := isUniqueInvolution_secImg hΩ' h.std.xMem_K h.std.hz
      have hJD : secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd) ≤
          imgD Rd L (u * t) :=
        le_iSup₂ (f := fun M (_ : M ∈ {M | M ∈ omegaNbr (CoreAssembly.conjClass
          (tightCore Rd)) L ∧ XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M}) =>
            secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M) (tightCore Rd)
          ⟨by rw [h.fam_eq, h.core]; exact h.J_mem_nbr, h.std.xMem_K⟩
      set x : ↥(imgD Rd L (u * t)) := ⟨_, hJD hub.mem⟩ with hxdef
      have hx2 : x * x = 1 := Subtype.ext hub.sq
      have hxO : x ∈ classicalInvolutionOddCore ↥(imgD Rd L (u * t)) := by
        rw [ht]
        exact Subgroup.mem_top x
      have hx1 := eq_one_of_isPGroup_of_mem_odd
        (CFSG.ComponentClassification.OddCore.odd_card ↥(imgD Rd L (u * t)))
        hxO (Balance.isPGroup_zpowers_of_mul_self_eq_one hx2)
      exact hub.ne_one (congrArg Subtype.val hx1)
  exact nonempty_mulEquiv_of_surjective f₁ hf₁ hk₁ hO

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
