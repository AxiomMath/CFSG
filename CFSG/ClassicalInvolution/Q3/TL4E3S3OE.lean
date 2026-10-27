module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODb

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.Blueprint
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

namespace E3S3O

section Cit3


theorem stepE_proved {n : ℕ} : StepE n := by
  intro Y _ _ R S t J u L Rd Sd S' R' T W h hLie
  classical
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  have hfam := h.fam_eq
  have hcΩ := h.frame.large.datum.hypOmegaGen.conjInvariant
  set Xh := E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J with hXh
  set Pm := orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J with hPm
  have hPmL : ∀ M ∈ Pm, M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L :=
    fun M hM => h.mem_omegaNbr_of_mem_orbOf hM
  have hPmΩ : Pm ⊆ CoreAssembly.conjClass (tightCore Rd) := fun M hM => by
    rw [hfam]
    exact (hPmL M hM).1
  have hXhN : Xh ≤ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L :=
    iSup₂_le fun M hM => le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj
      (CoreAssembly.conjClass (tightCore R)) L N}) => N) M ⟨h.star.1, hPmL M hM⟩
  have hPmX : ∀ M ∈ Pm, ∀ c ∈ Xh, conjSub c M ∈ Pm := by
    rintro _ ⟨l, hl, rfl⟩ c hc
    exact ⟨c * l, Subgroup.mul_mem _ (hXhN hc) hl, conjSub_mul c l J⟩
  have ha2 : u * t * (u * t) = 1 := by
    have htu := Subgroup.mem_centralizer_singleton_iff.mp h.frame.t_mem_centralizer
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [htu]
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [h.frame.inv.sq, h.frame.large.datum.isUniqueInvolution_core.sq, one_mul]
  have haX : u * t ∈ Subgroup.normalizer (Xh : Set Y) := by
    rw [mem_normalizer_iff_conjSub_eq]
    have hle : conjSub (u * t) Xh ≤ Xh := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have e : y = ⁅u * t, (u * t)⁻¹ * y * (u * t)⁆ * ((u * t)⁻¹ * y * (u * t)) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Xh.mul_mem (oddCoreOf_le_self _ (h.cent _ hy)) hy
    exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (K := Xh)
      (f := (MulAut.conj (u * t)).toMonoidHom)
      (fun x y hxy => (MulAut.conj _).injective hxy)).symm.le
  have hgen := le_sup_oddCoreOf hΩ' hPmΩ (fun M hM => hΩ'.closure_twoElts (hPmΩ hM)) rfl hPmX
    ha2 haX h.cent
  set D := coreD Rd L (u * t) with hDdef
  have hD' : (⨆ M ∈ {M | M ∈ Pm ∧ XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M},
      coreAt (u * t) M) ≤ D := iSup₂_le fun M hM => le_iSup₂ (f := fun N (_ : N ∈ {M |
        M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L ∧
        XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M}) => coreAt (u * t) N) M
          ⟨by rw [hfam]; exact hPmL M hM.1, hM.2⟩
  have hDX : D ≤ Xh := iSup₂_le fun M hM => (coreAt_le _ M).trans
    (le_iSup₂ (f := fun N (_ : N ∈ Pm) => N) M (h.mem_orbOf_of_mem (by rw [← hfam]; exact hM.1)))
  have hXhD : Xh ≤ oddCoreOf Xh ⊔ D := by
    rw [sup_comm]
    exact hgen.trans (sup_le_sup_right hD' _)
  set f₂ : ↥D →* ↥Xh ⧸ classicalInvolutionOddCore ↥Xh :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hDX) with hf₂def
  have hf₂ : Function.Surjective f₂ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨o, ho, d, hd, hxe⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer
      (hDX.trans fun y hy => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hy))
      (hXhD x.2)
    obtain ⟨hoX, hoO⟩ := mem_oddCoreOf_iff.mp ho
    refine ⟨⟨d, hd⟩, ?_⟩
    show QuotientGroup.mk' _ (Subgroup.inclusion hDX ⟨d, hd⟩) = QuotientGroup.mk' _ x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (Subgroup.inclusion hDX ⟨d, hd⟩)⁻¹ * x =
        (⟨d, hDX hd⟩ : ↥Xh)⁻¹ * ⟨o, hoX⟩ * ((⟨d, hDX hd⟩ : ↥Xh)⁻¹)⁻¹ :=
      Subtype.ext (by simp [hxe, mul_assoc])
    rw [e]
    exact (classicalInvolutionOddCore_normal ↥Xh).conj_mem _ hoO _
  have hk₂ : Odd (Nat.card f₂.ker) := by
    have hmap : f₂.ker.map (Subgroup.inclusion hDX) ≤ classicalInvolutionOddCore ↥Xh := by
      rintro _ ⟨d, hd, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hd
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDX)]
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥Xh).of_dvd_nat
      (Subgroup.card_dvd_of_le hmap)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_of_surjective f₂ hf₂ hk₂
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥Xh)
  obtain ⟨e₁⟩ := h.nonempty_mulEquiv_imgD hLie
  obtain ⟨g, hgK, hgJ, -⟩ := h.exists_conj
  have hXhc :
      conjSub g (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) = Xh := by
    have h1 := E3.orbGen_conj hcΩ h.frame.maxAdj.1.2.1 (J := tightCore R) g
    rw [hgJ, hgK] at h1
    exact h1.symm
  let φ : ↥(E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) ≃* ↥Xh :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hXhc)
  let ψ : E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≃*
      ↥Xh ⧸ classicalInvolutionOddCore ↥Xh :=
    QuotientGroup.congr _ _ φ (E3.map_oddCore_mulEquiv φ)
  let E := (ψ.trans e₂).trans e₁.symm
  rcases hLie with hU | hL
  · exact Or.inr (lieModel_congr E.symm (Or.inr rfl) hU)
  · exact Or.inl (lieModel_congr E.symm (Or.inl rfl) hL)

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
