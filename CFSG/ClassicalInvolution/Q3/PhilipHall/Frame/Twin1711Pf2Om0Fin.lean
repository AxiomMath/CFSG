module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Cls
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Om0Inv
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Block

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0

open CFSG.EvenSmallLie.OmegaEight CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4O8

set_option linter.unusedSectionVars false

structure Om0GenFacts : Prop where
  comm : ∀ l, l < 8 → l ≠ 3 → gen l * mainPerm 0 = mainPerm 0 * gen l
  prod : gen 3 * mainPerm 0 * (gen 3)⁻¹ =
    (gen 0 * v0 * (gen 0)⁻¹) * (gen 2 * v0 * (gen 2)⁻¹) * (gen 4 * v0 * (gen 4)⁻¹) *
      (gen 6 * (v0 * mainPerm 0) * (gen 6)⁻¹)


theorem coreData_map {H : Type} [Group H] (α : H ≃* H) {R : Subgroup H} {t : H}
    (hC : CoreData (⊤ : Subgroup H) R t) :
    CoreData (⊤ : Subgroup H) (R.map α.toMonoidHom) (α t) := by
  let ψ : H →* H := α.symm.toMonoidHom
  have hψ : Function.Injective ψ := α.symm.injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 α.symm.surjective
  have ht' : ψ (α t) = t := by simp [ψ]
  rw [← hr] at hC
  have := hC.comap hψ ht'
  have hRc : R.comap ψ = R.map α.toMonoidHom := by
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, by simp [ψ]⟩
    · rintro ⟨r, hr', rfl⟩
      simpa [ψ] using hr'
  rwa [hRc] at this

theorem ambient_of_coreData {R : Subgroup omegaT} {t : omegaT}
    (hC : CoreData (⊤ : Subgroup omegaT) R t) :
    Vtx.AmbientQuatDatum omegaT (R.map omegaT.subtype) (t : Equiv.Perm (Fin 360)) where
  le := Subgroup.map_subtype_le R
  q8 := by
    obtain ⟨e⟩ := hC.q8
    exact ⟨(R.equivMapOfInjective omegaT.subtype omegaT.subtype_injective).symm.trans e⟩
  inv := Vtx.isUniqueInvolution_map omegaT.subtype omegaT.subtype_injective hC.inv
  twins := by
    intro c hc hcs
    have hcH : (⟨c, hc⟩ : omegaT) ∈
        (⊤ : Subgroup omegaT) ⊓ Subgroup.centralizer ({t} : Set omegaT) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_top _,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hcs)⟩
    have hmap : conjSub c (R.map omegaT.subtype) = (conjSub ⟨c, hc⟩ R).map omegaT.subtype := by
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rcases hC.twins _ hcH with h | h
    · left
      rw [hmap, h]
    · right
      rw [hmap]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (h a ha b hb)

@[expose] noncomputable def R0H : Subgroup omegaT := K0.comap omegaT.subtype

theorem coreData_ident {R : Subgroup omegaT} {t : omegaT}
    (hC : CoreData (⊤ : Subgroup omegaT) R t) :
    ∃ α : omegaT ≃* omegaT, α t = xOm 0 ∧ R.map α.toMonoidHom = R0H := by
  obtain ⟨i, α₁, hα₁⟩ := om0_h1 t hC.inv.sq hC.inv.ne_one
  have hC₁ := coreData_map α₁ hC
  rw [hα₁] at hC₁
  have hd := ambient_of_coreData hC₁
  obtain ⟨g, hg, hgK⟩ := ident_omega hd
  let gH : omegaT := ⟨g, hg⟩
  have hu : IsUniqueInvolution K0 (g * (xOm i : Equiv.Perm (Fin 360)) * g⁻¹) := by
    have := hd.inv.conj g
    rwa [hgK] at this
  have hx : g * (xOm i : Equiv.Perm (Fin 360)) * g⁻¹ = mainPerm 0 :=
    eq_x0_of_isUniqueInvolution hu
  refine ⟨α₁.trans (MulAut.conj gH), Subtype.ext ?_, ?_⟩
  · have e1 : (α₁.trans (MulAut.conj gH)) t = gH * (α₁ t) * gH⁻¹ := rfl
    rw [e1, hα₁]
    exact hx
  · apply Subgroup.map_injective omegaT.subtype_injective
    have h1 : (R.map (α₁.trans (MulAut.conj gH)).toMonoidHom).map omegaT.subtype =
        conjSub g ((R.map α₁.toMonoidHom).map omegaT.subtype) := by
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1, hgK, R0H, Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact K0_le)]

theorem om0_h4 (hg : Om0GenFacts) (B : Set (Subgroup omegaT)) (N : Subgroup omegaT)
    (hR : IsUniqueInvolution R0H (xOm 0))
    (hS : SandwichData (⊤ : Subgroup omegaT) R0H (xOm 0) B N) : False := by
  let y : omegaT := ⟨gen 3, gen_mem_omegaT (by norm_num)⟩
  have hc : ∀ l (hl : l < 8), l ≠ 3 → (⟨gen l, gen_mem_omegaT hl⟩ : omegaT) ∈
      (⊤ : Subgroup omegaT) ⊓ Subgroup.centralizer ({xOm 0} : Set omegaT) := by
    intro l hl hl3
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_top _,
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hg.comm l hl hl3))⟩
  have hv0 : (⟨v0, v0_spec.2⟩ : omegaT) ∈ R0H :=
    Subgroup.mem_comap.2 (Subgroup.subset_closure (by simp))
  have hx0 : xOm 0 ∈ R0H := by
    refine Subgroup.mem_comap.2 ?_
    show mainPerm 0 ∈ K0
    rw [← u0_sq]
    exact K0.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hfac : ∀ l, (hl : l < 8) → l ≠ 3 → ∀ e ∈ R0H,
      (⟨gen l, gen_mem_omegaT hl⟩ : omegaT) * e * (⟨gen l, gen_mem_omegaT hl⟩ : omegaT)⁻¹ ∈
        twinClosure (⊤ : Subgroup omegaT) R0H (xOm 0) := fun l hl hl3 e he =>
    conjSub_le_twinClosure (X := ⊤) (hc l hl hl3) (conj_mem_conjSub he)
  refine false_of_generating hS hR (y := y) (Subgroup.mem_top _) ?_ ?_
  · have h0 := hfac 0 (by norm_num) (by norm_num) _ hv0
    have h2 := hfac 2 (by norm_num) (by norm_num) _ hv0
    have h4 := hfac 4 (by norm_num) (by norm_num) _ hv0
    have h6 := hfac 6 (by norm_num) (by norm_num) _ (R0H.mul_mem hv0 hx0)
    have hprod := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h0 h2) h4) h6
    convert hprod using 1
    exact Subtype.ext hg.prod
  · intro M hM _ hyM
    have hgen : ∀ l, l < 8 → gen l ∈ M.map omegaT.subtype := by
      intro l hl
      by_cases hl3 : l = 3
      · subst hl3
        exact ⟨y, hyM, rfl⟩
      · exact ⟨_, hM (hc l hl hl3), rfl⟩
    rw [eq_top_iff]
    intro h _
    have hh : h.1 ∈ Subgroup.closure {g | ∃ i < 8, gen i = g} := omegaT_eq.le h.2
    have hle : Subgroup.closure {g | ∃ i < 8, gen i = g} ≤ M.map omegaT.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hgen i hi
    obtain ⟨m, hm, hmh⟩ := hle hh
    have : m = h := Subtype.ext hmh
    exact this ▸ hm

theorem noSandwichIn_omegaT_of_gen (hg : Om0GenFacts) : NoSandwichIn omegaT :=
  noSandwichIn_of_ident R0H (xOm 0) (fun R t hC => coreData_ident hC)
    (fun B N hR hS => om0_h4 hg B N hR hS)

theorem om0_of_gen (hg : Om0GenFacts) : NoSandwichAt ModOm0 :=
  noSandwichAt_of_in (noSandwichIn_omegaT_of_gen hg)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0
