module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact34Holds
import CFSG.Quasithin.Background.B69Cent
import CFSG.Quasithin.Background.B2FactorizationSum

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem ffJ_le_normalizer_of_gomiFact37Hyp (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact37Hyp Y S L) (hq : CFSG.IsQuasisimple ↥L) :
    ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hLY : L ≤ Y := h.2.2.1
  have hcomp : CFSG.IsComponent (L.subgroupOf Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLY).symm hq, h.2.2.2.1⟩
  refine iSup_le fun A => iSup_le fun hA => ?_
  exact le_normalizer_of_offender_component (fun w => by rw [← pow_two]; exact hW w)
    hLY hcomp ⟨hA.1.trans h.2.1.le, hA.2⟩

omit [Finite W] in
theorem exists_isFFStarOffender_commutator_ne_bot {S L : Subgroup (MulAut W)}
    (hJ : ⁅L, ffJ S⁆ ≠ ⊥) :
    ∃ A : Subgroup (MulAut W), IsFFStarOffender S A ∧ ⁅L, A⁆ ≠ ⊥ := by
  by_contra h
  have hzero : ∀ A : Subgroup (MulAut W), IsFFStarOffender S A → ⁅L, A⁆ = ⊥ := by
    intro A hA
    by_contra hne
    exact h ⟨A, hA, hne⟩
  have hzero' : ∀ A : Subgroup (MulAut W), IsFFStarOffender S A → ⁅A, L⁆ = ⊥ := by
    intro A hA
    rw [Subgroup.commutator_comm]
    exact hzero A hA
  have hle : ffJ S ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    iSup_le fun A => iSup_le fun hA =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hzero' A hA)
  apply hJ
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle

omit [Finite W] in
private theorem commV_le_fixV_offender_of_commutator_eq_bot (hW : ∀ w : W, w ^ 2 = 1)
    {S L A : Subgroup (MulAut W)} (hirr : commV L ∈ IrrPlus L ⊤)
    (hJ : ⁅L, ffJ S⁆ = ⊥) (hA : IsFFStarOffender S A) : commV L ≤ fixV A := by
  have hAle : A ≤ ffJ S :=
    le_iSup₂ (f := fun B (_ : IsFFStarOffender S B) => B) A hA
  have hAc : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
    intro a ha l hl
    exact Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJ) hl) a (hAle ha)
  intro w hw
  rw [mem_fixV]
  intro a ha
  exact CFSG.Quasithin.B69.comm_trivial_on_commV_of_elem hW hA.2.2.1 hAc hirr a ha w hw

omit [Finite W] in
theorem not_inf_fixV_ffJ_le_of_commutator_eq_bot (hW : ∀ w : W, w ^ 2 = 1)
    {S L : Subgroup (MulAut W)} (hirr : commV L ∈ IrrPlus L ⊤) (hJ : ⁅L, ffJ S⁆ = ⊥) :
    ¬ commV L ⊓ fixV (ffJ S) ≤ gomiWXKer L := by
  have hfix : commV L ≤ fixV (ffJ S) := by
    unfold ffJ
    rw [CFSG.Quasithin.fixV_iSup]
    refine le_iInf fun A => ?_
    rw [CFSG.Quasithin.fixV_iSup]
    exact le_iInf fun hA => commV_le_fixV_offender_of_commutator_eq_bot hW hirr hJ hA
  have hlt : commV L ⊓ fixV L < commV L :=
    (CFSG.Quasithin.mem_irrPlus_top_iff.1 hirr).2.2.1
  intro h
  rw [inf_eq_left.mpr hfix, gomiWXKer] at h
  have hle : commV L ≤ fixV L := h.trans inf_le_right
  have heq : commV L ⊓ fixV L = commV L := inf_eq_left.mpr hle
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem gomiCSP_le_normalizer_of_not_le (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact37Hyp Y S L) (hq : CFSG.IsQuasisimple ↥L)
    (hirr : commV L ∈ IrrPlus L ⊤) (hF : ¬ commV L ⊓ fixV (ffJ S) ≤ gomiWXKer L) :
    gomiCSP S L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  intro s hs
  by_contra hsn
  have hsS : s ∈ S := hs.1
  have hsY : s ∈ Y := h.2.1.le hsS
  have hLY : L ≤ Y := h.2.2.1
  have hfixF : ∀ f ∈ commV L ⊓ fixV (ffJ S), s f = f := fun f hf =>
    (mem_fixingSubgroup_iff (MulAut W)).mp hs.2 f hf
  have hcomp : CFSG.IsComponent (L.subgroupOf Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLY).symm hq, h.2.2.2.1⟩
  have hCo : CFSG.Open.IsComponentOf L Y :=
    CFSG.Quasithin.isComponentOf_iff_subgroupOf.mpr
      ⟨hLY, (CFSG.isComponent_iff_open (L.subgroupOf Y)).mp hcomp⟩
  let L' : Subgroup (MulAut W) := CFSG.Quasithin.A1b.conjSub s L
  have hL' : CFSG.Open.IsComponentOf L' Y :=
    CFSG.Quasithin.B113.isComponentOf_conj hCo hsY
  have hne : L' ≠ L := by
    intro heq
    exact hsn (CFSG.Quasithin.A1b.conjSub_eq_iff_mem_normalizer.mp heq)
  have hL'q : CFSG.Open.IsQuasisimple ↥L' := hL'.2.2
  have hcomm : ∀ k ∈ L', ∀ l ∈ L, k * l = l * k :=
    CFSG.Quasithin.B69.components_mul_comm_of_ne hCo hL' hne.symm
  have htriv : ∀ k ∈ L', ∀ w ∈ commV L, k w = w :=
    CFSG.Quasithin.B69.comm_trivial_on_commV hW hL'q hcomm hirr
  have hstep : ∀ l ∈ L, ∀ w ∈ commV L, l (s⁻¹ w) = s⁻¹ w := by
    intro l hl w hw
    have hmem : s * l * s⁻¹ ∈ L' :=
      Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hl
    have h1 : s (l (s⁻¹ w)) = w := by
      simpa [MulAut.mul_apply] using htriv (s * l * s⁻¹) hmem w hw
    simpa using congrArg (fun x => s⁻¹ x) h1
  have hFfix : commV L ⊓ fixV (ffJ S) ≤ fixV L := by
    intro f hf
    rw [mem_fixV]
    intro l hl
    have hsf : s f = f := hfixF f hf
    have hw : s f ∈ commV L := by simpa [hsf] using hf.1
    simpa using hstep l hl (s f) hw
  exact hF fun f hf => ⟨hf.1, hFfix hf⟩

end CFSG.GroupTheory

end
