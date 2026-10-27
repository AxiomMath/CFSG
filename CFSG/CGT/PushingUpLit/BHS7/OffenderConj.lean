module

public import CFSG.CGT.PushingUpLit.BHS7.Offenders
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixA

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem autOn_conjSub_of_mem {V : Subgroup Γ} {t : Γ} (ht : t ∈ Subgroup.normalizer (V : Set Γ))
    {X : Subgroup Γ} :
    autOn (conjSub t X) V = conjSub (conjAct V ⟨t, ht⟩) (autOn X V) := by
  ext y
  rw [mem_autOn_iff, mem_conjSub_iff, mem_autOn_iff]
  constructor
  · rintro ⟨a, haX, rfl⟩
    refine ⟨⟨t⁻¹ * a * t, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) a.2) ht⟩,
      mem_conjSub_iff.1 haX, ?_⟩
    rw [show (⟨t⁻¹ * (a : Γ) * t, _⟩ : ↥(Subgroup.normalizer (V : Set Γ))) =
      ⟨t, ht⟩⁻¹ * a * ⟨t, ht⟩ from rfl, map_mul, map_mul, map_inv]
  · rintro ⟨b, hbX, hb⟩
    refine ⟨⟨t * b * t⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ht b.2)
      (Subgroup.inv_mem _ ht)⟩, mem_conjSub_of_mem hbX, ?_⟩
    have : conjAct V b = (conjAct V ⟨t, ht⟩)⁻¹ * y * conjAct V ⟨t, ht⟩ := hb
    rw [show (⟨t * (b : Γ) * t⁻¹, _⟩ : ↥(Subgroup.normalizer (V : Set Γ))) =
      ⟨t, ht⟩ * b * ⟨t, ht⟩⁻¹ from rfl, map_mul, map_mul, map_inv, this]
    group


theorem conjSub_inv_conjSub_self (g : Γ) (X : Subgroup Γ) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv_self (g : Γ) (X : Subgroup Γ) : conjSub g (conjSub g⁻¹ X) = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_le_normalizer {V A : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) (hA : A ≤ Subgroup.normalizer (V : Set Γ)) :
    conjSub g A ≤ Subgroup.normalizer (V : Set Γ) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hA hx)) (Subgroup.inv_mem _ hg)
  simpa [mul_assoc] using h1

theorem wtG_conjSub {V A : Subgroup Γ} (hV : IsElemAbelian 2 V) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) (hA : A ≤ Subgroup.normalizer (V : Set Γ)) :
    wtG V (conjSub g A) = wtG V A := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hA' := conjSub_le_normalizer hg hA
  rw [← wt_autOn hV hA', ← wt_autOn hV hA, autOn_conjSub_of_mem hg]
  exact wt_conjSub _ _

theorem isOffG_conjSub {V A : Subgroup Γ} (hV : IsElemAbelian 2 V) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) (hA : A ≤ Subgroup.normalizer (V : Set Γ))
    (h : IsOffG V A) : IsOffG V (conjSub g A) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hA' := conjSub_le_normalizer hg hA
  have h1 := (isOffG_iff_isOff_autOn hV hA).mp h
  refine (isOffG_iff_isOff_autOn hV hA').mpr ?_
  rw [autOn_conjSub_of_mem hg]
  exact h1.conj _

theorem isOffStarG_conjSub {V A : Subgroup Γ} (hV : IsElemAbelian 2 V) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) (h : IsOffStarG V A) :
    IsOffStarG V (conjSub g A) :=
  ⟨isOffG_conjSub hV hg h.1.1 h.1, by rw [wtG_conjSub hV hg h.1.1]; exact h.2⟩

theorem offStarT_conjSub {V T A : Subgroup Γ} (hV : IsElemAbelian 2 V) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) (hA : A ∈ offStarT V T) :
    conjSub g A ∈ offStarT V (conjSub g T) :=
  ⟨conjSub_mono g hA.1, isOffStarG_conjSub hV hg hA.2⟩

theorem offStarMin_conjSub {V T A : Subgroup Γ} (hV : IsElemAbelian 2 V) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) (hA : A ∈ offStarMin V T) :
    conjSub g A ∈ offStarMin V (conjSub g T) := by
  refine ⟨offStarT_conjSub hV hg hA.1, fun B hB hBA => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (V : Set Γ) := Subgroup.inv_mem _ hg
  have hB' : conjSub g⁻¹ B ∈ offStarT V T := by
    have := offStarT_conjSub hV hg' hB
    rwa [conjSub_inv_conjSub_self] at this
  have hle : conjSub g⁻¹ B ≤ A := by
    have := conjSub_mono g⁻¹ hBA
    rwa [conjSub_inv_conjSub_self] at this
  have heq := hA.2 _ hB' hle
  calc B = conjSub g (conjSub g⁻¹ B) := (conjSub_conjSub_inv_self g B).symm
    _ = conjSub g A := by rw [heq]

theorem qSub_conjSub {V T : Subgroup Γ} (hV : IsElemAbelian 2 V) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (V : Set Γ)) :
    qSub V (conjSub g T) = conjSub g (qSub V T) := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (V : Set Γ) := Subgroup.inv_mem _ hg
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun B hB => ?_
    have h1 : conjSub g⁻¹ B ∈ offStarMin V T := by
      have := offStarMin_conjSub hV hg' hB
      rwa [conjSub_inv_conjSub_self] at this
    have h2 := conjSub_mono g (le_qSub h1)
    rwa [conjSub_conjSub_inv_self] at h2
  · rw [qSub, conjSub_iSup]
    refine iSup_le fun A => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hA => ?_
    exact le_qSub (offStarMin_conjSub hV hg hA)

theorem conjSub_tZero [Finite Γ] {G T : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowTwoOf T G)
    {g : Γ} (hgG : g ∈ G) : tZero G (conjSub g T) = conjSub g (tZero G T) := by
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub hG hT
  have hgV : g ∈ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T hgG
  have hVg : vSub G (conjSub g T) = vSub G T := vSub_conjSub hgG T
  have hZg : zSub (conjSub g T) = conjSub g (zSub T) := by
    unfold zSub
    rw [baum_conjSub, omegaOneCenterOf_conjSub]
  have hcomm : ⁅vSub G (conjSub g T), zSub (conjSub g T)⁆ = ⊥ ↔ ⁅vSub G T, zSub T⁆ = ⊥ := by
    rw [hVg, hZg]
    have : ⁅vSub G T, conjSub g (zSub T)⁆ = conjSub g ⁅vSub G T, zSub T⁆ := by
      calc ⁅vSub G T, conjSub g (zSub T)⁆ = ⁅conjSub g (vSub G T), conjSub g (zSub T)⁆ := by
            rw [conjSub_eq_of_mem_normalizer hgV]
        _ = conjSub g ⁅vSub G T, zSub T⁆ := commutator_conjSub g _ _
    rw [this, conjSub_eq_bot_iff]
  by_cases h : ⁅vSub G T, zSub T⁆ = ⊥
  · have h' := hcomm.mpr h
    rw [tZero_of_eq h', tZero_of_eq h, hVg]
    exact qSub_conjSub hV hgV
  · have h' : ⁅vSub G (conjSub g T), zSub (conjSub g T)⁆ ≠ ⊥ := fun h0 => h (hcomm.mp h0)
    rw [tZero_of_ne h', tZero_of_ne h, hZg]

end CFSG.CGT.PushingUpLit.BHS7
