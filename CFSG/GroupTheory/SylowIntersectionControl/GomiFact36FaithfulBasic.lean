module

public import CFSG.Quasithin.Background.SmithB51LnSecC
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefOffender
import CFSG.Quasithin.SteinbergCDBestOffenderRestriction
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem IsGomiNoncentralFactor.le_stabSub_left {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hIZ : IsGomiNoncentralFactor L I Z) : L ≤ stabSub I :=
  B1.le_stabSub_of_invariant fun a ha w hw => by
    have h := hIZ.1 ⟨a, ha⟩ w hw
    rwa [Subgroup.smul_def, MulAut.smul_def] at h

theorem IsGomiNoncentralFactor.le_stabSub_right {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hIZ : IsGomiNoncentralFactor L I Z) : L ≤ stabSub Z :=
  B1.le_stabSub_of_invariant fun a ha w hw => by
    have h := hIZ.2.1 ⟨a, ha⟩ w hw
    rwa [Subgroup.smul_def, MulAut.smul_def] at h

theorem mem_ker_secHomL {L : Subgroup (MulAut W)} {I Z : Subgroup W} (hLI : L ≤ stabSub I)
    (hLZ : L ≤ stabSub Z) (g : ↥L) :
    g ∈ (B5.Ln.secHomL L hLI hLZ).ker ↔ (g : MulAut W) ∈ centSec I Z := by
  have hker : (B5.Ln.secHomL L hLI hLZ).ker = (B5.secHom L hLI hLZ).ker :=
    MonoidHom.ker_codRestrict (B5.secHom L hLI hLZ) (autSec L I Z) _
  rw [hker]
  exact B5.mem_ker_secHom L hLI hLZ g

private theorem ker_secHomL_eq_inf_fak {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) :
    (B5.Ln.secHomL L hLI hLZ).ker = (L ⊓ centSec I Z).subgroupOf L := by
  ext g
  rw [mem_ker_secHomL hLI hLZ g, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem card_ker_secHomL {L : Subgroup (MulAut W)} {I Z : Subgroup W} (hLI : L ≤ stabSub I)
    (hLZ : L ≤ stabSub Z) :
    Nat.card (B5.Ln.secHomL L hLI hLZ).ker = Nat.card ↥(L ⊓ centSec I Z) := by
  rw [ker_secHomL_eq_inf_fak hLI hLZ]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ centSec I Z ≤ L)).toEquiv

theorem inf_centSec_le_centralizer {L : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) :
    L ⊓ centSec I Z ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  intro a ha
  exact mem_centralizer_of_mem_centSec hL hIZ.le_stabSub_left hIZ.le_stabSub_right hIZ.2.2.2
    (Subgroup.le_normalizer ha.1) ha.2

theorem ker_secHomL_le_center {L : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) (hLI : L ≤ stabSub I)
    (hLZ : L ≤ stabSub Z) : (B5.Ln.secHomL L hLI hLZ).ker ≤ Subgroup.center ↥L := by
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  have hcent : (g : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
    inf_centSec_le_centralizer hL hIZ
      (Subgroup.mem_inf.mpr ⟨g.2, (mem_ker_secHomL hLI hLZ g).mp hg⟩)
  exact (Subgroup.mem_centralizer_iff.mp hcent) (x : MulAut W) x.2

theorem odd_card_inf_centSec [Finite W] {L : Subgroup (MulAut W)} (hL : IsGomiChevTwo ↥L)
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) :
    Odd (Nat.card ↥(L ⊓ centSec I Z)) := by
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  have hle : (L ⊓ centSec I Z).subgroupOf L ≤ Subgroup.center ↥L := by
    rw [← ker_secHomL_eq_inf_fak hLI hLZ]
    exact ker_secHomL_le_center hL.1 hIZ hLI hLZ
  have hodd : Odd (Nat.card ↥((L ⊓ centSec I Z).subgroupOf L)) :=
    Odd.of_dvd_nat (SteinbergCD.odd_card_center_of_pCore_eq_bot hL.2.1)
      (Subgroup.card_dvd_of_le hle)
  rwa [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ centSec I Z ≤ L)).toEquiv] at hodd

theorem le_normalizer_inf_centSec {L A : Subgroup (MulAut W)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {I Z : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) :
    A ≤ Subgroup.normalizer ((L ⊓ centSec I Z : Subgroup (MulAut W)) : Set (MulAut W)) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  rw [Subgroup.mem_inf] at hx ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp (hAL ha) x).mp hx.1,
    StabLat.conj_mem_centSec (hAI ha) (hAZ ha) hx.2⟩

private theorem exists_notMem_commOf_fak {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hnc : ¬ XMod.commOf ↥L I ≤ Z) :
    ∃ (a : ↥L) (i : ↥I), ((a : MulAut W) (i : W)) * (i : W)⁻¹ ∉ Z := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hnc (by
    rw [XMod.commOf_le_iff]
    intro a i hi
    simpa [Subgroup.smul_def, MulAut.smul_def] using h a ⟨i, hi⟩)

private theorem not_commOf_autSec_le_bot_fak {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hIZ : IsGomiNoncentralFactor L I Z) :
    ¬ XMod.commOf ↥(autSec L I Z) (⊤ : Subgroup (Sec I Z)) ≤ ⊥ := by
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  obtain ⟨a, i, hi⟩ := exists_notMem_commOf_fak hIZ.2.2.2
  intro hle
  let φ : ↥(autSec L I Z) := ⟨B5.secHom L hLI hLZ a, by
    rw [← B5.range_secHom L hLI hLZ]
    exact ⟨a, rfl⟩⟩
  let s : Sec I Z := QuotientGroup.mk i
  have hφs : φ • s = QuotientGroup.mk
      (⟨(a : MulAut W) (i : W), (hLI a.2 (i : W)).2 i.2⟩ : ↥I) := by
    rw [Subgroup.smul_def, MulAut.smul_def]
    exact B5.secHom_mk L hLI hLZ a i
  have hcne : (φ • s) * s⁻¹ ≠ 1 := by
    intro hc
    have hfix : φ • s = s := mul_inv_eq_one.mp hc
    rw [hφs] at hfix
    have hmem : (⟨(a : MulAut W) (i : W), (hLI a.2 (i : W)).2 i.2⟩ / i : ↥I) ∈
        Z.subgroupOf I := QuotientGroup.eq_iff_div_mem.mp hfix
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv] at hmem
    exact hi hmem
  have hgen : (φ • s) * s⁻¹ ∈ XMod.commOf ↥(autSec L I Z) (⊤ : Subgroup (Sec I Z)) :=
    XMod.mem_commOf_of_mem φ trivial
  have hmem := hle hgen
  rw [Subgroup.mem_bot] at hmem
  exact hcne hmem

theorem isGomiNoncentralFactor_autSec {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hIZ : IsGomiNoncentralFactor L I Z) : IsGomiNoncentralFactor (autSec L I Z) ⊤ ⊥ := by
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  have hirr : ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → Z ≤ J → J ≤ I →
      J = Z ∨ J = I := fun J hJ hZJ hJI =>
    hIZ.2.2.1.2 J (fun a w hw => by
      rw [Subgroup.smul_def, MulAut.smul_def]
      exact hJ a a.2 w hw) hZJ hJI
  refine ⟨fun _ _ _ => trivial, ?_, ?_, not_commOf_autSec_le_bot_fak hIZ⟩
  · intro a l hl
    rw [Subgroup.mem_bot] at hl ⊢
    rw [hl]
    exact smul_one a
  · exact B5.isIrrSec_autSec hIZ.2.2.1.1 hirr hLI hLZ

end CFSG.GroupTheory
