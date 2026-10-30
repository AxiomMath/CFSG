module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSecAct

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V]

theorem sec_sq_eq_one (hV : ∀ v : V, v ^ 2 = 1) (Z' Z : Subgroup V) (s : Sec Z Z') :
    s ^ 2 = 1 := by
  induction s using QuotientGroup.induction_on with
  | H z =>
    rw [← QuotientGroup.mk_pow]
    have hz : z ^ 2 = 1 := Subtype.ext (by simpa using hV (z : V))
    rw [hz, QuotientGroup.mk_one]

theorem inf_centSec_eq_bot {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L) {Z' Z : Subgroup V}
    (hLZ : L ≤ stabSub Z) (hLZ' : L ≤ stabSub Z') (hnc : ¬ LTrivOn L Z' Z) :
    L ⊓ centSec Z Z' = ⊥ := by
  let K : Subgroup ↥L := (L ⊓ centSec Z Z').subgroupOf L
  have hKn : K.Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hk ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hk.1) (L.inv_mem g.2), ?_, ?_⟩
    · exact (stabSub Z).mul_mem ((stabSub Z).mul_mem (hLZ g.2) hk.2.1)
        ((stabSub Z).inv_mem (hLZ g.2))
    · intro z hz
      have hz1 : (g : MulAut V)⁻¹ z ∈ Z := mem_of_stab (hLZ (L.inv_mem g.2)) hz
      have h1 := hk.2.2 _ hz1
      have h2 := mem_of_stab (hLZ' g.2) h1
      have e : ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹) z * z⁻¹ =
          (g : MulAut V) ((k : MulAut V) ((g : MulAut V)⁻¹ z) * ((g : MulAut V)⁻¹ z)⁻¹) := by
        simp
      show ((g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹) z * z⁻¹ ∈ Z'
      rw [e]; exact h2⟩
  haveI := hKn
  have hKbot : K = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      apply hnc
      intro g hg z hz
      have : (⟨g, hg⟩ : ↥L) ∈ K := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2.2 z hz
  rw [eq_bot_iff]
  intro g hg
  have hgK : (⟨g, (Subgroup.mem_inf.mp hg).1⟩ : ↥L) ∈ K := Subgroup.mem_subgroupOf.mpr hg
  rw [hKbot, Subgroup.mem_bot] at hgK
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hgK

theorem secAct_injective {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L) {Z' Z : Subgroup V}
    (hZ'Z : Z' ≤ Z) (hLZ : L ≤ stabSub Z) (hLZ' : L ≤ stabSub Z') (hnc : ¬ LTrivOn L Z' Z) :
    Function.Injective (secAct L hLZ hLZ') := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [ker_secAct L hZ'Z hLZ hLZ', inf_centSec_eq_bot hs hLZ hLZ' hnc]
  ext x
  simp [Subgroup.mem_subgroupOf]

noncomputable def secIso {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L) {Z' Z : Subgroup V}
    (hZ'Z : Z' ≤ Z) (hLZ : L ≤ stabSub Z) (hLZ' : L ≤ stabSub Z') (hnc : ¬ LTrivOn L Z' Z) :
    ↥L ≃* ↥(autSec L Z Z') :=
  (MonoidHom.ofInjective (secAct_injective hs hZ'Z hLZ hLZ' hnc)).trans
    (MulEquiv.subgroupCongr (range_secAct L hLZ hLZ'))

theorem secIso_apply {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L) {Z' Z : Subgroup V}
    (hZ'Z : Z' ≤ Z) (hLZ : L ≤ stabSub Z) (hLZ' : L ≤ stabSub Z') (hnc : ¬ LTrivOn L Z' Z)
    (l : ↥L) :
    ((secIso hs hZ'Z hLZ hLZ' hnc l : ↥(autSec L Z Z')) : MulAut (Sec Z Z')) =
      secAct L hLZ hLZ' l := by
  rfl

theorem isElemAbelian2_autSec {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) {Z' Z : Subgroup V}
    (hAZ : A ≤ stabSub Z) (hAZ' : A ≤ stabSub Z') : IsElemAbelian2 (autSec A Z Z') := by
  rw [← range_secAct A hAZ hAZ']
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ a.2 _ b.2)
  · rintro _ ⟨a, rfl⟩
    have ha : a ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ a.2)
    rw [← map_pow, ha, map_one]

theorem sec_conj_mem {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) {α l : MulAut V} (hα : α ∈ A)
    (hl : l ∈ L) : α * l * α⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp (hAL hα) l).mp hl

theorem secAct_conj_eq {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) {Z' Z : Subgroup V}
    (hZ : XInv L A Z) (hZ' : XInv L A Z') {α l : MulAut V} (hα : α ∈ A) (hl : l ∈ L) :
    secAct L hZ.1 hZ'.1 ⟨α * l * α⁻¹, sec_conj_mem hAL hα hl⟩ =
      secAct A hZ.2 hZ'.2 ⟨α, hα⟩ * secAct L hZ.1 hZ'.1 ⟨l, hl⟩ *
        (secAct A hZ.2 hZ'.2 ⟨α, hα⟩)⁻¹ := by
  have hX : L ⊔ A ≤ stabSub Z := sup_le hZ.1 hZ.2
  have hX' : L ⊔ A ≤ stabSub Z' := sup_le hZ'.1 hZ'.2
  calc secAct L hZ.1 hZ'.1 ⟨α * l * α⁻¹, sec_conj_mem hAL hα hl⟩
      = secAct (L ⊔ A) hX hX'
          (⟨α, Subgroup.mem_sup_right hα⟩ * ⟨l, Subgroup.mem_sup_left hl⟩ *
            (⟨α, Subgroup.mem_sup_right hα⟩ : ↥(L ⊔ A))⁻¹) := rfl
    _ = secAct (L ⊔ A) hX hX' ⟨α, Subgroup.mem_sup_right hα⟩ *
          secAct (L ⊔ A) hX hX' ⟨l, Subgroup.mem_sup_left hl⟩ *
          (secAct (L ⊔ A) hX hX' ⟨α, Subgroup.mem_sup_right hα⟩)⁻¹ := by
        simp only [map_mul, map_inv]
    _ = secAct A hZ.2 hZ'.2 ⟨α, hα⟩ * secAct L hZ.1 hZ'.1 ⟨l, hl⟩ *
          (secAct A hZ.2 hZ'.2 ⟨α, hα⟩)⁻¹ := rfl

theorem autSec_normalizes {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) {Z' Z : Subgroup V}
    (hZ : XInv L A Z) (hZ' : XInv L A Z') :
    autSec A Z Z' ≤ Subgroup.normalizer (autSec L Z Z' : Set (MulAut (Sec Z Z'))) := by
  have key : ∀ g ∈ autSec A Z Z', ∀ y ∈ autSec L Z Z', g * y * g⁻¹ ∈ autSec L Z Z' := by
    intro g hg y hy
    rw [← range_secAct A hZ.2 hZ'.2] at hg
    rw [← range_secAct L hZ.1 hZ'.1] at hy ⊢
    obtain ⟨⟨α, hα⟩, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨⟨l, hl⟩, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_range.mpr ⟨⟨α * l * α⁻¹, sec_conj_mem hAL hα hl⟩,
      secAct_conj_eq hAL hZ hZ' hα hl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => key g hg y hy
  · intro hy
    have h := key g⁻¹ ((autSec A Z Z').inv_mem hg) _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h

theorem exists_noncomm_autSec {L A : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) {Z' Z : Subgroup V}
    (hZ'Z : Z' ≤ Z) (hZ : XInv L A Z) (hZ' : XInv L A Z') (hnc : ¬ LTrivOn L Z' Z)
    (h : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a) :
    ∃ a ∈ autSec A Z Z', ∃ l ∈ autSec L Z Z', a * l ≠ l * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨α, hα, l, hl, hne⟩ := h
  apply hne
  have hmA : secAct A hZ.2 hZ'.2 ⟨α, hα⟩ ∈ autSec A Z Z' := by
    rw [← range_secAct A hZ.2 hZ'.2]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hmL : secAct L hZ.1 hZ'.1 ⟨l, hl⟩ ∈ autSec L Z Z' := by
    rw [← range_secAct L hZ.1 hZ'.1]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hcomm := hcon _ hmA _ hmL
  have h1 : secAct L hZ.1 hZ'.1 ⟨α * l * α⁻¹, sec_conj_mem hAL hα hl⟩ =
      secAct L hZ.1 hZ'.1 ⟨l, hl⟩ := by
    rw [secAct_conj_eq hAL hZ hZ' hα hl, hcomm, mul_inv_cancel_right]
  have h2 : α * l * α⁻¹ = l :=
    congrArg Subtype.val (secAct_injective hs hZ'Z hZ.1 hZ'.1 hnc h1)
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem isIrrOn_autSec {L A : Subgroup (MulAut V)} {Z' Z : Subgroup V}
    (hch : IsXChief L A Z' Z) : IsIrrOn (autSec L Z Z' ⊔ autSec A Z Z') := by
  obtain ⟨hZ', hZ, hlt, hmax⟩ := hch
  intro W hW
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup V,
      P = (W.comap (QuotientGroup.mk' (Z'.subgroupOf Z))).map Z.subtype := ⟨_, rfl⟩
  have hPmem : ∀ z : ↥Z, (z : V) ∈ P ↔ (QuotientGroup.mk z : ↥Z ⧸ Z'.subgroupOf Z) ∈ W := by
    intro z
    rw [hPdef, Subgroup.mem_map]
    constructor
    · rintro ⟨z', hz', hzz⟩
      obtain rfl : z' = z := Subtype.ext hzz
      exact hz'
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hPZ : P ≤ Z := by
    intro v hv
    rw [hPdef, Subgroup.mem_map] at hv
    obtain ⟨z, -, hz⟩ := hv
    rw [← hz]
    exact z.2
  have hZ'P : Z' ≤ P := by
    intro v hv
    have hvZ : v ∈ Z := hlt.le hv
    have h1 : (QuotientGroup.mk (⟨v, hvZ⟩ : ↥Z) : ↥Z ⧸ Z'.subgroupOf Z) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hv
    exact (hPmem ⟨v, hvZ⟩).2 (by rw [h1]; exact W.one_mem)
  have hfwd : ∀ Y : Subgroup (MulAut V), Y ≤ stabSub Z → Y ≤ stabSub Z' →
      autSec Y Z Z' ≤ autSec L Z Z' ⊔ autSec A Z Z' → ∀ g ∈ Y, ∀ v ∈ P, g v ∈ P := by
    intro Y hYZ hYZ' hYX g hg v hv
    have hvZ : v ∈ Z := hPZ hv
    refine (hPmem ⟨g v, mem_of_stab (hYZ hg) hvZ⟩).2 ?_
    have hmem : secAct Y hYZ hYZ' ⟨g, hg⟩ ∈ autSec Y Z Z' := by
      rw [← range_secAct Y hYZ hYZ']
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hact := hW _ (hYX hmem) _ ((hPmem ⟨v, hvZ⟩).1 hv)
    rw [secAct_mk] at hact
    exact hact
  have hstab : ∀ Y : Subgroup (MulAut V), Y ≤ stabSub Z → Y ≤ stabSub Z' →
      autSec Y Z Z' ≤ autSec L Z Z' ⊔ autSec A Z Z' → Y ≤ stabSub P := by
    intro Y hYZ hYZ' hYX g hg
    exact mem_stabSub_of_inv (hfwd Y hYZ hYZ' hYX g hg) (hfwd Y hYZ hYZ' hYX g⁻¹ (Y.inv_mem hg))
  have hPinv : XInv L A P :=
    ⟨hstab L hZ.1 hZ'.1 le_sup_left, hstab A hZ.2 hZ'.2 le_sup_right⟩
  rcases hmax P hPinv hZ'P hPZ with hPeq | hPeq
  · left
    rw [eq_bot_iff]
    intro s hs
    induction s using QuotientGroup.induction_on with
    | H z =>
      have hzP : (z : V) ∈ Z' := by
        rw [← hPeq]
        exact (hPmem z).2 hs
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hzP
  · right
    rw [eq_top_iff]
    intro s _
    induction s using QuotientGroup.induction_on with
    | H z =>
      have hzP : (z : V) ∈ P := by
        rw [hPeq]
        exact z.2
      exact (hPmem z).1 hzP

theorem IsU4Group.one_le {n : ℕ} {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}
    (h : IsU4Group n L) : 1 ≤ n := by
  obtain ⟨_, ⟨q, _, hqn, _⟩, _⟩ := h
  have := q.exponent_pos
  omega

theorem isU4_autSec {n : ℕ} {L : Subgroup (MulAut V)} (h : IsU4Group n L) {Z' Z : Subgroup V}
    (hZ'Z : Z' ≤ Z) (hLZ : L ≤ stabSub Z) (hLZ' : L ≤ stabSub Z') (hnc : ¬ LTrivOn L Z' Z) :
    IsU4Group n (autSec L Z Z') := by
  have hs : IsSimpleGroup ↥L := (isU4_simple h).1
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  exact ⟨d, hd, ⟨(secIso hs hZ'Z hLZ hLZ' hnc).symm.trans e⟩⟩

theorem thmC_sec [Finite V] (hC : U4FFNatural) (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    {L A : Subgroup (MulAut V)} (h : U4OffenderData n L A) {Z' Z : Subgroup V}
    (hch : IsXChief L A Z' Z) (hnc : ¬ LTrivOn L Z' Z) (hZD : Z ≤ fixV (cenD L A)) :
    IsIrrOn (autSec L Z Z') ∧ NaturalU4Mod n (autSec L Z Z') := by
  obtain ⟨hZ', hZ, hlt, hmax⟩ := hch
  have hZ'Z : Z' ≤ Z := hlt.le
  haveI : Finite (Sec Z Z') := inferInstance
  exact hC (Sec Z Z') (sec_sq_eq_one hV Z' Z) n (autSec L Z Z') (autSec A Z Z')
    (isU4_autSec h.isU4 hZ'Z hZ.1 hZ'.1 hnc)
    (isElemAbelian2_autSec h.elemAbelian hZ.2 hZ'.2)
    (autSec_normalizes h.normalizes hZ hZ')
    (exists_noncomm_autSec h.simple h.normalizes hZ'Z hZ hZ' hnc h.noncomm)
    (isIrrOn_autSec ⟨hZ', hZ, hlt, hmax⟩)
    (card_sec_le h hZ'Z hZ hZ' hZD hnc)

end CFSG.LocalAnalysis.RankThreeUC
