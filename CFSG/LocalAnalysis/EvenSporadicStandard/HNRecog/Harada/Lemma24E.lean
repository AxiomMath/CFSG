module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Ind

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {a : G}

private theorem coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) :=
  fun _ _ huv => Multiplicative.ofAdd.injective (hι huv)

private theorem mem_range_iff_exists_coordElt {x : G} :
    x ∈ ι.range ↔ ∃ v : V6, x = coordElt ι v := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx
    refine ⟨Multiplicative.toAdd y, ?_⟩
    rw [← hy]
    simp [coordElt]
  · rintro ⟨v, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, rfl⟩

theorem mem_E24_iff (h : Setting24 ι a) {x : G} :
    x ∈ E24 ι a ↔ ∃ v ∈ Fix3, x = coordElt ι v := by
  rw [E24, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxrange, hxcent⟩
    obtain ⟨v, rfl⟩ := mem_range_iff_exists_coordElt.mp hxrange
    refine ⟨v, ?_, rfl⟩
    rw [mem_Fix3]
    have hcomm : coordElt ι v * a = a * coordElt ι v :=
      Subgroup.mem_centralizer_singleton_iff.mp hxcent
    have hconj : a * coordElt ι v * a⁻¹ = coordElt ι v := by
      rw [← hcomm]; group
    have hw : coordElt ι (w3 v) = coordElt ι v := by
      rw [← h.a_induces v, hconj]
    exact coordElt_injective h.inj hw
  · rintro ⟨v, hv, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : w3 v = v := mem_Fix3.mp hv
    have hconj : a * coordElt ι v * a⁻¹ = coordElt ι v := by
      rw [h.a_induces v, hfix]
    have hcomm : a * coordElt ι v = coordElt ι v * a := by
      calc a * coordElt ι v = a * coordElt ι v * a⁻¹ * a := by group
        _ = coordElt ι v * a := by rw [hconj]
    exact hcomm.symm

theorem card_E24 (h : Setting24 ι a) : Nat.card (E24 ι a) = 16 := by
  let f : ↥Fix3 → E24 ι a := fun v =>
    ⟨coordElt ι v.1, (mem_E24_iff h).mpr ⟨v.1, v.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      exact Subtype.ext (coordElt_injective h.inj (Subtype.ext_iff.mp huv))
    · intro x
      obtain ⟨v, hv, hxv⟩ := (mem_E24_iff h).mp x.2
      exact ⟨⟨v, hv⟩, Subtype.ext hxv.symm⟩
  calc Nat.card (E24 ι a) = Nat.card ↥Fix3 :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = 16 := by rw [Nat.card_eq_finsetCard, card_Fix3]

theorem E24_le_P24 : E24 ι a ≤ P24 ι a := by
  intro x hx
  rw [E24, Subgroup.mem_inf] at hx
  obtain ⟨hxrange, hxcent⟩ := hx
  obtain ⟨v, rfl⟩ := mem_range_iff_exists_coordElt.mp hxrange
  rw [P24, Subgroup.mem_inf]
  exact ⟨mem_indSub.mpr ⟨1, Vg.one_mem, induces_coordElt v⟩, hxcent⟩

theorem P24_le_F24 : P24 ι a ≤ F24 ι a := by
  intro x hx
  rw [P24, Subgroup.mem_inf] at hx
  obtain ⟨hxind, hxcent⟩ := hx
  obtain ⟨g, hg, hind⟩ := mem_indSub.mp hxind
  rw [F24, Subgroup.mem_inf]
  exact ⟨mem_indSub.mpr ⟨g, Vg_le_A5g hg, hind⟩, hxcent⟩

theorem F24_inf_range : F24 ι a ⊓ ι.range = E24 ι a := by
  rw [F24, E24]
  have hle : ι.range ≤ indSub ι A5g := fun x hx => by
    obtain ⟨v, rfl⟩ := mem_range_iff_exists_coordElt.mp hx
    exact coordElt_mem_indSub A5g v
  rw [inf_assoc, inf_comm (centralizer ({a} : Set G)) ι.range, ← inf_assoc,
    inf_eq_right.mpr hle]

theorem P24_inf_range : P24 ι a ⊓ ι.range = E24 ι a := by
  rw [P24, E24]
  have hle : ι.range ≤ indSub ι Vg := fun x hx => by
    obtain ⟨v, rfl⟩ := mem_range_iff_exists_coordElt.mp hx
    exact coordElt_mem_indSub Vg v
  rw [inf_assoc, inf_comm (centralizer ({a} : Set G)) ι.range, ← inf_assoc,
    inf_eq_right.mpr hle]

theorem exists_lift_F24 (h : Setting24 ι a) {g : Equiv.Perm V6} (hg : g ∈ A5g) :
    ∃ x ∈ F24 ι a, Induces ι x g := by
  have hgOmega : g ∈ inducedGroup ι := by
    rw [h.induced]
    exact A5g_le_omegaPlus hg
  obtain ⟨n, hn, hng⟩ := hgOmega
  obtain ⟨c, hc⟩ := exists_mul_comm_of_induces h.inj h.centralizer_le h.a_cube h.a_induces hng
    (A5g_comm_w3 g hg)
  refine ⟨coordElt ι c * n, ?_, ?_⟩
  · rw [F24, Subgroup.mem_inf]
    refine ⟨mem_indSub.mpr ⟨g, hg, ?_⟩, ?_⟩
    · have h1 := (induces_coordElt (ι := ι) c).mul hng
      simpa using h1
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc
  · have h1 := (induces_coordElt (ι := ι) c).mul hng
    simpa using h1

theorem exists_lift_P24 (h : Setting24 ι a) {g : Equiv.Perm V6} (hg : g ∈ Vg) :
    ∃ x ∈ P24 ι a, Induces ι x g := by
  obtain ⟨x, hx, hxind⟩ := exists_lift_F24 h (Vg_le_A5g hg)
  refine ⟨x, ?_, hxind⟩
  have hx' : x ∈ indSub ι A5g ⊓ centralizer ({a} : Set G) := by
    simpa [F24] using hx
  rw [P24, Subgroup.mem_inf]
  exact ⟨mem_indSub.mpr ⟨g, hg, hxind⟩, hx'.2⟩

theorem card_P24 (h : Setting24 ι a) : Nat.card (P24 ι a) = 64 := by
  have hcard := card_eq_mul_of_lift (K := P24 ι a) (Hg := Vg) h.inj h.centralizer_le
    (show P24 ι a ≤ indSub ι Vg from inf_le_left) (fun g hg => exists_lift_P24 h hg)
  rw [P24_inf_range, card_E24 h, card_Vg] at hcard
  norm_num at hcard
  exact hcard

end CFSG.EvenSporadicStandard.HNRecog.Harada
