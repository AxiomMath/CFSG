module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24E

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {a : G}

private lemma coordElt_injective {ι : Elem2 6 →* G} (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private lemma induced_fixes {B : Subgroup G} (hι : Function.Injective ι)
    (hBab : IsMulCommutative B) {g : Equiv.Perm V6} (hg : g ∈ indGroup ι B) {v : V6}
    (hv : coordElt ι v ∈ B) : g v = v := by
  obtain ⟨b, hb, hb_ind⟩ := mem_indGroup.mp hg
  have hcommB : (⟨b, hb⟩ : B) * ⟨coordElt ι v, hv⟩ = ⟨coordElt ι v, hv⟩ * ⟨b, hb⟩ :=
    (isMulCommutative_iff.mp hBab) _ _
  have hcomm : b * coordElt ι v = coordElt ι v * b := by
    simpa using congrArg Subtype.val hcommB
  have h1 : b * coordElt ι v * b⁻¹ = coordElt ι v := by
    rw [hcomm]; group
  have h2 := hb_ind v
  rw [h1] at h2
  exact (coordElt_injective hι h2).symm

private lemma card_inf_range_le_fixed {B : Subgroup G} (h : Setting24 ι a)
    (hB : B ≤ P24 ι a) (hBab : IsMulCommutative B) (S : Finset (Equiv.Perm V6))
    (hS : ∀ g ∈ S, g ∈ indGroup ι B) :
    Nat.card ↥(B ⊓ ι.range) ≤ (Fix3.filter fun v => ∀ g ∈ S, g v = v).card := by
  classical
  have hD_le_E : B ⊓ ι.range ≤ E24 ι a := by
    rw [← P24_inf_range (ι := ι) (a := a)]
    exact inf_le_inf hB le_rfl
  let φ : ↥(B ⊓ ι.range) → V6 := fun x =>
    Classical.choose ((mem_E24_iff h).mp (hD_le_E x.2))
  have φ_spec (x : ↥(B ⊓ ι.range)) : φ x ∈ Fix3 ∧ (x : G) = coordElt ι (φ x) :=
    Classical.choose_spec ((mem_E24_iff h).mp (hD_le_E x.2))
  have φ_mem_B (x : ↥(B ⊓ ι.range)) : coordElt ι (φ x) ∈ B := by
    rw [← (φ_spec x).2]; exact x.2.1
  have φ_fixed (x : ↥(B ⊓ ι.range)) : ∀ g ∈ S, g (φ x) = φ x := fun g hg =>
    induced_fixes h.inj hBab (hS g hg) (φ_mem_B x)
  let f : ↥(B ⊓ ι.range) → {v : V6 // v ∈ Fix3.filter fun v => ∀ g ∈ S, g v = v} :=
    fun x => ⟨φ x, by
      rw [Finset.mem_filter]
      exact ⟨(φ_spec x).1, φ_fixed x⟩⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h1 : φ x = φ y := congrArg Subtype.val hxy
    rw [(φ_spec x).2, (φ_spec y).2, h1]
  have hcardF : Nat.card {v : V6 // v ∈ Fix3.filter fun v => ∀ g ∈ S, g v = v}
      = (Fix3.filter fun v => ∀ g ∈ S, g v = v).card :=
    Nat.subtype_card _ (fun _ => Iff.rfl)
  exact (Nat.card_le_card_of_injective f hf_inj).trans hcardF.le

theorem E24_unique (h : Setting24 ι a) {B : Subgroup G} (hB : B ≤ P24 ι a)
    (hBab : IsMulCommutative B) (hBcard : Nat.card B = 16) : B = E24 ι a := by
  classical
  haveI hBfin : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hBcard]; norm_num)
  haveI hEfin : Finite ↥(E24 ι a) :=
    Nat.finite_of_card_ne_zero (by rw [card_E24 h]; norm_num)
  have hBle_top : B ≤ indSub ι ⊤ := fun x hx => by
    obtain ⟨g, hg, hgind⟩ := mem_indSub.mp (hB hx).1
    exact mem_indSub.mpr ⟨g, Subgroup.mem_top g, hgind⟩
  have hcard : Nat.card B = Nat.card ↥(B ⊓ ι.range) * Nat.card (indGroup ι B) :=
    card_eq_mul_indGroup h.inj h.centralizer_le hBle_top
  have hcard16 : Nat.card ↥(B ⊓ ι.range) * Nat.card (indGroup ι B) = 16 := by
    rw [← hcard, hBcard]
  have hRleVg : indGroup ι B ≤ Vg := by
    intro g hg
    obtain ⟨x, hx, hxind⟩ := mem_indGroup.mp hg
    exact Induces.mem_of_mem_indSub h.inj (hB hx).1 hxind
  by_cases hRbot : indGroup ι B = ⊥
  ·
    have hRcard1 : Nat.card (indGroup ι B) = 1 := by rw [hRbot, Subgroup.card_bot]
    have hDcard : Nat.card ↥(B ⊓ ι.range) = 16 := by
      rw [hRcard1, mul_one] at hcard16
      exact hcard16
    have hD_le_E : B ⊓ ι.range ≤ E24 ι a := by
      rw [← P24_inf_range (ι := ι) (a := a)]
      exact inf_le_inf hB le_rfl
    have hDE : B ⊓ ι.range = E24 ι a := by
      apply Subgroup.eq_of_le_of_card_ge hD_le_E
      rw [hDcard, card_E24 h]
    have hE_le_B : E24 ι a ≤ B := by
      rw [← hDE]
      exact inf_le_left
    have hEB : E24 ι a = B := by
      apply Subgroup.eq_of_le_of_card_ge hE_le_B
      rw [hBcard, card_E24 h]
    exact hEB.symm
  ·
    obtain ⟨a', ha'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRbot
    let g : Equiv.Perm V6 := a'
    have hgR : g ∈ indGroup ι B := a'.2
    have hgne : g ≠ 1 := fun hh => ha' (Subtype.ext hh)
    have hfixg : (Fix3.filter fun v => g v = v).card = 4 :=
      card_fix_Vg_ne_one g (hRleVg hgR) hgne
    have hDle4 : Nat.card ↥(B ⊓ ι.range) ≤ 4 := by
      have hb := card_inf_range_le_fixed h hB hBab ({g} : Finset (Equiv.Perm V6)) (by
        intro h' hh'
        rw [Finset.mem_singleton] at hh'
        rw [hh']
        exact hgR)
      have hfilt : (Fix3.filter fun v => ∀ h' ∈ ({g} : Finset (Equiv.Perm V6)), h' v = v)
          = Fix3.filter fun v => g v = v := by
        apply Finset.filter_congr
        intro v hv
        simp
      rw [hfilt, hfixg] at hb
      exact hb
    have hRge4 : 4 ≤ Nat.card (indGroup ι B) := by
      have h1 : 4 * 4 ≤ 4 * Nat.card (indGroup ι B) := by
        calc 4 * 4 = 16 := by norm_num
          _ = Nat.card ↥(B ⊓ ι.range) * Nat.card (indGroup ι B) := hcard16.symm
          _ ≤ 4 * Nat.card (indGroup ι B) := Nat.mul_le_mul_right _ hDle4
      exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
    have hRle4 : Nat.card (indGroup ι B) ≤ 4 := by
      have h4 := Subgroup.card_le_of_le hRleVg
      rw [card_Vg] at h4
      exact h4
    have hRcard : Nat.card (indGroup ι B) = 4 := le_antisymm hRle4 hRge4
    have hReqVg : indGroup ι B = Vg := by
      apply Subgroup.eq_of_le_of_card_ge hRleVg
      rw [card_Vg, hRcard]
    have huV : uV ∈ indGroup ι B := by
      rw [hReqVg]; exact Subgroup.subset_closure (by simp)
    have hwV : wV ∈ indGroup ι B := by
      rw [hReqVg]; exact Subgroup.subset_closure (by simp)
    have hDle2 : Nat.card ↥(B ⊓ ι.range) ≤ 2 := by
      have hb := card_inf_range_le_fixed h hB hBab ({uV, wV} : Finset (Equiv.Perm V6)) (by
        intro h' hh'
        rw [Finset.mem_insert, Finset.mem_singleton] at hh'
        rcases hh' with rfl | rfl
        · exact huV
        · exact hwV)
      have hfilt : (Fix3.filter fun v =>
            ∀ h' ∈ ({uV, wV} : Finset (Equiv.Perm V6)), h' v = v)
          = Fix3.filter fun v => uV v = v ∧ wV v = v := by
        apply Finset.filter_congr
        intro v hv
        simp
      rw [hfilt, card_fix_Vg] at hb
      exact hb
    have hle : 16 ≤ 8 := by
      calc 16 = Nat.card ↥(B ⊓ ι.range) * Nat.card (indGroup ι B) := hcard16.symm
        _ ≤ 2 * 4 := Nat.mul_le_mul hDle2 hRcard.le
        _ = 8 := by norm_num
    exact absurd hle (by norm_num)

end CFSG.EvenSporadicStandard.HNRecog.Harada
