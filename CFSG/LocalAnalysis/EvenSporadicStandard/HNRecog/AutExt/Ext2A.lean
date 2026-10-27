module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.ExtendCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.TypingA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XNonempty

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

private theorem exists_iso_cent (h : F5Std a z) (h' : F5Std a' z') :
    ∃ α : G → G', IsIsoOn (Gx a) (Gx a') α := by
  obtain ⟨E, hE⟩ := h.typ.cent_a
  obtain ⟨E', hE'⟩ := h'.typ.cent_a
  obtain ⟨e⟩ := h.iface.nonempty_mulEquiv _ _ E E' hE hE'
  obtain ⟨f, hf, -⟩ := exists_isIsoOn_of_mulEquiv e
  exact ⟨f, hf⟩

theorem exists_iso_2A (h : F5Std a z) (h' : F5Std a' z') {α : G → G'}
    (hα : IsIsoOn (Gx a) (Gx a') α) {b : G} (hb : b ∈ orb2A a a) :
    ∃ β : G → G', IsIsoOn (Gx b) (Gx (α b)) β ∧ ∀ x ∈ Gxy a b, β x = α x := by
  have hαa : α a = a' := iso_apply_self h h' hα
  have hb' : α b ∈ orb2A a' a' := typing_2A h h' hα hb
  have hFb : F5Std b z := h.of_isConj hb.1 (IsConj.refl z)
  have hFb' : F5Std (α b) z' := h'.of_isConj hb'.1 (IsConj.refl z')
  have hab : b * a = a * b :=
    (h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb.1) (Or.inl hb.2)).symm
  have hat : a ∈ Gx b := mem_Gx.mpr hab
  have hab' : a' * (α b) = (α b) * a' :=
    h'.mul_comm (Or.inl (IsConj.refl a')) (Or.inl hb'.1) (Or.inl hb'.2)
  obtain ⟨β₀, hβ₀⟩ := exists_iso_cent hFb hFb'
  have ha_orb : a ∈ orb2A b b :=
    ⟨hb.1.symm, by rw [hab]; exact hb.1.symm.trans hb.2⟩
  have ha'_orb : a' ∈ orb2A (α b) (α b) :=
    ⟨hb'.1.symm, by rw [← hab']; exact hb'.1.symm.trans hb'.2⟩
  have horb : IsConjOrbit (Gx (α b)) (orb2A (α b) (α b)) := by
    simpa [tab5Set] using hFb'.loc.tableV.self.partition.orbit 0
  obtain ⟨k, hk, hkk⟩ :=
    horb.transitive (β₀ a) (typing_2A hFb hFb' hβ₀ ha_orb) a' ha'_orb
  obtain ⟨β, hβ, hβa⟩ :=
    exists_isIsoOn_fix (M := Gx b) (M' := Gx (α b)) (x := a) (x' := a') hβ₀ ⟨k, hk, hkk⟩
  have hβb : β b = α b := iso_apply_self hFb hFb' hβ
  have hdec : ∀ y ∈ Gxy a b, ∃ u ∈ Subgroup.closure ({a, b} : Set G),
      ∃ n ∈ derivedOf (Gxy a b), y = u * n := by
    intro y hy
    obtain ⟨n, hn, hyn⟩ := decomp_2A h hb y hy
    have haS : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hbS : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    have habS : a * b ∈ Subgroup.closure ({a, b} : Set G) :=
      (Subgroup.closure ({a, b} : Set G)).mul_mem haS hbS
    rcases hyn with hyn | hyn | hyn | hyn
    · exact ⟨1, Subgroup.one_mem _, n, hn, by rw [hyn, one_mul]⟩
    · exact ⟨a, haS, n, hn, by rw [hyn]⟩
    · exact ⟨b, hbS, n, hn, by rw [hyn]⟩
    · exact ⟨a * b, habS, n, hn, by rw [hyn]⟩
  obtain ⟨η, hη, hηa, hηb, hηout⟩ := exists_eta_A8 h hb
  exact extend_iso_cent (a := a) (t := b) (a' := a') (α := α) (β := β) (η := η)
    hα hαa hat hβ hβa hβb hdec hη hηa hηb hηout
    (fun ψ₁ ψ₂ h₁ h₂ n₁ n₂ => out_A8 h hb h₁ h₂ n₁ n₂)

theorem typing_2B (h : F5Std a z) (h' : F5Std a' z') {α : G → G'}
    (hα : IsIsoOn (Gx a) (Gx a') α) {b : G} (hb : b ∈ orb2B a z a) : α b ∈ orb2B a' z' a' := by
  have hαa : α a = a' := iso_apply_self h h' hα
  have hbG : b ∈ Gx a := h.mem_Gx_of_orb2B (IsConj.refl a) hb
  have hb2 : orderOf b = 2 := h.orderOf_eq_two (Or.inl hb.1)
  obtain ⟨c, hc1, hc2⟩ := exists_orb2A_inter_orb2A h hb
  have hcb : c * b = b * c :=
    (h.mul_comm (Or.inl hb.1) (Or.inl hc1.1) (Or.inl hc2.2)).symm
  obtain ⟨β, hβ, hβα⟩ := exists_iso_2A h h' hα hc1
  have hbGxy : b ∈ Gxy a c := mem_Gxy.mpr ⟨hbG, mem_Gx.mpr hcb⟩
  have hβb : β b = α b := hβα b hbGxy
  have hbc_orb : b ∈ orb2A c c :=
    ⟨hc1.1.symm.trans hb.1, by rw [hcb]; exact hc1.1.symm.trans hc2.2⟩
  have hFc : F5Std c z := h.of_isConj hc1.1 (IsConj.refl z)
  have hFc' : F5Std (α c) z' :=
    h'.of_isConj (typing_2A h h' hα hc1).1 (IsConj.refl z')
  have hβb_mem : β b ∈ orb2A (α c) (α c) := typing_2A hFc hFc' hβ hbc_orb
  have hA : IsConj a' (α b) := by
    rw [← hβb]
    exact (typing_2A h h' hα hc1).1.trans hβb_mem.1
  have hcard : Nat.card ↥(Gxy a' (α b)) = 30720 := by
    rw [card_Gxy_iso hα hbG, card_Gxy_2B h hb]
  have hinv : α b ∈ InvIn (Gx a') := iso_mem_inv hα ⟨hbG, hb2⟩
  rcases inv_cover h' hinv with h1 | h2 | h3 | h4 | h5
  · exfalso
    have hx : Nat.card ↥(Gxy a' a') = 177408000 := by
      rw [Gxy_eq_inf, inf_idem, card_Gx_a h']
    rw [h1] at hcard
    omega
  · exfalso
    have := card_Gxy_2A h' h2
    omega
  · exact h3
  · exfalso
    exact (not_isConj_of_isF5Type h'.iface h'.typ) (hA.trans h4.1.symm)
  · exfalso
    have := card_Gxy_2BB h' h5
    omega

theorem typing_2AB (h : F5Std a z) (h' : F5Std a' z') {α : G → G'}
    (hα : IsIsoOn (Gx a) (Gx a') α) {w : G} (hw : w ∈ orb2AB a z a) :
    α w ∈ orb2AB a' z' a' := by
  have hαa : α a = a' := iso_apply_self h h' hα
  have hwG : w ∈ Gx a := h.mem_Gx_of_orb2AB (IsConj.refl a) hw
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h2
  have haw : a * (a * w) = w := by rw [← mul_assoc, ha2, one_mul]
  have hb : a * w ∈ orb2B a z a := ⟨hw.2, by rw [haw]; exact hw.1⟩
  have h2B : α (a * w) ∈ orb2B a' z' a' := typing_2B h h' hα hb
  have hbG : a * w ∈ Gx a := (Gx a).mul_mem (self_mem_Gx a) hwG
  have hαw : α w = a' * α (a * w) := by
    have hm := hα.map_mul a (self_mem_Gx a) (a * w) hbG
    rw [haw, hαa] at hm
    exact hm
  have ha'a' : a' * a' = 1 := by
    have h2 : a' ^ 2 = 1 := by rw [← h'.typ.orderOf_a]; exact pow_orderOf_eq_one a'
    simpa [pow_two] using h2
  refine ⟨?_, ?_⟩
  · rw [hαw]; exact h2B.2
  · have hw' : a' * α w = α (a * w) := by rw [hαw, ← mul_assoc, ha'a', one_mul]
    rw [hw']; exact h2B.1

end CFSG.EvenSporadicStandard.HNRecog.Section4
