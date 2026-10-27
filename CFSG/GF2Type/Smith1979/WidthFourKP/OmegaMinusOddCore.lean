module

public import CFSG.GF2Type.Smith1979.W4AsE11Five
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Minus

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open Subgroup Module
open CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem centralizer_eq_bot_or_card_eq_three_not_plus (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (hP : ¬ PlusAt H C) {F : Subgroup S.O}
    (hFM : F ≤ S.Mbar) (hodd : Odd (Nat.card F))
    (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    F ⊓ centralizer ({t} : Set S.O) = ⊥ ∨ Nat.card (F ⊓ centralizer ({t} : Set S.O) : _) = 3 := by
  by_cases hbot : F ⊓ centralizer ({t} : Set S.O) = ⊥
  · exact Or.inl hbot
  right
  set F' := F ⊓ centralizer ({t} : Set S.O) with hF'
  have hodd' : Odd (Nat.card F') :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hF'M : F' ≤ S.Mbar := inf_le_left.trans hFM
  have hFt : ∀ x ∈ F', x * t = t * x :=
    fun x hx => mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hnorm' : ∀ s ∈ S.Lbar g, ∀ x ∈ F', s * x * s⁻¹ ∈ F' :=
    fun s hs x hx => conj_mem_inf_centralizer H hnorm ht hs hx
  have hCF : ∀ x ∈ F', (∀ s ∈ S.Lbar g, s * x = x * s) → x = 1 :=
    fun x hx hc => eq_one_of_mem_of_commute H hodd' hx hc
  have hFR : F' ≤ Rbar S g t :=
    le_Rbar_of_commute H ht _ F' le_rfl hF'M hodd' hFt hnorm' hCF
  have hR : Rbar S g t ≠ S.Lbar g := by
    intro h
    apply hbot
    have h0 := inf_eq_bot_of_odd_of_isPGroup hodd' (S4.isPGroup_Lbar S H.conj_mem)
    rw [← h0]
    exact (inf_eq_left.mpr (h ▸ hFR)).symm
  have hLF : S.Lbar g ≤ normalizer (F' : Set S.O) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hnorm' s hs y, fun hy' => ?_⟩
    have := hnorm' s⁻¹ (inv_mem hs) _ hy'
    simpa [mul_assoc] using this
  rcases timmesfeld_4_8_F H hNo C ht ht1 hR hodd' hbot hFR hLF hCF with
    h3 | ⟨hVQ, h4, hΩ, -, f, hf, ha, hβ⟩
  · exact h3
  · exfalso
    apply hP
    obtain ⟨Qf, -, hpol, -, -, hsing⟩ := hΩ.exists_form
    set b : Vt S g t := orbV H.conj_mem ht (hFR hf) with hb
    have hb_orbit : b ∈ orbitOf (RmodN S g t) (aV ht) :=
      (mem_orbitOf_RmodN_iff H.conj_mem ht).mpr
        ⟨f, hFR hf, by rw [← coe_orbV H.conj_mem ht (hFR hf)]⟩
    have hb0 : b ≠ 0 := by
      intro h0
      exact ha (h0.symm ▸ Submodule.zero_mem _)
    have hbQ : Qf b = 0 := (hsing b hb0).mpr hb_orbit
    have ha_orbit : aV ht ∈ orbitOf (RmodN S g t) (aV ht) := ⟨1, one_mem _, rfl⟩
    have haQ0 : Qf (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ha_orbit
    have hβ' : Qf.polarBilin (aV ht) b = 0 := by
      rw [hpol]
      exact hβ
    refine ⟨t, ht, ht1, hVQ, hΩ, h4, ?_⟩
    refine ⟨Submodule.span (ZMod 2) ({aV ht, b} : Set (Vt S g t)), ?_, ?_⟩
    ·
      have hb_not : b ∉ Submodule.span (ZMod 2) ({aV ht} : Set (Vt S g t)) := ha
      have hli : LinearIndependent (ZMod 2) ![aV ht, b] := by
        rw [LinearIndependent.pair_iff]
        intro s u hsu
        rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
        · rcases zmod2_eq_zero_or_eq_one u with rfl | rfl
          · exact ⟨rfl, rfl⟩
          · simp only [zero_smul, one_smul, zero_add] at hsu
            exact absurd (by rw [hsu]; exact Submodule.zero_mem _) hb_not
        · rcases zmod2_eq_zero_or_eq_one u with rfl | rfl
          · simp only [one_smul, zero_smul, add_zero] at hsu
            exact absurd hsu (by simpa using aV_ne_zero H ht)
          · simp only [one_smul] at hsu
            have hb_eq : b = aV ht := by
              have h : aV ht = -b := eq_neg_of_add_eq_zero_left hsu
              rw [ZModModule.neg_eq_self] at h
              exact h.symm
            exact absurd (hb_eq.symm ▸ Submodule.subset_span (by simp)) hb_not
      have hdim := finrank_span_eq_card hli
      rw [show ({aV ht, b} : Set (Vt S g t)) = Set.range ![aV ht, b] by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        tauto]
      simpa using hdim
    ·
      intro v hv hv0
      obtain ⟨s, u, rfl⟩ := Submodule.mem_span_pair.mp hv
      rcases zmod2_eq_zero_or_eq_one s with rfl | rfl <;>
        rcases zmod2_eq_zero_or_eq_one u with rfl | rfl
      · simp only [zero_smul, add_zero] at hv0
        exact False.elim (hv0 rfl)
      · simpa using hb_orbit
      · simpa using ha_orbit
      · have hsum : Qf (aV ht + b) = 0 := by
          rw [QuadraticMap.map_add Qf (aV ht) b, haQ0, hbQ,
            ← QuadraticMap.polarBilin_apply_apply, hβ', add_zero, add_zero]
        exact (hsing _ hv0).mp (by simpa using hsum)

theorem card_oddCore_dvd_three_not_plus (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hP : ¬ PlusAt H C) (hw : S.width = 4) :
    Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 :=
  W4As.card_oddCore_dvd_three_of_centralizer H C hw fun hFM hodd hnorm =>
    centralizer_eq_bot_or_card_eq_three_not_plus H hNo C hP hFM hodd hnorm

end CFSG.GF2Type.Smith1979.W4Minus
