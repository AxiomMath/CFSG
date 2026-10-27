module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG CFSG.Open

theorem exists_noncomm_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∃ a b : G, a * b ≠ b * a) : ∃ a b : H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem stronglyClosed_contains_involutions (hG : Goldschmidt1974) {F : Type} [Group F] [Finite F]
    [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) (T : Sylow 2 F) {A : Subgroup F}
    (hA1 : A ≠ ⊥) (hAT : A ≤ (T : Subgroup F)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : F, g⁻¹ * a * g ∈ (T : Subgroup F) → g⁻¹ * a * g ∈ A) :
    ∀ x ∈ (T : Subgroup F), x * x = 1 → x ∈ A := by
  obtain ⟨-, hb, -⟩ := hG F T A hAT hAab hcl
  set M : Subgroup F := Subgroup.normalClosure (A : Set F) with hM
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h0 | h0
    · exact absurd (le_bot_iff.mp (h0 ▸ hAM)) hA1
    · exact h0
  let eM : ↥M ≃* F := (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hF2 : 2 ∣ Nat.card F := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := T.isPGroup'.exists_card_eq
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hT1 : Nat.card (T : Subgroup F) = 1 := by simpa using ha
      have : (T : Subgroup F) = ⊥ := Subgroup.eq_bot_of_card_eq _ hT1
      exact hA1 (le_bot_iff.mp (this ▸ hAT))
    exact (dvd_pow_self 2 ha0).trans (ha ▸ Subgroup.card_subgroup_dvd_card (T : Subgroup F))
  have hodd : goldschmidtOddCore ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (goldschmidtOddCore ↥M) with h0 | h0
    · exact h0
    · exfalso
      have hoddcard : Odd (Nat.card (goldschmidtOddCore ↥M)) :=
        CFSG.ComponentClassification.OddCore.odd_card ↥M
      rw [h0, Subgroup.card_top, Nat.card_congr eM.toEquiv] at hoddcard
      exact (Nat.not_even_iff_odd.mpr hoddcard) (even_iff_two_dvd.mpr hF2)
  let eQ : (↥M ⧸ goldschmidtOddCore ↥M) ≃* F :=
    ((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).trans eM
  have : IsSimpleGroup (↥M ⧸ goldschmidtOddCore ↥M) := eQ.isSimpleGroup
  have hP : IsSimpleGroup ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) :=
    Subgroup.topEquiv.isSimpleGroup
  have hPnab : ∃ a b : ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)), a * b ≠ b * a :=
    exists_noncomm_of_mulEquiv'
      (Subgroup.topEquiv (G := ↥M ⧸ goldschmidtOddCore ↥M)).symm
      (exists_noncomm_of_mulEquiv' eQ.symm hnab)
  obtain ⟨hquasi, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hPnab
  have hcomp : IsComponentOf (⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _, Group.isPerfect_def.mp hquasi.1, hquasi.2.1⟩
  have hlayer : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊤ :=
    top_le_iff.mp (le_sSup hcomp)
  intro x hxT hx2
  have hxM : x ∈ M := by rw [hMtop]; exact Subgroup.mem_top x
  set xm : ↥M := ⟨x, hxM⟩ with hxm
  set y := QuotientGroup.mk' (goldschmidtOddCore ↥M) xm with hy
  have hxsub : xm ∈ (T : Subgroup F).subgroupOf M := Subgroup.mem_subgroupOf.mpr hxT
  have hy2 : y ^ 2 = 1 := by
    have : xm ^ 2 = 1 := Subtype.ext (by simpa [sq] using hx2)
    rw [hy, ← map_pow, this, map_one]
  have hyc : y ∈ Subgroup.closure {t | t ∈ ((T : Subgroup F).subgroupOf M).map
      (QuotientGroup.mk' (goldschmidtOddCore ↥M)) ⊓
        goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) ∧ t ^ 2 = 1} := by
    refine Subgroup.subset_closure ⟨⟨Subgroup.mem_map.mpr ⟨xm, hxsub, rfl⟩, ?_⟩, hy2⟩
    rw [hlayer]
    exact Subgroup.mem_top _
  have hyA : y ∈ (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore ↥M)) := by
    rw [hb]
    exact Subgroup.mem_sup_right hyc
  obtain ⟨a, haA, hae⟩ := Subgroup.mem_map.1 hyA
  have hn : a⁻¹ * xm ∈ goldschmidtOddCore ↥M := QuotientGroup.eq.1 hae
  rw [hodd, Subgroup.mem_bot] at hn
  have hax : a = xm := by
    have := congrArg (a * ·) hn
    simpa using this.symm
  have haA' : (a : F) ∈ A := Subgroup.mem_subgroupOf.1 haA
  rw [hax] at haA'
  exact haA'

end CFSG.CGT.Timmesfeld75
