module

public import CFSG.GF2Type.Smith1979.W4AsE11Layer
public import CFSG.GF2Type.Smith1979.W4AsE11Step

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S11

@[expose] def ShultInput111W4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → S.width = 4 →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.O), t ∈ S.Lbar g → t ≠ 1 →
      (∀ x ∈ (P : Subgroup S.Mbar), (x : S.O) * t = t * x) →
      ¬ IsMulCommutative (closure {y : S.O | ∃ m ∈ S.Mbar, y = m * t * m⁻¹ ∧ y * t = t * y})

@[expose] def ShultF6ResidualW4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → S.width = 4 →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.Mbar), (t : S.O) ∈ S.Lbar g → t ≠ 1 →
      t ∈ (P : Subgroup S.Mbar) → (∀ x ∈ (P : Subgroup S.Mbar), x * t = t * x) →
      IsMulCommutative (wcl t) → wcl t ≤ P →
      (∀ a ∈ wcl t, ∀ x : S.Mbar, x⁻¹ * a * x ∈ (P : Subgroup S.Mbar) → x⁻¹ * a * x ∈ wcl t) →
      GoldschmidtConcl S.Mbar P (wcl t) →
      (Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
        timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) →
      False

@[expose] def ShultF6ResidualNIW4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → S.width = 4 →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.Mbar), (t : S.O) ∈ S.Lbar g → t ≠ 1 →
      t ∈ (P : Subgroup S.Mbar) → (∀ x ∈ (P : Subgroup S.Mbar), x * t = t * x) →
      IsMulCommutative (wcl t) → wcl t ≤ P →
      (∀ a ∈ wcl t, ∀ x : S.Mbar, x⁻¹ * a * x ∈ (P : Subgroup S.Mbar) → x⁻¹ * a * x ∈ wcl t) →
      GoldschmidtConcl S.Mbar P (wcl t) →
      (Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
        timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) →
      (∃ s ∈ wclSet t, s ≠ t) →
      False

theorem shultF6ResidualNIW4_of (h : ShultF6ResidualEW4) : ShultF6ResidualNIW4 := by
  intro G _ _ _ S g hy hirr hw hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni
  have ht2 : t * t = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S hy.hyp4.conj_mem ht)
  exact h G S g hy hirr hw hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni
    (not_centralizes_layer h55.1 h55.2.2 ht2 ht1 hni)

theorem shultF6ResidualW4_of (h : ShultF6ResidualNIW4) : ShultF6ResidualW4 := by
  intro G _ _ _ S g hy hirr hw hT P t ht ht1 htP htc hab hWP hcl hGo h55
  by_cases hni : ∃ s ∈ wclSet t, s ≠ t
  · exact h G S g hy hirr hw hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni
  · push Not at hni
    refine false_of_isolated_w4 hy hirr hw ht (fun e => ht1 (Subtype.ext e)) fun x hx hc => ?_
    have hs : (⟨x, hx⟩ : S.Mbar) * t * (⟨x, hx⟩ : S.Mbar)⁻¹ ∈ wclSet t :=
      ⟨⟨x, hx⟩, rfl, Subtype.ext (by simpa using hc)⟩
    simpa using congrArg Subtype.val (hni _ hs)

theorem shultInput111_of_w4
    (h : ShultF6ResidualW4) : ShultInput111W4 := by
  intro G _ _ _ S g hy hirr hw hT P t ht ht1 htP hab
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have hab' := isMulCommutative_wcl_of S htM hab
  have ht2 : (⟨t, htM⟩ : S.Mbar) * ⟨t, htM⟩ = 1 :=
    Subtype.ext (S4.mul_self_of_mem_Lbar S hy.hyp4.conj_mem ht)
  have htc : ∀ x ∈ (P : Subgroup S.Mbar), x * ⟨t, htM⟩ = ⟨t, htM⟩ * x := fun x hx =>
    Subtype.ext (htP x hx)
  have htP' : (⟨t, htM⟩ : S.Mbar) ∈ (P : Subgroup S.Mbar) := mem_sylow_of_commute P ht2 htc
  obtain ⟨hWP, hcl⟩ := wcl_stronglyClosed P htP' htc hab'
  have hGo := goldschmidtConcl_of S.Mbar P _ hWP hab' hcl
  have h55 := timmesfeld_5_5_of_hyp_w4 hy hirr hw
  exact h G S g hy hirr hw hT P ⟨t, htM⟩ ht (fun e => ht1 (congrArg Subtype.val e)) htP' htc
    hab' hWP hcl hGo h55

theorem shultInput111_w4
    (hL : LayerSurvivorsW4) : ShultInput111W4 :=
  shultInput111_of_w4 (shultF6ResidualW4_of (shultF6ResidualNIW4_of (shultF6ResidualEW4_of hL)))

@[expose] def S11_1StmtW4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    S11.Hyp S g → ¬ S.IsReducible → S.width = 4 →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) → S11.Timmesfeld11_1Stmt S

theorem s11_1Stmt_w4
    (hL : LayerSurvivorsW4) : S11_1StmtW4 := by
  intro G _ _ _ S g hy hirr hw hT
  by_contra hn
  obtain ⟨A, C⟩ := Cfg111.exists hy hirr hT hn
  obtain ⟨P, t, ht, ht1, htP, hab⟩ := C.exists_shult (noCommuting111_w4 G S g A C hw)
  exact shultInput111_w4 hL G S g hy hirr hw hT P t ht ht1 htP hab

end CFSG.GF2Type.Smith1979.W4As
