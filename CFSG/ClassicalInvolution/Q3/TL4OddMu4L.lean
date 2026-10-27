module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XAlpha

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Three


theorem hyp51At_of_threeLayers (hM11 : Q3CH.M11OddAutInner3) {G : Type} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) (hBelow : CIT3Below (Nat.card G)) {A : Subgroup G}
    {s z₁ z₂ : G} (hA : CFSG.Open.IsElemAbelian 2 A) (hsA : s ∈ A) (hz₁A : z₁ ∈ A)
    (hz₂A : z₂ ∈ A) (hAgen : A = Subgroup.closure {z₁, z₂, s}) (hs1 : s ≠ 1) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) (hz₁s : z₁ ≠ s) (hz₂s : z₂ ≠ s) (hz₃s : z₁ * z₂ ≠ s)
    {L₁ L₂ L₃ : Subgroup G}
    (h₁ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (h₃ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₃ (z₁ * z₂)) :
    Hyp51At A s := by
  have hsnc : ¬ ({s} : Set G) ⊆ Subgroup.center G := fun hs => hs1 (by
    have h1 : s ∈ Subgroup.center G := hs (Set.mem_singleton s)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := Q3CH.secData3_sFamily3 h₁ h₂ h₃
  obtain ⟨ι, -, ⟨D⟩⟩ := Q3CH.lieSystemMod3_of_secData3 hΦ hBelow hsnc
  have hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G) := h₁.le h₁.mem
  have hz₂C : z₂ ∈ Subgroup.centralizer ({s} : Set G) := h₂.le h₂.mem
  have hz₃C : z₁ * z₂ ∈ Subgroup.centralizer ({s} : Set G) := h₃.le h₃.mem
  have hz₃A : z₁ * z₂ ∈ A := A.mul_mem hz₁A hz₂A
  have hz₃1 : z₁ * z₂ ≠ 1 := fun h => hz₁₂ (by
    have hz₂2 : z₂ * z₂ = 1 := Lemma52Proof.mul_self_eq_one_of_mem hA hz₂A
    calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, hz₂2, mul_one]
      _ = z₂ := by rw [h, one_mul])
  obtain ⟨j₁, hj₁⟩ := Q3CH.exists_modOdd_le_secComp hΦ D (Q3CH.mem_sFamily3_one s L₁ L₂ L₃)
  obtain ⟨j₂, hj₂⟩ := Q3CH.exists_modOdd_le_secComp hΦ D (Q3CH.mem_sFamily3_two s L₁ L₂ L₃)
  obtain ⟨j₃, hj₃⟩ := Q3CH.exists_modOdd_le_secComp hΦ D (Q3CH.mem_sFamily3_three s L₁ L₂ L₃)
  have hmov : ∀ {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hbs : b ≠ s)
      (hbC : b ∈ Subgroup.centralizer ({s} : Set G)) {j : ι},
      oddQuotMk s ⟨b, hbC⟩ ∈ Q3CH.secComp hΦ D j → ∀ L : Subgroup (OddQuot s),
        CFSG.IsComponent L → MovedByAll A s L → L = Q3CH.secComp hΦ D j :=
    fun hbA hb1 hbs hbC _ hbj L hL hm =>
      Q3CH.eq_secComp_of_movedByAll hΦ D hA hsA hs1 hbA hb1 hbs hbC hbj hL hm
  have hm₁ := hmov hz₁A hz₁1 hz₁s hz₁C (hj₁ (oddQuotMk_mem_modOdd h₁.mem hz₁C))
  have hm₂ := hmov hz₂A hz₂1 hz₂s hz₂C (hj₂ (oddQuotMk_mem_modOdd h₂.mem hz₂C))
  have hm₃ := hmov hz₃A hz₃1 hz₃s hz₃C (hj₃ (oddQuotMk_mem_modOdd h₃.mem hz₃C))
  refine ⟨fun L L' hL hL' hm hm' => (hm₁ L hL hm).trans (hm₁ L' hL' hm').symm,
    fun L hL hm => ?_⟩
  have hnc : ∀ {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hbs : b ≠ s)
      (hbC : b ∈ Subgroup.centralizer ({s} : Set G)),
      ∃ y ∈ L, oddQuotMk s ⟨b, hbC⟩ * y ≠ y * oddQuotMk s ⟨b, hbC⟩ :=
    fun hbA hb1 hbs hbC => hm _ (oddQuotMk_mem_modOdd hbA hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hA hsA hs1 hbA hb1 hbs hbC)
  have hle₁ : modOdd s L₁ ≤ L := (hm₁ L hL hm) ▸ hj₁
  have hle₂ : modOdd s L₂ ≤ L := (hm₂ L hL hm) ▸ hj₂
  have hle₃ : modOdd s L₃ ≤ L := (hm₃ L hL hm) ▸ hj₃
  have hcl : ∀ d ∈ ({z₁, z₂, z₁ * z₂} : Set G), ∀ hdC : d ∈ Subgroup.centralizer ({s} : Set G),
      ∃ hdL : oddQuotMk s ⟨d, hdC⟩ ∈ L, ∃ K : Subgroup (↥L ⧸ Subgroup.center ↥L),
        IsClassicalMember3 K (QuotientGroup.mk ⟨oddQuotMk s ⟨d, hdC⟩, hdL⟩) := by
    rintro d (rfl | rfl | rfl) hdC
    · exact Q3CH.exists_classical_center h₁ hdC hle₁ (hnc hz₁A hz₁1 hz₁s hdC)
    · exact Q3CH.exists_classical_center h₂ hdC hle₂ (hnc hz₂A hz₂1 hz₂s hdC)
    · exact Q3CH.exists_classical_center h₃ hdC hle₃ (hnc hz₃A hz₃1 hz₃s hdC)
  have hrow : Q3NM.AutOddFreeOn ↥L (Q3CH.ClassicalInner ↥L) := by
    have hL₁ := hm₁ L hL hm
    have hk := Q3CH.kind_of_isComponent_secComp hΦ D (hL₁ ▸ hL)
    subst hL₁
    exact Q3CH.autOddFreeOn_range hM11 hk _
      (Q3CH.ker_comp_le_center D _ (sectionQuotientHom_injective _) j₁)
      (Q3CH.exists_comp_ne_one D _ (sectionQuotientHom_injective _) j₁)
  exact Q3CH.alphaOf_inducedImage_eq_bot_of_classical hA hAgen hrow hcl hz₁C
    (hnc hz₁A hz₁1 hz₁s hz₁C)

end Three

section Two


theorem hyp51At_of_twoLayersWC {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) (hBelow : CITBelowU p f (Nat.card G)) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {s z₁ z₂ : G}
    (hA : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂, s} : Set G)))
    (hA8 : Nat.card (Subgroup.closure ({z₁, z₂, s} : Set G)) = 8) (hs1 : s ≠ 1) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) (hz₁s : z₁ ≠ s) (hz₂s : z₂ ≠ s) {L₁ L₂ : Subgroup G}
    (h₁ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (hwc : Q3AM.WeakClosureAt s L₁) (hnorm : Q3AM.NormalizesImageAt s z₂ L₁) :
    Hyp51At (Subgroup.closure ({z₁, z₂, s} : Set G)) s := by
  classical
  set B := Subgroup.closure ({z₁, z₂, s} : Set G) with hB
  have hsB : s ∈ B := Subgroup.subset_closure (by simp)
  have hz₁B : z₁ ∈ B := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ B := Subgroup.subset_closure (by simp)
  have hsnc : ¬ ({s} : Set G) ⊆ Subgroup.center G := fun hs => hs1 (by
    have h1 : s ∈ Subgroup.center G := hs (Set.mem_singleton s)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hs := NDB.S.secData_sFamily h₁ h₂
  obtain ⟨D⟩ := hs.nonempty_lieSystem hBelow hsnc
  have key : ∀ L : Subgroup (OddQuot s), CFSG.IsComponent L → MovedByAll B s L →
      ∃ (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K),
        NDB.S.SComponent B s z₁ z₂ L₁ L₂ hs.normalizes D j₀ R₁ R₂ := fun L hL hmov =>
    NDB.S.exists_sComponent hp2 hq hA hsB hz₁B hz₂B hs1 hz₁1 hz₂1 hz₁s hz₂s hz₁₂ h₁ h₂ D hL hmov
  refine ⟨fun L L' hL hL' hm hm' => ?_, fun L hL hm => ?_⟩
  · obtain ⟨j₀, R₁, R₂, hC⟩ := key L hL hm
    rw [hC.moved L hL hm, hC.moved L' hL' hm']
  · obtain ⟨j₀, R₁, R₂, hC⟩ := key L hL hm
    have hLe := hC.moved L hL hm
    rw [hLe] at hm ⊢
    exact Q3AM.alphaOf_moved_of_wc hp2 hq hA hA8 hs1 hz₁1 hz₂1 hz₁₂ h₁ h₂ hs.normalizes D j₀ R₁
      R₂ hC hwc hnorm hm

end Two

section Cit3


@[expose] def TightE4LayersR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      LinkE4 R t → ¬ TriNbrAll R t → ∀ (J K' : Subgroup Y) (u x y x' : Y),
        E4FrameAt R t J K' u x y x' →
          (∃ L₁ L₂ L₃ : Subgroup Y,
            Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₁ t ∧
              Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₂ u ∧
              Q3NL.IsSectionMember3 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₃ (t * u)) ∨
          ∃ L₁ L₂ : Subgroup Y,
            IsSectionMember 3 2 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₁ t ∧
              IsSectionMember 3 2 (Subgroup.centralizer ({x * y * x'} : Set Y)) L₂ u ∧
              Q3AM.WeakClosureAt (x * y * x') L₁ ∧ Q3AM.NormalizesImageAt (x * y * x') u L₁


variable {n : ℕ}

theorem tightE4VtxSR_of_layers (hlay : TightE4LayersR 3 n) (h9 : CITBelowU 3 2 n) :
    TightE4VtxSR 3 n := by
  intro Y _ _ R S t hL hc hcase hA J K' u x y x' hF
  have ht := hL.datum.isUniqueInvolution_core
  have hYn : Nat.card Y ≤ n := hL.card.le
  have htu : t ≠ u := fun h =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (h ▸ hF.invJ))
  have htB : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hs1 : x * y * x' ≠ 1 := fun h => hF.notMem (h ▸ Subgroup.one_mem _)
  have hts : t ≠ x * y * x' := fun h => hF.notMem (h ▸ htB)
  have hus : u ≠ x * y * x' := fun h => hF.notMem (h ▸ huB)
  have htus : t * u ≠ x * y * x' := fun h => hF.notMem (h ▸ Subgroup.mul_mem _ htB huB)
  rcases hlay Y R S t hL hc hcase hA J K' u x y x' hF with
    ⟨L₁, L₂, L₃, h₁, h₂, h₃⟩ | ⟨L₁, L₂, h₁, h₂, hwc, hnorm⟩
  · exact hyp51At_of_threeLayers Q3CH.m11OddAutInner3 hL.center (hL.below.mono hYn)
      (hF.isElemAbelian hL) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) rfl hs1 ht.ne_one
      hF.invJ.ne_one htu hts hus htus h₁ h₂ h₃
  · exact hyp51At_of_twoLayersWC hL.center (CITBelowU.mono 3 2 hYn h9) (by norm_num) (by norm_num)
      (hF.isElemAbelian hL) (hF.natCard hL) hs1 ht.ne_one hF.invJ.ne_one htu hts hus h₁ h₂ hwc
      hnorm

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
