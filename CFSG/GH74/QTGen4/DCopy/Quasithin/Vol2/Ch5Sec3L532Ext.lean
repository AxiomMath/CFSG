module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3PerType
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsLoc

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

section Lemma

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem le_normalizer_sec53S_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    B ⊔ D ≤ Sec53F.fG1 M L H B ⊓ Sec53F.fG2 M L H D ∧
      Sec53F.fG1 M L H B ⊓ Sec53F.fG2 M L H D ≤
        Subgroup.normalizer (sec53S T L : Set G) := by
  refine ⟨?_, ?_⟩
  · rw [Sec53F.fG12_eq_F4 h527 hyp]
    exact le_sup_right
  · rw [← Sec53F.pCoreOf_fG12_F4 h527 hyp]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem stmt5_3_2At_of_modelAt_F4 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4) (hM : ModelAt t m) : Stmt5_3_2At_F4 t m := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨Y, _, hY, TY, P₁, P₂, hpair, ⟨φ⟩⟩ := hty.1
  obtain ⟨hfinY, hZ, hP⟩ := hM Y f hpar hY
  obtain ⟨hLF, hrig⟩ := hP TY P₁ P₂ hpair
  obtain ⟨-, ⟨hCT1, hO1, hCT2, hO2⟩, ⟨hN12, -, -⟩, ⟨hM1, hM2⟩⟩ :=
    h531 G T M L V H B D L₂ n t m f hyp hty hpar
  obtain ⟨hBD, hG12N⟩ := le_normalizer_sec53S_F4 h527 hyp
  have hSA : sec53S T L ≤ Sec53F.fG1 M L H B ⊓ Sec53F.fG2 M L H D := Sec53F.sec53S_le_fG12_F4 h527 hyp
  have hSL : sec52S M H ⊓ L = sec53S T L := (h527 G T M L V H B D L₂ n hyp).2.1.2.2.2.1
  have hmemS : ∀ s : ↥(Sec53F.fG1 M L H B ⊓ Sec53F.fG2 M L H D), (s : G) ∈ sec53S T L ↔
      ((S1421QA18.iso12 φ s : ↥(P₁ ⊓ P₂)) : Y) ∈ TY := fun s => by
    rw [← Sec53F.pCoreOf_fG12_F4 h527 hyp, ← pCoreOf_inf_eq hpair hLF]
    exact Sec53F.mem_pCoreOf_iff_of_equiv (S1421QA18.iso12 φ) s
  have h12 : ∀ y, y ∈ Sec53F.fG1 M L H B → y ∈ Subgroup.normalizer (sec53S T L : Set G) →
      y ∈ Sec53F.fG2 M L H D := fun y hy hyS => mem_A₂_of_normalizes φ hpair hmemS hSA hy hyS
  have h21 : ∀ y, y ∈ Sec53F.fG2 M L H D → y ∈ Subgroup.normalizer (sec53S T L : Set G) →
      y ∈ Sec53F.fG1 M L H B := fun y hy hyS => mem_A₁_of_normalizes φ hpair hmemS hSA hy hyS
  have hM12S : sec53M12 L H ≤ Subgroup.normalizer (sec53S T L : Set G) := hN12.ge

  have hLA1 : L ≤ Sec53F.fG1 M L H B := le_sup_left.trans le_sup_left
  have hKA2 : oTwoUpper H ≤ Sec53F.fG2 M L H D := le_sup_right
  have hA1 : Sec53F.fG1 M L H B ≤ sec53M1 L :=
    sup_le (sup_le Subgroup.le_normalizer (inf_le_right.trans Subgroup.le_normalizer))
      (inf_le_left.trans (Sec53F.B_le_normalizer_L hyp))
  have hA2 : Sec53F.fG2 M L H D ≤ sec53M2 H :=
    sup_le (sup_le hyp.D_le (inf_le_left.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (inf_le_right.trans (le_normalizer_oTwoUpper H))))) Subgroup.le_normalizer

  have hconj : ∀ {X : Subgroup G} {x : G}, X ≤ (X.comap (MulAut.conj x).toMonoidHom) →
      ∀ a ∈ X, x * a * x⁻¹ ∈ X := fun hX a ha => by
    have := hX ha
    simpa [MulAut.conj_apply] using this
  have hcomap : ∀ {X Z : Subgroup G} {x : G}, (∀ a ∈ Z, x * a * x⁻¹ ∈ X) →
      Z ≤ X.comap (MulAut.conj x).toMonoidHom := fun {X} {Z} {x} h a ha => by
    show (MulAut.conj x) a ∈ X
    rw [MulAut.conj_apply]
    exact h a ha
  have hN1 : sec53M12 L H ≤ Subgroup.normalizer (Sec53F.fG1 M L H B : Set G) := by
    intro x hx
    refine S1421QA18.normalizer_of_forall (M := sec53M12 L H) (fun x hx => hconj ?_) hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hx.1
    have hxK : x ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hx.2
    have hxS : x ∈ Subgroup.normalizer (sec53S T L : Set G) := hM12S hx
    refine sup_le (sup_le (hcomap fun a ha => hLA1 ((Subgroup.mem_normalizer_iff.mp hxL a).mp ha))
      (hcomap fun a ha => ?_)) (hcomap fun a ha => ?_)
    · rw [hSL] at ha
      exact (hSA.trans inf_le_left) ((Subgroup.mem_normalizer_iff.mp hxS a).mp ha)
    · have haS : a ∈ Subgroup.normalizer (sec53S T L : Set G) :=
        hG12N (hBD (Subgroup.mem_sup_left ha.1))
      have h1 : x * a * x⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp hxK a).mp ha.2
      have h2 : x * a * x⁻¹ ∈ Subgroup.normalizer (sec53S T L : Set G) :=
        (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hxS haS)
          ((Subgroup.normalizer _).inv_mem hxS)
      exact h21 _ (hKA2 h1) h2
  have hN2 : sec53M12 L H ≤ Subgroup.normalizer (Sec53F.fG2 M L H D : Set G) := by
    intro x hx
    refine S1421QA18.normalizer_of_forall (M := sec53M12 L H) (fun x hx => hconj ?_) hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hx.1
    have hxK : x ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hx.2
    have hxS : x ∈ Subgroup.normalizer (sec53S T L : Set G) := hM12S hx
    refine sup_le (sup_le (hcomap fun a ha => ?_) (hcomap fun a ha => ?_))
      (hcomap fun a ha => hKA2 ((Subgroup.mem_normalizer_iff.mp hxK a).mp ha))
    · have haS : a ∈ Subgroup.normalizer (sec53S T L : Set G) :=
        hG12N (hBD (Subgroup.mem_sup_right ha))
      have h1 : x * a * x⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hxL a).mp (Sec53F.D_le_L hyp ha)
      have h2 : x * a * x⁻¹ ∈ Subgroup.normalizer (sec53S T L : Set G) :=
        (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hxS haS)
          ((Subgroup.normalizer _).inv_mem hxS)
      exact h12 _ (hLA1 h1) h2
    · rw [hSL] at ha
      exact (hSA.trans inf_le_right) ((Subgroup.mem_normalizer_iff.mp hxS a).mp ha)
  have hNA1 : sec53M1 L ≤ Subgroup.normalizer (Sec53F.fG1 M L H B : Set G) := by
    rw [← hM1]
    exact sup_le (hLA1.trans Subgroup.le_normalizer) hN1
  have hNA2 : sec53M2 H ≤ Subgroup.normalizer (Sec53F.fG2 M L H D : Set G) := by
    rw [← hM2]
    exact sup_le (hKA2.trans Subgroup.le_normalizer) hN2
  refine ⟨Y, inferInstance, hY, S1421QA18.isExtension_of_rigid φ hpair hrig hA1 hA2
    (fun m hm a ha => (Subgroup.mem_normalizer_iff.mp (hNA1 hm) a).mp ha)
    (fun m hm a ha => (Subgroup.mem_normalizer_iff.mp (hNA2 hm) a).mp ha) ?_ ?_ ?_ ?_ ?_⟩
  · intro x hx
    rw [← hM1] at hx
    exact (sup_le_sup_right hLA1 _) hx
  · intro x hx
    rw [← hM2] at hx
    exact (sup_le_sup_right hKA2 _) hx
  · rintro y ⟨hy1, hy2⟩
    exact h12 y hy1 (hM12S ⟨hA1 hy1, hy2⟩)
  · rintro y ⟨hy2, hy1⟩
    exact h21 y hy2 (hM12S ⟨hy1, hA2 hy2⟩)
  · intro x hx hc₁ hc₂

    have hx₁ : x ∈ pCoreOf 2 L := by
      rw [← hO1]
      refine hCT1 ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have hhL : h ∈ Sec53F.fG1 M L H B :=
        hLA1 (CFSG.LieType.BorelTits.pCoreOf_le 2 L (hO1 ▸ hh))
      have := hc₁ h hhL
      calc h * x = (x * h * x⁻¹) * x := by rw [this]
        _ = x * h := by group
    have hx₂ : x ∈ pCoreOf 2 (oTwoUpper H) := by
      rw [← hO2]
      refine hCT2 ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have hhK : h ∈ Sec53F.fG2 M L H D :=
        hKA2 (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoUpper H) (hO2 ▸ hh))
      have := hc₂ h hhK
      calc h * x = (x * h * x⁻¹) * x := by rw [this]
        _ = x * h := by group
    exact eq_one_of_centralizes φ hrig.1 hZ
      (hLA1 (CFSG.LieType.BorelTits.pCoreOf_le 2 L hx₁))
      (hKA2 (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoUpper H) hx₂)) hc₁ hc₂

end Lemma

end CFSG.Quasithin.H13.L532
