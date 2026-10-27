module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellExclTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDouble

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Exclusion

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem cj_sup_eq_of_commutator_le [Finite G] {F₁ F₂ : Subgroup G} [F₁.Normal] {a : G}
    (h : ∀ w ∈ F₂, a * w * a⁻¹ * w⁻¹ ∈ F₁) : cj (F₁ ⊔ F₂) a = F₁ ⊔ F₂ := by
  have hle : F₁ ⊔ F₂ ≤ cj (F₁ ⊔ F₂) a := by
    refine sup_le (fun x hx => mem_cj.mpr (Subgroup.mem_sup_left
      ((inferInstance : F₁.Normal).conj_mem x hx a))) (fun w hw => mem_cj.mpr ?_)
    have : a * w * a⁻¹ = (a * w * a⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (h w hw)) (Subgroup.mem_sup_right hw)
  exact (Subgroup.eq_of_le_of_card_ge hle card_cj.le).symm

namespace DoubleSetup

variable [Finite G] [Finite k] {α : (S : Subgroup G) ≃* (S : Subgroup G)} {A : Subgroup G} {g : G}
  (c : DoubleSetup S ρ ψ α A g)
include c

omit [Finite G] [Finite k] in
theorem g_inv : g⁻¹ = g := inv_eq_of_mul_eq_one_right c.hg2

theorem commutator_B0_Y_le (hYB : Ysub S α g ≤ Bb S α A g) :
    ⁅B0 S α A, Ysub S α g⁆ ≤ aimg (S : Subgroup G) α.symm (Zfix S) := by
  obtain ⟨hB0Q, hB0S, hB0le⟩ := c.seed.B0_isMax α c.hV c.hA
  have hCB0 : ∀ y ∈ Cc S α A g, ∀ w ∈ B0 S α A, y * w = w * y := fun y hy w hw =>
    (isElemAbelian_iff.mp hB0S.2.1).1 y hy.1 w hw
  have hPC : ∀ x ∈ Pminus S α g, ∀ y ∈ Cc S α A g, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have h1 : ⁅B0 S α A, Bb S α A g⁆ ≤ ⁅B0 S α A, Pminus S α g⁆ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_comm (B0 S α A) (Pminus S α g)]
    exact commutator_sup_of_commute hPC hCB0
  have h2 : ⁅B0 S α A, Pminus S α g⁆ ≤ aimg (S : Subgroup G) α.symm (Zfix S) := by
    have hR : B0 S α A ≤ thompsonJ (CFSG.pCore 2 G) := maxElem_le_thompsonJ hB0Q
    calc ⁅B0 S α A, Pminus S α g⁆ ≤ ⁅thompsonJ (CFSG.pCore 2 G), Pminus S α g⁆ :=
          Subgroup.commutator_mono hR le_rfl
      _ = ⁅Pminus S α g, thompsonJ (CFSG.pCore 2 G)⁆ := Subgroup.commutator_comm _ _
      _ ≤ aimg (S : Subgroup G) α.symm (Zfix S) :=
          c.seed.commutator_cj_Fa_R0_le α.symm c.hV' c.hFi g
  exact (Subgroup.commutator_mono le_rfl hYB).trans (h1.trans h2)

@[expose] def D0 (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G)
    (g : G) : Subgroup G :=
  cj (aimg (S : Subgroup G) α (cj (B0 S α A) g)) g

theorem D0_le_core (hYB : Ysub S α g ≤ Bb S α A g) : D0 S α A g ≤ CFSG.pCore 2 G := by
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  obtain ⟨hB0Q, hB0S, hB0le⟩ := c.seed.B0_isMax α c.hV c.hA
  have hS1 := c.commutator_B0_Y_le hYB
  have hYg : cj (Ysub S α g) g = aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g) := by
    rw [Ysub, cj_cj, c.hg2, cj_one]
  have hFaQ := c.seed.aimg_Fcore_le_core α c.hV
  have hPS : cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) :=
    (cj_le_core hFaQ g).trans hQS
  have h2 : ⁅cj (B0 S α A) g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ ≤ aimg (S : Subgroup G) α.symm (Zfix S) := by
    have := cj_mono (g := g) hS1
    rw [cj_commutator, hYg, cj_eq_of_le_center c.Zi_central g] at this
    exact this
  have hB0gS : cj (B0 S α A) g ≤ (S : Subgroup G) := (cj_le_core hB0le g).trans hQS
  have hUS : aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) ≤
      (S : Subgroup G) := aimg_le
  have h3 := aimg_mono (S := (S : Subgroup G)) (α := α) h2
  rw [aimg_commutator hB0gS hUS, aimg_aimg_symm hPS, aimg_aimg_symm Zfix_le_sylow] at h3
  have h4 := cj_mono (g := g) h3
  rw [cj_commutator, cj_cj, c.hg2, cj_one] at h4
  have hZF : cj (Zfix S) g ≤ Fcore G := by
    have := cj_mono (g := g) c.seed.Zfix_le_Fcore
    rwa [cj_eq_self_of_normal (Y := Fcore G)] at this
  have h5 : ⁅D0 S α A g, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G := h4.trans hZF
  intro d hd
  have hdS : d ∈ cj (S : Subgroup G) g :=
    cj_mono (aimg_le : aimg (S : Subgroup G) α (cj (B0 S α A) g) ≤ (S : Subgroup G)) hd
  have hdM : d ∈ Mnorm S ρ := by
    by_contra hdM
    apply c.hα
    exact c.seed.commutator_Hone_le_of_not_Mnorm α hdM fun f hf =>
      h5 (Subgroup.commutator_mem_commutator hd hf)
  exact c.seed.mem_core_of_mem_Mnorm_of_mem_cj c.hgM hdS hdM

theorem Pminus_le_B0_and (hYB : Ysub S α g ≤ Bb S α A g) :
    Pminus S α g ≤ B0 S α A ∧ Bb S α A g = B0 S α A := by
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  obtain ⟨hB0Q, hB0S, hB0le⟩ := c.seed.B0_isMax α c.hV c.hA
  have hD0 := c.D0_le_core hYB
  have hαBg : aimg (S : Subgroup G) α (cj (B0 S α A) g) ≤ CFSG.pCore 2 G := by
    have e : cj (D0 S α A g) g = aimg (S : Subgroup G) α (cj (B0 S α A) g) := by
      rw [D0, cj_cj, c.hg2, cj_one]
    rw [← e]
    exact cj_le_core hD0 g
  have hBgQ : IsMaxElemAbelian (CFSG.pCore 2 G) (cj (B0 S α A) g) := by
    have := isMaxElemAbelian_cj g hB0Q
    rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at this
  have hBgS := c.seed.max_core_facts.1 _ hBgQ
  have hαBgS := isMaxElemAbelian_aimg α hBgS
  have hαBgQ := IsSeed.isMaxElemAbelian_core_of_le hαBgS hαBg
  have hαBgR : aimg (S : Subgroup G) α (cj (B0 S α A) g) ≤ thompsonJ (CFSG.pCore 2 G) :=
    maxElem_le_thompsonJ hαBgQ
  have hFB : ⁅aimg (S : Subgroup G) α (cj (B0 S α A) g), Fcore G⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun x hx f hf => Fcore_commute_thompsonJ_core hf (hαBgR hx)
  have hBgFi : ⁅cj (B0 S α A) g, aimg (S : Subgroup G) α.symm (Fcore G)⁆ = ⊥ := by
    have h1 := aimg_commutator (S := (S : Subgroup G)) (α := α.symm)
      (aimg_le : aimg (S : Subgroup G) α (cj (B0 S α A) g) ≤ (S : Subgroup G)) Fcore_le_sylow
    rw [hFB, aimg_bot, aimg_symm_aimg hBgS.1] at h1
    exact h1.symm
  have hB0P : ⁅B0 S α A, Pminus S α g⁆ = ⊥ := by
    have := congrArg (fun H => cj H g) hBgFi
    simp only [cj_commutator, cj_cj, c.hg2, cj_one, cj_bot] at this
    exact this
  have hPQ : Pminus S α g ≤ CFSG.pCore 2 G := c.seed.Pminus_le_core α c.hV' g
  have hPB : Pminus S α g ≤ B0 S α A :=
    maxElem_le_of_commute hB0Q hPQ isElemAbelian_Pminus fun y hy b hb =>
      (mul_comm_of_commutator_eq_bot hB0P hb hy).symm
  refine ⟨hPB, le_antisymm (sup_le hPB inf_le_left) ?_⟩
  have hBC : B0 S α A ≤ Subgroup.centralizer ((Pminus S α g : Subgroup G) : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (mul_comm_of_commutator_eq_bot hB0P hb hy).symm
  exact (le_inf le_rfl hBC : B0 S α A ≤ Cc S α A g).trans le_sup_right

@[expose] def Xsub (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) : Subgroup G :=
  thompsonJ (CFSG.pCore 2 G ⊓ Subgroup.centralizer
    ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G))

theorem commutator_Hone_Fi_le (hP : Pminus S α g ≤ B0 S α A) :
    ⁅Hone S, aimg (S : Subgroup G) α.symm (Fcore G)⁆ ≤ Fcore G := by
  have hZiF : aimg (S : Subgroup G) α.symm (Zfix S) ≤ Fcore G := c.seed.aimg_Zfix_le_Fcore α.symm
  have hT : ⁅aimg (S : Subgroup G) α.symm (Fcore G), thompsonJ (S : Subgroup G)⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm, c.seed.commutator_thompsonJ_aimg_Fcore α.symm]; exact hZiF
  have hAg : ⁅aimg (S : Subgroup G) α.symm (Fcore G), cj A g⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm]
    have e : ⁅cj A g, aimg (S : Subgroup G) α.symm (Fcore G)⁆ =
        cj ⁅A, cj (aimg (S : Subgroup G) α.symm (Fcore G)) g⁻¹⁆ g := by
      rw [cj_commutator, cj_cj_inv]
    rw [e, c.g_inv]
    calc cj ⁅A, cj (aimg (S : Subgroup G) α.symm (Fcore G)) g⁆ g ≤ cj (Fcore G) g :=
          cj_mono ((Subgroup.commutator_mono le_rfl hP).trans c.commutator_A_B0_le_F)
      _ = Fcore G := cj_eq_self_of_normal
  rw [c.Hone_eq_sup, Subgroup.commutator_comm]
  exact commutator_sup_le (N := ⊤)
    (fun n _ v hv => (inferInstance : (Fcore G).Normal).conj_mem v hv n) le_top le_top hT hAg

theorem X_facts :
    aimg (S : Subgroup G) α.symm (B0 S α A) ≤ Xsub S α ∧ Xsub S α ≤ thompsonJ (CFSG.pCore 2 G) ∧
      Xsub S α ≤ aimg (S : Subgroup G) α.symm (thompsonJ (CFSG.pCore 2 G)) := by
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  obtain ⟨hB0Q, hB0S, hB0le⟩ := c.seed.B0_isMax α c.hV c.hA
  have hFaB0 : aimg (S : Subgroup G) α (Fcore G) ≤ B0 S α A :=
    (le_sup_right : aimg (S : Subgroup G) α (Fcore G) ≤
      Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)).trans le_sup_left
  have hFB0 : Fcore G ≤ B0 S α A := IsSeed.Fcore_le_B0 α A
  have hFiS : aimg (S : Subgroup G) α.symm (Fcore G) ≤ (S : Subgroup G) := aimg_le
  have hB0aQ : B0 S α A ≤ aimg (S : Subgroup G) α (CFSG.pCore 2 G) := by
    intro x hx
    have hxS : x ∈ (S : Subgroup G) := hB0S.1 hx
    have hxc : x ∈ Subgroup.centralizer ((aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (isElemAbelian_iff.mp hB0S.2.1).1 w (hFaB0 hw) x hx
    have h1 : aimg (S : Subgroup G) α ((S : Subgroup G) ⊓
        Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)) =
        (S : Subgroup G) ⊓ Subgroup.centralizer
          ((aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G) := by
      rw [aimg_centralizer Fcore_le_sylow, aimg_self]
    have h2 : x ∈ aimg (S : Subgroup G) α ((S : Subgroup G) ⊓
        Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)) := by
      rw [h1]; exact ⟨hxS, hxc⟩
    exact aimg_mono c.seed.sylow_inf_centralizer_Fcore_le h2
  have hB0'Q : aimg (S : Subgroup G) α.symm (B0 S α A) ≤ CFSG.pCore 2 G := by
    have := aimg_mono (S := (S : Subgroup G)) (α := α.symm) hB0aQ
    rwa [aimg_symm_aimg hQS] at this
  have hB0'max : IsMaxElemAbelian (CFSG.pCore 2 G) (aimg (S : Subgroup G) α.symm (B0 S α A)) :=
    ⟨hB0'Q, isElemAbelian_aimg α.symm hB0S.2.1, fun B hBQ hBe => by
      have := maxElem_card_le hB0S (hBQ.trans hQS) hBe
      rwa [← card_aimg (α := α.symm) hB0S.1] at this⟩
  have hFB0' : Fcore G ≤ aimg (S : Subgroup G) α.symm (B0 S α A) := fun f hf =>
    (mem_Fcore_iff.mp hf).2 _ hB0'max
  have hFiB0' : aimg (S : Subgroup G) α.symm (Fcore G) ≤
      aimg (S : Subgroup G) α.symm (B0 S α A) := aimg_mono hFB0
  have hB0'D : aimg (S : Subgroup G) α.symm (B0 S α A) ≤ CFSG.pCore 2 G ⊓ Subgroup.centralizer
      ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G) :=
    le_inf hB0'Q fun x hx => mem_centralizer_sup
      (fun y hy => (isElemAbelian_iff.mp hB0'max.2.1).1 y (hFB0' hy) x hx)
      (fun y hy => (isElemAbelian_iff.mp hB0'max.2.1).1 y (hFiB0' hy) x hx)
  have hB0'DAe : IsMaxElemAbelian (CFSG.pCore 2 G ⊓ Subgroup.centralizer
      ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G))
      (aimg (S : Subgroup G) α.symm (B0 S α A)) :=
    ⟨hB0'D, hB0'max.2.1, fun B hBD hBe => hB0'max.2.2 B (hBD.trans inf_le_left) hBe⟩
  have hAe : ∀ A', IsMaxElemAbelian (CFSG.pCore 2 G ⊓ Subgroup.centralizer
      ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G)) A' →
      IsMaxElemAbelian (CFSG.pCore 2 G) A' := fun A' hA' =>
    ⟨hA'.1.trans inf_le_left, hA'.2.1, fun B hBQ hBe =>
      (hB0'max.2.2 B hBQ hBe).trans (maxElem_card_le hA' hB0'D hB0'max.2.1)⟩
  refine ⟨maxElem_le_thompsonJ hB0'DAe, ?_, ?_⟩
  · exact thompsonJ_le_of_forall fun A' hA' => maxElem_le_thompsonJ (hAe A' hA')
  · refine thompsonJ_le_of_forall fun A' hA' => ?_
    have hA'D := hA'.1
    have hA'S : A' ≤ (S : Subgroup G) := (hA'D.trans inf_le_left).trans hQS
    have hDC : CFSG.pCore 2 G ⊓ Subgroup.centralizer
        ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G) ≤
        (S : Subgroup G) ⊓ Subgroup.centralizer
          ((aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G) :=
      le_inf (inf_le_left.trans hQS) (inf_le_right.trans
        (Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_right hy)))
    have hαD : aimg (S : Subgroup G) α (CFSG.pCore 2 G ⊓ Subgroup.centralizer
        ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G)) ≤
        CFSG.pCore 2 G := by
      have h1 := aimg_mono (S := (S : Subgroup G)) (α := α) hDC
      rw [aimg_centralizer hFiS, aimg_self, aimg_aimg_symm Fcore_le_sylow] at h1
      exact h1.trans c.seed.sylow_inf_centralizer_Fcore_le
    have hαA'Q : IsMaxElemAbelian (CFSG.pCore 2 G) (aimg (S : Subgroup G) α A') :=
      ⟨(aimg_mono hA'D).trans hαD, isElemAbelian_aimg α hA'.2.1, fun B hBQ hBe => by
        have := (hAe A' hA').2.2 B hBQ hBe
        rwa [← card_aimg (α := α) hA'S] at this⟩
    have hαA'R : aimg (S : Subgroup G) α A' ≤ thompsonJ (CFSG.pCore 2 G) :=
      maxElem_le_thompsonJ hαA'Q
    have := aimg_mono (S := (S : Subgroup G)) (α := α.symm) hαA'R
    rwa [aimg_symm_aimg hA'S] at this

theorem Y_not_le_B : ¬ Ysub S α g ≤ Bb S α A g := by
  classical
  intro hYB
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  obtain ⟨hB0Q, hB0S, hB0le⟩ := c.seed.B0_isMax α c.hV c.hA
  obtain ⟨hPB0, hBeq⟩ := c.Pminus_le_B0_and hYB
  have hR := c.commutator_Hone_Fi_le hPB0
  obtain ⟨hX1, hX2, hX3⟩ := c.X_facts
  obtain ⟨hPQ, hPAdm, hUF, hUQ, hUAdm⟩ := c.seed.U_facts α c.hV c.hg2
  have hPS : cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) := hPQ.trans hQS
  have hUR : aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) ≤
      thompsonJ (CFSG.pCore 2 G) := by
    obtain ⟨A', hA', hle⟩ := hUAdm
    exact hle.trans (maxElem_le_thompsonJ hA')
  have hYB0 : Ysub S α g ≤ B0 S α A := hBeq ▸ hYB
  have hAY : ⁅A, Ysub S α g⁆ ≤ Fcore G :=
    (Subgroup.commutator_mono le_rfl hYB0).trans c.commutator_A_B0_le_F
  have hAgU : ⁅cj A g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ ≤ Fcore G := by
    have e : ⁅cj A g, aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ =
        cj ⁅A, cj (aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g⁻¹⁆ g := by
      rw [cj_commutator, cj_cj_inv]
    rw [e, c.g_inv]
    calc cj ⁅A, cj (aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g⁆ g ≤ cj (Fcore G) g := cj_mono hAY
      _ = Fcore G := cj_eq_self_of_normal
  have hZX : ⁅Xsub S α, Fcore G ⊔ aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = Zfix S := by
    apply le_antisymm
    · have h1 : ⁅Xsub S α, Fcore G ⊔ aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ ≤
          ⁅Xsub S α, aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ := by
        rw [Subgroup.commutator_comm, sup_comm, Subgroup.commutator_comm (Xsub S α)]
        exact commutator_sup_of_commute
          (fun x hx y hy => Fcore_commute_thompsonJ_core hy (hUR hx))
          (fun y hy w hw => (Fcore_commute_thompsonJ_core hy (hX2 hw)).symm)
      have h2 : ⁅Xsub S α, aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ ≤
          ⁅aimg (S : Subgroup G) α.symm (thompsonJ (CFSG.pCore 2 G)), aimg (S : Subgroup G) α.symm
            (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ := Subgroup.commutator_mono hX3 le_rfl
      have h3 : ⁅aimg (S : Subgroup G) α.symm (thompsonJ (CFSG.pCore 2 G)),
          aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = Zfix S := by
        have := aimg_commutator (S := (S : Subgroup G)) (α := α.symm)
          ((thompsonJ_le_self' _).trans hQS) hPS
        rw [c.commutator_R0_Pg, aimg_symm_aimg Zfix_le_sylow] at this
        exact this.symm
      exact h1.trans (h2.trans h3.le)
    · have h1 : ⁅aimg (S : Subgroup G) α.symm (B0 S α A), aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = Zfix S := by
        have := aimg_commutator (S := (S : Subgroup G)) (α := α.symm) hB0S.1 hPS
        rw [c.commutator_B0_Pg, aimg_symm_aimg Zfix_le_sylow] at this
        exact this.symm
      calc Zfix S = ⁅aimg (S : Subgroup G) α.symm (B0 S α A), aimg (S : Subgroup G) α.symm
            (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ := h1.symm
        _ ≤ ⁅Xsub S α, aimg (S : Subgroup G) α.symm
            (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ := Subgroup.commutator_mono hX1 le_rfl
        _ ≤ _ := Subgroup.commutator_mono le_rfl le_sup_right
  have hZa : ∀ a ∈ cj A g, cj (Zfix S) a = Zfix S := by
    intro a ha
    have haH : a ∈ Hone S := by rw [c.Hone_eq_sup]; exact Subgroup.mem_sup_right ha
    have e1 : cj (Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G)) a =
        Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) :=
      cj_sup_eq_of_commutator_le fun w hw => hR (Subgroup.commutator_mem_commutator haH hw)
    have e2 : cj (Fcore G ⊔ aimg (S : Subgroup G) α.symm
        (cj (aimg (S : Subgroup G) α (Fcore G)) g)) a =
        Fcore G ⊔ aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) :=
      cj_sup_eq_of_commutator_le fun u hu => hAgU (Subgroup.commutator_mem_commutator ha hu)
    have hD : cj (CFSG.pCore 2 G ⊓ Subgroup.centralizer
        ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G)) a =
        CFSG.pCore 2 G ⊓ Subgroup.centralizer
          ((Fcore G ⊔ aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G) := by
      rw [cj_inf, cj_eq_self_of_normal (Y := CFSG.pCore 2 G), ← centralizer_cj, e1]
    have hX : cj (Xsub S α) a = Xsub S α := cj_thompsonJ_eq hD
    calc cj (Zfix S) a = cj ⁅Xsub S α, Fcore G ⊔ aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ a := by rw [hZX]
      _ = ⁅cj (Xsub S α) a, cj (Fcore G ⊔ aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)) a⁆ := cj_commutator
      _ = ⁅Xsub S α, Fcore G ⊔ aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ := by rw [hX, e2]
      _ = Zfix S := hZX
  obtain ⟨a₀, ha₀, ha₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
  have ha : g * a₀ * g⁻¹ ∈ cj A g := by
    rw [mem_cj]
    have : g * (g * a₀ * g⁻¹) * g⁻¹ = a₀ := by
      calc g * (g * a₀ * g⁻¹) * g⁻¹ = (g * g) * a₀ * (g⁻¹ * g⁻¹) := by group
        _ = a₀ := by rw [c.hg2, c.g_inv, c.hg2]; group
    rw [this]; exact ha₀
  have hmemN : g * a₀ * g⁻¹ ∈ Subgroup.normalizer (Zfix S : Set G) :=
    mem_normalizer_of_le_cj (hZa _ ha).symm.le
  have hM := c.seed.normalizer_Zfix_le_Mnorm hmemN
  exact c.hgM (c.seed.mem_Mnorm_of_conj_mem (c.hA.1 ha₀) ha₀Q hM)

end DoubleSetup

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem final_translated_containment_exclusion (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hVall : ∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) β (Vmod G) ≤ CFSG.pCore 2 G)
    (hα : ¬ ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) {g : G}
    (hgH : g ∈ Hone S) (hgM : g ∉ Mnorm S ρ) (hg2 : g ^ 2 = 1) :
    ¬ Ysub S α g ≤ Bb S α A g :=
  (⟨h, hVall α, hVall α.symm, hα, hA, hAQ, hgH, hgM, by rw [← pow_two]; exact hg2⟩ :
    DoubleSetup S ρ ψ α A g).Y_not_le_B

end IsSeed

end Exclusion

end CFSG.QuasithinUnique.Setup.Campbell
