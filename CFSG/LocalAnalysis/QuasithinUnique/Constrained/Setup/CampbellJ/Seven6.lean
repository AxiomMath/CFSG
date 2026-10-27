module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven5
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalTr
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalAimg
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4a
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4b
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellExclTools
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDouble

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))}
  {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} {A : Subgroup G} {g : G}

private theorem aimgJ_Fcore_ne_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G := by
  intro e
  apply c.hα
  rw [e, c.seed.commutator_Hone_Fcore]
  exact Vmod_le_Ecore.trans c.seed.Ecore_le_Fcore

private theorem cj_eq_of_le_centralizer_Hone_Seven6 {N : Subgroup G}
    (hN : N ≤ Subgroup.centralizer (Hone S : Set G)) {g₀ : G} (hg : g₀ ∈ Hone S) :
    cj N g₀ = N := by
  apply le_antisymm
  · intro x hx
    have hxN : g₀ * x * g₀⁻¹ ∈ N := mem_cj.mp hx
    have hc : g₀ * (g₀ * x * g₀⁻¹) = (g₀ * x * g₀⁻¹) * g₀ :=
      Subgroup.mem_centralizer_iff.mp (hN hxN) g₀ hg
    have hx' : x = g₀ * x * g₀⁻¹ := by
      calc x = g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ := by group
        _ = g₀⁻¹ * ((g₀ * x * g₀⁻¹) * g₀) := by group
        _ = g₀⁻¹ * (g₀ * (g₀ * x * g₀⁻¹)) := by rw [← hc]
        _ = g₀ * x * g₀⁻¹ := by group
    rw [hx']; exact hxN
  · intro x hx
    rw [mem_cj]
    have hc : g₀ * x = x * g₀ := Subgroup.mem_centralizer_iff.mp (hN hx) g₀ hg
    have hx' : g₀ * x * g₀⁻¹ = x := by
      calc g₀ * x * g₀⁻¹ = (g₀ * x) * g₀⁻¹ := by group
        _ = (x * g₀) * g₀⁻¹ := by rw [hc]
        _ = x := by group
    rw [hx']; exact hx

private theorem cj_aimgJ_Zfix_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
  cj_eq_of_le_centralizer_Hone_Seven6
    (fun x hx => (aimgJ_Zfix_le_center_Hone c.seed α (c.lam.vmod α c.hαΛ)
      (aimgJ_Fcore_ne_Seven6 c) (x := x) hx).2)
    c.hgH

private theorem isElemAbelian_Ysub_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    CFSG.Open.IsElemAbelian 2 (YsubJ S α g) :=
  isElemAbelian_cj (isElemAbelian_aimg
    (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (isElemAbelian_cj (isElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      isElemAbelian_Fcore) g)) g

private theorem Ysub_le_core_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    YsubJ S α g ≤ CFSG.pCore 2 G := by
  obtain ⟨-, -, -, hUQ, -⟩ := U_factsJ c.seed c.lam c.hαΛ c.hgH c.hg2
  exact cj_le_core hUQ g

private theorem cj_Bb_g_le_J_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    cj (BbJ S α A g) g ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := by
  have hBQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    (c.facts71).2.2.1
  have h1 : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (cj (BbJ S α A g) g) := by
    have h2 := isMaxElemAbelian_cj g hBQ
    rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h2
  exact maxElem_le_thompsonJ (c.seed.max_core_facts.1 _ h1)

private theorem aimgJ_cj_Bb_g_le_core_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ≤
      CFSG.pCore 2 G := by
  have hBQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    (c.facts71).2.2.1
  have hBS : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (BbJ S α A g) :=
    c.seed.max_core_facts.1 _ hBQ
  have hBP : ⁅BbJ S α A g, PminusJ S α g⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun b hb y hy =>
      (isElemAbelian_iff.mp hBS.2.1).1 b hb y (Subgroup.mem_sup_left hy)
  have hPg : cj (PminusJ S α g) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) := by
    rw [PminusJ, cj_cj, c.hg2, cj_one]
  have hBgFi : ⁅cj (BbJ S α A g) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)⁆ = ⊥ := by
    have h := congrArg (fun H => cj H g) hBP
    simp only [cj_commutator, cj_bot, hPg] at h
    exact h
  have hFiJ : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le
  have hBgJ := cj_Bb_g_le_J_Seven6 c
  have hBgC : cj (BbJ S α A g) g ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) ⊓
      Subgroup.centralizer ((aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (Fcore G) : Subgroup G) : Set G) :=
    le_inf hBgJ fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (mul_comm_of_commutator_eq_bot hBgFi hx hw).symm
  have h1 := aimg_mono (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) hBgC
  rw [aimg_centralizer (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) hFiJ,
    aimg_self (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α),
    aimg_aimg_symm (Fcore_le_JS c.seed)] at h1
  have h2 : CFSG.Quasithin.thompsonJ (S : Subgroup G) ⊓
      Subgroup.centralizer (Fcore G : Set G) ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer (Fcore G : Set G) :=
    le_inf (inf_le_left.trans (thompsonJ_le_self' (S : Subgroup G))) inf_le_right
  exact h1.trans (h2.trans c.seed.sylow_inf_centralizer_Fcore_le)

private theorem aimgJ_cj_Bb_g_isMax_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g)) := by
  have hBQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    (c.facts71).2.2.1
  have hBgJ := cj_Bb_g_le_J_Seven6 c
  have hQ := aimgJ_cj_Bb_g_le_core_Seven6 c
  refine ⟨hQ, isElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
    (isElemAbelian_cj hBQ.2.1 g), fun B' hB'Q hB'e => ?_⟩
  rw [card_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) hBgJ, card_cj]
  exact hBQ.2.2 B' hB'Q hB'e

private theorem E_isMax_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G)
      (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ⊔
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ⊓
          Subgroup.centralizer ((tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
            (Fcore G) : Subgroup G) : Set G))) := by
  have hαBgmax := aimgJ_cj_Bb_g_isMax_Seven6 c
  have hA' : CFSG.Quasithin.IsMaxElemAbelian
      (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g)) :=
    (isMaxElemAbelian_cj_thompsonJ_iff (S := S) g).mpr
      (c.seed.isMaxElemAbelian_cj_of_core hαBgmax g)
  have hE := isMaxElemAbelian_tr_Fcore_supJ c.seed α g
    (A' := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g)) hA'
  have hE'Q : tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ⊔
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ⊓
        Subgroup.centralizer ((tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
          (Fcore G) : Subgroup G) : Set G)) ≤ CFSG.pCore 2 G :=
    sup_le (cj_le_core ((c.facts71).1 α c.hαΛ) g)
      (inf_le_left.trans (aimgJ_cj_Bb_g_le_core_Seven6 c))
  exact isMaxElemAbelian_core_of_le_cj (core_le_sylow S)
    ((isMaxElemAbelian_cj_thompsonJ_iff (S := S) g).mp hE) hE'Q

private theorem E_le_J_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ⊔
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ⊓
        Subgroup.centralizer ((tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
          (Fcore G) : Subgroup G) : Set G)) ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
  maxElem_le_thompsonJ (c.seed.max_core_facts.1 _ (E_isMax_Seven6 c))

private theorem cj_Bb_eq_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, cj (BbJ S α A g) a = BbJ S α A g := by
  intro a ha
  apply cj_eq_of_forall_mem
  intro b hb
  have hcomm : a * b * a⁻¹ * b⁻¹ ∈ BbJ S α A g :=
    (c.commutator_A_Bb_le (Subgroup.commutator_mem_commutator ha hb)).1
  have h : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
  rw [h]
  exact mul_mem hcomm hb

private theorem cj_C1_eq_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, cj (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) a =
      BbJ S α A g ⊓ Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) := by
  intro a ha
  apply cj_eq_of_forall_mem
  intro x hx
  have hcomm : a * x * a⁻¹ * x⁻¹ ∈ BbJ S α A g ⊓
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) :=
    c.commutator_A_Bb_le (Subgroup.commutator_mem_commutator ha hx.1)
  have h : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
  rw [h]
  exact mul_mem hcomm hx

private theorem C1_le_centralizer_cj_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((cj (YsubJ S α g) a : Subgroup G) : Set G) := by
  intro a ha
  have h1 : BbJ S α A g ⊓
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) := inf_le_right
  have h2 := cj_mono (g := a) h1
  rw [cj_C1_eq_Seven6 c a ha, ← centralizer_cj] at h2
  exact h2

private theorem YsupC1_eq_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) =
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ⊔
          (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ⊓
            Subgroup.centralizer ((tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
              (Fcore G) : Subgroup G) : Set G)))) g := by
  have hBgJ := cj_Bb_g_le_J_Seven6 c
  have hPJ : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    tr_Fcore_le_thompsonJ_sylowJ c.seed α g (c.lam.vmod α c.hαΛ)
  have hint : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ⊓
      Subgroup.centralizer ((cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (Fcore G)) g : Subgroup G) : Set G) ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    inf_le_left.trans aimg_le
  show YsubJ S α g ⊔ (BbJ S α A g ⊓
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) =
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ⊔
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g) ⊓
          Subgroup.centralizer ((cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
            (Fcore G)) g : Subgroup G) : Set G)))) g
  rw [aimg_sup hPJ hint, aimg_centralizer hPJ, aimg_symm_aimg hBgJ, cj_sup, cj_inf, cj_cj,
    c.hg2, cj_one, ← centralizer_cj]
  rfl

private theorem YsupC1_isMax_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G)
      (YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) := by
  have hBQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    (c.facts71).2.2.1
  have hYQ := Ysub_le_core_Seven6 c
  have hE'max := E_isMax_Seven6 c
  have hE'J := E_le_J_Seven6 c
  refine ⟨sup_le hYQ (inf_le_left.trans hBQ.1), ?_, fun B' hB'Q hB'e => ?_⟩
  · rw [YsupC1_eq_Seven6 c]
    exact isElemAbelian_cj (isElemAbelian_aimg
      (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm hE'max.2.1) g
  · rw [YsupC1_eq_Seven6 c, card_cj,
      card_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm) hE'J]
    exact hE'max.2.2 B' hB'Q hB'e

private theorem cj_Y_le_sup_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ x ∈ A, x ∉ CFSG.pCore 2 G →
      cj (YsubJ S α g) x ≤ YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) := by
  intro x hx hxQ
  have hYC₁max := YsupC1_isMax_Seven6 c
  have hYQ := Ysub_le_core_Seven6 c
  have hYel := isElemAbelian_Ysub_Seven6 c
  have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 x hx
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact c.hg2
  have hcomm : ⁅cj (YsubJ S α g) x, YsubJ S α g⁆ = ⊥ := by
    have h := (mixed_conjugation_calculusJ_def c.seed c.lam c.hαΛ c.hgH c.hgM hg2
      c.hgH c.hgM hg2 (maxElem_le_thompsonJ c.hA hx) hxQ hx2).2.1
    rw [YsubJ, cj_cj]
    exact h
  refine maxElem_le_of_commute hYC₁max (cj_le_core hYQ x) (isElemAbelian_cj hYel x) ?_
  have hYC : ∀ x ∈ YsubJ S α g, ∀ y ∈ (BbJ S α A g ⊓
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx
  intro y hy u hu
  obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := mem_sup_of_commute hYC hu
  have h1 : y * y₁ = y₁ * y := mul_comm_of_commutator_eq_bot hcomm hy hy₁
  have h2 : y * c₁ = c₁ * y :=
    Subgroup.mem_centralizer_iff.mp (C1_le_centralizer_cj_Seven6 c x hx hc₁) y hy
  calc y * (y₁ * c₁) = (y * y₁) * c₁ := by group
    _ = (y₁ * y) * c₁ := by rw [h1]
    _ = y₁ * (y * c₁) := by group
    _ = y₁ * (c₁ * y) := by rw [h2]
    _ = y₁ * c₁ * y := by group

private theorem cj_YsupC1_le_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) a ≤
      YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) := by
  intro a ha
  have hC₁inv := cj_C1_eq_Seven6 c
  have hYx := cj_Y_le_sup_Seven6 c
  by_cases haQ : a ∈ CFSG.pCore 2 G
  · obtain ⟨x₀, hx₀, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
    have hy₀ : x₀⁻¹ * a ∈ A := mul_mem (A.inv_mem hx₀) ha
    have hy₀Q : x₀⁻¹ * a ∉ CFSG.pCore 2 G := by
      intro hQ
      apply hx₀Q
      have h : x₀ = a * (x₀⁻¹ * a)⁻¹ := by group
      rw [h]
      exact mul_mem haQ ((CFSG.pCore 2 G).inv_mem hQ)
    have e1 : cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) a =
        cj (cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) x₀) (x₀⁻¹ * a) := by
      rw [cj_cj]; congr 1; group
    have h1 : cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) x₀ ≤
        YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) := by
      rw [cj_sup, hC₁inv x₀ hx₀]
      exact sup_le (hYx x₀ hx₀ hx₀Q) le_sup_right
    have h2 : cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) (x₀⁻¹ * a) ≤
        YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) := by
      rw [cj_sup, hC₁inv _ hy₀]
      exact sup_le (hYx _ hy₀ hy₀Q) le_sup_right
    rw [e1]
    exact (cj_mono h1).trans h2
  · rw [cj_sup, hC₁inv a ha]
    exact sup_le (hYx a ha haQ) le_sup_right

private theorem cj_YsupC1_eq_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) a =
      YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)) :=
  fun a ha => cj_eq_of_le (cj_YsupC1_le_Seven6 c a ha)

private theorem commutator_B_YsupC1_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅BbJ S α A g, YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))⁆ =
      ⁅BbJ S α A g, YsubJ S α g⁆ := by
  have hBQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    (c.facts71).2.2.1
  have hBS : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (BbJ S α A g) :=
    c.seed.max_core_facts.1 _ hBQ
  have hYC : ∀ x ∈ YsubJ S α g, ∀ y ∈ (BbJ S α A g ⊓
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G)), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx
  apply le_antisymm
  · rw [Subgroup.commutator_comm, Subgroup.commutator_comm (BbJ S α A g) (YsubJ S α g)]
    exact commutator_sup_of_commute hYC fun y hy w hw =>
      (isElemAbelian_iff.mp hBS.2.1).1 y hy.1 w hw
  · exact Subgroup.commutator_mono le_rfl le_sup_left

private theorem cj_commutator_B_Y_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, cj ⁅BbJ S α A g, YsubJ S α g⁆ a = ⁅BbJ S α A g, YsubJ S α g⁆ := by
  intro a ha
  have h1 : cj ⁅BbJ S α A g, YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))⁆ a =
      ⁅BbJ S α A g, YsubJ S α g ⊔ (BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))⁆ := by
    calc cj ⁅BbJ S α A g, YsubJ S α g ⊔ (BbJ S α A g ⊓
          Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))⁆ a
        = ⁅cj (BbJ S α A g) a, cj (YsubJ S α g ⊔ (BbJ S α A g ⊓
            Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))) a⁆ := cj_commutator
      _ = ⁅BbJ S α A g, YsubJ S α g ⊔ (BbJ S α A g ⊓
            Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G))⁆ := by
          rw [cj_Bb_eq_Seven6 c a ha, cj_YsupC1_eq_Seven6 c a ha]
  rw [commutator_B_YsupC1_Seven6 c] at h1
  exact h1

theorem DoubleSetupJ.commutator_B_Y_invariant (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ a ∈ A, ∀ b ∈ (⁅BbJ S α A g, YsubJ S α g⁆ : Subgroup G),
      a * b * a⁻¹ ∈ (⁅BbJ S α A g, YsubJ S α g⁆ : Subgroup G) := by
  intro a ha b hb
  exact mem_cj.mp (by rw [cj_commutator_B_Y_Seven6 c a ha]; exact hb)

private theorem commutator_B_Y_ne_bot_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅BbJ S α A g, YsubJ S α g⁆ ≠ ⊥ := by
  intro hb
  apply c.Y_not_le_B
  exact maxElem_le_of_commute ((c.facts71).2.2.1) (Ysub_le_core_Seven6 c)
    (isElemAbelian_Ysub_Seven6 c) fun y hy b hb' =>
      (mul_comm_of_commutator_eq_bot hb hb' hy).symm

private theorem aimgJ_commutator_cj_B_U_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      ⁅cj (BbJ S α A g) g,
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ =
      ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g),
        cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆ := by
  rw [aimg_commutator (cj_Bb_g_le_J_Seven6 c) aimg_le,
    aimg_aimg_symm (Y := cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)
      (tr_Fcore_le_thompsonJ_sylowJ c.seed α g (c.lam.vmod α c.hαΛ))]

private theorem commutator_cj_B_U_le_J_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅cj (BbJ S α A g) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
  commutator_le_of_le (cj_Bb_g_le_J_Seven6 c) aimg_le

private theorem ne_bot_aimgJ_cj_B_commutator_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g),
      tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G)⁆ ≠ ⊥ := by
  intro hb
  apply commutator_B_Y_ne_bot_Seven6 c
  have h2 := aimgJ_commutator_cj_B_U_Seven6 c
  have h3 : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      ⁅cj (BbJ S α A g) g,
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ = ⊥ := by
    rw [h2]; exact hb
  have h4 := (aimg_eq_bot_iff (S₀ := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
    (commutator_cj_B_U_le_J_Seven6 c)).mp h3
  have hYg : cj (YsubJ S α g) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) := by
    rw [YsubJ, cj_cj, c.hg2, cj_one]
  have h5 : cj ⁅BbJ S α A g, YsubJ S α g⁆ g = ⊥ := by
    rw [cj_commutator, hYg]; exact h4
  calc ⁅BbJ S α A g, YsubJ S α g⁆ = cj (cj ⁅BbJ S α A g, YsubJ S α g⁆ g) g⁻¹ :=
        cj_inv_cj.symm
    _ = ⊥ := by rw [h5, cj_bot]

private theorem cj_B_U_eq_Zfix_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅cj (BbJ S α A g) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ = Zfix S := by
  have hne := ne_bot_aimgJ_cj_B_commutator_Seven6 c
  have hαBgmax := aimgJ_cj_Bb_g_isMax_Seven6 c
  have hA' : CFSG.Quasithin.IsMaxElemAbelian
      (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (BbJ S α A g) g)) :=
    (isMaxElemAbelian_cj_thompsonJ_iff (S := S) g).mpr
      (c.seed.isMaxElemAbelian_cj_of_core hαBgmax g)
  have hcomm := (tr_commutator_eq_of_ne_botJ c.seed α g hA' hne).1
  have hZaeq : tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Zfix S) =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := cj_aimgJ_Zfix_Seven6 c
  rw [hZaeq] at hcomm
  have h2 := aimgJ_commutator_cj_B_U_Seven6 c
  have h7 : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      ⁅cj (BbJ S α A g) g,
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
    rw [h2]; exact hcomm
  calc ⁅cj (BbJ S α A g) g,
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
          ⁅cj (BbJ S α A g) g,
            aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
              (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆) :=
        (aimg_symm_aimg (commutator_cj_B_U_le_J_Seven6 c)).symm
    _ = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) := by rw [h7]
    _ = Zfix S := aimg_symm_aimg (Zfix_le_JS c.seed)

private theorem commutator_B_Y_eq_cj_Zfix_Seven6 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅BbJ S α A g, YsubJ S α g⁆ = cj (Zfix S) g := by
  have hUeq := cj_B_U_eq_Zfix_Seven6 c
  have hYg : cj (YsubJ S α g) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) := by
    rw [YsubJ, cj_cj, c.hg2, cj_one]
  have h1 : cj ⁅BbJ S α A g, YsubJ S α g⁆ g = Zfix S := by
    rw [cj_commutator, hYg]; exact hUeq
  calc ⁅BbJ S α A g, YsubJ S α g⁆ = cj (cj ⁅BbJ S α A g, YsubJ S α g⁆ g) g⁻¹ :=
        cj_inv_cj.symm
    _ = cj (Zfix S) g⁻¹ := by rw [h1]
    _ = cj (Zfix S) g := by rw [inv_eq_of_mul_eq_one_right c.hg2]

theorem DoubleSetupJ.absurd (c : DoubleSetupJ S ρ ψ Λ α A g) : False := by
  obtain ⟨a₀, ha₀, ha₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
  have hcj : cj (cj (Zfix S) g) a₀ = cj (Zfix S) g := by
    rw [← commutator_B_Y_eq_cj_Zfix_Seven6 c]
    exact cj_eq_of_forall_mem (c.commutator_B_Y_invariant a₀ ha₀)
  have hM := c.seed.normalizer_Zfix_le_Mnorm (mem_normalizer_of_cj_cj_eq hcj)
  exact c.hgM (c.seed.mem_Mnorm_of_conj_mem (c.hA.1 ha₀) ha₀Q hM)

end CFSG.QuasithinUnique.Setup.CampbellJ

end
