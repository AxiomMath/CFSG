module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalAimg
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4a
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellExclTools
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDouble

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))}
  {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} {A : Subgroup G} {g : G}

private theorem cj_eq_of_le_centralizer_HoneJ_Seven34 {N : Subgroup G}
    (hN : N ≤ Subgroup.centralizer (Hone S : Set G)) {g : G} (hg : g ∈ Hone S) :
    cj N g = N :=
  cj_eq_of_forall_mem fun x hx => mem_of_central_conj hN hg hx

private def CcJ_Seven34 (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (A : Subgroup G) (g : G) :
    Subgroup G :=
  B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G)

private def D0J_Seven34 (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (A : Subgroup G) (g : G) :
    Subgroup G :=
  cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g)) g

private theorem hF_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G := by
  intro e
  apply c.hα
  rw [e, c.seed.commutator_Hone_Fcore]
  exact Vmod_le_Ecore.trans c.seed.Ecore_le_Fcore

private theorem hFi_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) ≠ Fcore G := by
  intro e
  apply hF_Seven34 c
  calc aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)
      = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
          (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) := by rw [e]
    _ = Fcore G := aimg_aimg_symm (Fcore_le_JS c.seed)

private theorem hV'_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Vmod G) ≤ CFSG.pCore 2 G := by
  have h : α.symm ∈ Λ := by
    have := Λ.inv_mem c.hαΛ
    rwa [MulAut.inv_def] at this
  exact c.lam.vmod α.symm h

private theorem Zi_central_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) ≤
      Hone S ⊓ Subgroup.centralizer (Hone S : Set G) :=
  aimgJ_Zfix_le_center_Hone c.seed α.symm (hV'_Seven34 c) (hFi_Seven34 c)

private theorem cj_Zi_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S)) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) :=
  cj_eq_of_le_centralizer_HoneJ_Seven34 (fun z hz => (Zi_central_Seven34 c hz).2) c.hgH

private theorem commutator_A_B0_le_F_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅A, B0J S α A⁆ ≤ Fcore G :=
  (c.facts71).2.2.2.trans
    (sup_le c.seed.Zfix_le_Fcore (aimgJ_Zfix_le_Fcore c.seed α))

private theorem commutator_Hone_le_of_not_MnormJ_Seven34 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {d : G}
    (hdM : d ∉ Mnorm S ρ)
    (hd : ∀ f ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
      d * f * d⁻¹ * f⁻¹ ∈ Fcore G) :
    ⁅Hone S, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ ≤ Fcore G := by
  have hNV : ∀ n ∈ (⊤ : Subgroup G), ∀ v ∈ Fcore G, n * v * n⁻¹ ∈ Fcore G :=
    fun n _ v hv => (inferInstance : (Fcore G).Normal).conj_mem v hv n
  set K := commModIn (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G))
    (Fcore G) ⊤ hNV with hK
  have hZaF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ≤ Fcore G :=
    aimgJ_Zfix_le_Fcore h α
  have hTJ : CFSG.Quasithin.thompsonJ (S : Subgroup G) ≤ K := by
    intro t ht
    refine ⟨trivial, fun f hf => ?_⟩
    have h1 : t * f * t⁻¹ * f⁻¹ ∈ (⁅CFSG.Quasithin.thompsonJ (S : Subgroup G),
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator ht hf
    rw [commutator_thompsonJ_aimgJ_Fcore h α] at h1
    have h2 := (Fcore G).inv_mem (hZaF h1)
    have e : ⁅f, t⁆ = (t * f * t⁻¹ * f⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact h2
  have hdK : d ∈ K := by
    refine ⟨trivial, fun f hf => ?_⟩
    have e : ⁅f, d⁆ = (d * f * d⁻¹ * f⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact (Fcore G).inv_mem (hd f hf)
  have hH := h.Hone_le_of_mem_not_Mnorm hTJ hdK hdM
  rw [Subgroup.commutator_le]
  intro y hy f hf
  have e : ⁅y, f⁆ = ⁅f, y⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Fcore G).inv_mem ((hH hy).2 f hf)

private theorem commutator_B0_Y_leJ_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hYB : YsubJ S α g ≤ BbJ S α A g) :
    ⁅B0J S α A, YsubJ S α g⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) := by
  have hB0Q := (c.facts71).2.1
  have hB0S := c.seed.max_core_facts.1 _ hB0Q
  have hCB0 : ∀ y ∈ CcJ_Seven34 S α A g, ∀ w ∈ B0J S α A, y * w = w * y := fun y hy w hw =>
    (isElemAbelian_iff.mp hB0S.2.1).1 y hy.1 w hw
  have hPC : ∀ x ∈ PminusJ S α g, ∀ y ∈ CcJ_Seven34 S α A g, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have h1 : ⁅B0J S α A, BbJ S α A g⁆ ≤ ⁅B0J S α A, PminusJ S α g⁆ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_comm (B0J S α A) (PminusJ S α g)]
    exact commutator_sup_of_commute hPC hCB0
  have h2 : ⁅B0J S α A, PminusJ S α g⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) := by
    have hR : B0J S α A ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
      maxElem_le_thompsonJ hB0Q
    calc ⁅B0J S α A, PminusJ S α g⁆
        ≤ ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), PminusJ S α g⁆ :=
          Subgroup.commutator_mono hR le_rfl
      _ = ⁅PminusJ S α g, CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆ :=
          Subgroup.commutator_comm _ _
      _ ≤ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) :=
          commutator_cj_Fa_R0_leJ c.seed α.symm (hV'_Seven34 c) (hFi_Seven34 c) c.hgH
  exact (Subgroup.commutator_mono le_rfl hYB).trans (h1.trans h2)

private theorem D0J_le_core_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hYB : YsubJ S α g ≤ BbJ S α A g) : D0J_Seven34 S α A g ≤ CFSG.pCore 2 G := by
  have hB0Q := (c.facts71).2.1
  have hS1 := commutator_B0_Y_leJ_Seven34 c hYB
  have hYg : cj (YsubJ S α g) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) := by
    rw [YsubJ, cj_cj, c.hg2, cj_one]
  have hPS : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    tr_Fcore_le_thompsonJ_sylowJ c.seed α g (c.lam.vmod α c.hαΛ)
  have h2 : ⁅cj (B0J S α A) g, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) := by
    have := cj_mono (g := g) hS1
    rw [cj_commutator, hYg, cj_Zi_Seven34 c] at this
    exact this
  have hBgQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (cj (B0J S α A) g) := by
    have := isMaxElemAbelian_cj g hB0Q
    rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at this
  have hB0gJ : cj (B0J S α A) g ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    maxElem_le_thompsonJ (c.seed.max_core_facts.1 _ hBgQ)
  have hUS : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le
  have h3 := aimg_mono (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) h2
  rw [aimg_commutator hB0gJ hUS, aimg_aimg_symm hPS, aimg_aimg_symm (Zfix_le_JS c.seed)] at h3
  have h4 := cj_mono (g := g) h3
  rw [cj_commutator, cj_cj, c.hg2, cj_one] at h4
  have hZF : cj (Zfix S) g ≤ Fcore G := by
    have := cj_mono (g := g) c.seed.Zfix_le_Fcore
    rwa [cj_eq_self_of_normal (Y := Fcore G)] at this
  have h5 : ⁅D0J_Seven34 S α A g, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (Fcore G)⁆ ≤ Fcore G := h4.trans hZF
  intro d hd
  have hdJ : d ∈ cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g :=
    cj_mono (aimg_le : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (cj (B0J S α A) g) ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G)) hd
  have hdS : d ∈ cj (S : Subgroup G) g :=
    cj_mono (thompsonJ_le_self' (S : Subgroup G)) hdJ
  have hdM : d ∈ Mnorm S ρ := by
    by_contra hdM
    apply c.hα
    exact commutator_Hone_le_of_not_MnormJ_Seven34 c.seed α hdM fun f hf =>
      h5 (Subgroup.commutator_mem_commutator hd hf)
  exact c.seed.mem_core_of_mem_Mnorm_of_mem_cj c.hgM hdS hdM

private theorem commutator_B0_PminusJ_Seven34 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hY : YsubJ S α g ≤ BbJ S α A g) :
    ⁅B0J S α A, PminusJ S α g⁆ = ⊥ := by
  have hB0Q := (c.facts71).2.1
  have hD0 := D0J_le_core_Seven34 c hY
  have hαBg : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g) ≤
      CFSG.pCore 2 G := by
    have e : cj (D0J_Seven34 S α A g) g =
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g) := by
      rw [D0J_Seven34, cj_cj, c.hg2, cj_one]
    rw [← e]
    exact cj_le_core hD0 g
  have hBgQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (cj (B0J S α A) g) := by
    have := isMaxElemAbelian_cj g hB0Q
    rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at this
  have hBgS := c.seed.max_core_facts.1 _ hBgQ
  have hαBgS : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g)) :=
    (isMaxElemAbelian_JS_iff _).mp
      (isMaxElemAbelian_aimg α ((isMaxElemAbelian_JS_iff _).mpr hBgS))
  have hαBgQ := IsSeed.isMaxElemAbelian_core_of_le hαBgS hαBg
  have hαBgR : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := maxElem_le_thompsonJ hαBgQ
  have hFB : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g),
      Fcore G⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun x hx f hf =>
      Fcore_commute_thompsonJ_core hf (hαBgR hx)
  have hB0gJ : cj (B0J S α A) g ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    maxElem_le_thompsonJ hBgS
  have hBgFi : ⁅cj (B0J S α A) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)⁆ = ⊥ := by
    have h1 := aimg_commutator (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm)
      (aimg_le : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj (B0J S α A) g) ≤
        CFSG.Quasithin.thompsonJ (S : Subgroup G)) (Fcore_le_JS c.seed)
    rw [hFB, aimg_bot, aimg_symm_aimg hB0gJ] at h1
    exact h1.symm
  have hB0P : ⁅B0J S α A, PminusJ S α g⁆ = ⊥ := by
    have := congrArg (fun H => cj H g) hBgFi
    simp only [cj_commutator, cj_cj, c.hg2, cj_one, cj_bot] at this
    exact this
  exact hB0P

theorem DoubleSetupJ.lemma73 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hY : YsubJ S α g ≤ BbJ S α A g) :
    PminusJ S α g ≤ B0J S α A ∧ BbJ S α A g = B0J S α A := by
  have hB0Q := (c.facts71).2.1
  have hB0P := commutator_B0_PminusJ_Seven34 c hY
  have hPQ : PminusJ S α g ≤ CFSG.pCore 2 G :=
    cj_le_core (aimgJ_Fcore_le_core c.seed α.symm (hV'_Seven34 c)) g
  have hPmin_ea : CFSG.Open.IsElemAbelian 2 (PminusJ S α g) :=
    isElemAbelian_cj (isElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G))
      α.symm isElemAbelian_Fcore) g
  have hPB : PminusJ S α g ≤ B0J S α A :=
    maxElem_le_of_commute hB0Q hPQ hPmin_ea fun y hy b hb =>
      (mul_comm_of_commutator_eq_bot hB0P hb hy).symm
  have hBC : B0J S α A ≤ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) :=
    fun b hb => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (mul_comm_of_commutator_eq_bot hB0P hb hy).symm
  refine ⟨hPB, le_antisymm (sup_le hPB inf_le_left) ?_⟩
  exact (le_inf le_rfl hBC : B0J S α A ≤ CcJ_Seven34 S α A g).trans le_sup_right

theorem DoubleSetupJ.lemma74 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hY : YsubJ S α g ≤ BbJ S α A g) :
    ⁅Hone S, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)⁆ ≤ Fcore G := by
  have hP : PminusJ S α g ≤ B0J S α A := (DoubleSetupJ.lemma73 c hY).1
  have hg_inv : g⁻¹ = g := inv_eq_of_mul_eq_one_right c.hg2
  have hZiF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) ≤ Fcore G :=
    aimgJ_Zfix_le_Fcore c.seed α.symm
  have hT : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G),
      CFSG.Quasithin.thompsonJ (S : Subgroup G)⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm, commutator_thompsonJ_aimgJ_Fcore c.seed α.symm]
    exact hZiF
  have hAg : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G), cj A g⁆ ≤
      Fcore G := by
    rw [Subgroup.commutator_comm]
    have e : ⁅cj A g, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)⁆ =
        cj ⁅A, cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) g⁻¹⁆ g := by
      rw [cj_commutator, cj_cj_inv]
    rw [e, hg_inv]
    calc cj ⁅A, cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) g⁆ g
        ≤ cj (Fcore G) g :=
          cj_mono ((Subgroup.commutator_mono le_rfl hP).trans (commutator_A_B0_le_F_Seven34 c))
      _ = Fcore G := cj_eq_self_of_normal
  rw [c.Hone_eq_sup, Subgroup.commutator_comm]
  exact commutator_sup_le (N := ⊤)
    (fun n _ v hv => (inferInstance : (Fcore G).Normal).conj_mem v hv n) le_top le_top hT hAg

end CFSG.QuasithinUnique.Setup.CampbellJ

end
