module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4a
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem cj_eq_self_of_le_inf_centralizer_Hone_Six4b {Y : Subgroup G} {g : G}
    (hY : Y ≤ Hone S ⊓ Subgroup.centralizer (Hone S : Set G)) (hg : g ∈ Hone S) :
    cj Y g = Y := by
  refine cj_eq_of_forall_mem fun x hx => ?_
  have hxg : g * x = x * g :=
    (Subgroup.mem_centralizer_iff.mp (hY hx).2) g hg
  have hconj : g * x * g⁻¹ = x := by
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hxg]
      _ = x := by group
  rw [hconj]
  exact hx

private theorem w_calculusJ_WPZa_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g hh : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  classical
  have hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤
      CFSG.pCore 2 G := hΛ.vmod α hα
  obtain ⟨-, -, -, hWAdm⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 hhH hhM hh2).1
  obtain ⟨A, hA, hle⟩ := hWAdm
  have hWR : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    hle.trans (maxElem_le_thompsonJ hA)
  calc ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
        cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆
      ≤ ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G),
          cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆ :=
        Subgroup.commutator_mono hWR le_rfl
    _ = ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
          CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆ := Subgroup.commutator_comm _ _
    _ ≤ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
        commutator_cj_Fa_R0_leJ h α hV hF hgH

private theorem w_calculusJ_le_Da_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g hh : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G ⊓ Subgroup.center G) := by
  classical
  obtain ⟨hPT, hUhT⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 hhH hhM hh2).2
  set Fa := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) with hFa
  set P := cj Fa g with hP
  set U := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm P with hU
  set W := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj U hh) with hW
  have hPS : P ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := hPT
  have hUS : U ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le (S :=
    CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm) (Y := P)
  have hLS : ⁅cj U hh, U⁆ ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    commutator_le_of_le hUhT hUS
  have hαL : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α ⁅cj U hh, U⁆ =
      ⁅W, P⁆ := by
    rw [aimg_commutator hUhT hUS, ← hW, hU,
      aimg_aimg_symm (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) hPS]
  have hWPZa := w_calculusJ_WPZa_Six4b h hΛ hα hF hgH hg2 hhH hhM hh2
  have hLZ : ⁅cj U hh, U⁆ ≤ Zfix S := by
    have h1 := aimg_mono (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm)
      (hαL.le.trans hWPZa)
    rwa [aimg_symm_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) hLS,
      aimg_symm_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
        (Zfix_le_JS h)] at h1
  have hcjL : cj ⁅cj U hh, U⁆ hh = ⁅cj U hh, U⁆ := by
    rw [cj_commutator, cj_cj, show hh * hh = 1 from by rw [← pow_two]; exact hh2,
      cj_one, Subgroup.commutator_comm]
  have hLD : ⁅cj U hh, U⁆ ≤ Vmod G ⊓ Subgroup.center G := by
    have h1 : ⁅cj U hh, U⁆ ≤ cj (Zfix S) hh := by
      have h2 := cj_mono (g := hh) hLZ
      rwa [hcjL] at h2
    exact (le_inf hLZ h1).trans (h.inf_cj_Zfix_le_D hhM)
  exact hαL.symm.le.trans (aimg_mono hLD)

private theorem w_calculusJ_W_le_cj_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    {g hh : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh)) ≤
      cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g := by
  classical
  obtain ⟨-, -, -, hWAdm⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 hhH hhM hh2).1
  have hWR : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
    obtain ⟨A, hA, hle⟩ := hWAdm
    exact hle.trans (maxElem_le_thompsonJ hA)
  have hRcj : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤
      cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g := by
    have h1 := cj_mono (g := g) h.thompsonJ_core_le_thompsonJ_sylow
    rwa [cj_eq_self_of_normal
      (Y := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G))] at h1
  exact hWR.trans hRcj

private theorem w_calculusJ_S7_mem_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g hh s w : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1)
    (hs : s ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh))
    (hw : w ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g) :
    s * w * s⁻¹ * w⁻¹ ∈ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
      (Vmod G ⊓ Subgroup.center G) := by
  classical
  have hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤
      CFSG.pCore 2 G := hΛ.vmod α hα
  set P := cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g with hP
  set U := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm P with hU
  set W := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj U hh) with hW
  have hDaH : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (Vmod G ⊓ Subgroup.center G) ≤
      Hone S ⊓ Subgroup.centralizer (Hone S : Set G) := by
    refine (aimg_mono (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) ?_).trans
      (aimgJ_Zfix_le_center_Hone h α hV hF)
    intro d hd
    exact ⟨hd.1, Subgroup.mem_centralizer_iff.mpr fun s _ =>
      (Subgroup.mem_center_iff.mp hd.2 s)⟩
  have hcjDa : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (Vmod G ⊓ Subgroup.center G)) g =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (Vmod G ⊓ Subgroup.center G) :=
    cj_eq_self_of_le_inf_centralizer_Hone_Six4b hDaH hgH
  have hWPDa := w_calculusJ_le_Da_Six4b h hΛ hα hF hgH hg2 hhH hhM hh2
  have hVaFa : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) :=
    aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hwP : w ∈ P := by
    rw [hP]
    exact cj_mono hVaFa hw
  have hmem : s * w * s⁻¹ * w⁻¹ ∈ ⁅W, P⁆ :=
    Subgroup.commutator_mem_commutator hs hwP
  show s * w * s⁻¹ * w⁻¹ ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
    (Vmod G ⊓ Subgroup.center G)) g
  rw [hcjDa]
  exact hWPDa hmem

private theorem w_calculusJ_S7_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g hh : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    ∀ s ∈ (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh)),
      ∀ w ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g,
        s * w * s⁻¹ * w⁻¹ = 1 := by
  intro s hs w hw
  exact tr_commutator_central_eq_oneJ h α g
    (w_calculusJ_W_le_cj_Six4b h hΛ hα hgH hg2 hhH hhM hh2 hs) hw
    (w_calculusJ_S7_mem_Six4b h hΛ hα hF hgH hg2 hhH hhM hh2 hs hw)

private theorem w_calculusJ_centralizer_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g hh : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤
      Subgroup.centralizer
        ((aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
            (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh)
          : Set G)) := by
  classical
  set P := cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g with hP
  set U := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm P with hU
  set W := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj U hh) with hW
  have S7 := w_calculusJ_S7_Six4b h hΛ hα hF hgH hg2 hhH hhM hh2
  obtain ⟨-, -, -, hWAdm⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 hhH hhM hh2).1
  have hWAdmCj : Adm (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) W :=
    (adm_cj_thompsonJ_iff (S := S) g).mpr (h.adm_cj_of_adm_core hWAdm g)
  have hrepW : P = cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g ⊔
      (P ⊓ Subgroup.centralizer (W : Set G)) := by
    simpa only [tr, ← hP] using
      tr_Fcore_repJ h α g (Y := W) hWAdmCj
  have hsup : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g ⊔
      (P ⊓ Subgroup.centralizer (W : Set G)) ≤ Subgroup.centralizer (W : Set G) :=
    sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      mul_comm_of_comm_eq_one (S7 s hs w hw)) inf_le_right
  intro x hx
  exact hsup (hrepW.le hx)

private theorem w_calculusJ_commutator_eq_bot_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g hh : G} (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ = ⊥ := by
  classical
  set P := cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g with hP
  set U := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm P with hU
  set W := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj U hh) with hW
  have hPCW := w_calculusJ_centralizer_Six4b h hΛ hα hF hgH hg2 hhH hhM hh2
  have hWPbot : ⁅W, P⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (hPCW hb) a ha
  obtain ⟨hPT, hUhT⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 hhH hhM hh2).2
  have hUS : U ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le (S :=
    CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm) (Y := P)
  have hLS : ⁅cj U hh, U⁆ ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    commutator_le_of_le hUhT hUS
  have hαL : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α ⁅cj U hh, U⁆ =
      ⁅W, P⁆ := by
    rw [aimg_commutator hUhT hUS, ← hW, hU,
      aimg_aimg_symm (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α) hPT]
  have h1 : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α ⁅cj U hh, U⁆ = ⊥ := by
    rw [hαL, hWPbot]
  exact (aimg_eq_bot_iff α hLS).mp h1

theorem mixed_conjugation_calculusJ_d (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ = ⊥ := by
  classical
  by_cases hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) = Fcore G
  · have hFi : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) =
        Fcore G := by
      calc aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)
          = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
              (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) := by rw [hF]
        _ = Fcore G := aimg_symm_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G))
            (α := α) (Fcore_le_JS h)
    have hP : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g =
        Fcore G := by
      rw [hF, cj_eq_self_of_normal (Y := Fcore G)]
    have hU : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) =
        Fcore G := by
      rw [hP]
      exact hFi
    have hcjU : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh =
        Fcore G := by
      rw [hU, cj_eq_self_of_normal (Y := Fcore G)]
    rw [hcjU, hU]
    exact commutator_eq_bot_of_commute fun a ha b hb =>
      (isElemAbelian_iff.mp (isElemAbelian_Fcore (G := G))).1 a ha b hb
  · exact w_calculusJ_commutator_eq_bot_Six4b h hΛ hα hF hgH hg2 hhH hhM hh2

private theorem gxg_sq_one_Six4b {g x : G} (hg2 : g ^ 2 = 1) (hx2 : x ^ 2 = 1) :
    (g * x * g) ^ 2 = 1 := by
  have hg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hx : x * x = 1 := by rw [← pow_two]; exact hx2
  rw [pow_two]
  calc (g * x * g) * (g * x * g) = g * x * (g * g) * x * g := by group
    _ = 1 := by rw [hg, mul_one, mul_assoc g x x, hx, mul_one, hg]

private theorem gxg_not_mem_Mnorm_Six4b (h : IsSeed S ρ (Ecore G) ψ) {g x : G}
    (hgM : g ∉ Mnorm S ρ) (hxT : x ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hxQ : x ∉ CFSG.pCore 2 G) (hg2 : g ^ 2 = 1) : g * x * g ∉ Mnorm S ρ := by
  have hg : g * g = 1 := by rw [← pow_two]; exact hg2
  intro hM
  apply hgM
  refine h.mem_Mnorm_of_conj_mem (thompsonJ_le_self' _ hxT) hxQ ?_
  rw [show g⁻¹ = g from inv_eq_of_mul_eq_one_right hg]
  exact hM

private theorem mixed_conjugation_calculusJ_e_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g x : G}
    (hgH : g ∈ Hone S) (hgM : g ∉ Mnorm S ρ) (hg2 : g ^ 2 = 1)
    (hxT : x ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G)) (hxQ : x ∉ CFSG.pCore 2 G)
    (hx2 : x ^ 2 = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) (g * x),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) g⁆ = ⊥ := by
  classical
  have hg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hxH : x ∈ Hone S := Subgroup.le_normalClosure hxT
  have hhH : g * x * g ∈ Hone S := mul_mem (mul_mem hgH hxH) hgH
  have hh2 : (g * x * g) ^ 2 = 1 := gxg_sq_one_Six4b hg2 hx2
  have hhM : g * x * g ∉ Mnorm S ρ := gxg_not_mem_Mnorm_Six4b h hgM hxT hxQ hg2
  have hd := mixed_conjugation_calculusJ_d h hΛ hα hgH hg2 hhH hhM hh2
  have e1 : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) (g * x) =
      cj (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g))
        (g * x * g)) g := by
    rw [cj_cj]
    congr 1
    calc g * x = g * x * (g * g) := by rw [hg, mul_one]
      _ = g * x * g * g := by simp only [mul_assoc]
  rw [e1, ← cj_commutator, hd, cj_bot]

private theorem w_calculusJ_f_comm_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g x : G}
    (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (h₀H : g * x * g ∈ Hone S) (h₀M : g * x * g ∉ Mnorm S ρ)
    (h₀2 : (g * x * g) ^ 2 = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) (g * x * g),
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)⁆ = ⊥ := by
  classical
  set U := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) with hU
  set Fi := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) with hFi
  set W₀ := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (cj U (g * x * g)) with hW₀
  obtain ⟨-, hUh₀T⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 h₀H h₀M h₀2).2
  obtain ⟨-, -, -, hW₀Adm⟩ :=
    (mixed_conjugation_calculusJ_abc h hΛ hα hgH hg2 h₀H h₀M h₀2).1
  have hW₀R : W₀ ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
    obtain ⟨A, hA, hle⟩ := hW₀Adm
    exact hle.trans (maxElem_le_thompsonJ hA)
  have hWF₀ : ⁅W₀, Fcore G⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun a ha b hb =>
      Fcore_commute_thompsonJ_core hb (hW₀R ha)
  have hFiT : Fi ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := by
    rw [hFi]
    exact aimg_le (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm)
      (Y := Fcore G)
  have h1 := aimg_commutator (S := CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (α := α) hUh₀T hFiT
  rw [hFi] at h1
  rw [aimg_aimg_symm (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
    (Fcore_le_JS h)] at h1
  rw [← hW₀, hWF₀] at h1
  exact (aimg_eq_bot_iff α (commutator_le_of_le hUh₀T hFiT)).mp h1

private theorem mixed_conjugation_calculusJ_f_Six4b (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g x : G}
    (hgH : g ∈ Hone S) (hgM : g ∉ Mnorm S ρ) (hg2 : g ^ 2 = 1)
    (hxT : x ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G)) (hxQ : x ∉ CFSG.pCore 2 G)
    (hx2 : x ^ 2 = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) g,
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) (g * x)⁆ =
      ⊥ := by
  classical
  have hg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hxH : x ∈ Hone S := Subgroup.le_normalClosure hxT
  have hhH : g * x * g ∈ Hone S := mul_mem (mul_mem hgH hxH) hgH
  have hh2 : (g * x * g) ^ 2 = 1 := gxg_sq_one_Six4b hg2 hx2
  have hhM : g * x * g ∉ Mnorm S ρ := gxg_not_mem_Mnorm_Six4b h hgM hxT hxQ hg2
  set U := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) with hU
  set Fi := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) with hFi
  have hcomm₀ := w_calculusJ_f_comm_Six4b h hΛ hα hgH hg2 hhH hhM hh2
  have e1 : cj (cj U g) (x * g) = cj U (g * x * g) := by
    rw [cj_cj, ← mul_assoc]
  have e2 : cj (cj Fi (g * x)) (x * g) = Fi := by
    rw [cj_cj]
    have h1 : g * x * (x * g) = 1 := by
      calc g * x * (x * g) = g * (x * x) * g := by group
        _ = 1 := by rw [hx, mul_one, hg]
    rw [h1, cj_one]
  have e3 : cj ⁅cj U g, cj Fi (g * x)⁆ (x * g) = ⊥ := by
    rw [cj_commutator, e1, e2, hcomm₀]
  calc ⁅cj U g, cj Fi (g * x)⁆
      = cj (cj ⁅cj U g, cj Fi (g * x)⁆ (x * g)) (x * g)⁻¹ := cj_inv_cj.symm
    _ = ⊥ := by rw [e3, cj_bot]

theorem mixed_conjugation_calculusJ_def (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh x : G}
    (hgH : g ∈ Hone S) (hgM : g ∉ Mnorm S ρ) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1)
    (hxT : x ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G)) (hxQ : x ∉ CFSG.pCore 2 G)
    (hx2 : x ^ 2 = 1) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ = ⊥ ∧
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) (g * x),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) g⁆ = ⊥ ∧
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) g,
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) (g * x)⁆ = ⊥ := by
  refine ⟨mixed_conjugation_calculusJ_d h hΛ hα hgH hg2 hhH hhM hh2, ?_, ?_⟩
  · exact mixed_conjugation_calculusJ_e_Six4b h hΛ hα hgH hgM hg2 hxT hxQ hx2
  · exact mixed_conjugation_calculusJ_f_Six4b h hΛ hα hgH hgM hg2 hxT hxQ hx2

end CFSG.QuasithinUnique.Setup.CampbellJ

end
