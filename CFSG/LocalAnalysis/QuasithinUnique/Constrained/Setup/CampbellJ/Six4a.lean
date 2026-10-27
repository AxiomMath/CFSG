module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six3b
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMixedTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTwoElement

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem Vmod_inf_centralizer_Hone_le_center_Six4a (h : IsSeed S ρ (Ecore G) ψ) :
    Vmod G ⊓ Subgroup.centralizer (Hone S : Set G) ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro x
  have hzV : z ∈ Vmod G := hz.1
  have hzc := hz.2
  have hx : x ∈ Hone S ⊔ CFSG.pCore 2 G := by rw [h.Hone_sup_core]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hjz : j * z = z * j := Subgroup.mem_centralizer_iff.mp hzc j hj
  have hqz : q * z = z * q := Ecore_commute_core hq (Vmod_le_Ecore hzV)
  calc (j * q) * z = j * (q * z) := by group
    _ = j * (z * q) := by rw [hqz]
    _ = (j * z) * q := by group
    _ = (z * j) * q := by rw [hjz]
    _ = z * (j * q) := by group

private theorem cj_eq_self_of_le_center_Hone_Six4a {Y : Subgroup G}
    (hY : Y ≤ Hone S ⊓ Subgroup.centralizer (Hone S : Set G)) {g : G} (hg : g ∈ Hone S) :
    cj Y g = Y := by
  apply cj_eq_of_forall_mem
  intro z hz
  have hcomm : g * z = z * g :=
    Subgroup.mem_centralizer_iff.mp (hY hz).2 g hg
  have hgz : g * z * g⁻¹ = z := by rw [hcomm]; group
  rwa [hgz]

theorem commutator_cj_Fa_R0_leJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) {g : G}
    (hg : g ∈ Hone S) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hZc := aimgJ_Zfix_le_center_Hone h α hV hF
  have hRT : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := h.thompsonJ_core_le_thompsonJ_sylow
  have e : ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆ =
      cj ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
        CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆ g := by
    rw [cj_commutator, cj_eq_self_of_normal
      (Y := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G))]
  rw [e]
  calc cj ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
        CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆ g
      ≤ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) g := by
        refine cj_mono ?_
        calc ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
              CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)⁆
            ≤ ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
                CFSG.Quasithin.thompsonJ (S : Subgroup G)⁆ :=
              Subgroup.commutator_mono le_rfl hRT
          _ = ⁅CFSG.Quasithin.thompsonJ (S : Subgroup G),
                aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ :=
              Subgroup.commutator_comm _ _
          _ = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
              commutator_thompsonJ_aimgJ_Fcore h α
    _ = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
        cj_eq_self_of_le_center_Hone_Six4a hZc hg

theorem tr_commutator_central_eq_oneJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) {s w : G}
    (hs : s ∈ cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g)
    (hw : w ∈ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Vmod G))
    (hc : s * w * s⁻¹ * w⁻¹ ∈
      tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Vmod G ⊓ Subgroup.center G)) :
    s * w * s⁻¹ * w⁻¹ = 1 := by
  have hs1 : g * s * g⁻¹ ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := mem_cj.mp hs
  have hw1 : g * w * g⁻¹ ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) :=
    mem_cj.mp hw
  have hw1T : g * w * g⁻¹ ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le hw1
  have hwV : ((α.symm ⟨g * w * g⁻¹, hw1T⟩ :
      ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈ Vmod G :=
    (mem_aimg_symm_iff hw1T).mp hw1
  have hcD : g * (s * w * s⁻¹ * w⁻¹) * g⁻¹ ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G ⊓ Subgroup.center G) :=
    mem_cj.mp hc
  have hcT : g * (s * w * s⁻¹ * w⁻¹) * g⁻¹ ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le hcD
  have hD := (mem_aimg_symm_iff hcT).mp hcD
  have key : α.symm ⟨g * s * g⁻¹, hs1⟩ * α.symm ⟨g * w * g⁻¹, hw1T⟩ *
      (α.symm ⟨g * s * g⁻¹, hs1⟩)⁻¹ * (α.symm ⟨g * w * g⁻¹, hw1T⟩)⁻¹ =
      α.symm ⟨g * (s * w * s⁻¹ * w⁻¹) * g⁻¹, hcT⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * s * g⁻¹ * (g * w * g⁻¹) * (g * s * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ =
      g * (s * w * s⁻¹ * w⁻¹) * g⁻¹
    group
  have key' := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key'
  have h1 := h.commutator_eq_one_of_central
    (thompsonJ_le_self' _ (α.symm ⟨g * s * g⁻¹, hs1⟩).2) hwV
    (by rw [key']; exact hD.2)
  rw [key'] at h1
  have h2 : α.symm ⟨g * (s * w * s⁻¹ * w⁻¹) * g⁻¹, hcT⟩ = 1 := Subtype.ext h1
  have h3 : (⟨g * (s * w * s⁻¹ * w⁻¹) * g⁻¹, hcT⟩ :
      ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) = 1 := by
    apply α.symm.injective
    rw [h2, map_one]
  have h4 : g * (s * w * s⁻¹ * w⁻¹) * g⁻¹ = 1 := congrArg Subtype.val h3
  simpa using h4

theorem U_factsJ (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) :
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤ CFSG.pCore 2 G ∧
    Adm (CFSG.pCore 2 G)
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) ∧
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g), Fcore G⁆ = ⊥ ∧
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) ≤ CFSG.pCore 2 G ∧
    Adm (CFSG.pCore 2 G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  have hV := hΛ.vmod α hα
  have hPQ : cj (aimg T α (Fcore G)) g ≤ CFSG.pCore 2 G :=
    cj_le_core (aimgJ_Fcore_le_core h α hV) g
  have hPAdm : Adm (CFSG.pCore 2 G) (cj (aimg T α (Fcore G)) g) :=
    adm_core_cj (adm_core_aimgJ_Fcore h α hV) g
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hcomm : ⁅cj (aimg T α (Fcore G)) g, aimg T α (Fcore G)⁆ = ⊥ := by
    have h1 := two_element_conjugate_commutationJ h hΛ hα hgH (Subgroup.inv_mem _ hgH)
      (x := g⁻¹) ⟨1, by rw [hginv, pow_one, pow_two]; exact hg⟩
    rwa [mul_inv_cancel, cj_one] at h1
  have hPT : cj (aimg T α (Fcore G)) g ≤ T := by
    simpa only [tr] using tr_Fcore_le_thompsonJ_sylowJ h α g hV
  have hFaT : aimg T α (Fcore G) ≤ T := aimg_le
  have hUF : ⁅aimg T α.symm (cj (aimg T α (Fcore G)) g), Fcore G⁆ = ⊥ := by
    have h1 := aimg_commutator (S := T) (α := α.symm) hPT hFaT
    rw [hcomm, aimg_bot, aimg_symm_aimg (Fcore_le_JS h)] at h1
    exact h1.symm
  have hUQ : aimg T α.symm (cj (aimg T α (Fcore G)) g) ≤ CFSG.pCore 2 G := by
    intro x hx
    exact h.sylow_inf_centralizer_Fcore_le
      ⟨thompsonJ_le_self' _ (aimg_le hx), Subgroup.mem_centralizer_iff.mpr fun f hf =>
        (mul_comm_of_commutator_eq_bot hUF hx hf).symm⟩
  refine ⟨hPQ, hPAdm, hUF, hUQ, ?_⟩
  exact h.adm_core_of_adm ((adm_thompsonJ_iff (S := S) (Y := _)).mp
    (adm_aimg α.symm ((adm_thompsonJ_iff (S := S) (Y := _)).mpr
      (h.adm_sylow_of_adm_core hPAdm)))) hUQ

private theorem le_thompsonJ_of_adm_Six4a {Q' Y : Subgroup G} (hY : Adm Q' Y) :
    Y ≤ CFSG.Quasithin.thompsonJ Q' := by
  obtain ⟨A, hA, hle⟩ := hY
  exact hle.trans (maxElem_le_thompsonJ hA)

private theorem cj_Zfix_le_thompsonJ_Six4a (h : IsSeed S ρ (Ecore G) ψ) {hh : G} :
    cj (Zfix S) hh ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := by
  have hZR : Zfix S ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    ((inf_le_left : Zfix S ≤ Vmod G).trans (Vmod_le_Ecore.trans h.Ecore_le_Fcore)).trans
      Fcore_le_thompsonJ
  have h1 := cj_mono (g := hh) hZR
  rw [cj_eq_self_of_normal (Y := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G))] at h1
  exact h1.trans h.thompsonJ_core_le_thompsonJ_sylow

private theorem aimg_symm_delta_Za_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {hh : G}
    (hZhT : cj (Zfix S) hh ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G)) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (delta (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α hh
          (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S))) =
      cj (Zfix S) hh := by
  unfold delta
  rw [aimg_symm_aimg (Zfix_le_JS h)]
  exact aimg_symm_aimg hZhT

private theorem commutator_W_F_le_delta_Za_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
      Fcore G⁆ ≤
      delta (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α hh
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Fa := aimg T α (Fcore G) with hFa
  set Za := aimg T α (Zfix S) with hZa
  set Fi := aimg T α.symm (Fcore G) with hFidef
  set P := cj Fa g with hP
  set P' := aimg T α (cj Fi hh) with hP'
  set U := aimg T α.symm P with hU
  set W := aimg T α (cj U hh) with hW
  have hV : aimg T α (Vmod G) ≤ CFSG.pCore 2 G := hΛ.vmod α hα
  have hRT : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤ T :=
    h.thompsonJ_core_le_thompsonJ_sylow
  obtain ⟨-, -, -, -, hUAdm⟩ := U_factsJ h hΛ hα hgH hg
  obtain ⟨-, hFiAdm, -, -, hP'Adm⟩ := U_factsJ h hΛ (Λ.inv_mem hα) hhH hh2
  have hFiHT : cj Fi hh ≤ T := (le_thompsonJ_of_adm_Six4a hFiAdm).trans hRT
  have hPT : P ≤ T := by
    simpa only [tr] using tr_Fcore_le_thompsonJ_sylowJ h α g hV
  have hP'T : P' ≤ T := aimg_le
  have hdomP : U ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    le_thompsonJ_of_adm_Six4a hUAdm
  have hP'symm : aimg T α.symm P' = cj Fi hh := aimg_symm_aimg hFiHT
  have hdomP' : aimg T α.symm P' ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    hP'symm.trans_le (le_thompsonJ_of_adm_Six4a hFiAdm)
  have hP'R : P' ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    le_thompsonJ_of_adm_Six4a hP'Adm
  have S1 : ⁅P, P'⁆ ≤ Za :=
    (Subgroup.commutator_mono le_rfl hP'R).trans (commutator_cj_Fa_R0_leJ h α hV hF hgH)
  have hdP : delta T α hh P = W := rfl
  have hdP' : delta T α hh P' = Fcore G := by
    unfold delta
    rw [hP'symm, cj_cj, hh2, cj_one, aimg_aimg_symm (Fcore_le_JS h)]
  have S2 : delta T α hh ⁅P, P'⁆ = ⁅W, Fcore G⁆ := by
    rw [delta_commutator hRT α hh hPT hP'T hdomP hdomP', hdP, hdP']
  rw [← S2]
  exact delta_mono α hh S1

private structure WContext_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) : Prop where
  hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G
  hRT : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤
    CFSG.Quasithin.thompsonJ (S : Subgroup G)
  hZαc : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ≤
    Hone S ⊓ Subgroup.centralizer (Hone S : Set G)
  hZic : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Zfix S) ≤
    Hone S ⊓ Subgroup.centralizer (Hone S : Set G)
  hUAdm : Adm (CFSG.pCore 2 G) (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g))
  hFiAdm : Adm (CFSG.pCore 2 G) (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (Fcore G)) hh)
  hP'Adm : Adm (CFSG.pCore 2 G) (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh))
  hPT : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤
    CFSG.Quasithin.thompsonJ (S : Subgroup G)
  hP'T : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh) ≤
    CFSG.Quasithin.thompsonJ (S : Subgroup G)
  hdomP : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) ≤
    CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  hdomP' : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh)) ≤
    CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  hFiHT : cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh ≤
    CFSG.Quasithin.thompsonJ (S : Subgroup G)

private theorem wcontext_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    WContext_Six4a h hΛ hα hgH hg hhH hh2 hF := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  have hV : aimg T α (Vmod G) ≤ CFSG.pCore 2 G := hΛ.vmod α hα
  have hRT : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤ T :=
    h.thompsonJ_core_le_thompsonJ_sylow
  obtain ⟨-, -, -, -, hUAdm⟩ := U_factsJ h hΛ hα hgH hg
  obtain ⟨-, hFiAdm, -, -, hP'Adm⟩ := U_factsJ h hΛ (Λ.inv_mem hα) hhH hh2
  have hFi : aimg T α.symm (Fcore G) ≠ Fcore G := by
    intro e
    apply hF
    calc aimg T α (Fcore G) = aimg T α (aimg T α.symm (Fcore G)) := by rw [e]
      _ = Fcore G := aimg_aimg_symm (Fcore_le_JS h)
  have hZαc := aimgJ_Zfix_le_center_Hone h α hV hF
  have hZic := aimgJ_Zfix_le_center_Hone h α.symm (hΛ.vmod α.symm (Λ.inv_mem hα)) hFi
  have hFiHT : cj (aimg T α.symm (Fcore G)) hh ≤ T :=
    (le_thompsonJ_of_adm_Six4a hFiAdm).trans hRT
  have hPT : cj (aimg T α (Fcore G)) g ≤ T := by
    simpa only [tr] using tr_Fcore_le_thompsonJ_sylowJ h α g hV
  have hP'T : aimg T α (cj (aimg T α.symm (Fcore G)) hh) ≤ T := aimg_le
  have hdomP : aimg T α.symm (cj (aimg T α (Fcore G)) g) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    le_thompsonJ_of_adm_Six4a hUAdm
  have hP'symm : aimg T α.symm (aimg T α (cj (aimg T α.symm (Fcore G)) hh)) =
      cj (aimg T α.symm (Fcore G)) hh :=
    aimg_symm_aimg hFiHT
  have hdomP' : aimg T α.symm (aimg T α (cj (aimg T α.symm (Fcore G)) hh)) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    hP'symm.trans_le (le_thompsonJ_of_adm_Six4a hFiAdm)
  exact ⟨hV, hRT, hZαc, hZic, hUAdm, hFiAdm, hP'Adm, hPT, hP'T, hdomP, hdomP', hFiHT⟩

private theorem commutator_W_F_le_Da_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    (d : WContext_Six4a h hΛ hα hgH hg hhH hh2 hF)
    (hWFd : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
      Fcore G⁆ ≤
      delta (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α hh
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S))) :
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
      Fcore G⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (Vmod G ⊓ Subgroup.center G) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let W := aimg T α (cj (aimg T α.symm (cj (aimg T α (Fcore G)) g)) hh)
  have hZhT : cj (Zfix S) hh ≤ T := cj_Zfix_le_thompsonJ_Six4a h
  have hWFST : ⁅W, Fcore G⁆ ≤ T := commutator_le_of_le (aimg_le : W ≤ T) (Fcore_le_JS h)
  have hWFZ : ⁅W, Fcore G⁆ ≤ Zfix S := by
    rw [← h.commutator_thompsonJ_Fcore]
    exact Subgroup.commutator_mono (aimg_le : W ≤ T) le_rfl
  have hD1a : aimg T α.symm ⁅W, Fcore G⁆ ≤ Vmod G := by
    have h1 : aimg T α.symm ⁅W, Fcore G⁆ ≤ cj (Zfix S) hh := by
      have h2 := aimg_mono (S := T) (α := α.symm) hWFd
      rwa [aimg_symm_delta_Za_Six4a h α hZhT] at h2
    have h3 : cj (Zfix S) hh ≤ Vmod G := by
      have h4 := cj_mono (g := hh) (inf_le_left : Zfix S ≤ Vmod G)
      rwa [cj_eq_self_of_normal (Y := Vmod G)] at h4
    exact h1.trans h3
  have hD1b : aimg T α.symm ⁅W, Fcore G⁆ ≤ Subgroup.centralizer (Hone S : Set G) :=
    (aimg_mono (S := T) (α := α.symm) hWFZ).trans fun z hz => (d.hZic hz).2
  have hD1 : aimg T α.symm ⁅W, Fcore G⁆ ≤ Vmod G ⊓ Subgroup.center G :=
    (le_inf hD1a hD1b).trans (le_inf inf_le_left (Vmod_inf_centralizer_Hone_le_center_Six4a h))
  have h1 := aimg_mono (S := T) (α := α) hD1
  rwa [aimg_aimg_symm hWFST] at h1

private theorem commutator_P_P'_le_Da_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    (d : WContext_Six4a h hΛ hα hgH hg hhH hh2 hF)
    (hWFDa : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh),
      Fcore G⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (Vmod G ⊓ Subgroup.center G)) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh)⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (Vmod G ⊓ Subgroup.center G) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let Fa := aimg T α (Fcore G)
  let Fi := aimg T α.symm (Fcore G)
  let P := cj Fa g
  let P' := aimg T α (cj Fi hh)
  let W := aimg T α (cj (aimg T α.symm P) hh)
  let Da := aimg T α (Vmod G ⊓ Subgroup.center G)
  have hP'symm : aimg T α.symm P' = cj Fi hh := aimg_symm_aimg d.hFiHT
  have hdP : delta T α hh P = W := rfl
  have hdP' : delta T α hh P' = Fcore G := by
    unfold delta
    rw [hP'symm, cj_cj, hh2, cj_one, aimg_aimg_symm (Fcore_le_JS h)]
  have S2 : delta T α hh ⁅P, P'⁆ = ⁅W, Fcore G⁆ := by
    rw [delta_commutator d.hRT α hh d.hPT d.hP'T d.hdomP d.hdomP', hdP, hdP']
  have hdDa : delta T α hh Da = Da := by
    unfold delta
    rw [aimg_symm_aimg (inf_le_left.trans (Vmod_le_JS h)), cj_eq_of_le_center inf_le_right hh]
  have hPP'T : ⁅P, P'⁆ ≤ T := commutator_le_of_le d.hPT d.hP'T
  have hPP'dom : aimg T α.symm ⁅P, P'⁆ ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
    rw [aimg_commutator d.hPT d.hP'T]
    exact commutator_le_of_le d.hdomP d.hdomP'
  have hPP' : ⁅P, P'⁆ = delta T α hh ⁅W, Fcore G⁆ := by
    rw [← S2, delta_delta d.hRT α hh hPP'T hPP'dom hh2]
  rw [hPP']
  calc delta T α hh ⁅W, Fcore G⁆ ≤ delta T α hh Da := delta_mono α hh hWFDa
    _ = Da := hdDa

private theorem commutator_P_P'_bot_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    (d : WContext_Six4a h hΛ hα hgH hg hhH hh2 hF)
    (hPP'Da : ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh)⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (Vmod G ⊓ Subgroup.center G)) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh)⁆ = ⊥ := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let Fa := aimg T α (Fcore G)
  let Za := aimg T α (Zfix S)
  let Fi := aimg T α.symm (Fcore G)
  let P := cj Fa g
  let P' := aimg T α (cj Fi hh)
  let Da := aimg T α (Vmod G ⊓ Subgroup.center G)
  have hDaZa : Da ≤ Za := aimg_mono fun dz hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun s _ =>
      (Subgroup.mem_center_iff.mp hz.2 s)⟩
  have hRcj : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤ cj T g := by
    have h1 := cj_mono (g := g) d.hRT
    rwa [cj_eq_self_of_normal (Y := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G))] at h1
  have hcjDa : cj Da g = Da := cj_eq_self_of_le_center_Hone_Six4a (hDaZa.trans d.hZαc) hgH
  have hP'R : P' ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    le_thompsonJ_of_adm_Six4a d.hP'Adm
  have hVaFa : aimg T α (Vmod G) ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have S3 : ∀ s ∈ P', ∀ w ∈ cj (aimg T α (Vmod G)) g, s * w * s⁻¹ * w⁻¹ = 1 := by
    intro s hs w hw
    have hwP : w ∈ P := cj_mono hVaFa hw
    have hmem : s * w * s⁻¹ * w⁻¹ ∈ (⁅P', P⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hs hwP
    rw [Subgroup.commutator_comm] at hmem
    have hDa' : s * w * s⁻¹ * w⁻¹ ∈ tr T α g (Vmod G ⊓ Subgroup.center G) := by
      change s * w * s⁻¹ * w⁻¹ ∈ cj Da g
      rw [hcjDa]; exact hPP'Da hmem
    exact tr_commutator_central_eq_oneJ h α g (hRcj (hP'R hs)) hw hDa'
  have hrepP : P = cj (aimg T α (Vmod G)) g ⊔ (P ⊓ Subgroup.centralizer (P' : Set G)) := by
    have h1 := tr_Fcore_repJ h α g (Y := P')
      ((adm_cj_thompsonJ_iff g).mpr (h.adm_cj_of_adm_core d.hP'Adm g))
    simpa only [tr] using h1
  have hPC : P ≤ Subgroup.centralizer (P' : Set G) :=
    hrepP.le.trans (sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      mul_comm_of_comm_eq_one (S3 s hs w hw)) inf_le_right)
  exact commutator_eq_bot_of_commute fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hPC ha) b hb).symm

private theorem adm_W_Six4a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg : g * g = 1) (hhH : hh ∈ Hone S) (hh2 : hh * hh = 1)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    (d : WContext_Six4a h hΛ hα hgH hg hhH hh2 hF)
    (hPP'bot : ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) hh)⁆ = ⊥) :
    Adm (CFSG.pCore 2 G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh)) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let Fa := aimg T α (Fcore G)
  let Fi := aimg T α.symm (Fcore G)
  let P := cj Fa g
  let P' := aimg T α (cj Fi hh)
  let U := aimg T α.symm P
  let W := aimg T α (cj U hh)
  have hP'symm : aimg T α.symm P' = cj Fi hh := aimg_symm_aimg d.hFiHT
  have hdP : delta T α hh P = W := rfl
  have hdP' : delta T α hh P' = Fcore G := by
    unfold delta
    rw [hP'symm, cj_cj, hh2, cj_one, aimg_aimg_symm (Fcore_le_JS h)]
  have S2 : delta T α hh ⁅P, P'⁆ = ⁅W, Fcore G⁆ := by
    rw [delta_commutator d.hRT α hh d.hPT d.hP'T d.hdomP d.hdomP', hdP, hdP']
  have S5 : ⁅W, Fcore G⁆ = ⊥ := by rw [← S2, hPP'bot, delta_bot]
  have hUhAdm : Adm (CFSG.pCore 2 G) (cj U hh) := adm_core_cj d.hUAdm hh
  have hWAdmS : Adm (S : Subgroup G) W :=
    (adm_thompsonJ_iff (S := S) (Y := W)).mp
      (adm_aimg α ((adm_thompsonJ_iff (S := S) (Y := cj U hh)).mpr
        (h.adm_sylow_of_adm_core hUhAdm)))
  have hWS : W ≤ (S : Subgroup G) := (aimg_le : W ≤ T).trans (thompsonJ_le_self' _)
  have hWQ : W ≤ CFSG.pCore 2 G := fun x hx =>
    h.sylow_inf_centralizer_Fcore_le ⟨hWS hx, Subgroup.mem_centralizer_iff.mpr fun f hf =>
      (mul_comm_of_commutator_eq_bot S5 hx hf).symm⟩
  exact h.adm_core_of_adm hWAdmS hWQ

theorem mixed_conjugation_calculusJ_abc (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ) {g hh : G}
    (hgH : g ∈ Hone S) (hg2 : g ^ 2 = 1)
    (hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1) :
    (Adm (CFSG.pCore 2 G)
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g) ∧
      Adm (CFSG.pCore 2 G)
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) ∧
      Adm (CFSG.pCore 2 G)
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh) ∧
      Adm (CFSG.pCore 2 G)
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
            (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh))) ∧
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤
        CFSG.Quasithin.thompsonJ (S : Subgroup G) ∧
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) hh ≤
        CFSG.Quasithin.thompsonJ (S : Subgroup G)) := by
  classical
  by_cases hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) = Fcore G
  · have hFi : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) =
        Fcore G := by
      calc aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)
          = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
              (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) := by rw [hF]
        _ = Fcore G := aimg_symm_aimg (Fcore_le_JS h)
    have hAdm : Adm (CFSG.pCore 2 G) (Fcore G) := by
      have h1 := adm_core_aimgJ_Fcore h α (hΛ.vmod α hα)
      rwa [hF] at h1
    simp only [hF, hFi, cj_eq_self_of_normal (Y := Fcore G)]
    exact ⟨⟨hAdm, hAdm, hAdm, hAdm⟩, Fcore_le_JS h, Fcore_le_JS h⟩
  · have hg : g * g = 1 := by rw [← pow_two]; exact hg2
    have hhsq : hh * hh = 1 := by rw [← pow_two]; exact hh2
    have d := wcontext_Six4a h hΛ hα hgH hg hhH hhsq hF
    have hWFd := commutator_W_F_le_delta_Za_Six4a h hΛ hα hgH hg hhH hhsq hF
    have hWFDa := commutator_W_F_le_Da_Six4a h hΛ hα hgH hg hhH hhsq hF d hWFd
    have hPP'Da := commutator_P_P'_le_Da_Six4a h hΛ hα hgH hg hhH hhsq hF d hWFDa
    have hPP'bot := commutator_P_P'_bot_Six4a h hΛ hα hgH hg hhH hhsq hF d hPP'Da
    have hWAdm := adm_W_Six4a h hΛ hα hgH hg hhH hhsq hF d hPP'bot
    obtain ⟨-, hPAdm, -, -, hUAdm⟩ := U_factsJ h hΛ hα hgH hg
    exact ⟨⟨hPAdm, hUAdm, adm_core_cj hUAdm hh, hWAdm⟩, d.hPT,
      (le_thompsonJ_of_adm_Six4a (adm_core_cj hUAdm hh)).trans d.hRT⟩

end CFSG.QuasithinUnique.Setup.CampbellJ

end
