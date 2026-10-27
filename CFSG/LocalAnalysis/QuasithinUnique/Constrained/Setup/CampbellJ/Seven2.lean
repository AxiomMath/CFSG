module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalTr
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalAimg
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB52
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six3b
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4a
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4b
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCalc
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMnorm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTwoElement
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDouble
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))}
  {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} {A : Subgroup G} {g : G}

local notation "J" => CFSG.Quasithin.thompsonJ (S : Subgroup G)

private theorem hV_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg J α (Vmod G) ≤ CFSG.pCore 2 G := c.lam.vmod α c.hαΛ

private theorem hV'_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg J α.symm (Vmod G) ≤ CFSG.pCore 2 G := by
  have h : α.symm ∈ Λ := by
    have h1 := Λ.inv_mem c.hαΛ
    rwa [MulAut.inv_def] at h1
  exact c.lam.vmod α.symm h

private theorem hF_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg J α (Fcore G) ≠ Fcore G := by
  intro e
  apply c.hα
  rw [e, c.seed.commutator_Hone_Fcore]
  exact Vmod_le_Ecore.trans c.seed.Ecore_le_Fcore

private theorem cj_eq_of_le_centralizer_Hone_Seven2 {N : Subgroup G}
    (hN : N ≤ Subgroup.centralizer (Hone S : Set G)) {g : G} (hg : g ∈ Hone S) :
    cj N g = N := by
  refine cj_eq_of_forall_mem fun x hx => ?_
  have hxg : g * x = x * g := Subgroup.mem_centralizer_iff.mp (hN hx) g hg
  have : g * x * g⁻¹ = x := by rw [hxg]; group
  rw [this]; exact hx

private theorem B0J_eq_BoneP_Seven2 (h : IsSeed S ρ (Ecore G) ψ) (α : MulAut J)
    (hV : aimg J α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) :
    B0J S α A = CFSG.Quasithin.BoneP (aimg J α (Fcore G)) A := by
  have hFaJ := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hFFa : ∀ x ∈ Fcore G, ∀ w ∈ aimg J α (Fcore G), x * w = w * x :=
    fun x hx w hw => (Fcore_commute_thompsonJ_core hx (hFaJ hw)).symm
  apply le_antisymm
  · refine sup_le (sup_le ?_ le_sup_left) ?_
    · exact PartnerCoreJ.Fcore_le_BoneP h (partnerCoreJ_aimg h α)
        (aimgJ_Fcore_le_core h α hV) A
    · rintro x ⟨hxA, hxc⟩
      have hxF : x ∈ A ⊓ Subgroup.centralizer (Fcore G : Set G) :=
        ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun f hf =>
          Subgroup.mem_centralizer_iff.mp hxc f (Subgroup.mem_sup_left hf)⟩
      rw [h.inf_centralizer_Fcore hA] at hxF
      apply Subgroup.mem_sup_right
      refine ⟨Subgroup.mem_sup_left hxF, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      exact Subgroup.mem_centralizer_iff.mp hxc w (Subgroup.mem_sup_right hw)
  · refine sup_le ((le_sup_right : aimg J α (Fcore G) ≤
        Fcore G ⊔ aimg J α (Fcore G)).trans le_sup_left) (fun u hu => ?_)
    obtain ⟨huB, huc⟩ := hu
    have hFB0 : Fcore G ≤ B0J S α A := le_sup_left.trans le_sup_left
    have hcommAF : ∀ x ∈ A ⊓ CFSG.pCore 2 G, ∀ y ∈ Fcore G, x * y = y * x := by
      intro x hx y hy
      have : x ∈ A ⊓ Subgroup.centralizer (Fcore G : Set G) := by
        rw [h.inf_centralizer_Fcore hA]; exact hx
      exact (Subgroup.mem_centralizer_iff.mp this.2 y hy).symm
    obtain ⟨a, ha, f, hf, rfl⟩ := mem_sup_of_commute hcommAF huB
    have hac : a ∈ Subgroup.centralizer
        ((Fcore G ⊔ aimg J α (Fcore G) : Subgroup G) : Set G) := by
      refine mem_centralizer_sup (fun x hx => (hcommAF a ha x hx).symm) (fun w hw => ?_)
      have h1 := Subgroup.mem_centralizer_iff.mp huc w hw
      have h2 := hFFa f hf w hw
      calc w * a = w * (a * f) * f⁻¹ := by group
        _ = (a * f) * w * f⁻¹ := by rw [h1]
        _ = a * (f * w) * f⁻¹ := by group
        _ = a * (w * f) * f⁻¹ := by rw [h2]
        _ = a * w := by group
    exact mul_mem (Subgroup.mem_sup_right
      (⟨ha.1, hac⟩ : a ∈ A ⊓ Subgroup.centralizer
        ((Fcore G ⊔ aimg J α (Fcore G) : Subgroup G) : Set G))) (hFB0 hf)

private theorem B0_normalized_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {a : G} (ha : a ∈ A)
    {b : G} (hb : b ∈ B0J S α A) : a * b * a⁻¹ ∈ B0J S α A := by
  rw [B0J_eq_BoneP_Seven2 c.seed α (hV_Seven2 c) c.hA] at hb ⊢
  exact PartnerCoreJ.BoneP_normalized (partnerCoreJ_aimg c.seed α) c.hA ha hb

private theorem cj_Za_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    cj (aimg J α (Zfix S)) g = aimg J α (Zfix S) :=
  cj_eq_of_le_centralizer_Hone_Seven2
    (fun z hz => (aimgJ_Zfix_le_center_Hone c.seed α (hV_Seven2 c) (hF_Seven2 c) hz).2)
    c.hgH

private theorem commutator_A_B0_le_ZZ_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅A, B0J S α A⁆ ≤ Zfix S ⊔ aimg J α (Zfix S) := c.facts71.2.2.2

private theorem commutator_A_B0_le_F_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅A, B0J S α A⁆ ≤ Fcore G :=
  (commutator_A_B0_le_ZZ_Seven2 c).trans
    (sup_le c.seed.Zfix_le_Fcore (aimgJ_Zfix_le_Fcore c.seed α))

private theorem Pminus_le_core_Seven2 (h : IsSeed S ρ (Ecore G) ψ) (α : MulAut J)
    (hV' : aimg J α.symm (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    PminusJ S α g ≤ CFSG.pCore 2 G :=
  cj_le_core (aimgJ_Fcore_le_core h α.symm hV') g

private theorem Pminus_le_R0_Seven2 (h : IsSeed S ρ (Ecore G) ψ) (α : MulAut J)
    (hV' : aimg J α.symm (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    PminusJ S α g ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
  tr_Fcore_le_thompsonJ_coreJ h α.symm g hV'

private theorem isElemAbelian_Pminus_Seven2 (α : MulAut J) (g : G) :
    CFSG.Open.IsElemAbelian 2 (PminusJ S α g) :=
  isElemAbelian_cj (isElemAbelian_aimg (S := J) α.symm isElemAbelian_Fcore) g

private theorem Pminus_commute_cj_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {a : G}
    (ha : a ∈ A) : ⁅cj (PminusJ S α g) a, PminusJ S α g⁆ = ⊥ := by
  have hax : ∃ n : ℕ, a⁻¹ ^ (2 ^ n) = 1 := ⟨1, by
    have : a ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 a ha
    rw [pow_one, inv_pow, this, inv_one]⟩
  have haH : a ∈ Hone S :=
    Subgroup.le_normalClosure (maxElem_le_thompsonJ c.hA ha)
  have hαsymm : α.symm ∈ Λ := by
    have h1 := Λ.inv_mem c.hαΛ
    rwa [MulAut.inv_def] at h1
  have h1 := two_element_conjugate_commutationJ c.seed c.lam hαsymm
    (g := g * a) (x := a⁻¹) ((Hone S).mul_mem c.hgH haH) ((Hone S).inv_mem haH) hax
  rw [mul_inv_cancel_right] at h1
  have e : cj (aimg J α.symm (Fcore G)) (g * a) = cj (PminusJ S α g) a := by
    rw [PminusJ, cj_cj]
  rw [e] at h1
  exact h1

private theorem cj_Cc_eq_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {a : G} (ha : a ∈ A) :
    cj (B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G)) a =
      B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) := by
  apply cj_eq_of_forall_mem
  intro x hx
  have hxB0 : x ∈ B0J S α A := hx.1
  have h1 : a * x * a⁻¹ ∈ B0J S α A := B0_normalized_Seven2 c ha hxB0
  have hcomm : a * x * a⁻¹ * x⁻¹ ∈
      B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) := by
    refine ⟨mul_mem h1 ((B0J S α A).inv_mem hxB0),
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hF1 : a * x * a⁻¹ * x⁻¹ ∈ Fcore G :=
      commutator_A_B0_le_F_Seven2 c (Subgroup.commutator_mem_commutator ha hxB0)
    exact Fcore_commute_thompsonJ_core hF1 (Pminus_le_R0_Seven2 c.seed α (hV'_Seven2 c) g hw)
  have : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
  rw [this]
  exact mul_mem hcomm hx

private theorem Cc_le_centralizer_cj_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {a : G}
    (ha : a ∈ A) :
    B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((cj (PminusJ S α g) a : Subgroup G) : Set G) := by
  have h1 : B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) := inf_le_right
  have h2 := cj_mono (g := a) h1
  rw [cj_Cc_eq_Seven2 c ha, ← centralizer_cj] at h2
  exact h2

private theorem cj_Bb_le_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {a : G} (ha : a ∈ A) :
    cj (BbJ S α A g) a ≤ BbJ S α A g := by
  have hBbQ : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    c.facts71.2.2.1
  have hPC : ∀ x ∈ PminusJ S α g,
      ∀ y ∈ B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G),
      x * y = y * x := fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have hPa : cj (PminusJ S α g) a ≤ BbJ S α A g := by
    refine maxElem_le_of_commute hBbQ
      (cj_le_core (Pminus_le_core_Seven2 c.seed α (hV'_Seven2 c) g) a)
      (isElemAbelian_cj (isElemAbelian_Pminus_Seven2 (S := S) α g) a) ?_
    intro y hy u hu
    obtain ⟨p, hp, cc, hcc, rfl⟩ := mem_sup_of_commute hPC hu
    have h1 : y * p = p * y :=
      mul_comm_of_commutator_eq_bot (Pminus_commute_cj_Seven2 c ha) hy hp
    have h2 : y * cc = cc * y :=
      Subgroup.mem_centralizer_iff.mp (Cc_le_centralizer_cj_Seven2 c ha hcc) y hy
    calc y * (p * cc) = (y * p) * cc := by group
      _ = (p * y) * cc := by rw [h1]
      _ = p * (y * cc) := by group
      _ = p * (cc * y) := by rw [h2]
      _ = p * cc * y := by group
  calc cj (BbJ S α A g) a
      = cj (PminusJ S α g) a ⊔
        cj (B0J S α A ⊓ Subgroup.centralizer
          ((PminusJ S α g : Subgroup G) : Set G)) a := cj_sup
    _ ≤ BbJ S α A g := sup_le hPa ((cj_Cc_eq_Seven2 c ha).le.trans le_sup_right)

private theorem Bb_normalized_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {a : G} (ha : a ∈ A)
    {b : G} (hb : b ∈ BbJ S α A g) : a * b * a⁻¹ ∈ BbJ S α A g := by
  have hcj : cj (BbJ S α A g) a = BbJ S α A g := cj_eq_of_le (cj_Bb_le_Seven2 c ha)
  have : b ∈ cj (BbJ S α A g) a := by rw [hcj]; exact hb
  exact mem_cj.mp this

private theorem Ysub_le_J_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) : YsubJ S α g ≤ J := by
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact c.hg2
  have h := mixed_conjugation_calculusJ_abc c.seed c.lam c.hαΛ c.hgH hg2 c.hgH c.hgM hg2
  exact h.2.2

private theorem commutator_Pminus_Ysub_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅PminusJ S α g, YsubJ S α g⁆ = ⊥ := by
  have hPR := tr_Fcore_le_thompsonJ_coreJ c.seed α g (hV_Seven2 c)
  have hFP : ⁅Fcore G, cj (aimg J α (Fcore G)) g⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun f hf p hp =>
      (Fcore_commute_thompsonJ_core hf (hPR hp)).symm
  have hPS : cj (aimg J α (Fcore G)) g ≤ J :=
    tr_Fcore_le_thompsonJ_sylowJ c.seed α g (hV_Seven2 c)
  have hFiU : ⁅aimg J α.symm (Fcore G),
      aimg J α.symm (cj (aimg J α (Fcore G)) g)⁆ = ⊥ := by
    have := aimg_commutator (S := J) (α := α.symm) (Fcore_le_JS c.seed) hPS
    rw [hFP, aimg_bot] at this
    exact this.symm
  show ⁅cj (aimg J α.symm (Fcore G)) g,
    cj (aimg J α.symm (cj (aimg J α (Fcore G)) g)) g⁆ = ⊥
  rw [← cj_commutator, hFiU, cj_bot]

private theorem commutator_Ysub_cj_Pminus_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) {x : G}
    (hx : x ∈ A) (hxQ : x ∉ CFSG.pCore 2 G) :
    ⁅YsubJ S α g, cj (PminusJ S α g) x⁆ = ⊥ := by
  have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 x hx
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact c.hg2
  have h := mixed_conjugation_calculusJ_def c.seed c.lam c.hαΛ c.hgH c.hgM hg2
    c.hgH c.hgM hg2 (maxElem_le_thompsonJ c.hA hx) hxQ hx2
  rw [YsubJ, PminusJ, cj_cj]
  exact h.2.2

private theorem commutator_A_Bb_case_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ x ∈ A, x ∉ CFSG.pCore 2 G → ∀ b ∈ BbJ S α A g,
      x * b * x⁻¹ * b⁻¹ ∈ BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) := by
  have hZZc : Zfix S ⊔ aimg J α (Zfix S) ≤
      Subgroup.centralizer ((J : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · intro z hz
      exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
        IsSeed.Zfix_central hz (thompsonJ_le_self' (S : Subgroup G) hj)
    · intro z hz
      exact Subgroup.mem_centralizer_iff.mpr fun j hj => aimgJ_Zfix_central α hj hz
  have hYJ : YsubJ S α g ≤ J := Ysub_le_J_Seven2 c
  have hPC : ∀ x ∈ PminusJ S α g,
      ∀ y ∈ B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G),
      x * y = y * x := fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx
  intro x hx hxQ b hb
  have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 x hx
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  refine ⟨mul_mem (Bb_normalized_Seven2 c hx hb) ((BbJ S α A g).inv_mem hb),
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨p, hp, cc, hcc, rfl⟩ := mem_sup_of_commute hPC hb
  have e : x * (p * cc) * x⁻¹ * (p * cc)⁻¹ =
      (x * p * x⁻¹) * (x * cc * x⁻¹ * cc⁻¹) * p⁻¹ := by group
  rw [e]
  have c1 : Commute y (x * p * x⁻¹) := by
    have hmem : x * p * x⁻¹ ∈ cj (PminusJ S α g) x := by
      rw [mem_cj]
      have : x * (x * p * x⁻¹) * x⁻¹ = p := by
        calc x * (x * p * x⁻¹) * x⁻¹ = (x * x) * p * (x⁻¹ * x⁻¹) := by group
          _ = p := by rw [hxx, hxinv, hxx, one_mul, mul_one]
      rw [this]; exact hp
    exact mul_comm_of_commutator_eq_bot
      (commutator_Ysub_cj_Pminus_Seven2 c hx hxQ) hy hmem
  have c2 : Commute y (x * cc * x⁻¹ * cc⁻¹) := by
    have hmem : x * cc * x⁻¹ * cc⁻¹ ∈ Zfix S ⊔ aimg J α (Zfix S) :=
      commutator_A_B0_le_ZZ_Seven2 c (Subgroup.commutator_mem_commutator hx hcc.1)
    exact Subgroup.mem_centralizer_iff.mp (hZZc hmem) y (hYJ hy)
  have c3 : Commute y p⁻¹ := by
    have hYP : ⁅YsubJ S α g, PminusJ S α g⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact commutator_Pminus_Ysub_Seven2 c
    exact mul_comm_of_commutator_eq_bot hYP hy ((PminusJ S α g).inv_mem hp)
  exact ((c1.mul_right c2).mul_right c3).eq

private theorem commutator_A_Bb_norm_Seven2 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ∀ x ∈ A, x ∉ CFSG.pCore 2 G → ∀ u ∈ BbJ S α A g ⊓
      Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G),
      x * u * x⁻¹ ∈ BbJ S α A g ⊓
        Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) := by
  intro x hx hxQ u hu
  have : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
  rw [this]
  exact mul_mem (commutator_A_Bb_case_Seven2 c x hx hxQ u hu.1) hu

theorem DoubleSetupJ.Hone_eq_sup (c : DoubleSetupJ S ρ ψ Λ α A g) :
    Hone S = CFSG.Quasithin.thompsonJ (S : Subgroup G) ⊔ cj A g := by
  apply le_antisymm
  · refine Hone_le_of_sup_core_eq_top le_sup_left ?_
    obtain ⟨ℓ, hℓ⟩ := c.seed.exists_rootGrp_eq
    obtain ⟨hmapA, -⟩ := c.seed.max_outside c.hA c.hAQ
    have hne : ℓ ≠ (ρ g)⁻¹ • ℓ := by
      intro e
      apply c.hgM
      rw [mem_Mnorm_iff hℓ]
      rw [eq_inv_smul_iff] at e
      exact e
    refine c.seed.sup_core_eq_top hne ?_ ?_
    · rw [← hℓ, ← hmapA]
      exact Subgroup.map_mono fun a ha => Subgroup.mem_sup_left (maxElem_le_thompsonJ c.hA ha)
    · rw [rootGrp_smul_eq_map, ← hℓ, ← hmapA]
      rintro _ ⟨u, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨g⁻¹ * a * g, Subgroup.mem_sup_right ?_, by simp [map_mul, map_inv]⟩
      rw [mem_cj]
      simpa [mul_assoc] using ha
  · refine sup_le Subgroup.le_normalClosure ?_
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Hone S :=
      Subgroup.le_normalClosure (maxElem_le_thompsonJ c.hA (mem_cj.mp hx))
    have := (inferInstance : (Hone S).Normal).conj_mem _ h1 g⁻¹
    simpa [mul_assoc] using this

theorem DoubleSetupJ.commutator_A_Bb_le (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅A, BbJ S α A g⁆ ≤
      BbJ S α A g ⊓ Subgroup.centralizer ((YsubJ S α g : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  by_cases haQ : a ∈ CFSG.pCore 2 G
  · obtain ⟨x₀, hx₀, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
    have hy₀ : x₀⁻¹ * a ∈ A := mul_mem (A.inv_mem hx₀) ha
    have hy₀Q : x₀⁻¹ * a ∉ CFSG.pCore 2 G := by
      intro hQ
      apply hx₀Q
      have : x₀ = a * (x₀⁻¹ * a)⁻¹ := by group
      rw [this]
      exact mul_mem haQ ((CFSG.pCore 2 G).inv_mem hQ)
    have e : a * b * a⁻¹ * b⁻¹ =
        (x₀ * (x₀⁻¹ * a * b * (x₀⁻¹ * a)⁻¹ * b⁻¹) * x₀⁻¹) *
        (x₀ * b * x₀⁻¹ * b⁻¹) := by group
    show a * b * a⁻¹ * b⁻¹ ∈ _
    rw [e]
    exact mul_mem (commutator_A_Bb_norm_Seven2 c x₀ hx₀ hx₀Q _
      (commutator_A_Bb_case_Seven2 c _ hy₀ hy₀Q b hb))
      (commutator_A_Bb_case_Seven2 c x₀ hx₀ hx₀Q b hb)
  · exact commutator_A_Bb_case_Seven2 c a ha haQ b hb

theorem DoubleSetupJ.not_Pg_le_B0 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ¬ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g ≤ B0J S α A := by
  intro hPB
  apply c.hα
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right c.hg2
  have hT : ⁅aimg J α (Fcore G), J⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm, commutator_thompsonJ_aimgJ_Fcore c.seed α]
    exact aimgJ_Zfix_le_Fcore c.seed α
  have hAg : ⁅aimg J α (Fcore G), cj A g⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm]
    have e : ⁅cj A g, aimg J α (Fcore G)⁆ =
        cj ⁅A, cj (aimg J α (Fcore G)) g⁻¹⁆ g := by
      rw [cj_commutator, cj_cj_inv]
    rw [e, hginv]
    calc cj ⁅A, cj (aimg J α (Fcore G)) g⁆ g ≤ cj (Fcore G) g :=
          cj_mono ((Subgroup.commutator_mono le_rfl hPB).trans
            (commutator_A_B0_le_F_Seven2 c))
      _ = Fcore G := cj_eq_self_of_normal
  have : ⁅aimg J α (Fcore G), Hone S⁆ ≤ Fcore G := by
    rw [c.Hone_eq_sup]
    exact commutator_sup_le (N := ⊤)
      (fun n _ v hv => (inferInstance : (Fcore G).Normal).conj_mem v hv n)
      le_top le_top hT hAg
  rw [Subgroup.commutator_comm]; exact this

theorem DoubleSetupJ.commutator_B0_Pg (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅B0J S α A, cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆ =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hB0Q : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (B0J S α A) :=
    c.facts71.2.1
  have hPQ : cj (aimg J α (Fcore G)) g ≤ CFSG.pCore 2 G :=
    cj_le_core (aimgJ_Fcore_le_core c.seed α (hV_Seven2 c)) g
  have hPel : CFSG.Open.IsElemAbelian 2 (cj (aimg J α (Fcore G)) g) :=
    isElemAbelian_cj (isElemAbelian_aimg (S := J) α isElemAbelian_Fcore) g
  have hne : ⁅B0J S α A, tr J α g (Fcore G)⁆ ≠ ⊥ := by
    intro hb
    apply c.not_Pg_le_B0
    exact maxElem_le_of_commute hB0Q hPQ hPel fun y hy b hb' =>
      (mul_comm_of_commutator_eq_bot hb hb' hy).symm
  have hA' : CFSG.Quasithin.IsMaxElemAbelian (cj J g) (B0J S α A) :=
    (isMaxElemAbelian_cj_thompsonJ_iff (S := S) g).mpr
      (c.seed.isMaxElemAbelian_cj_of_core hB0Q g)
  have hthis := (tr_commutator_eq_of_ne_botJ c.seed α g hA' hne).1
  rw [show tr J α g (Fcore G) = cj (aimg J α (Fcore G)) g from rfl] at hthis
  rw [hthis]
  exact cj_Za_Seven2 c

theorem DoubleSetupJ.commutator_R0_Pg (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G),
        cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g⁆ =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  apply le_antisymm
  · rw [Subgroup.commutator_comm]
    exact commutator_cj_Fa_R0_leJ c.seed α (hV_Seven2 c) (hF_Seven2 c) c.hgH
  · rw [← c.commutator_B0_Pg]
    exact Subgroup.commutator_mono (maxElem_le_thompsonJ c.facts71.2.1) le_rfl

end CFSG.QuasithinUnique.Setup.CampbellJ

end
