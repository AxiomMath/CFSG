module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMixed

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Double

variable {G : Type*} [Group G]

@[expose] def B0 (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G) :
    Subgroup G :=
  Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) ⊔
    (A ⊓ Subgroup.centralizer ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G))

@[expose] def Pminus (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) :
    Subgroup G :=
  cj (aimg (S : Subgroup G) α.symm (Fcore G)) g

@[expose] def Cc (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G)
    (g : G) : Subgroup G :=
  B0 S α A ⊓ Subgroup.centralizer ((Pminus S α g : Subgroup G) : Set G)

@[expose] def Bb (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G)
    (g : G) : Subgroup G :=
  Pminus S α g ⊔ Cc S α A g

@[expose] def Ysub (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) :
    Subgroup G :=
  cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g

theorem mem_centralizer_sup {P P' : Subgroup G} {a : G} (h1 : ∀ x ∈ P, x * a = a * x)
    (h2 : ∀ x ∈ P', x * a = a * x) : a ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G) := by
  have : P ⊔ P' ≤ Subgroup.centralizer ({a} : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (h1 x hx).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (h2 x hx).symm)
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  exact (Subgroup.mem_centralizer_iff.mp (this hy) a (Set.mem_singleton a)).symm

section Seed

variable {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem B0_eq_Bone (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) : B0 S α A = Bone S α A := by
  have hFaJ := h.aimg_Fcore_le_thompsonJ_core α hV
  have hFFa : ∀ x ∈ Fcore G, ∀ w ∈ aimg (S : Subgroup G) α (Fcore G), x * w = w * x :=
    fun x hx w hw => (Fcore_commute_thompsonJ_core hx (hFaJ hw)).symm
  apply le_antisymm
  · refine sup_le (sup_le (h.Fcore_le_Bone α hV A) le_sup_left) ?_
    rintro x ⟨hxA, hxc⟩
    have hxF : x ∈ A ⊓ Subgroup.centralizer (Fcore G : Set G) :=
      ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun f hf =>
        Subgroup.mem_centralizer_iff.mp hxc f (Subgroup.mem_sup_left hf)⟩
    rw [h.inf_centralizer_Fcore hA] at hxF
    apply Subgroup.mem_sup_right
    refine ⟨Subgroup.mem_sup_left hxF, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hxc w (Subgroup.mem_sup_right hw)
  · refine sup_le ((le_sup_right : aimg (S : Subgroup G) α (Fcore G) ≤
      Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)).trans le_sup_left) (fun u hu => ?_)
    obtain ⟨huB, huc⟩ := hu
    have hFB0 : Fcore G ≤ B0 S α A := le_sup_left.trans le_sup_left
    have hcommAF : ∀ x ∈ A ⊓ CFSG.pCore 2 G, ∀ y ∈ Fcore G, x * y = y * x := by
      intro x hx y hy
      have : x ∈ A ⊓ Subgroup.centralizer (Fcore G : Set G) := by
        rw [h.inf_centralizer_Fcore hA]; exact hx
      exact (Subgroup.mem_centralizer_iff.mp this.2 y hy).symm
    obtain ⟨a, ha, f, hf, rfl⟩ := mem_sup_of_commute hcommAF huB
    have hac : a ∈ Subgroup.centralizer ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) :
        Subgroup G) : Set G) := by
      refine mem_centralizer_sup (fun x hx => (hcommAF a ha x hx).symm) (fun w hw => ?_)
      have h1 := Subgroup.mem_centralizer_iff.mp huc w hw
      have h2 := hFFa f hf w hw
      calc w * a = w * (a * f) * f⁻¹ := by group
        _ = (a * f) * w * f⁻¹ := by rw [h1]
        _ = a * (f * w) * f⁻¹ := by group
        _ = a * (w * f) * f⁻¹ := by rw [h2]
        _ = a * w := by group
    exact mul_mem (Subgroup.mem_sup_right (⟨ha.1, hac⟩ : a ∈ A ⊓ Subgroup.centralizer ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G))) (hFB0 hf)

theorem aimg_Fcore_ne (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hα : ¬ ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G) :
    aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G := by
  intro e
  apply hα
  rw [e, h.commutator_Hone_Fcore]
  exact Vmod_le_Ecore.trans h.Ecore_le_Fcore

omit [Field k] [Finite G] [Finite k] h in
theorem aimg_symm_Fcore_ne [Finite G] (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    aimg (S : Subgroup G) α.symm (Fcore G) ≠ Fcore G := by
  intro e
  apply hF
  calc aimg (S : Subgroup G) α (Fcore G)
      = aimg (S : Subgroup G) α (aimg (S : Subgroup G) α.symm (Fcore G)) := by rw [e]
    _ = Fcore G := aimg_aimg_symm Fcore_le_sylow

theorem B0_isMax (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    IsMaxElemAbelian (CFSG.pCore 2 G) (B0 S α A) ∧ IsMaxElemAbelian (S : Subgroup G) (B0 S α A) ∧
      B0 S α A ≤ CFSG.pCore 2 G := by
  rw [h.B0_eq_Bone α hV hA]
  obtain ⟨hS, hQ, hQmax⟩ := h.Bone_isMax α hV hA
  exact ⟨hQmax, hS, hQ⟩

theorem Pminus_le_core (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    Pminus S α g ≤ CFSG.pCore 2 G := cj_le_core (h.aimg_Fcore_le_core α.symm hV') g

theorem Pminus_adm (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    Adm (CFSG.pCore 2 G) (Pminus S α g) := adm_core_cj (h.adm_core_aimg_Fcore α.symm hV') g

theorem Pminus_le_R0 (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    Pminus S α g ≤ thompsonJ (CFSG.pCore 2 G) := h.tr_Fcore_le_thompsonJ_core α.symm hV' g

theorem Fcore_le_centralizer_Pminus (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    Fcore G ≤ Subgroup.centralizer ((Pminus S α g : Subgroup G) : Set G) := fun _ hf =>
  Subgroup.mem_centralizer_iff.mpr fun _ hw =>
    Fcore_commute_thompsonJ_core hf (h.Pminus_le_R0 α hV' g hw)

theorem Bb_isMax (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (g : G) :
    IsMaxElemAbelian (CFSG.pCore 2 G) (Bb S α A g) ∧
      IsMaxElemAbelian (S : Subgroup G) (Bb S α A g) ∧ Bb S α A g ≤ CFSG.pCore 2 G := by
  obtain ⟨hB0Q, hB0S, hB0le⟩ := h.B0_isMax α hV hA
  have h1 := h.isMaxElemAbelian_tr_Fcore_sup α.symm g (A' := B0 S α A)
    (h.isMaxElemAbelian_cj_of_core hB0Q g)
  have hBbQ : Bb S α A g ≤ CFSG.pCore 2 G :=
    sup_le (h.Pminus_le_core α hV' g) ((inf_le_left : Cc S α A g ≤ B0 S α A).trans hB0le)
  have hQ : IsMaxElemAbelian (CFSG.pCore 2 G) (Bb S α A g) :=
    isMaxElemAbelian_core_of_le_cj (core_le_sylow S) h1 hBbQ
  exact ⟨hQ, h.max_core_facts.1 _ hQ, hBbQ⟩

omit [Field k] [Finite G] [Finite k] h in
theorem Fcore_le_B0 (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G) :
    Fcore G ≤ B0 S α A := le_sup_left.trans le_sup_left

theorem Fcore_le_Bb (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) (A : Subgroup G) (g : G) :
    Fcore G ≤ Bb S α A g :=
  (le_inf (Fcore_le_B0 α A) (h.Fcore_le_centralizer_Pminus α hV' g) : Fcore G ≤ Cc S α A g).trans
    le_sup_right

end IsSeed

structure DoubleSetup (S : Sylow 2 G) (ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k)
    (ψ : Ecore G →* Multiplicative (Fin 2 → k))
    (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G) (g : G) : Prop where
  seed : IsSeed S ρ (Ecore G) ψ
  hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G
  hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G
  hα : ¬ ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G
  hA : IsMaxElemAbelian (S : Subgroup G) A
  hAQ : ¬ A ≤ CFSG.pCore 2 G
  hgH : g ∈ Hone S
  hgM : g ∉ Mnorm S ρ
  hg2 : g * g = 1

namespace DoubleSetup

variable [Finite G] [Finite k] {α : (S : Subgroup G) ≃* (S : Subgroup G)} {A : Subgroup G} {g : G}
  (c : DoubleSetup S ρ ψ α A g)
include c

theorem hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G := c.seed.aimg_Fcore_ne α c.hα

theorem hFi : aimg (S : Subgroup G) α.symm (Fcore G) ≠ Fcore G :=
  IsSeed.aimg_symm_Fcore_ne α c.hF

theorem Za_central : aimg (S : Subgroup G) α (Zfix S) ≤ Subgroup.center G :=
  c.seed.aimg_Zfix_le_center α c.hV c.hF

theorem Zi_central : aimg (S : Subgroup G) α.symm (Zfix S) ≤ Subgroup.center G :=
  c.seed.aimg_Zfix_le_center α.symm c.hV' c.hFi

theorem B0_normalized {a : G} (ha : a ∈ A) {b : G} (hb : b ∈ B0 S α A) :
    a * b * a⁻¹ ∈ B0 S α A := by
  rw [c.seed.B0_eq_Bone α c.hV c.hA] at hb ⊢
  exact IsSeed.Bone_normalized α c.hA ha hb

theorem commutator_A_B0_le_ZZ : ⁅A, B0 S α A⁆ ≤ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) := by
  rw [c.seed.B0_eq_Bone α c.hV c.hA]
  exact c.seed.commutator_A_Bone_le α c.hA c.hAQ

theorem commutator_A_B0_le_F : ⁅A, B0 S α A⁆ ≤ Fcore G :=
  c.commutator_A_B0_le_ZZ.trans (c.seed.Zfix_sup_aimg_le_Fcore α)

theorem cj_Cc_eq {a : G} (ha : a ∈ A) : cj (Cc S α A g) a = Cc S α A g := by
  apply cj_eq_of_forall_mem
  intro x hx
  have hxB0 : x ∈ B0 S α A := hx.1
  have h1 : a * x * a⁻¹ ∈ B0 S α A := c.B0_normalized ha hxB0
  have hcomm : a * x * a⁻¹ * x⁻¹ ∈ Cc S α A g := by
    refine ⟨mul_mem h1 ((B0 S α A).inv_mem hxB0), Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hF1 : a * x * a⁻¹ * x⁻¹ ∈ Fcore G :=
      c.commutator_A_B0_le_F (Subgroup.commutator_mem_commutator ha hxB0)
    exact Fcore_commute_thompsonJ_core hF1 (c.seed.Pminus_le_R0 α c.hV' g hw)
  have : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
  rw [this]
  exact mul_mem hcomm hx

theorem Cc_le_centralizer_cj {a : G} (ha : a ∈ A) :
    Cc S α A g ≤ Subgroup.centralizer ((cj (Pminus S α g) a : Subgroup G) : Set G) := by
  have h1 : Cc S α A g ≤ Subgroup.centralizer ((Pminus S α g : Subgroup G) : Set G) := inf_le_right
  have h2 := cj_mono (g := a) h1
  rw [c.cj_Cc_eq ha, ← centralizer_cj] at h2
  exact h2

omit [Field k] [Finite G] [Finite k] c in
theorem isElemAbelian_Pminus : CFSG.Open.IsElemAbelian 2 (Pminus S α g) :=
  isElemAbelian_cj (isElemAbelian_aimg α.symm isElemAbelian_Fcore) g

theorem Pminus_commute_cj {a : G} (ha : a ∈ A) :
    ⁅cj (Pminus S α g) a, Pminus S α g⁆ = ⊥ := by
  have hax : ∃ n : ℕ, a⁻¹ ^ (2 ^ n) = 1 := ⟨1, by
    have : a ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 a ha
    rw [pow_one, inv_pow, this, inv_one]⟩
  have h1 := c.seed.two_element_conjugate_commutation α.symm c.hV' (g * a) a⁻¹ hax
  rw [mul_inv_cancel_right] at h1
  have e : cj (aimg (S : Subgroup G) α.symm (Fcore G)) (g * a) = cj (Pminus S α g) a := by
    rw [Pminus, cj_cj]
  rw [e] at h1
  exact h1

theorem cj_Bb_le {a : G} (ha : a ∈ A) : cj (Bb S α A g) a ≤ Bb S α A g := by
  obtain ⟨hBbQ, hBbS, hBble⟩ := c.seed.Bb_isMax α c.hV c.hV' c.hA g
  have hPC : ∀ x ∈ Pminus S α g, ∀ y ∈ Cc S α A g, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have hPa : cj (Pminus S α g) a ≤ Bb S α A g := by
    refine maxElem_le_of_commute hBbQ (cj_le_core (c.seed.Pminus_le_core α c.hV' g) a)
      (isElemAbelian_cj isElemAbelian_Pminus a) ?_
    intro y hy u hu
    obtain ⟨p, hp, cc, hcc, rfl⟩ := mem_sup_of_commute hPC hu
    have h1 : y * p = p * y := mul_comm_of_commutator_eq_bot (c.Pminus_commute_cj ha) hy hp
    have h2 : y * cc = cc * y :=
      Subgroup.mem_centralizer_iff.mp (c.Cc_le_centralizer_cj ha hcc) y hy
    calc y * (p * cc) = (y * p) * cc := by group
      _ = (p * y) * cc := by rw [h1]
      _ = p * (y * cc) := by group
      _ = p * (cc * y) := by rw [h2]
      _ = p * cc * y := by group
  calc cj (Bb S α A g) a = cj (Pminus S α g) a ⊔ cj (Cc S α A g) a := cj_sup
    _ ≤ Bb S α A g := sup_le hPa ((c.cj_Cc_eq ha).le.trans le_sup_right)

theorem Bb_normalized {a : G} (ha : a ∈ A) {b : G} (hb : b ∈ Bb S α A g) :
    a * b * a⁻¹ ∈ Bb S α A g := by
  have hcj : cj (Bb S α A g) a = Bb S α A g := cj_eq_of_le (c.cj_Bb_le ha)
  have : b ∈ cj (Bb S α A g) a := by rw [hcj]; exact hb
  exact mem_cj.mp this

theorem Ysub_le_core : Ysub S α g ≤ CFSG.pCore 2 G := by
  obtain ⟨-, -, -, hUQ, -⟩ := c.seed.U_facts α c.hV (c.hg2)
  exact cj_le_core hUQ g

theorem commutator_Pminus_Ysub : ⁅Pminus S α g, Ysub S α g⁆ = ⊥ := by
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hPR := c.seed.tr_Fcore_le_thompsonJ_core α c.hV g
  have hFP : ⁅Fcore G, cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun f hf p hp =>
      (Fcore_commute_thompsonJ_core hf (hPR hp)).symm
  have hPS : cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) :=
    (cj_le_core (c.seed.aimg_Fcore_le_core α c.hV) g).trans hQS
  have hFiU : ⁅aimg (S : Subgroup G) α.symm (Fcore G),
      aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = ⊥ := by
    have := aimg_commutator (S := (S : Subgroup G)) (α := α.symm) Fcore_le_sylow hPS
    rw [hFP, aimg_bot] at this
    exact this.symm
  show ⁅cj (aimg (S : Subgroup G) α.symm (Fcore G)) g,
    cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g⁆ = ⊥
  rw [← cj_commutator, hFiU, cj_bot]

theorem commutator_Ysub_cj_Pminus {x : G} (hx : x ∈ A) (hxQ : x ∉ CFSG.pCore 2 G) :
    ⁅Ysub S α g, cj (Pminus S α g) x⁆ = ⊥ := by
  have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 x hx
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact c.hg2
  have := (c.seed.mixed_conjugation_calculus α c.hV c.hV' c.hgH c.hgM hg2 c.hgH c.hgM hg2
    (maxElem_le_thompsonJ c.hA hx) hxQ hx2).2.2.2.2
  rw [Ysub, Pminus, cj_cj]
  exact this

open scoped commutatorElement in
theorem commutator_A_Bb_le :
    ⁅A, Bb S α A g⁆ ≤ Bb S α A g ⊓ Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G) := by
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hZZc := Zfix_sup_aimg_le_centralizer (S := S) α
  have hYS : Ysub S α g ≤ (S : Subgroup G) := c.Ysub_le_core.trans hQS
  have hPC : ∀ x ∈ Pminus S α g, ∀ y ∈ Cc S α A g, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have hxcase : ∀ x ∈ A, x ∉ CFSG.pCore 2 G → ∀ b ∈ Bb S α A g,
      x * b * x⁻¹ * b⁻¹ ∈ Bb S α A g ⊓ Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G) := by
    intro x hx hxQ b hb
    have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 x hx
    have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    refine ⟨mul_mem (c.Bb_normalized hx hb) ((Bb S α A g).inv_mem hb),
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨p, hp, cc, hcc, rfl⟩ := mem_sup_of_commute hPC hb
    have e : x * (p * cc) * x⁻¹ * (p * cc)⁻¹ = (x * p * x⁻¹) * (x * cc * x⁻¹ * cc⁻¹) * p⁻¹ := by
      group
    rw [e]
    have c1 : Commute y (x * p * x⁻¹) := by
      have hmem : x * p * x⁻¹ ∈ cj (Pminus S α g) x := by
        rw [mem_cj]
        have : x * (x * p * x⁻¹) * x⁻¹ = p := by
          calc x * (x * p * x⁻¹) * x⁻¹ = (x * x) * p * (x⁻¹ * x⁻¹) := by group
            _ = p := by rw [hxx, hxinv, hxx, one_mul, mul_one]
        rw [this]; exact hp
      exact mul_comm_of_commutator_eq_bot (c.commutator_Ysub_cj_Pminus hx hxQ) hy hmem
    have c2 : Commute y (x * cc * x⁻¹ * cc⁻¹) := by
      have hmem : x * cc * x⁻¹ * cc⁻¹ ∈ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) :=
        c.commutator_A_B0_le_ZZ (Subgroup.commutator_mem_commutator hx hcc.1)
      exact Subgroup.mem_centralizer_iff.mp (hZZc hmem) y (hYS hy)
    have c3 : Commute y p⁻¹ := by
      have hYP : ⁅Ysub S α g, Pminus S α g⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]; exact c.commutator_Pminus_Ysub
      exact mul_comm_of_commutator_eq_bot hYP hy ((Pminus S α g).inv_mem hp)
    exact ((c1.mul_right c2).mul_right c3).eq
  have hnorm : ∀ x ∈ A, x ∉ CFSG.pCore 2 G → ∀ u ∈ Bb S α A g ⊓
      Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G),
      x * u * x⁻¹ ∈ Bb S α A g ⊓ Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G) := by
    intro x hx hxQ u hu
    have : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    rw [this]
    exact mul_mem (hxcase x hx hxQ u hu.1) hu
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
    have e : a * b * a⁻¹ * b⁻¹ = (x₀ * (x₀⁻¹ * a * b * (x₀⁻¹ * a)⁻¹ * b⁻¹) * x₀⁻¹) *
        (x₀ * b * x₀⁻¹ * b⁻¹) := by group
    show a * b * a⁻¹ * b⁻¹ ∈ _
    rw [e]
    exact mul_mem (hnorm x₀ hx₀ hx₀Q _ (hxcase _ hy₀ hy₀Q b hb)) (hxcase x₀ hx₀ hx₀Q b hb)
  · exact hxcase a ha haQ b hb

theorem Hone_eq_sup : Hone S = thompsonJ (S : Subgroup G) ⊔ cj A g := by
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

theorem not_Pg_le_B0 : ¬ cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ B0 S α A := by
  intro hPB
  apply c.hα
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right c.hg2
  have hZaF : aimg (S : Subgroup G) α (Zfix S) ≤ Fcore G := c.seed.aimg_Zfix_le_Fcore α
  have hT : ⁅aimg (S : Subgroup G) α (Fcore G), thompsonJ (S : Subgroup G)⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm, c.seed.commutator_thompsonJ_aimg_Fcore α]; exact hZaF
  have hAg : ⁅aimg (S : Subgroup G) α (Fcore G), cj A g⁆ ≤ Fcore G := by
    rw [Subgroup.commutator_comm]
    have e : ⁅cj A g, aimg (S : Subgroup G) α (Fcore G)⁆ =
        cj ⁅A, cj (aimg (S : Subgroup G) α (Fcore G)) g⁻¹⁆ g := by
      rw [cj_commutator, cj_cj_inv]
    rw [e, hginv]
    calc cj ⁅A, cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ g ≤ cj (Fcore G) g :=
          cj_mono ((Subgroup.commutator_mono le_rfl hPB).trans c.commutator_A_B0_le_F)
      _ = Fcore G := cj_eq_self_of_normal
  have : ⁅aimg (S : Subgroup G) α (Fcore G), Hone S⁆ ≤ Fcore G := by
    rw [c.Hone_eq_sup]
    exact commutator_sup_le (N := ⊤)
      (fun n _ v hv => (inferInstance : (Fcore G).Normal).conj_mem v hv n) le_top le_top hT hAg
  rw [Subgroup.commutator_comm]; exact this

theorem commutator_B0_Pg :
    ⁅B0 S α A, cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ = aimg (S : Subgroup G) α (Zfix S) := by
  obtain ⟨hB0Q, hB0S, hB0le⟩ := c.seed.B0_isMax α c.hV c.hA
  have hPQ : cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ CFSG.pCore 2 G :=
    cj_le_core (c.seed.aimg_Fcore_le_core α c.hV) g
  have hPel : CFSG.Open.IsElemAbelian 2 (cj (aimg (S : Subgroup G) α (Fcore G)) g) :=
    isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Fcore) g
  have hne : ⁅B0 S α A, tr (S : Subgroup G) α g (Fcore G)⁆ ≠ ⊥ := by
    intro hb
    apply c.not_Pg_le_B0
    exact maxElem_le_of_commute hB0Q hPQ hPel fun y hy b hb' =>
      (mul_comm_of_commutator_eq_bot hb hb' hy).symm
  have := (c.seed.tr_commutator_eq_of_ne_bot α g (c.seed.isMaxElemAbelian_cj_of_core hB0Q g)
    hne).1
  rw [show tr (S : Subgroup G) α g (Fcore G) = cj (aimg (S : Subgroup G) α (Fcore G)) g from rfl]
    at this
  rw [this]
  exact cj_eq_of_le_center c.Za_central g

theorem commutator_R0_Pg :
    ⁅thompsonJ (CFSG.pCore 2 G), cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ =
      aimg (S : Subgroup G) α (Zfix S) := by
  apply le_antisymm
  · rw [Subgroup.commutator_comm]; exact c.seed.commutator_cj_Fa_R0_le α c.hV c.hF g
  · rw [← c.commutator_B0_Pg]
    exact Subgroup.commutator_mono (maxElem_le_thompsonJ (c.seed.B0_isMax α c.hV c.hA).1) le_rfl

end DoubleSetup

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem exists_A_g : ∃ A : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A ∧
    ¬ A ≤ CFSG.pCore 2 G ∧ ∃ g ∈ Hone S, g ∉ Mnorm S ρ ∧ g * g = 1 := by
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  obtain ⟨a₀, ha₀, ha₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  obtain ⟨c, hcH, hcM⟩ := h.exists_Hone_not_mem_Mnorm
  have ha₀2 : a₀ * a₀ = 1 := by
    rw [← pow_two]; exact (isElemAbelian_iff.mp hA.2.1).2 a₀ ha₀
  refine ⟨A, hA, hAQ, c⁻¹ * a₀ * c, ?_, ?_, ?_⟩
  · have h1 : a₀ ∈ Hone S := Subgroup.le_normalClosure (maxElem_le_thompsonJ hA ha₀)
    have := (inferInstance : (Hone S).Normal).conj_mem a₀ h1 c⁻¹
    simpa using this
  · intro hM
    apply hcM
    have : c⁻¹ ∈ Mnorm S ρ := by
      refine h.mem_Mnorm_of_conj_mem (hA.1 ha₀) ha₀Q ?_
      simpa using hM
    simpa using (Mnorm S ρ).inv_mem this
  · calc c⁻¹ * a₀ * c * (c⁻¹ * a₀ * c) = c⁻¹ * (a₀ * a₀) * c := by group
      _ = 1 := by rw [ha₀2]; group

theorem final_double_replacement_configuration (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hVall : ∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) β (Vmod G) ≤ CFSG.pCore 2 G)
    (hα : ¬ ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) {g : G}
    (hgH : g ∈ Hone S) (hgM : g ∉ Mnorm S ρ) (hg2 : g ^ 2 = 1) :
    cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) ∧
    (IsMaxElemAbelian (CFSG.pCore 2 G) (B0 S α A) ∧ IsMaxElemAbelian (S : Subgroup G) (B0 S α A)) ∧
    (IsMaxElemAbelian (CFSG.pCore 2 G) (Bb S α A g) ∧
      IsMaxElemAbelian (S : Subgroup G) (Bb S α A g)) ∧
    (∀ a ∈ A, ∀ b ∈ B0 S α A, a * b * a⁻¹ ∈ B0 S α A) ∧
    (∀ a ∈ A, ∀ b ∈ Bb S α A g, a * b * a⁻¹ ∈ Bb S α A g) ∧
    (∀ a ∈ A, ∀ b ∈ Cc S α A g, a * b * a⁻¹ ∈ Cc S α A g) ∧
    (Fcore G ≤ B0 S α A ∧ Fcore G ≤ Bb S α A g) ∧
    (aimg (S : Subgroup G) α (Zfix S) ≤ Subgroup.center G ∧
      aimg (S : Subgroup G) α.symm (Zfix S) ≤ Subgroup.center G) ∧
    ⁅A, B0 S α A⁆ ≤ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) ∧
    ⁅A, Bb S α A g⁆ ≤ Bb S α A g ⊓ Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G) ∧
    (⁅thompsonJ (CFSG.pCore 2 G), cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ =
        aimg (S : Subgroup G) α (Zfix S) ∧
      ⁅B0 S α A, cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ = aimg (S : Subgroup G) α (Zfix S)) ∧
    Hone S = thompsonJ (S : Subgroup G) ⊔ cj A g := by
  have c : DoubleSetup S ρ ψ α A g :=
    ⟨h, hVall α, hVall α.symm, hα, hA, hAQ, hgH, hgM, by rw [← pow_two]; exact hg2⟩
  obtain ⟨hB0Q, hB0S, -⟩ := h.B0_isMax α (hVall α) hA
  obtain ⟨hBbQ, hBbS, -⟩ := h.Bb_isMax α (hVall α) (hVall α.symm) hA g
  exact ⟨(cj_le_core (h.aimg_Fcore_le_core α (hVall α)) g).trans (core_le_sylow S),
    ⟨hB0Q, hB0S⟩, ⟨hBbQ, hBbS⟩, fun a ha b hb => c.B0_normalized ha hb,
    fun a ha b hb => c.Bb_normalized ha hb,
    fun a ha x hx => mem_cj.mp (by rw [c.cj_Cc_eq ha]; exact hx),
    ⟨Fcore_le_B0 α A, h.Fcore_le_Bb α (hVall α.symm) A g⟩, ⟨c.Za_central, c.Zi_central⟩,
    c.commutator_A_B0_le_ZZ, c.commutator_A_Bb_le, ⟨c.commutator_R0_Pg, c.commutator_B0_Pg⟩,
    c.Hone_eq_sup⟩

end IsSeed

end Seed

end Double

end CFSG.QuasithinUnique.Setup.Campbell
