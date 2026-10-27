module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelPlus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelMinus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Model
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelLink

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage0
open CFSG.EvenSmallLie.OmegaEight.CPrimeModel
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (toMat)

section Transport

variable {G X : Type*} [Group G] [Group X] {L : Subgroup G} {L' : Subgroup X} {θ : L ≃* L'}
  {c : G} {σ : X}

theorem conj_pullE (hcL : c ∈ normalizer (L : Set G))
    (hc : ∀ l l' : L, (l' : G) = c * l * c⁻¹ → σ * (θ l : X) * σ⁻¹ = θ l') {y : X}
    (hy : y ∈ L') (hσy : σ * y * σ⁻¹ ∈ L') :
    c * pullE θ y hy * c⁻¹ = pullE θ (σ * y * σ⁻¹) hσy := by
  set l : L := θ.symm ⟨y, hy⟩ with hl
  have hl' : c * (l : G) * c⁻¹ ∈ L := (mem_normalizer_iff.1 hcL l).1 l.2
  have h := hc l ⟨_, hl'⟩ rfl
  have hθl : ((θ l : L') : X) = y := by rw [hl, MulEquiv.apply_symm_apply]
  rw [hθl] at h
  exact eq_pullE_of_theta hl' hσy h.symm

theorem conj_mem_pull (hcL : c ∈ normalizer (L : Set G))
    (hc : ∀ l l' : L, (l' : G) = c * l * c⁻¹ → σ * (θ l : X) * σ⁻¹ = θ l') {H' : Subgroup X}
    (hH : H' ≤ L') (hσH : ∀ y ∈ H', σ * y * σ⁻¹ ∈ H') {g : G} (hg : g ∈ pull θ H') :
    c * g * c⁻¹ ∈ pull θ H' := by
  obtain ⟨hgL, hg'⟩ := mem_pull.1 hg
  have e : g = pullE θ (θ ⟨g, hgL⟩ : X) (θ ⟨g, hgL⟩).2 := (pullE_theta hgL).symm
  rw [e, conj_pullE hcL hc _ (hH (hσH _ hg'))]
  exact (pullE_mem_pull _).2 (hσH _ hg')

end Transport

section Plus

open OmegaEight (gen omegaT autT omega1T stab0 res0 omegaRes omegaRestrictEquiv autConj)

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

theorem mul_inv_gen9_mem {y : Equiv.Perm (Fin 360)} (h : y⁻¹ * gen 9 ∈ omegaT) :
    y * (gen 9)⁻¹ ∈ omegaT := by
  have h9 : gen 9 ∈ autT := OmegaEight.gen_mem_autT (by norm_num)
  have h1 := (OmegaEight.conj_mem_omegaT h9).1 (inv_mem h)
  have e : gen 9 * (y⁻¹ * gen 9)⁻¹ * (gen 9)⁻¹ = y * (gen 9)⁻¹ := by group
  rwa [e] at h1

theorem exists_automizer_tau (hK : StepK t L) (θ₀ : L ≃* omega1T) {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hxN : x ∉ L ⊔ zpowers t) (hx2 : x * x ∈ zpowers t) :
    ∃ (θ : L ≃* omega1T) (Θ : centralizer ({t} : Set G) →* autT),
      (∀ (y : centralizer ({t} : Set G)) (l l' : L), (l' : G) = y * l * (y : G)⁻¹ →
        (Θ y : Equiv.Perm (Fin 360)) * (omegaRestrictEquiv.symm (θ l) : Equiv.Perm (Fin 360)) *
          (Θ y : Equiv.Perm (Fin 360))⁻¹ = omegaRestrictEquiv.symm (θ l')) ∧
      (∀ y, Θ y = 1 ↔ (y : G) ∈ zpowers t) ∧
      (∀ y, (Θ y : Equiv.Perm (Fin 360)) ∈ omegaT ↔ (y : G) ∈ L ⊔ zpowers t) ∧
      (Θ ⟨x, hx⟩ : Equiv.Perm (Fin 360)) * (gen 9)⁻¹ ∈ omegaT := by
  obtain ⟨Θ₀, h1, h2, h3⟩ := exists_model_automizer_plus hK θ₀
  have hgΩ : (Θ₀ ⟨x, hx⟩ : Equiv.Perm (Fin 360)) ∉ omegaT := fun h => hxN ((h3 _).1 h)
  have hg2 : (Θ₀ ⟨x, hx⟩ : Equiv.Perm (Fin 360)) * Θ₀ ⟨x, hx⟩ = 1 := by
    have h4 : Θ₀ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := (h2 _).2 hx2
    rw [map_mul] at h4
    exact congrArg Subtype.val h4
  obtain ⟨a, haA, ha⟩ := exists_conj_outer_plus (Θ₀ ⟨x, hx⟩).2 hgΩ hg2
  refine ⟨θ₀.trans (omegaRestrictEquiv.symm.trans ((autConj ⟨a, haA⟩).trans omegaRestrictEquiv)),
    (MulAut.conj (⟨a, haA⟩ : autT)).toMonoidHom.comp Θ₀, fun y l l' hl' => ?_, fun y => ?_,
    fun y => ?_, ?_⟩
  · simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MonoidHom.coe_comp,
      MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply, coe_mul, coe_inv]
    rw [OmegaEight.autConj_apply, OmegaEight.autConj_apply, ← h1 y l l' hl']
    group
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    rw [← h2 y]
    constructor
    · intro h
      have := congrArg (fun z => (⟨a, haA⟩ : autT)⁻¹ * z * ⟨a, haA⟩) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      group
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, coe_mul, coe_inv]
    rw [← OmegaEight.conj_mem_omegaT haA, h3]
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, coe_mul, coe_inv]
    exact mul_inv_gen9_mem ha

theorem rep_res0_of {g : Equiv.Perm (Fin 360)} (hg : g ∈ stab0) {t : Array ℕ}
    (h : CFSG.Monster.B.Co2.Rep 360 t g) :
    CFSG.Monster.B.Co2.Rep 120 (OmegaEight.copy0Arr t) (res0 ⟨g, hg⟩) := by
  intro j
  rw [OmegaEight.copy0Arr_getElem! _ j.2, OmegaEight.res0_apply_val]
  exact h ⟨j, by omega⟩

@[expose] noncomputable def sigP : Equiv.Perm (Fin 120) := sig .plus

theorem res0_gen9 : res0 ⟨gen 9, gen9_mem_stab0⟩ = sigP :=
  (rep_res0_of gen9_mem_stab0 (OmegaEight.rep_gen (by norm_num))).unique (rep_sig (ε := .plus)).1

theorem inv_mul_gen9_mem {y : Equiv.Perm (Fin 360)} (h : y * (gen 9)⁻¹ ∈ omegaT) :
    y⁻¹ * gen 9 ∈ omegaT := by
  have h9 : (gen 9)⁻¹ ∈ autT := inv_mem (OmegaEight.gen_mem_autT (by norm_num))
  have h1 := (OmegaEight.conj_mem_omegaT h9).1 (inv_mem h)
  have e : (gen 9)⁻¹ * (y * (gen 9)⁻¹)⁻¹ * (gen 9)⁻¹⁻¹ = y⁻¹ * gen 9 := by group
  rwa [e] at h1

theorem mem_stab0_of {y : Equiv.Perm (Fin 360)} (h : y * (gen 9)⁻¹ ∈ omegaT) : y ∈ stab0 := by
  have e : y = y * (gen 9)⁻¹ * gen 9 := by group
  rw [e]
  exact mul_mem (OmegaEight.omegaT_le_stab0 h) gen9_mem_stab0

theorem exists_rechoice_plus (hK : StepK t L) {θ : L ≃* omega1T}
    {Θ : centralizer ({t} : Set G) →* autT}
    (h1 : ∀ (y : centralizer ({t} : Set G)) (l l' : L), (l' : G) = y * l * (y : G)⁻¹ →
      (Θ y : Equiv.Perm (Fin 360)) * (omegaRestrictEquiv.symm (θ l) : Equiv.Perm (Fin 360)) *
        (Θ y : Equiv.Perm (Fin 360))⁻¹ = omegaRestrictEquiv.symm (θ l'))
    (h3 : ∀ y, (Θ y : Equiv.Perm (Fin 360)) ∈ omegaT ↔ (y : G) ∈ L ⊔ zpowers t) {x : G}
    (hx : x ∈ centralizer ({t} : Set G))
    (hxτ : (Θ ⟨x, hx⟩ : Equiv.Perm (Fin 360)) * (gen 9)⁻¹ ∈ omegaT) :
    ∃ m, ∃ hm : m ∈ L, x * m * (x * m) ∈ centralizer (L : Set G) ∧
      (Θ ⟨x * m, mul_mem hx (hK.le_centralizer hm)⟩ : Equiv.Perm (Fin 360)) * (gen 9)⁻¹ ∈
        omegaT ∧
      ∀ l l' : L, (l' : G) = x * m * l * (x * m)⁻¹ →
        sigP * (θ l : Equiv.Perm (Fin 120)) * sigP⁻¹ = θ l' := by
  have h9A : gen 9 ∈ autT := OmegaEight.gen_mem_autT (by norm_num)
  set y : Equiv.Perm (Fin 360) := (Θ ⟨x, hx⟩ : Equiv.Perm (Fin 360)) with hy
  have hys : y ∈ stab0 := mem_stab0_of hxτ
  set g : Equiv.Perm (Fin 120) := res0 ⟨y, hys⟩ with hgdef
  have hres : ∀ z : omegaT, res0 ⟨(z : Equiv.Perm (Fin 360)), OmegaEight.omegaT_le_stab0 z.2⟩ =
      (omegaRestrictEquiv z : Equiv.Perm (Fin 120)) := fun z => rfl
  have hg : ∀ l l' : L, (l' : G) = x * l * x⁻¹ →
      g * (θ l : Equiv.Perm (Fin 120)) * g⁻¹ = θ l' := by
    intro l l' hl'
    have h := h1 ⟨x, hx⟩ l l' hl'
    have e1 := hres (omegaRestrictEquiv.symm (θ l))
    have e2 := hres (omegaRestrictEquiv.symm (θ l'))
    rw [MulEquiv.apply_symm_apply] at e1 e2
    have e3 : (⟨y, hys⟩ : stab0) *
        ⟨_, OmegaEight.omegaT_le_stab0 (omegaRestrictEquiv.symm (θ l)).2⟩ * (⟨y, hys⟩ : stab0)⁻¹ =
        ⟨_, OmegaEight.omegaT_le_stab0 (omegaRestrictEquiv.symm (θ l')).2⟩ := Subtype.ext h
    rw [← e1, ← e2, ← e3, map_mul, map_mul, map_inv]
  have hgσ : g⁻¹ * sigP ∈ omega1T := by
    have h9 := inv_mul_gen9_mem hxτ
    have e : g⁻¹ * sigP = res0 ⟨y⁻¹ * gen 9, mul_mem (inv_mem hys) gen9_mem_stab0⟩ := by
      rw [← res0_gen9, hgdef, ← map_inv, ← map_mul]
      rfl
    rw [e, ← OmegaEight.omegaRes_range]
    exact ⟨⟨_, h9⟩, rfl⟩
  have hσ : sigP * sigP = 1 := sig_mul_self
  obtain ⟨m, hm, hsq, hact⟩ := exists_rechoice θ (hK.le_normalizer hx) hg hgσ hσ
  refine ⟨m, hm, hsq, ?_, hact⟩
  have hmΩ : (Θ ⟨m, hK.le_centralizer hm⟩ : Equiv.Perm (Fin 360)) ∈ omegaT :=
    (h3 _).2 (mem_sup_left hm)
  have e : (Θ ⟨x * m, mul_mem hx (hK.le_centralizer hm)⟩ : Equiv.Perm (Fin 360)) =
      y * Θ ⟨m, hK.le_centralizer hm⟩ := by
    rw [show (⟨x * m, mul_mem hx (hK.le_centralizer hm)⟩ : centralizer ({t} : Set G)) =
      ⟨x, hx⟩ * ⟨m, hK.le_centralizer hm⟩ from rfl, map_mul]
    rfl
  rw [e]
  have e' : y * (Θ ⟨m, hK.le_centralizer hm⟩ : Equiv.Perm (Fin 360)) * (gen 9)⁻¹ =
      y * (gen 9)⁻¹ * (gen 9 * Θ ⟨m, hK.le_centralizer hm⟩ * (gen 9)⁻¹) := by group
  rw [e']
  exact mul_mem hxτ ((OmegaEight.conj_mem_omegaT h9A).1 hmΩ)

theorem automizer_eq_of_mem_plus {θ : L ≃* omega1T} {Θ : centralizer ({t} : Set G) →* autT}
    (h1 : ∀ (y : centralizer ({t} : Set G)) (l l' : L), (l' : G) = y * l * (y : G)⁻¹ →
      (Θ y : Equiv.Perm (Fin 360)) * (omegaRestrictEquiv.symm (θ l) : Equiv.Perm (Fin 360)) *
        (Θ y : Equiv.Perm (Fin 360))⁻¹ = omegaRestrictEquiv.symm (θ l'))
    {y : centralizer ({t} : Set G)} (hyL : (y : G) ∈ L) :
    (Θ y : Equiv.Perm (Fin 360)) = omegaRestrictEquiv.symm (θ ⟨y, hyL⟩) := by
  set w : omegaT := omegaRestrictEquiv.symm (θ ⟨y, hyL⟩) with hw
  have hc : (w : Equiv.Perm (Fin 360))⁻¹ * Θ y ∈
      centralizer (omegaT : Set (Equiv.Perm (Fin 360))) := by
    rw [mem_centralizer_iff]
    intro g hg
    set l' : L := θ.symm (omegaRestrictEquiv ⟨g, hg⟩) with hl'
    have hgl : (omegaRestrictEquiv.symm (θ l') : Equiv.Perm (Fin 360)) = g := by
      rw [hl', MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    have h2 := h1 y l' (⟨y, hyL⟩ * l' * ⟨y, hyL⟩⁻¹) (by simp)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv] at h2
    simp only [coe_mul, coe_inv] at h2
    rw [hgl, ← hw] at h2
    calc g * ((w : Equiv.Perm (Fin 360))⁻¹ * Θ y) =
        (w : Equiv.Perm (Fin 360))⁻¹ * (w * g * (w : Equiv.Perm (Fin 360))⁻¹) * Θ y := by group
      _ = (w : Equiv.Perm (Fin 360))⁻¹ * ((Θ y : Equiv.Perm (Fin 360)) * g *
          (Θ y : Equiv.Perm (Fin 360))⁻¹) * Θ y := by rw [h2]
      _ = (w : Equiv.Perm (Fin 360))⁻¹ * Θ y * g := by group
  rw [OmegaEight.centralizer_omegaT, mem_bot] at hc
  have := congrArg (fun z => (w : Equiv.Perm (Fin 360)) * z) hc
  simpa using this

theorem exists_outerLink_plus (hK : StepK t L) (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hxN : x ∉ L ⊔ zpowers t) (hx2 : x * x ∈ zpowers t) :
    ∃ m ∈ L, ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      OuterLink .plus t L U Q P a ψ p u (x * m) := by
  obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT hL
  obtain ⟨θ, Θ, h1, h2, h3, hτ⟩ := exists_automizer_tau hK
    ((OmegaEight.mulEquivQuotientCenter hZ).symm.trans (e.trans omegaRestrictEquiv)) hx hxN hx2
  obtain ⟨m, hm, hsq, hmτ, hact₀⟩ := exists_rechoice_plus hK h1 h3 hx hτ
  let θ' : L ≃* Model.Lm .plus := θ
  have hact : ∀ l l' : L, (l' : G) = x * m * l * (x * m)⁻¹ →
      sig .plus * (θ' l : Equiv.Perm (Fin (Model.deg .plus))) * (sig .plus)⁻¹ = θ' l' := hact₀
  have hM := Model.modelLinkFacts .plus
  have hF := hM.transport θ'
  have hA := (Model.autCent .plus).transport hM.Q_le_L θ'
  have hxm : x * m ∈ centralizer ({t} : Set G) := mul_mem hx (hK.le_centralizer hm)
  have hxmL : x * m ∈ normalizer (L : Set G) := hK.le_normalizer hxm
  have h9A : gen 9 ∈ autT := OmegaEight.gen_mem_autT (by norm_num)
  refine ⟨m, hm, _, _, _, _, _, _, _, hF, hA, hxm, fun h => hxN ?_, hsq, fun v => ?_,
    fun y hy => ?_, fun h hh hhQ => ?_, ?_⟩
  · simpa using mul_mem h (mem_sup_left (inv_mem hm) : m⁻¹ ∈ L ⊔ zpowers t)
  · have e := sig_act (ε := .plus) v
    rw [conj_pullE hxmL hact (hM.ψ_mem_L v) (by rw [e]; exact hM.ψ_mem_L _)]
    exact pullE_congr e _ _
  · exact conj_mem_pull hxmL hact hM.U_le_L (fun z hz => sig_conj_mem_U hz) hy
  · set z : Equiv.Perm (Fin 360) := (Θ ⟨h, hh⟩ : Equiv.Perm (Fin 360)) with hz
    have hr : ∀ v, omegaRestrictEquiv.symm (θ ⟨pullE θ' (Model.psiM .plus v) (hM.ψ_mem_L v),
        pullE_mem_L _⟩) = ⟨Model.psiTMp v, Model.psiTMp_mem_omegaT v⟩ := by
      intro v
      have h5 : θ ⟨pullE θ' (Model.psiM .plus v) (hM.ψ_mem_L v), pullE_mem_L _⟩ =
          ⟨Model.psiMp v, Model.psiMp_mem v⟩ := theta_pullE (θ := θ') (hM.ψ_mem_L v)
      rw [h5, MulEquiv.symm_apply_eq]
      exact (Model.restrict_psiTMp v).symm
    have hconj : ∀ v, ∃ w, z⁻¹ * Model.psiTMp v * z = Model.psiTMp w := by
      intro v
      have hq : h⁻¹ * pullE θ' (Model.psiM .plus v) (hM.ψ_mem_L v) * h⁻¹⁻¹ ∈
          pull θ' (Model.QMm .plus) :=
        (mem_normalizer_iff.1 (inv_mem hhQ) _).1 ((pullE_mem_pull _).2 (Model.psiM_mem_Q v))
      obtain ⟨w, hw⟩ := hF.mem_ψ _ hq
      refine ⟨w, ?_⟩
      have h4 := h1 ⟨h, hh⟩⁻¹ ⟨_, pullE_mem_L (θ := θ') (hM.ψ_mem_L v)⟩
        ⟨_, pullE_mem_L (θ := θ') (hM.ψ_mem_L w)⟩ (by simp only [coe_inv]; exact hw)
      rw [hr, hr, map_inv] at h4
      simpa [hz] using h4
    rcases mem_or_of_lt (Θ ⟨h, hh⟩).2 (apply_zero_lt hconj) with hzΩ | hzτ
    · exact Or.inl ((h3 _).1 hzΩ)
    · right
      have hy : h * (x * m)⁻¹ ∈ centralizer ({t} : Set G) := mul_mem hh (inv_mem hxm)
      refine (h3 ⟨_, hy⟩).1 ?_
      have e : (Θ ⟨h * (x * m)⁻¹, hy⟩ : Equiv.Perm (Fin 360)) =
          z * (gen 9)⁻¹ * ((Θ ⟨x * m, hxm⟩ : Equiv.Perm (Fin 360)) * (gen 9)⁻¹)⁻¹ := by
        rw [show (⟨h * (x * m)⁻¹, hy⟩ : centralizer ({t} : Set G)) =
          ⟨h, hh⟩ * (⟨x * m, hxm⟩ : centralizer ({t} : Set G))⁻¹ from rfl, map_mul, map_inv]
        simp only [coe_mul, coe_inv, hz]
        group
      rw [e]
      exact mul_mem hzτ (inv_mem hmτ)
  · refine ⟨autT.subtype.comp Θ, fun y => ?_, fun y => ?_, fun v hv => ?_⟩
    · rw [Model.AT_plus]
      exact (Θ y).2
    · rw [← h2 y]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    · have e1 := automizer_eq_of_mem_plus h1 (y := ⟨_, hv⟩) (pullE_mem_L (θ := θ') (hM.ψ_mem_L v))
      have h5 : θ ⟨pullE θ' (Model.psiM .plus v) (hM.ψ_mem_L v), pullE_mem_L _⟩ =
          ⟨Model.psiMp v, Model.psiMp_mem v⟩ := theta_pullE (θ := θ') (hM.ψ_mem_L v)
      have h6 : omegaRestrictEquiv.symm ⟨Model.psiMp v, Model.psiMp_mem v⟩ =
          ⟨Model.psiTMp v, Model.psiTMp_mem_omegaT v⟩ := by
        rw [MulEquiv.symm_apply_eq]
        exact (Model.restrict_psiTMp v).symm
      change (Θ ⟨_, hv⟩ : Equiv.Perm (Fin 360)) = Model.psiTMp v
      rw [e1, h5, h6]

end Plus

section Minus

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

theorem automizer_eq_of_mem_minus {θ : L ≃* OmegaEightMinus.omegaT}
    {Θ : centralizer ({t} : Set G) →* OmegaEightMinus.autT}
    (h1 : ∀ (y : centralizer ({t} : Set G)) (l l' : L), (l' : G) = y * l * (y : G)⁻¹ →
      (Θ y : Equiv.Perm (Fin 136)) * (θ l : Equiv.Perm (Fin 136)) *
        (Θ y : Equiv.Perm (Fin 136))⁻¹ = θ l')
    {y : centralizer ({t} : Set G)} (hyL : (y : G) ∈ L) :
    (Θ y : Equiv.Perm (Fin 136)) = θ ⟨y, hyL⟩ := by
  set w : OmegaEightMinus.omegaT := θ ⟨y, hyL⟩ with hw
  have hc : (w : Equiv.Perm (Fin 136))⁻¹ * Θ y ∈
      centralizer (OmegaEightMinus.omegaT : Set (Equiv.Perm (Fin 136))) := by
    rw [mem_centralizer_iff]
    intro g hg
    set l' : L := θ.symm ⟨g, hg⟩ with hl'
    have hgl : (θ l' : Equiv.Perm (Fin 136)) = g := by rw [hl', MulEquiv.apply_symm_apply]
    have h2 := h1 y l' (⟨y, hyL⟩ * l' * ⟨y, hyL⟩⁻¹) (by simp)
    rw [map_mul, map_mul, map_inv] at h2
    simp only [coe_mul, coe_inv] at h2
    rw [hgl, ← hw] at h2
    calc g * ((w : Equiv.Perm (Fin 136))⁻¹ * Θ y) =
        (w : Equiv.Perm (Fin 136))⁻¹ * (w * g * (w : Equiv.Perm (Fin 136))⁻¹) * Θ y := by group
      _ = (w : Equiv.Perm (Fin 136))⁻¹ * ((Θ y : Equiv.Perm (Fin 136)) * g *
          (Θ y : Equiv.Perm (Fin 136))⁻¹) * Θ y := by rw [h2]
      _ = (w : Equiv.Perm (Fin 136))⁻¹ * Θ y * g := by group
  rw [OmegaEightMinus.centralizer_omegaT, mem_bot] at hc
  have := congrArg (fun z => (w : Equiv.Perm (Fin 136)) * z) hc
  simpa using this

theorem exists_outerLink_minus (hK : StepK t L)
    (hL : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hxN : x ∉ L ⊔ zpowers t) :
    ∃ m ∈ L, ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      OuterLink .minus t L U Q P a ψ p u (x * m) := by
  obtain ⟨θ⟩ := OmegaEightMinus.nonempty_mulEquiv_omegaT hL
  obtain ⟨Θ, h1, h2, h3⟩ := exists_model_automizer_minus hK θ
  have hgA : (Θ ⟨x, hx⟩ : Equiv.Perm (Fin 136)) ∈ OmegaEightMinus.autT := (Θ ⟨x, hx⟩).2
  have hgΩ : (Θ ⟨x, hx⟩ : Equiv.Perm (Fin 136)) ∉ OmegaEightMinus.omegaT := fun h =>
    hxN ((h3 _).1 h)
  let θ' : L ≃* Model.Lm .minus := θ
  let g : Equiv.Perm (Fin (Model.deg .minus)) := (Θ ⟨x, hx⟩ : Equiv.Perm (Fin 136))
  have hgσ : g⁻¹ * sig .minus ∈ Model.Lm .minus := by
    rw [sig_minus_eq]
    exact inv_mul_gen10_mem hgA hgΩ
  obtain ⟨m, hm, hsq, hact⟩ := exists_rechoice θ' (hK.le_normalizer hx)
    (fun l l' hl' => h1 ⟨x, hx⟩ l l' hl') hgσ sig_mul_self
  have hM := Model.modelLinkFacts .minus
  have hF := hM.transport θ'
  have hA := (Model.autCent .minus).transport hM.Q_le_L θ'
  have hxm : x * m ∈ centralizer ({t} : Set G) := mul_mem hx (hK.le_centralizer hm)
  have hxmL : x * m ∈ normalizer (L : Set G) := hK.le_normalizer hxm
  have hxmN : x * m ∉ L ⊔ zpowers t := fun h => hxN (by
    simpa using mul_mem h (mem_sup_left (inv_mem hm) : m⁻¹ ∈ L ⊔ zpowers t))
  set r : Equiv.Perm (Fin 136) := OmegaEightMinus.gen 10 with hr
  have h10 : r ∈ OmegaEightMinus.autT := OmegaEightMinus.gen_mem_autT (by norm_num)
  refine ⟨m, hm, _, _, _, _, _, _, _, hF, hA, hxm, hxmN, hsq, fun v => ?_,
    fun y hy => ?_, fun h hh _ => ?_, ?_⟩
  · have e := sig_act (ε := .minus) v
    rw [conj_pullE hxmL hact (hM.ψ_mem_L v) (by rw [e]; exact hM.ψ_mem_L _)]
    exact pullE_congr e _ _
  · exact conj_mem_pull hxmL hact hM.U_le_L (fun z hz => sig_conj_mem_U hz) hy
  · by_cases hhN : h ∈ L ⊔ zpowers t
    · exact Or.inl hhN
    · right
      have hy : h * (x * m)⁻¹ ∈ centralizer ({t} : Set G) := mul_mem hh (inv_mem hxm)
      have ha := inv_mul_gen10_mem (Θ ⟨h, hh⟩).2 (fun h' => hhN ((h3 _).1 h'))
      have hb := inv_mul_gen10_mem (Θ ⟨x * m, hxm⟩).2 (fun h' => hxmN ((h3 _).1 h'))
      refine (h3 ⟨_, hy⟩).1 ?_
      have e : (Θ ⟨h * (x * m)⁻¹, hy⟩ : Equiv.Perm (Fin 136)) =
          r * ((((Θ ⟨h, hh⟩ : Equiv.Perm (Fin 136))⁻¹ * r)⁻¹ *
            ((Θ ⟨x * m, hxm⟩ : Equiv.Perm (Fin 136))⁻¹ * r))) * r⁻¹ := by
        rw [show (⟨h * (x * m)⁻¹, hy⟩ : centralizer ({t} : Set G)) =
          ⟨h, hh⟩ * (⟨x * m, hxm⟩ : centralizer ({t} : Set G))⁻¹ from rfl, map_mul, map_inv]
        simp only [coe_mul, coe_inv]
        group
      rw [e]
      exact (OmegaEightMinus.conj_mem_omegaT h10).1 (mul_mem (inv_mem ha) hb)
  · refine ⟨OmegaEightMinus.autT.subtype.comp Θ, fun y => ?_, fun y => ?_, fun v hv => ?_⟩
    · rw [Model.AT_minus]
      exact (Θ y).2
    · rw [← h2 y]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    · have e1 := automizer_eq_of_mem_minus h1 (y := ⟨_, hv⟩)
        (pullE_mem_L (θ := θ') (hM.ψ_mem_L v))
      have h5 : θ ⟨pullE θ' (Model.psiM .minus v) (hM.ψ_mem_L v), pullE_mem_L _⟩ =
          ⟨Model.psiMm v, hM.ψ_mem_L v⟩ := theta_pullE (θ := θ') (hM.ψ_mem_L v)
      change (Θ ⟨_, hv⟩ : Equiv.Perm (Fin 136)) = Model.psiTMm v
      rw [e1, h5, Model.psiTMm_eq]

end Minus

end CFSG.EvenSmallLie.OmegaEight.SplitIn
