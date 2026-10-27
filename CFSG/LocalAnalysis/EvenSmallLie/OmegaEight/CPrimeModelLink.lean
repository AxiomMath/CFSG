module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelPlus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelMinus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Model

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.OmegaEight.Stage0
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)

variable {G : Type} [Group G]

theorem link_act {ε : Eps} {L : Subgroup G} (θ : L ≃* Lm ε) {c : G}
    (hcL : c ∈ normalizer (L : Set G))
    (hact : ∀ l l' : L, (l' : G) = c * l * c⁻¹ →
      sig ε * (θ l : Equiv.Perm (Fin (deg ε))) * (sig ε)⁻¹ = θ l') :
    (∀ v, c * pullE θ (psiM ε v) ((Model.modelLinkFacts ε).ψ_mem_L v) * c⁻¹ =
      pullE θ (psiM ε (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v))
        ((Model.modelLinkFacts ε).ψ_mem_L _)) ∧
    ∀ u ∈ pull θ (UQm ε), c * u * c⁻¹ ∈ pull θ (UQm ε) := by
  have hF := Model.modelLinkFacts ε
  refine ⟨fun v => ?_, fun u hu => ?_⟩
  · have hl : pullE θ (psiM ε v) (hF.ψ_mem_L v) ∈ L := pullE_mem_L _
    have hl' := (mem_normalizer_iff.1 hcL _).1 hl
    have h := hact ⟨_, hl⟩ ⟨_, hl'⟩ rfl
    rw [theta_pullE, Subtype.coe_mk, sig_act] at h
    exact eq_pullE_of_theta hl' _ h.symm
  · obtain ⟨huL, huU⟩ := mem_pull.1 hu
    have hl' := (mem_normalizer_iff.1 hcL u).1 huL
    have h := hact ⟨u, huL⟩ ⟨_, hl'⟩ rfl
    exact mem_pull.2 ⟨hl', h ▸ sig_conj_mem_U huU⟩

theorem symm_psiM_plus (v : V6) :
    ((OmegaEight.omegaRestrictEquiv.symm ⟨psiMp v, psiMp_mem v⟩ : OmegaEight.omegaT) :
      Equiv.Perm (Fin 360)) = psiTMp v := by
  have h : OmegaEight.omegaRestrictEquiv.symm ⟨psiMp v, psiMp_mem v⟩ =
      ⟨psiTMp v, psiTMp_mem_omegaT v⟩ := by
    rw [MulEquiv.symm_apply_eq, restrict_psiTMp]
  rw [h]

theorem normalizes_of_mem_normalizer_plus {t : G} {L : Subgroup G} (θ : L ≃* OmegaEight.omega1T)
    (Θ : centralizer ({t} : Set G) →* OmegaEight.autT)
    (hΘ : ∀ (x : centralizer ({t} : Set G)) (l l' : L), (l' : G) = x * l * (x : G)⁻¹ →
      (Θ x : Equiv.Perm (Fin 360)) *
          (OmegaEight.omegaRestrictEquiv.symm (θ l) : Equiv.Perm (Fin 360)) *
          (Θ x : Equiv.Perm (Fin 360))⁻¹ = OmegaEight.omegaRestrictEquiv.symm (θ l'))
    (x : centralizer ({t} : Set G))
    (hxQ : (x : G) ∈ normalizer (pull θ (QMm .plus) : Set G)) :
    ∀ v, ∃ w, (Θ x : Equiv.Perm (Fin 360)) * psiTMp v * (Θ x : Equiv.Perm (Fin 360))⁻¹ =
      psiTMp w := by
  intro v
  have hF := Model.modelLinkFacts .plus
  have hlQ : pullE θ (psiM .plus v) (hF.ψ_mem_L v) ∈ pull θ (QMm .plus) :=
    (pullE_mem_pull _).2 (psiM_mem_Q v)
  have hl : pullE θ (psiM .plus v) (hF.ψ_mem_L v) ∈ L := pullE_mem_L _
  have hl'Q := (mem_normalizer_iff.1 hxQ _).1 hlQ
  obtain ⟨hl'L, hl'⟩ := mem_pull.1 hl'Q
  obtain ⟨w, hw⟩ := mem_QMm.1 hl'
  refine ⟨w, ?_⟩
  have h := hΘ x ⟨_, hl⟩ ⟨_, hl'L⟩ rfl
  have e1 : θ ⟨_, hl⟩ = ⟨psiMp v, psiMp_mem v⟩ := theta_pullE _
  have e2 : θ ⟨_, hl'L⟩ = ⟨psiMp w, psiMp_mem w⟩ := Subtype.ext hw.symm
  rw [e1, e2, symm_psiM_plus, symm_psiM_plus] at h
  exact h

theorem automizer_sq {t : G} {L : Subgroup G} (Θ : centralizer ({t} : Set G) →* OmegaEight.autT)
    (hinn : ∀ x, (Θ x : Equiv.Perm (Fin 360)) ∈ OmegaEight.omegaT ↔ (x : G) ∈ L ⊔ zpowers t)
    (x : centralizer ({t} : Set G))
    (hx : (Θ x : Equiv.Perm (Fin 360)) * (Θ x : Equiv.Perm (Fin 360)) ∈ OmegaEight.omegaT) :
    (x : G) * x ∈ L ⊔ zpowers t := by
  have h := (hinn (x * x)).1 (by rw [map_mul]; exact hx)
  exact h

theorem sq_mem_of_normalizer_plus {t : G} {L : Subgroup G} (hK : StepK t L)
    (θ : L ≃* OmegaEight.omega1T) {x : G} (hx : x ∈ centralizer ({t} : Set G))
    (hxQ : x ∈ normalizer (pull θ (QMm .plus) : Set G)) : x * x ∈ L ⊔ zpowers t := by
  obtain ⟨Θ, hΘ, -, hinn⟩ := exists_model_automizer_plus hK θ
  have hn := normalizes_of_mem_normalizer_plus θ Θ hΘ ⟨x, hx⟩ hxQ
  refine automizer_sq Θ hinn ⟨x, hx⟩ ?_
  rcases mem_of_normalizes_plus (Θ ⟨x, hx⟩).2 hn with h | h
  · exact mul_mem h h
  · rw [sq_mem_iff (OmegaEight.gen_mem_autT (by norm_num)) h, gen9_mul_self]
    exact one_mem _

theorem mem_of_normalizer_of_pow_three_plus {t : G} {L : Subgroup G} (hK : StepK t L)
    (θ : L ≃* OmegaEight.omega1T) {x : G} (hx : x ∈ centralizer ({t} : Set G))
    (hxQ : x ∈ normalizer (pull θ (QMm .plus) : Set G)) (hx3 : x ^ 3 ∈ L ⊔ zpowers t) :
    x ∈ L ⊔ zpowers t := by
  obtain ⟨Θ, hΘ, -, hinn⟩ := exists_model_automizer_plus hK θ
  have hn := normalizes_of_mem_normalizer_plus θ Θ hΘ ⟨x, hx⟩ hxQ
  by_contra hxN
  refine not_normalizes_of_pow_three (Θ ⟨x, hx⟩).2 (fun h => hxN ((hinn _).1 h)) ?_ hn
  have h3 := (hinn (⟨x, hx⟩ ^ 3)).2 hx3
  rwa [map_pow] at h3

@[expose] noncomputable def sigPlus : Equiv.Perm (Fin 120) := sig .plus

@[expose] noncomputable def sigMinus : Equiv.Perm (Fin 136) := sig .minus

theorem restrict_conj {s : Equiv.Perm (Fin 360)} (hs : s ∈ OmegaEight.stab0)
    {y y' : OmegaEight.omegaT} (h : (y' : Equiv.Perm (Fin 360)) = s * y * s⁻¹) :
    (OmegaEight.omegaRestrictEquiv y' : Equiv.Perm (Fin 120)) =
      OmegaEight.res0 ⟨s, hs⟩ * OmegaEight.omegaRestrictEquiv y *
        (OmegaEight.res0 ⟨s, hs⟩)⁻¹ := by
  rw [OmegaEight.omegaRestrictEquiv_apply, OmegaEight.omegaRestrictEquiv_apply,
    OmegaEight.omegaRes, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
    ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_inclusion, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_inclusion,
    Subtype.coe_mk, h]

theorem exists_rechoice_plus {t : G} {L : Subgroup G} (hK : StepK t L)
    (θ₀ : L ≃* OmegaEight.omega1T) {c : G} (hc : c ∈ centralizer ({t} : Set G))
    (hcN : c ∉ L ⊔ zpowers t) (hc2 : c * c ∈ zpowers t) :
    ∃ θ : L ≃* OmegaEight.omega1T, ∃ m ∈ L, c * m * (c * m) ∈ centralizer (L : Set G) ∧
      ∀ l l' : L, (l' : G) = c * m * l * (c * m)⁻¹ →
        sigPlus * (θ l : Equiv.Perm (Fin 120)) * sigPlus⁻¹ = θ l' := by
  obtain ⟨Θ, hΘ, hker, hinn⟩ := exists_model_automizer_plus hK θ₀
  set x : centralizer ({t} : Set G) := ⟨c, hc⟩ with hxdef
  have hg₀A : (Θ x : Equiv.Perm (Fin 360)) ∈ OmegaEight.autT := (Θ x).2
  have hg₀Ω : (Θ x : Equiv.Perm (Fin 360)) ∉ OmegaEight.omegaT := fun h => hcN ((hinn x).1 h)
  have hg₀2 : (Θ x : Equiv.Perm (Fin 360)) * (Θ x : Equiv.Perm (Fin 360)) = 1 := by
    have h1 : Θ (x * x) = 1 := (hker (x * x)).2 hc2
    rw [map_mul] at h1
    exact congrArg Subtype.val h1
  obtain ⟨a, haA, ha⟩ := exists_conj_outer_plus hg₀A hg₀Ω hg₀2
  set θ' : L ≃* OmegaEight.omegaT :=
    θ₀.trans (OmegaEight.omegaRestrictEquiv.symm.trans (OmegaEight.autEquiv ⟨a, haA⟩)) with hθ'
  have hθ'a : ∀ l, (θ' l : Equiv.Perm (Fin 360)) =
      a * (OmegaEight.omegaRestrictEquiv.symm (θ₀ l) : Equiv.Perm (Fin 360)) * a⁻¹ := by
    intro l
    rw [hθ', MulEquiv.trans_apply, MulEquiv.trans_apply, OmegaEight.autEquiv_apply]
  have hg : ∀ l l' : L, (l' : G) = c * l * c⁻¹ →
      a * (Θ x : Equiv.Perm (Fin 360)) * a⁻¹ * (θ' l : Equiv.Perm (Fin 360)) *
        (a * (Θ x : Equiv.Perm (Fin 360)) * a⁻¹)⁻¹ = θ' l' := by
    intro l l' hl'
    have h1 := hΘ x l l' hl'
    rw [hθ'a, hθ'a, ← h1]
    group
  obtain ⟨m, hm, hsq, hact⟩ := exists_rechoice θ' (hK.le_normalizer hc) hg ha gen9_mul_self
  refine ⟨θ'.trans OmegaEight.omegaRestrictEquiv, m, hm, hsq, fun l l' hl' => ?_⟩
  have key := restrict_conj gen9_mem_stab0 (hact l l' hl').symm
  rw [← sig_plus_eq] at key
  exact key.symm

theorem exists_rechoice_minus {t : G} {L : Subgroup G} (hK : StepK t L)
    (θ : L ≃* OmegaEightMinus.omegaT) {c : G} (hc : c ∈ centralizer ({t} : Set G))
    (hcN : c ∉ L ⊔ zpowers t) :
    ∃ m ∈ L, c * m * (c * m) ∈ centralizer (L : Set G) ∧
      ∀ l l' : L, (l' : G) = c * m * l * (c * m)⁻¹ →
        sigMinus * (θ l : Equiv.Perm (Fin 136)) * sigMinus⁻¹ = θ l' := by
  obtain ⟨Θ, hΘ, -, hinn⟩ := exists_model_automizer_minus hK θ
  set x : centralizer ({t} : Set G) := ⟨c, hc⟩ with hxdef
  have hg₀Ω : (Θ x : Equiv.Perm (Fin 136)) ∉ OmegaEightMinus.omegaT := fun h => hcN ((hinn x).1 h)
  obtain ⟨m, hm, hsq, hact⟩ := exists_rechoice θ (hK.le_normalizer hc) (hΘ x)
    (inv_mul_gen10_mem (Θ x).2 hg₀Ω) gen10_mul_self
  refine ⟨m, hm, hsq, fun l l' hl' => ?_⟩
  have key := hact l l' hl'
  rw [← sig_minus_eq] at key
  exact key

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
