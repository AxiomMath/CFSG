module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL8Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshCentralizerStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshOddCoprime
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylowHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylowType

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

structure Lemma8Out (G : Type) [Group G] (c : G) : Prop where
  out : CentralizerQuotientOut G c
  sylowType : ∃ (S₁ : Sylow 2 (↥(centralizer ({c} : Set G)) ⧸ center ↥(centralizer ({c} : Set G))))
    (S₂ : Sylow 2 (alternatingGroup (Fin 12))),
    Nonempty (↥(S₁ : Subgroup (↥(centralizer ({c} : Set G)) ⧸
      center ↥(centralizer ({c} : Set G)))) ≃* ↥(S₂ : Subgroup (alternatingGroup (Fin 12))))

section Lemma8

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

@[expose] noncomputable def imgEquiv (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))}
    (hK : K ≤ NG α k) : ↥K ≃* ↥(img E K) :=
  (Subgroup.subgroupOfEquivOfLe hK).symm.trans (Subgroup.equivMapOfInjective _ E.Ψ E.inj)

theorem coe_imgEquiv (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))}
    (hK : K ≤ NG α k) (g : ↥K) :
    ((imgEquiv E hK g : ↥(img E K)) : G) = ψ E (g : Equiv.Perm (Fin 16)) := by
  rw [ψ_of_mem E (hK g.2)]
  rfl

theorem tsubOK_sWords (hue : ueCheck α k = true) : tsubOK (wgens α k sWords) 1024 = true := by
  unfold ueCheck ueCheckG at hue
  simp only [Bool.and_eq_true] at hue
  exact hue.1.2

theorem sylowType_of_model [Finite G] (D : FusionData 1 k) (E : NEmb e₀ d 1 k) (F : ESFacts E)
    (hue : ueCheck 1 k = true)
    (hsyl : sylowHomCheck (wgens 1 k sWords) (nwT 1 k cWord) (sylowHomData k) = true)
    (hsyl2 : Nat.card (SG E) = 2 ^ (Nat.card (centralizer ({cG e₀} : Set G))).factorization 2)
    (hZ : ∀ z ∈ center ↥(centralizer ({cG e₀} : Set G)), (z : G) = 1 ∨ (z : G) = cG e₀) :
    ∃ (S₁ : Sylow 2 (↥(centralizer ({cG e₀} : Set G)) ⧸ center ↥(centralizer ({cG e₀} : Set G))))
      (S₂ : Sylow 2 (alternatingGroup (Fin 12))),
      Nonempty (↥(S₁ : Subgroup (↥(centralizer ({cG e₀} : Set G)) ⧸
        center ↥(centralizer ({cG e₀} : Set G)))) ≃*
          ↥(S₂ : Subgroup (alternatingGroup (Fin 12)))) := by
  have hSLe : tsub (wgens 1 k sWords) ≤ NG 1 k := by
    obtain ⟨-, hSs⟩ := ueCheck_enum hue
    exact tsub_wgens_le D hSs.perm
  obtain ⟨P, f₀, hP, hf₀, hker₀⟩ :=
    sylow_hom_model (rep_nwT D cWord) (tsubOK_sWords hue) hsyl
  let iso : ↥(SG E) ≃* ↥(tsub (wgens 1 k sWords)) := (imgEquiv E hSLe).symm
  let f : ↥(SG E) →* ↥P := f₀.comp iso.toMonoidHom
  refine sylowType_of_hom (cG e₀) (SG E) P f (cG_sq e₀) (cG_ne_one e₀) (F.ES F.cE) F.cSZ hZ
    hsyl2 hP (hf₀.comp iso.surjective) fun s => ?_
  have hcoe : ((s : ↥(SG E)) : G) = ψ E ((iso s : ↥(tsub (wgens 1 k sWords))) :
      Equiv.Perm (Fin 16)) := by
    have h1 := coe_imgEquiv E hSLe (iso s)
    rw [show imgEquiv E hSLe (iso s) = s from (imgEquiv E hSLe).apply_symm_apply s] at h1
    exact h1
  have hg : ((iso s : ↥(tsub (wgens 1 k sWords))) : Equiv.Perm (Fin 16)) ∈ NG 1 k :=
    hSLe (iso s).2
  show f₀ (iso s) = 1 ↔ _
  rw [hker₀ (iso s), hcoe]
  constructor
  · rintro (h | h)
    · left
      rw [h, ψ_one]
    · right
      rw [h, ψ_c]
  · rintro (h | h)
    · left
      exact ψ_inj E hg (NG 1 k).one_mem (h.trans (ψ_one E).symm)
    · right
      exact ψ_inj E hg (wp_mem 1 k _) (h.trans (ψ_c E).symm)

theorem yosh8_model [Finite G] (hG : IsSimpleGroup G) (D : FusionData 1 k) (E : NEmb e₀ d 1 k)
    (he2 : orderOf e = 2) (hd : CentralSwap e₀ 1 d) (hue : ueCheck 1 k = true)
    (hes : esCheck 1 k = true) (hl7 : l7Check 1 k = true) (hl8 : l8Check 1 k = true)
    (hsyl : sylowHomCheck (wgens 1 k sWords) (nwT 1 k cWord) (sylowHomData k) = true) :
    Lemma8Out G (cG e₀) := by
  have L7 := yosh7_model hG D E he2 hd hue hes hl7
  have F := esFacts D E hue hes
  obtain ⟨-, -, hA, -, hbad⟩ := l7Check_parts hl7
  have Ay := l7A_spec D E he2 hue hbad hA
  obtain ⟨hl8f, hl8z, hl8c⟩ := l8Check_parts hl8
  have Ch := l8Chain_spec D E hue hl8c
  have hZN := l8ZN_spec D E hue hl8z
  have hfact := l8Fact_spec D E he2 hl8f
  have hee : e * e = 1 := mul_self_eq_one_of_orderOf_eq_two he2
  have hcc : cG e₀ * cG e₀ = 1 := cG_sq e₀
  have hc1 : cG e₀ ≠ 1 := cG_ne_one e₀
  have hec : e * cG e₀ = cG e₀ * e := (cG_comm_e e₀).symm
  have hLc : ∀ ℓ ∈ normalizer (EG E : Set G), ℓ * cG e₀ = cG e₀ * ℓ := fun ℓ hℓ => by
    have h := L7.fixes_c ℓ hℓ
    calc ℓ * cG e₀ = (ℓ * cG e₀ * ℓ⁻¹) * ℓ := by group
      _ = cG e₀ * ℓ := by rw [h]
  have hSL : SG E ≤ normalizer (EG E : Set G) := fun s hs =>
    mem_normalizer_of_conj_mem _ s (F.SN s hs)
  have hNL : Nn e₀ ≤ normalizer (EG E : Set G) := fun n hn =>
    mem_normalizer_of_conj_mem _ n (F.EN n hn)
  have hSle : SG E ≤ centralizer ({cG e₀} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (F.cSZ s hs)
  have hLS : ∀ p : G, p * cG e₀ = cG e₀ * p → (∀ s ∈ SG E, p * s * p⁻¹ ∈ SG E) →
      p ∈ normalizer (EG E : Set G) := by
    intro p hp hpS
    have h := mem_normalizer_of_unique (S := SG E) (b := p⁻¹) ⟨F.sq, F.comm⟩
      (by rw [inv_inv]; exact hp)
      (fun u hu => by rw [inv_inv]; exact hpS u (F.ES hu))
      (fun D' hDS hDcard hDsq hDcomm => F.uniq D' hDS (hDcard.trans F.cardE) hDsq hDcomm)
    simpa using (normalizer (EG E : Set G)).inv_mem h
  have hO : ∀ Q : Subgroup G, (∀ q ∈ Q, q * cG e₀ = cG e₀ * q) →
      (∀ g : G, g * cG e₀ = cG e₀ * g → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) → Odd (Nat.card Q) →
        Q = ⊥ := by
    intro Q hQc hQn hodd
    obtain ⟨ℓu, hℓu, hu⟩ := L7.fuse_u
    obtain ⟨ℓue, hℓue, hue'⟩ := L7.fuse_ue
    have hcomm : Commute (uG E) (cG e₀) := by
      rw [← hu]
      exact ((show Commute ℓu (cG e₀) from hLc ℓu hℓu).mul_left
        (show Commute e (cG e₀) from hec)).mul_left
        (show Commute ℓu (cG e₀) from hLc ℓu hℓu).inv_left
    exact odd_normal_eq_bot_of_fourGroup (cG e₀) e (uG E) Q hec hcomm hee L7.sq_u
      L7.fusion.euComm (card_HcG e₀) hfact hQn hQc hodd ⟨ℓu, hLc ℓu hℓu, hu⟩
      ⟨ℓue, hLc ℓue hℓue, hue'⟩
  have hy0N : y0G e₀ d 1 ∈ Nn e₀ := by
    have h : ψ E (wp 1 k (jIn 1 (swN [7, 8]))) = y0G e₀ d 1 := ψ_wp E _
    rw [← h]
    exact ψ_mem_Nn E (wp_mem 1 k _)
  have hv2 : v2G E ∈ EG E := by
    refine Ay.le ?_
    rw [Ay.eq]
    exact Subgroup.subset_closure (by simp)
  haveI : ((EG E).subgroupOf (normalizer (EG E : Set G))).Normal := Subgroup.normal_in_normalizer
  have out : CentralizerQuotientOut G (cG e₀) :=
    centralizer_quotient_out (cG e₀) (normalizer (EG E : Set G)) (SG E) (EG E) (Nn e₀)
      (y0G e₀ d 1) (hElt E) hcc hc1 L7.sylow hSL hLc L7.perf hLS hO F.cE F.sq rfl
      (by rw [F.cardE]; norm_num) L7.card L7.gl L7.zl hNL hy0N hZN Ch.comm_c Ch.y0
      ⟨v2G E, hv2, Ch.v2⟩
  exact ⟨out, sylowType_of_model D E F hue hsyl (card_eq_two_pow_of_le _ _ hSle L7.sylow)
    out.center_le⟩

end Lemma8

end CFSG.EvenSporadicStandard.M12Std.Yosh
