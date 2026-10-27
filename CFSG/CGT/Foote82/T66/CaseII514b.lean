module

public import CFSG.CGT.Foote82.T66.CaseII514a
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.ClassicalInvolution.Orders.Classical
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.Foote82.T66.CaseII513End

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

theorem nontrivial_of_isQuasisimple' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

theorem ordBC_two_three : ordBC 2 (3 ^ 1) = 25920 := by
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem eq_component (hHE : HH G L v ≤ layerIn G) (h2E : ¬ 2 ^ 7 ∣ Nat.card ↥(layerIn G)) :
    ∃ K : Subgroup (GLV V), IsComponentOf K G ∧ layerIn G = K := by
  have hne : ∃ K : Subgroup (GLV V), IsComponentOf K G := by
    by_contra hno
    push Not at hno
    have hbot : layerIn G = ⊥ := by
      rw [layerIn_eq_sSup]
      exact sSup_eq_bot.2 fun K hK => absurd hK (hno K)
    have hH : HH G L v = ⊥ := le_bot_iff.1 (hbot ▸ hHE)
    have h1 := c.card_H
    rw [hH, Subgroup.card_bot] at h1
    norm_num at h1
  obtain ⟨K, hK⟩ := hne
  have hKE : K ≤ layerIn G := le_layerIn_of_isComponentOf hK
  have hHN : HH G L v ≤ Subgroup.normalizer (K : Set (GLV V)) := fun h hh =>
    Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => conj_mem_of_isComponentOf hK (hHE hh) hk,
      fun hk => by
        have := conj_mem_of_isComponentOf hK ((layerIn G).inv_mem (hHE hh)) hk
        simpa [mul_assoc] using this⟩
  have hHK : HH G L v ≤ K := by
    have hsimp := c.isSimpleGroup_H
    have hn : ((HH G L v ⊓ K).subgroupOf (HH G L v)).Normal := ⟨fun x hx h => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨(HH G L v).mul_mem ((HH G L v).mul_mem h.2 hx.1) ((HH G L v).inv_mem h.2),
        conj_mem_of_isComponentOf hK (hHE h.2) hx.2⟩⟩
    haveI := hsimp
    haveI := hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((HH G L v ⊓ K).subgroupOf (HH G L v)) with
      h | h
    · exfalso
      have hinf : HH G L v ⊓ K = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx.1⟩ : ↥(HH G L v)) ∈ (HH G L v ⊓ K).subgroupOf (HH G L v) :=
          Subgroup.mem_subgroupOf.2 hx
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      have h1 := card_sup_mul_card_inf hHN
      rw [hinf, Subgroup.card_bot, mul_one] at h1
      have hdvd : Nat.card ↥(HH G L v) * Nat.card ↥K ∣ Nat.card ↥(layerIn G) := by
        rw [← h1]
        exact Subgroup.card_dvd_of_le (sup_le hHE hKE)
      rw [c.card_H] at hdvd
      have hKodd : Odd (Nat.card ↥K) := by
        rw [Nat.odd_iff]
        by_contra h2
        have h2' : 2 ∣ Nat.card ↥K := by omega
        apply h2E
        exact (Nat.mul_dvd_mul (show 2 ^ 6 ∣ 25920 by norm_num) h2').trans hdvd
      have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
      have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
      haveI : Nontrivial ↥K := nontrivial_of_isQuasisimple' hq
      haveI : Group.IsPerfect ↥K := Group.isPerfect_def.2 hq.1
      exact Group.IsPerfect.not_isSolvable ↥K hsolv
    · intro x hx
      have : (⟨x, hx⟩ : ↥(HH G L v)) ∈ (HH G L v ⊓ K).subgroupOf (HH G L v) :=
        h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).2
  refine ⟨K, hK, le_antisymm ?_ hKE⟩
  rw [← c.std.extremal.setup.normalClosure_layerIn]
  show Subgroup.closure _ ≤ K
  rw [Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact conj_mem_of_isComponentOf hK hγ (hHK (c.L_le_H hl))

theorem false_of_alt_nine (hHE : HH G L v ≤ layerIn G)
    (e : ↥(layerIn G) ≃* alternatingGroup (Fin 9)) : False := by
  have hcard : Nat.card ↥(layerIn G) = 181440 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hsimp : IsSimpleGroup ↥(layerIn G) := by
    have := alternatingGroup.isSimpleGroup (α := Fin 9) (by simp)
    exact e.isSimpleGroup
  set H' := (HH G L v).subgroupOf (layerIn G) with hH'
  have hH'c : Nat.card ↥H' = 25920 := by
    rw [hH', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHE).toEquiv, c.card_H]
  have hidx : H'.index = 7 := by
    have h := H'.card_mul_index
    rw [hH'c, hcard] at h
    omega
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index H'
  rw [hidx] at hdvd
  haveI := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H'.normalCore with h | h
  · rw [h, Subgroup.index_bot, hcard] at hdvd
    exact absurd hdvd (by decide)
  · have h1 : H' = ⊤ := top_le_iff.1 (h ▸ Subgroup.normalCore_le H')
    rw [h1, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

theorem prop514 (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1) (hG2 : CaseIIG2)
    (h511b : CaseIILemma511b) (h513 : ∀ x ∈ G, x * z * x⁻¹ ∉ HH G L v) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, d⟩ := c.exists_gd hG1
  obtain ⟨T, hTH₁, hT2, hTc, hzT, huT⟩ := d.exists_T
  have hmaxT := c.sylow_T hs haut hG1 h513 d hTH₁ hT2 hTc hzT huT
  have hTc' : Nat.card ↥T = 2 ^ 7 := by rw [hTc, c.card_H₁, factorization_51840]
  have hTG : T ≤ G := hTH₁.trans c.H₁_le_G
  have hzE := c.z_not_mem_layerIn h513 hTH₁ hT2 hzT hmaxT
  have hGc := c.card_G_eq hzE
  have h2E : ¬ 2 ^ 7 ∣ Nat.card ↥(layerIn G) := by
    intro h7
    have h8 : 2 ^ (7 + 1) ∣ Nat.card ↥G := by
      rw [hGc, pow_succ, mul_comm]
      exact Nat.mul_dvd_mul_left 2 h7
    obtain ⟨K, hK, -⟩ := Sylow.exists_subgroup_card_pow_succ h8 (H := T.subgroupOf G)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv, hTc'])
    have h1 := hmaxT (K.map G.subtype) (Subgroup.map_subtype_le _)
      (IsPGroup.of_card (n := 7 + 1)
        (by rw [Subgroup.card_map_of_injective G.subtype_injective, hK]))
    rw [Subgroup.card_map_of_injective G.subtype_injective, hK, hTc'] at h1
    norm_num at h1
  have hHE : HH G L v ≤ layerIn G :=
    c.std.extremal.setup.le_layerIn_of_perfect c.H_le_G c.H_perfect
  obtain ⟨K, hK, hEK⟩ := c.eq_component hHE h2E
  have hEq : CFSG.IsQuasisimple ↥(layerIn G) := by
    rw [hEK]
    exact isQuasisimple_of_open' hK.2.2
  have hmaxE : ∀ Y : Subgroup (GLV V), Y ≤ layerIn G → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ 2 ^ 6 := by
    intro Y hYE hY2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY2
    have hdvd : 2 ^ k ∣ Nat.card ↥(layerIn G) := hk ▸ Subgroup.card_dvd_of_le hYE
    rw [hk]
    by_contra hlt
    push Not at hlt
    have hk7 : 7 ≤ k := by
      by_contra h
      push Not at h
      have : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact h2E ((Nat.pow_dvd_pow 2 hk7).trans hdvd)
  obtain ⟨TH⟩ : Nonempty (Sylow 2 ↥(HH G L v)) := inferInstance
  set T₀ := (TH : Subgroup ↥(HH G L v)).map (HH G L v).subtype with hT₀
  have hT₀c : Nat.card ↥T₀ = 2 ^ 6 := by
    rw [hT₀, Subgroup.card_map_of_injective (HH G L v).subtype_injective,
      Sylow.card_eq_multiplicity, c.card_H, factorization_25920]
  have hT₀E : T₀ ≤ layerIn G := (Subgroup.map_subtype_le _).trans hHE
  have hT₀2 : IsPGroup 2 ↥T₀ := TH.isPGroup'.map _
  have hsylE : ∀ (P : Sylow 2 ↥(layerIn G)) (Q : Sylow 2 ↥(alternatingGroup (Fin 8))),
      Nonempty (↥P ≃* ↥Q) := by
    intro P Q
    obtain ⟨e₁⟩ := sylow_equiv_of_max hT₀E hT₀2 (fun Y hY hY2 => hT₀c ▸ hmaxE Y hY hY2) P
    set TΩ := (TH : Subgroup ↥(HH G L v)).map c.phi.toMonoidHom with hTΩ
    have hTΩc : Nat.card ↥TΩ = 2 ^ (Nat.card ↥(omegaMinusTwo 2)).factorization 2 := by
      rw [hTΩ, Subgroup.card_map_of_injective (f := c.phi.toMonoidHom) c.phi.injective,
        Sylow.card_eq_multiplicity, c.card_H, card_omega]
    obtain ⟨e₂⟩ := hG2.2 (Sylow.ofCard TΩ hTΩc) Q
    exact ⟨((e₁.trans ((TH : Subgroup ↥(HH G L v)).equivMapOfInjective _
      (HH G L v).subtype_injective).symm).trans
      ((TH : Subgroup ↥(HH G L v)).equivMapOfInjective _ c.phi.injective)).trans e₂⟩
  obtain ⟨α, β, ad⟩ := c.exists_ad hs
  have hL := c.data.L_iso
  obtain ⟨ℓ₀, hℓ₀⟩ := ad.α_surj CFSG.ComponentClassification.RankTwoAlt.a6c012
  have hfin := ad.finrank_c₀ hL hℓ₀
  have hord : orderOf (ℓ₀ : GLV V) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq (ad.αe hL) ℓ₀, ad.αe_apply, hℓ₀]
    exact orderOf_eq_prime (by decide) (by decide)
  have hnorm : ((layerIn G).subgroupOf G).Normal := by
    rw [layerIn_subgroupOf]
    have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hidx : (layerIn G).relIndex G ≤ 2 := (c.index_layerIn hzE).le
  have hirrE : IsIrr (layerIn G) ⊤ := c.std.extremal.setup.isIrr_of_layerIn_le le_rfl
  have hEH : layerIn G = HH G L v := by
    have hCE : G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)) ≤
        (Subgroup.center ↥(layerIn G)).map (layerIn G).subtype := fun x hx =>
      mem_center_map_iff.2 ⟨c.centralizer_layerIn_le hzE hx, fun p hp =>
        Subgroup.mem_centralizer_iff.1 hx.2 p hp⟩
    rcases h511b V G (layerIn G) L z ℓ₀ (layerIn_le G) hnorm hidx hCE hEq c.odd_card_center_layerIn
        c.z_mem_G c.orderOf_z c.isComponentOf_Cz hL (c.isAltNaturalModule hs) hirrE ℓ₀.2 hord hfin
        hsylE with h | h | h
    · exfalso
      obtain ⟨e⟩ := h
      have h1 := Subgroup.card_le_of_le hHE
      rw [c.card_H, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
      exact absurd h1 (by decide)
    · exfalso
      obtain ⟨e⟩ := h
      exact c.false_of_alt_nine hHE e
    · have hc :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num) h).2.2.1 rfl
      rw [ordBC_two_three] at hc
      exact (Subgroup.eq_of_le_of_card_ge hHE (by rw [hc, c.card_H])).symm
  have hirrH : IsIrr (HH G L v) ⊤ := c.std.extremal.setup.isIrr_of_layerIn_le hEH.le
  have hfix : fixedSpace (HH G L v) = ⊥ := by
    rcases hirrH.2.2 (fixedSpace (HH G L v)) (invariant_fixedSpace fun k' hk' k hk =>
        (HH G L v).mul_mem ((HH G L v).mul_mem hk' hk) ((HH G L v).inv_mem hk')) bot_le le_top
      with h | h
    · exact h
    · exfalso
      have hH1 : HH G L v = ⊥ := by
        rw [eq_bot_iff]
        intro h' hh'
        rw [Subgroup.mem_bot]
        refine LinearEquiv.ext fun w => ?_
        have hw : w ∈ fixedSpace (HH G L v) := h ▸ Submodule.mem_top
        exact hw h' hh'
      have h1 := c.card_H
      rw [hH1, Subgroup.card_bot] at h1
      norm_num at h1
  have hV₀ : commSpace (HH G L v) ⊤ = ⊤ := by
    have h := (c.split hs).sup_eq_top
    rwa [hfix, sup_bot_eq] at h
  obtain ⟨βH, hβH, hβHe⟩ := c.exists_beta hs
  have hmem : ∀ w : V, w ∈ commSpace (HH G L v) ⊤ := fun w => by
    rw [hV₀]
    exact Submodule.mem_top
  let ι : V →+ ↥(commSpace (HH G L v) ⊤) :=
    { toFun := fun w => ⟨w, hmem w⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : V →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) := βH.comp ι
  have hfapp : ∀ w, f w = βH ⟨w, hmem w⟩ := fun w => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro w w' h
      rw [hfapp, hfapp] at h
      exact congrArg Subtype.val (hβH.1 h)
    · intro t
      obtain ⟨w, hw⟩ := hβH.2 t
      exact ⟨w, by rw [hfapp]; exact hw⟩
  let ψ' : V ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => by
        rw [map_smul_pi f r x]
        rfl
      invFun := Function.surjInv hf.2
      left_inv := Function.leftInverse_surjInv hf
      right_inv := Function.rightInverse_surjInv hf.2 }
  have hψ' : ∀ w, ψ' w = βH ⟨w, hmem w⟩ := fun w => rfl
  have hΩ : IsOmegaMinusFor (layerIn G) 2 := by
    refine ⟨(MulEquiv.subgroupCongr hEH).trans c.phi, ψ', fun e w => ?_⟩
    have heH : (e : GLV V) ∈ HH G L v := hEH ▸ e.2
    rw [hψ', hψ']
    have h1 := hβHe ⟨e, c.H_le heH⟩ ⟨w, hmem w⟩ ⟨(e : GLV V) w, hmem _⟩ rfl
    rw [h1]
    rfl
  exact c.std.extremal.not_concl (Or.inr (Or.inr ⟨hL, hΩ⟩))

end Ctx

end CaseII

end CFSG.CGT.Foote82
