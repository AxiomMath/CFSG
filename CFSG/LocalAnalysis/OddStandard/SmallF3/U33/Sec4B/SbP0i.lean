module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.DihedralRec
public import CFSG.GroupTheory.CoprimeCentralizerCover

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem mem_normalizer_of_normalIn {H K : Subgroup G} (hK : NormalIn H K) {g : G}
    (hg : g ∈ K) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hK.2 g hg x hx, fun hx => by
    have h1 := hK.2 g⁻¹ (K.inv_mem hg) (g * x * g⁻¹) hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1⟩

private lemma baseGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp, Subgroup.closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with ha | ha
  · have hmem : a ∈ S ⊓ L := by
      rw [h.inf_eq, ha]
      exact Subgroup.subset_closure (by simp)
    exact hmem.2
  · have hmem : a ∈ S ⊓ L := by
      rw [h.inf_eq, ha]
      exact Subgroup.subset_closure (by simp)
    exact hmem.2

private lemma p0_eq_one_of_commute_rho (h : Ctx0 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) (hcomm : rho * f = f * rho) : f = 1 := by
  have hfB : f ∈ baseGrp x₁ x₂ := by
    have hfeq := hf
    rw [(WreathRel.fourGrp_eq_omega h.wreath).1] at hfeq
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr (fun a ha => ha.1) hfeq
  have hfL : f ∈ L := baseGrp_le_L h hfB
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hfB
  have hfC : f ∈ Subgroup.centralizer ({rho} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hfP : f ∈ twoCore t := by
    have hmem : f ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨hfW, hfC⟩
    rwa [h.cent_rho] at hmem
  have hmem : f ∈ twoCore t ⊓ L := ⟨hfP, hfL⟩
  rwa [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem

private lemma mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private lemma card_closure_pair_general {t tau : G} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hτ2 : tau ^ 2 = 1) (hτ1 : tau ≠ 1) (htτ : t * tau = tau * t)
    (hτt : tau ∉ zpowers t) : Nat.card ↥(closure ({t, tau} : Set G)) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htτc : Commute t tau := htτ
  have hcl : closure ({t, tau} : Set G) = zpowers t ⊔ zpowers tau := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcardt : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht2 ht1
  have hcardτ : Nat.card ↥(zpowers tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hτ2 hτ1
  have hinf : zpowers t ⊓ zpowers tau = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(zpowers t ⊓ zpowers tau) ∣ 2 := by
      rw [← hcardτ]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact hne ((Subgroup.card_eq_one).mp h1)
    · have heq : (zpowers t ⊓ zpowers tau) = zpowers tau :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardτ])
      have hle : zpowers tau ≤ zpowers t := heq ▸ inf_le_left
      exact hτt (hle (Subgroup.mem_zpowers tau))
  have hnorm : ∀ k ∈ zpowers tau, ∀ h ∈ zpowers t, k * h * k⁻¹ ∈ zpowers t := by
    intro k hk h hh
    have hkh : k * h = h * k := by
      rw [Subgroup.mem_zpowers_iff] at hk hh
      obtain ⟨m, rfl⟩ := hk
      obtain ⟨n, rfl⟩ := hh
      exact htτc.symm.zpow_zpow m n
    rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hcard := card_sup_eq_mul (H := zpowers t) (K := zpowers tau) hnorm hinf
  rw [hcl, hcard, hcardt, hcardτ]

private lemma p0_comm_t_tau (hc : Ctx8e t L S x₁ x₂ lam rho tau) : t * tau = tau * t :=
  (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm

private lemma p0_tau_ne_one (hc : Ctx8e t L S x₁ x₂ lam rho tau) : tau ≠ 1 := by
  intro h
  apply hc.tau_not_mem
  rw [h]
  exact Subgroup.mem_sup_left (Subgroup.one_mem (twoCore t))

private lemma p0_tau_not_mem_zpowers_t (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    tau ∉ zpowers t := by
  intro h
  rcases mem_zpowers_eq_one_or_eq (S4A.t_mul_self hc.hyp) h with h1 | h1
  · exact p0_tau_ne_one hc h1
  · apply hc.tau_not_mem
    rw [h1]
    exact Subgroup.mem_sup_left hc.hyp.mem_twoCore

private lemma p0_card_T (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(closure {t, tau}) = 4 :=
  card_closure_pair_general (by simpa [pow_two] using S4A.t_mul_self hc.hyp)
    (S4A.t_ne_one hc.hyp) hc.l44.1 (p0_tau_ne_one hc) (p0_comm_t_tau hc)
    (p0_tau_not_mem_zpowers_t hc)

private lemma p0_R_inf_CO (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ⊓ ctxCO t tau x₁ x₂ rho = closure {t, tau} := by
  apply le_antisymm
  · intro x hx
    have hxRC : x ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hx.1, hx.2.2⟩
    rwa [hc.CR_rho] at hxRC
  · intro x hx
    have hxRC : x ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
      rwa [hc.CR_rho]
    exact ⟨hxRC.1, hc.R_le_O hxRC.1, hxRC.2⟩

private lemma p0_t_mem_CO (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    t ∈ ctxCO t tau x₁ x₂ rho := by
  have hRC : t ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    rw [hc.CR_rho]; exact Subgroup.subset_closure (by simp)
  exact ⟨hc.R_le_O hRC.1, hRC.2⟩

private lemma p0_tau_mem_CO (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    tau ∈ ctxCO t tau x₁ x₂ rho := by
  have hRC : tau ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    rw [hc.CR_rho]; exact Subgroup.subset_closure (by simp)
  exact ⟨hc.R_le_O hRC.1, hRC.2⟩

theorem p0_comm_O_le_R (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ⁅ctxO t tau x₁ x₂, zpowers rho⁆ ≤ ctxR t tau x₁ x₂ := by
  rw [Subgroup.commutator_le]
  intro o ho k hk
  have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx4).2.2.2.2.1
  have hkM : k ∈ ctxM t tau x₁ x₂ := Subgroup.zpowers_le.mpr hρM hk
  have hoM : o ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ ho
  by_cases hR : o ∈ ctxR t tau x₁ x₂
  · have h1 : k * o⁻¹ * k⁻¹ ∈ ctxR t tau x₁ x₂ :=
      hc.normal_R.2 k hkM o⁻¹ ((ctxR t tau x₁ x₂).inv_mem hR)
    have heq : ⁅o, k⁆ = o * (k * o⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [heq]
    exact (ctxR t tau x₁ x₂).mul_mem hR h1
  · have ho' : k * o * k⁻¹ ∈ ctxO t tau x₁ x₂ :=
      (p0_normal_O t tau x₁ x₂).2 k hkM o ho
    have ho'R : k * o * k⁻¹ ∉ ctxR t tau x₁ x₂ := by
      intro hcon
      apply hR
      have h := hc.normal_R.2 k⁻¹ ((ctxM t tau x₁ x₂).inv_mem hkM) (k * o * k⁻¹) hcon
      have heq : k⁻¹ * (k * o * k⁻¹) * (k⁻¹)⁻¹ = o := by group
      rwa [heq] at h
    have hcoset : o⁻¹ * (k * o * k⁻¹) ∈ ctxR t tau x₁ x₂ :=
      hc.coset o ho (k * o * k⁻¹) ho' hR ho'R
    have hconj : o * (o⁻¹ * (k * o * k⁻¹))⁻¹ * o⁻¹ ∈ ctxR t tau x₁ x₂ :=
      hc.normal_R.2 o hoM _ ((ctxR t tau x₁ x₂).inv_mem hcoset)
    have heq : ⁅o, k⁆ = o * (o⁻¹ * (k * o * k⁻¹))⁻¹ * o⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact hconj

theorem p0_O_eq (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ = ctxR t tau x₁ x₂ ⊔ ctxCO t tau x₁ x₂ rho := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc.toCtx4).2.2.2.2.1
  have hRX : zpowers rho ≤ Subgroup.normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_normalIn (p0_normal_O t tau x₁ x₂) hρM)
  have hRN : zpowers rho ≤ Subgroup.normalizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_normalIn hc.normal_R hρM)
  have hR : IsPGroup 3 (zpowers rho) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.ord_rho]
    norm_num
  have hN : ¬ 3 ∣ Nat.card ↥(ctxR t tau x₁ x₂) := by
    rw [hc.card_R]; norm_num
  have hmain := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) (X := ctxO t tau x₁ x₂) (N := ctxR t tau x₁ x₂) (R := zpowers rho)
    hc.R_le_O hRX hRN hR hN (p0_comm_O_le_R hc)
  have hcent : Subgroup.centralizer ((zpowers rho : Subgroup G) : Set G) =
      Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent, sup_comm] at hmain
  rw [show ctxCO t tau x₁ x₂ rho = ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) from rfl]
  exact hmain.symm

private lemma p0_CO_not_le_R (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ¬ ctxCO t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
  intro hle
  have hOeq : ctxO t tau x₁ x₂ = ctxR t tau x₁ x₂ := by
    rw [p0_O_eq hc, sup_eq_left.mpr hle]
  have hcard : (2 : ℕ) ^ 9 = 2 ^ 8 := by rw [← hc.card_O, hOeq, hc.card_R]
  norm_num at hcard

theorem p0_card_CO (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxCO t tau x₁ x₂ rho) = 8 := by
  have hT4 : Nat.card ↥(closure {t, tau}) = 4 := p0_card_T hc
  have hRT : ctxR t tau x₁ x₂ ⊓ ctxCO t tau x₁ x₂ rho = closure {t, tau} := p0_R_inf_CO hc
  have hRrel : (ctxR t tau x₁ x₂).relIndex (ctxO t tau x₁ x₂) = 2 := by
    have h := Subgroup.relIndex_mul_card (ctxR t tau x₁ x₂) (ctxO t tau x₁ x₂)
    rw [inf_eq_left.mpr hc.R_le_O, hc.card_R, hc.card_O] at h
    norm_num at h ⊢
    omega
  have hub : Nat.card ↥(ctxCO t tau x₁ x₂ rho) ≤ 8 := by
    have h := card_le_two_mul_card_inf (A := ctxO t tau x₁ x₂) (B := ctxCO t tau x₁ x₂ rho)
      (Q := ctxR t tau x₁ x₂) inf_le_left hRrel
    rw [inf_comm, hRT, hT4] at h
    norm_num at h
    exact h
  have hex : ∃ g ∈ ctxCO t tau x₁ x₂ rho, g ∉ ctxR t tau x₁ x₂ := by
    by_contra h
    apply p0_CO_not_le_R hc
    intro g hg
    by_contra hgR
    exact h ⟨g, hg, hgR⟩
  obtain ⟨g, hgCO, hgR⟩ := hex
  have hgT : g ∉ closure {t, tau} := by
    intro hgT
    have hmem : g ∈ ctxR t tau x₁ x₂ ⊓ ctxCO t tau x₁ x₂ rho := by
      rw [hRT]; exact hgT
    exact hgR hmem.1
  have hTle : closure {t, tau} ≤ ctxCO t tau x₁ x₂ rho := by
    rw [← hRT]; exact inf_le_right
  have hTne : closure {t, tau} ≠ ctxCO t tau x₁ x₂ rho := by
    intro heq
    exact hgT (heq ▸ hgCO)
  have hlt : Nat.card ↥(closure {t, tau}) < Nat.card ↥(ctxCO t tau x₁ x₂ rho) :=
    Nat.lt_of_not_ge fun hge => hTne (Subgroup.eq_of_le_of_card_ge hTle hge)
  rw [hT4] at hlt
  have hdvd : 4 ∣ Nat.card ↥(ctxCO t tau x₁ x₂ rho) := by
    have h := Subgroup.card_dvd_of_le hTle
    rwa [hT4] at h
  obtain ⟨k, hk⟩ := hdvd
  omega

theorem p0_CO_outer (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ∃ g ∈ ctxCO t tau x₁ x₂ rho, g ∉ ctxR t tau x₁ x₂ ∧ g * t * g⁻¹ = t * tau ∧
      g * tau * g⁻¹ = tau ∧ (g ^ 2 = 1 ∨ g ^ 2 = tau) ∧
      ∀ h ∈ ctxCO t tau x₁ x₂ rho, h ∈ closure {t, tau} ∨ g⁻¹ * h ∈ closure {t, tau} := by
  have hex : ∃ g ∈ ctxCO t tau x₁ x₂ rho, g ∉ ctxR t tau x₁ x₂ := by
    by_contra h
    apply p0_CO_not_le_R hc
    intro g hg
    by_contra hgR
    exact h ⟨g, hg, hgR⟩
  obtain ⟨g, hgCO, hgR⟩ := hex
  have hgO : g ∈ ctxO t tau x₁ x₂ := hgCO.1
  have hgM : g ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hgO
  have hgCent : rho * g = g * rho :=
    (Subgroup.mem_centralizer_singleton_iff.mp hgCO.2).symm
  have hcomm_g : Commute rho g := hgCent
  have hρt : rho * t = t * rho :=
    S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)
  have hρtau : rho * tau = tau * rho := hc.tau_rho.symm
  have hcomm_rho_t : Commute rho t := hρt
  have hcomm_rho_tau : Commute rho tau := hρtau
  have hg_inv : rho * g⁻¹ = g⁻¹ * rho := hcomm_g.inv_right
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have hρt_conj : rho * t * rho⁻¹ = t := by rw [hcomm_rho_t.eq]; group
  have hρtau_conj : rho * tau * rho⁻¹ = tau := by rw [hcomm_rho_tau.eq]; group
  have hcomm_ttau : rho * (t * tau) * rho⁻¹ = t * tau := by
    rw [show rho * (t * tau) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * tau * rho⁻¹) from by group,
      hρt_conj, hρtau_conj]
  have hconj_t : rho * (g * t * g⁻¹) * rho⁻¹ = g * t * g⁻¹ := by
    rw [show rho * (g * t * g⁻¹) * rho⁻¹ =
      (rho * g * rho⁻¹) * (rho * t * rho⁻¹) * (rho * g⁻¹ * rho⁻¹) from by group]
    rw [show rho * g * rho⁻¹ = g from by rw [hcomm_g.eq]; group, hρt_conj,
      show rho * g⁻¹ * rho⁻¹ = g⁻¹ from by rw [hg_inv]; group]
  have hconj_tau : rho * (g * tau * g⁻¹) * rho⁻¹ = g * tau * g⁻¹ := by
    rw [show rho * (g * tau * g⁻¹) * rho⁻¹ =
      (rho * g * rho⁻¹) * (rho * tau * rho⁻¹) * (rho * g⁻¹ * rho⁻¹) from by group]
    rw [show rho * g * rho⁻¹ = g from by rw [hcomm_g.eq]; group, hρtau_conj,
      show rho * g⁻¹ * rho⁻¹ = g⁻¹ from by rw [hg_inv]; group]
  have hgt : g * t * g⁻¹ = t * tau := by
    have hconj : g * t * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨g, hgM, rfl⟩
    rw [hc.tM] at hconj
    rcases hconj with hconj | hconj
    · exfalso
      apply hgR
      rw [p0_mem_R_iff hc.toCtx8c hgO]
      exact hconj
    · obtain ⟨v, hv, hvEq⟩ := Set.mem_smul_set.mp hconj
      have hvEq' : (t * tau) * v = g * t * g⁻¹ := hvEq
      have hvfix : (t * tau) * (rho * v * rho⁻¹) = (t * tau) * v := by
        calc (t * tau) * (rho * v * rho⁻¹) = rho * ((t * tau) * v) * rho⁻¹ := by
              rw [show rho * ((t * tau) * v) * rho⁻¹ =
                (rho * (t * tau) * rho⁻¹) * (rho * v * rho⁻¹) from by group, hcomm_ttau]
          _ = rho * (g * t * g⁻¹) * rho⁻¹ := by rw [hvEq']
          _ = g * t * g⁻¹ := hconj_t
          _ = (t * tau) * v := hvEq'.symm
      have hv_eq : v = rho * v * rho⁻¹ := (mul_left_cancel hvfix).symm
      have hvcomm : rho * v = v * rho := by
        have h : v * rho = rho * v := by
          calc v * rho = (rho * v * rho⁻¹) * rho := by
                conv_lhs => rw [hv_eq]
            _ = rho * v := by group
        exact h.symm
      have hv1 : v = 1 := p0_eq_one_of_commute_rho hc.toCtx0 hv hvcomm
      rw [← hvEq', hv1, mul_one]
  have hgtau : g * tau * g⁻¹ = tau := by
    have hconj : g * tau * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) tau := ⟨g, hgM, rfl⟩
    rw [hc.tauM] at hconj
    obtain ⟨w, hw, hwEq⟩ := Set.mem_smul_set.mp hconj
    have hwEq' : tau * w = g * tau * g⁻¹ := hwEq
    have hwfix : tau * (rho * w * rho⁻¹) = tau * w := by
      calc tau * (rho * w * rho⁻¹) = rho * (tau * w) * rho⁻¹ := by
            rw [show rho * (tau * w) * rho⁻¹ =
              (rho * tau * rho⁻¹) * (rho * w * rho⁻¹) from by group, hρtau_conj]
        _ = rho * (g * tau * g⁻¹) * rho⁻¹ := by rw [hwEq']
        _ = g * tau * g⁻¹ := hconj_tau
        _ = tau * w := hwEq'.symm
    have hw_eq : w = rho * w * rho⁻¹ := (mul_left_cancel hwfix).symm
    have hwcomm : rho * w = w * rho := by
      have h : w * rho = rho * w := by
        calc w * rho = (rho * w * rho⁻¹) * rho := by
              conv_lhs => rw [hw_eq]
          _ = rho * w := by group
      exact h.symm
    have hw1 : w = 1 := p0_eq_one_of_commute_rho hc.toCtx0 hw hwcomm
    rw [← hwEq', hw1, mul_one]
  have hg2 : g ^ 2 = 1 ∨ g ^ 2 = tau := by
    have hg2T : g ^ 2 ∈ closure {t, tau} := by
      have hg2R : g ^ 2 ∈ ctxR t tau x₁ x₂ := by
        have hgOinv : g⁻¹ ∈ ctxO t tau x₁ x₂ := (ctxO t tau x₁ x₂).inv_mem hgO
        have hgRinv : g⁻¹ ∉ ctxR t tau x₁ x₂ :=
          fun h => hgR (by simpa using (ctxR t tau x₁ x₂).inv_mem h)
        have h := hc.coset g⁻¹ hgOinv g hgO hgRinv hgR
        simpa [pow_two] using h
      have hg2cent : g ^ 2 ∈ centralizer ({rho} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc g ^ 2 * rho = g * (g * rho) := by rw [pow_two, mul_assoc]
          _ = g * (rho * g) := by rw [hgCent]
          _ = (g * rho) * g := by rw [mul_assoc]
          _ = (rho * g) * g := by rw [hgCent]
          _ = rho * g ^ 2 := by rw [mul_assoc, ← pow_two]
      have hmem : g ^ 2 ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hg2R, hg2cent⟩
      rwa [hc.CR_rho] at hmem
    rcases (mem_closure_pair_of_invol (S4A.t_mul_self hc.hyp)
      (by simpa [pow_two] using hc.l44.1) (p0_comm_t_tau hc)).mp hg2T with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 (hc.l44.2 g)
    · exact Or.inr h1
    · exfalso
      have hconj : g * (t * tau) * g⁻¹ = t := by
        have h := show g * (t * tau) * g⁻¹ = (g * t * g⁻¹) * (g * tau * g⁻¹) from by group
        rw [h, hgt, hgtau, mul_assoc, hτ2, mul_one]
      have hfix : g * (t * tau) * g⁻¹ = g ^ 2 := by rw [← h1]; group
      have ht_eq : t = t * tau := by
        calc t = g * (t * tau) * g⁻¹ := hconj.symm
          _ = g ^ 2 := hfix
          _ = t * tau := h1
      have htau1 : tau = 1 := by
        have h4 : t * 1 = t * tau := by rw [mul_one]; exact ht_eq
        exact (mul_left_cancel h4).symm
      exact p0_tau_ne_one hc htau1
  refine ⟨g, hgCO, hgR, hgt, hgtau, hg2, ?_⟩
  intro h hh
  by_cases hhR : h ∈ ctxR t tau x₁ x₂
  · left
    have hmem : h ∈ ctxR t tau x₁ x₂ ⊓ ctxCO t tau x₁ x₂ rho := ⟨hhR, hh⟩
    rwa [p0_R_inf_CO hc] at hmem
  · right
    have hghR : g⁻¹ * h ∈ ctxR t tau x₁ x₂ := hc.coset g hgO h hh.1 hgR hhR
    have hghCO : g⁻¹ * h ∈ ctxCO t tau x₁ x₂ rho :=
      (ctxCO t tau x₁ x₂ rho).mul_mem ((ctxCO t tau x₁ x₂ rho).inv_mem hgCO) hh
    have hmem : g⁻¹ * h ∈ ctxR t tau x₁ x₂ ⊓ ctxCO t tau x₁ x₂ rho := ⟨hghR, hghCO⟩
    rwa [p0_R_inf_CO hc] at hmem

private lemma p0_dihedral_of_pair (hc : Ctx8e t L S x₁ x₂ lam rho tau) {a b : G}
    (hab : closure {a, b} ≤ ctxCO t tau x₁ x₂ rho) (ha : orderOf a = 4) (hb : b ^ 2 = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hb' : b ∉ zpowers a) :
    Nonempty (↥(ctxCO t tau x₁ x₂ rho) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedral_four ha hb hba hb'
  have hcard : Nat.card ↥(closure {a, b}) = 8 := by
    rw [Nat.card_congr (e : ↥(closure {a, b}) ≃ DihedralGroup 4), DihedralGroup.nat_card]
  have heq : closure {a, b} = ctxCO t tau x₁ x₂ rho :=
    Subgroup.eq_of_le_of_card_ge hab (by rw [p0_card_CO hc, hcard])
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩

theorem p0_CO_dihedral (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    Nonempty (↥(ctxCO t tau x₁ x₂ rho) ≃* DihedralGroup 4) := by
  obtain ⟨g, hgCO, hgR, hgt, hgtau, hg2, hTdec⟩ := p0_CO_outer hc
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have htCO : t ∈ ctxCO t tau x₁ x₂ rho := p0_t_mem_CO hc
  rcases hg2 with hg2 | hg2
  ·
    have hg2' : g * g = 1 := by simpa [pow_two] using hg2
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2'
    have hgt' : g * t = (t * tau) * g := by rw [← hgt]; group
    have hab : closure {t * g, t} ≤ ctxCO t tau x₁ x₂ rho := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact (ctxCO t tau x₁ x₂ rho).mul_mem htCO hgCO
      · rw [hx]; exact htCO
    have ha2 : (t * g) ^ 2 = tau := by
      rw [pow_two]
      calc (t * g) * (t * g) = t * (g * t) * g := by group
        _ = t * ((t * tau) * g) * g := by rw [hgt']
        _ = (t * t) * tau * (g * g) := by group
        _ = tau := by rw [ht2, hg2']; group
    have ha4 : (t * g) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2]
      exact hc.l44.1
    have ha : orderOf (t * g) = 4 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t * g) ?_ ?_
      · simpa using h
      · rw [show (2 : ℕ) ^ 1 = 2 from rfl, ha2]
        exact p0_tau_ne_one hc
      · rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl]
        exact ha4
    have hb : t ^ 2 = 1 := by simpa [pow_two] using ht2
    have hba : t * (t * g) * t⁻¹ = (t * g)⁻¹ := by
      rw [mul_inv_rev, htinv, hginv, ← mul_assoc, ht2, one_mul]
    have hb' : t ∉ zpowers (t * g) := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcomm : (t * g) * t = t * (t * g) := by
        have h := (Commute.refl (t * g)).zpow_right k
        rwa [hk] at h
      have h1 : t * (t * g) = g := by rw [← mul_assoc, ht2, one_mul]
      have h2 : (t * g) * t = tau * g := by
        rw [show (t * g) * t = t * (g * t) from by group, hgt']
        rw [show t * ((t * tau) * g) = (t * t) * tau * g from by group, ht2, one_mul]
      rw [h1] at hcomm
      rw [h2] at hcomm
      have htau1 : tau = 1 := by
        have h := congrArg (fun x => x * g⁻¹) hcomm
        simp only [mul_assoc, mul_inv_cancel, mul_one] at h
        exact h
      exact p0_tau_ne_one hc htau1
    exact p0_dihedral_of_pair hc hab ha hb hba hb'
  ·
    have hab : closure {g, t} ≤ ctxCO t tau x₁ x₂ rho := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact hgCO
      · rw [hx]; exact htCO
    have hg4 : g ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hg2]
      exact hc.l44.1
    have ha : orderOf g = 4 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) ?_ ?_
      · simpa using h
      · rw [show (2 : ℕ) ^ 1 = 2 from rfl, hg2]
        exact p0_tau_ne_one hc
      · rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl]
        exact hg4
    have hb : t ^ 2 = 1 := by simpa [pow_two] using ht2
    have hgt' : g * t = (t * tau) * g := by rw [← hgt]; group
    have hg3 : g ^ 2 * g = g ^ 3 := by rw [← pow_succ]
    have hg3inv : g ^ 3 = g⁻¹ :=
      (eq_inv_iff_mul_eq_one).mpr (by rw [← pow_succ]; exact hg4)
    have hba : t * g * t⁻¹ = g⁻¹ := by
      rw [htinv]
      have htg : t * g * t = tau * g := by
        rw [show t * g * t = t * (g * t) from by group, hgt']
        rw [show t * ((t * tau) * g) = (t * t) * tau * g from by group, ht2, one_mul]
      rw [htg, ← hg2, hg3]
      exact hg3inv
    have hb' : t ∉ zpowers g := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcomm : g * t = t * g := by
        have h := (Commute.refl g).zpow_right k
        rwa [hk] at h
      have h2 : t * g = (t * tau) * g := by rw [← hcomm, hgt']
      have h3 : t = t * tau := mul_right_cancel h2
      have htau1 : tau = 1 := by
        have h4 : t * 1 = t * tau := by rw [mul_one]; exact h3
        exact (mul_left_cancel h4).symm
      exact p0_tau_ne_one hc htau1
    exact p0_dihedral_of_pair hc hab ha hb hba hb'

theorem p0_CO_center (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ctxCO t tau x₁ x₂ rho ⊓ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) =
      zpowers tau := by
  obtain ⟨g, hgCO, hgR, hgt, hgtau, hg2, hTdec⟩ := p0_CO_outer hc
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have hcomm : t * tau = tau * t := p0_comm_t_tau hc
  haveI : IsMulCommutative (closure {t, tau}) :=
    Subgroup.isMulCommutative_closure (by
      intro a ha b hb _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb]
      · rw [ha, hb]; exact hcomm
      · rw [ha, hb]; exact hcomm.symm
      · rw [ha, hb])
  have htT : t ∈ closure {t, tau} := Subgroup.subset_closure (by simp)
  have hτT : tau ∈ closure {t, tau} := Subgroup.subset_closure (by simp)
  have htCO : t ∈ ctxCO t tau x₁ x₂ rho := p0_t_mem_CO hc
  have hτCO : tau ∈ ctxCO t tau x₁ x₂ rho := p0_tau_mem_CO hc
  apply le_antisymm
  · intro z hz
    have hzCO : z ∈ ctxCO t tau x₁ x₂ rho := hz.1
    have hzCent : ∀ h ∈ ctxCO t tau x₁ x₂ rho, h * z = z * h :=
      Subgroup.mem_centralizer_iff.mp hz.2
    rcases hTdec z hzCO with hzT | hzT
    · rcases (mem_closure_pair_of_invol ht2 hτ2 hcomm).mp hzT with h1 | h1 | h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · exfalso
        have hgt_comm : g * t = t * g := by
          calc g * t = g * z := by rw [h1]
            _ = z * g := hzCent g hgCO
            _ = t * g := by rw [h1]
        have hgt' : g * t = (t * tau) * g := by rw [← hgt]; group
        have h2 : t * g = (t * tau) * g := by rw [hgt_comm.symm, hgt']
        have h3 : t = t * tau := mul_right_cancel h2
        have htau1 : tau = 1 := by
          have h4 : t * 1 = t * tau := by rw [mul_one]; exact h3
          exact (mul_left_cancel h4).symm
        exact p0_tau_ne_one hc htau1
      · rw [h1]; exact Subgroup.mem_zpowers tau
      · exfalso
        have hcent : (t * tau) * g = g * (t * tau) := by
          have h := hzCent g hgCO
          rw [h1] at h
          exact h.symm
        have hconj : g * (t * tau) * g⁻¹ = t := by
          have h := show g * (t * tau) * g⁻¹ = (g * t * g⁻¹) * (g * tau * g⁻¹) from by group
          rw [h, hgt, hgtau, mul_assoc, hτ2, mul_one]
        have hgz : g * (t * tau) * g⁻¹ = t * tau := by rw [← hcent]; group
        have ht_eq : t * tau = t := by rw [← hgz, hconj]
        have htau1 : tau = 1 := by
          have h4 : t * tau = t * 1 := by rw [mul_one]; exact ht_eq
          exact mul_left_cancel h4
        exact p0_tau_ne_one hc htau1
    · exfalso
      have hcT : g⁻¹ * z ∈ closure {t, tau} := hzT
      have hct : (g⁻¹ * z) * t = t * (g⁻¹ * z) :=
        Subgroup.mul_comm_of_mem_isMulCommutative (closure {t, tau}) hcT htT
      have hz_eq : z = g * (g⁻¹ * z) := by group
      have hzt : t * z = z * t := hzCent t htCO
      have h1 : (g * t) * (g⁻¹ * z) = (t * g) * (g⁻¹ * z) := by
        calc (g * t) * (g⁻¹ * z) = g * (t * (g⁻¹ * z)) := by group
          _ = g * ((g⁻¹ * z) * t) := by rw [hct]
          _ = (g * (g⁻¹ * z)) * t := by group
          _ = z * t := by rw [← hz_eq]
          _ = t * z := hzt.symm
          _ = t * (g * (g⁻¹ * z)) := by rw [← hz_eq]
          _ = (t * g) * (g⁻¹ * z) := by group
      have hgtg : g * t = t * g := mul_right_cancel h1
      have hgt' : g * t = (t * tau) * g := by rw [← hgt]; group
      have h2 : t * g = (t * tau) * g := by rw [← hgtg, hgt']
      have h3 : t = t * tau := mul_right_cancel h2
      have htau1 : tau = 1 := by
        have h4 : t * 1 = t * tau := by rw [mul_one]; exact h3
        exact (mul_left_cancel h4).symm
      exact p0_tau_ne_one hc htau1
  · intro z hz
    rcases mem_zpowers_eq_one_or_eq hτ2 hz with h1 | h1
    · rw [h1]; exact ⟨(ctxCO t tau x₁ x₂ rho).one_mem, Subgroup.one_mem _⟩
    · rw [h1]
      refine ⟨hτCO, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rcases hTdec h hh with hhT | hhT
      · exact Subgroup.mul_comm_of_mem_isMulCommutative (closure {t, tau}) hhT hτT
      · have hcomm1 : (g⁻¹ * h) * tau = tau * (g⁻¹ * h) :=
          Subgroup.mul_comm_of_mem_isMulCommutative (closure {t, tau}) hhT hτT
        have hgtau' : g * tau = tau * g := by
          calc g * tau = (g * tau * g⁻¹) * g := by group
            _ = tau * g := by rw [hgtau]
        calc h * tau = g * ((g⁻¹ * h) * tau) := by group
          _ = g * (tau * (g⁻¹ * h)) := by rw [hcomm1]
          _ = (g * tau) * (g⁻¹ * h) := by group
          _ = (tau * g) * (g⁻¹ * h) := by rw [hgtau']
          _ = tau * (g * (g⁻¹ * h)) := by group
          _ = tau * h := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
