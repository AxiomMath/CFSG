module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeAD1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23DiagJB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23JSide

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem piK_comm_alpha (hαN : phi hKa (abar h) ∈ NL hKa) {r : H} (hrS : r ∈ h.S)
    (hrK : r ∈ h.K) :
    piK hKa ⟨r, hrK⟩ * ⟨phi hKa (abar h), hαN⟩ = ⟨phi hKa (abar h), hαN⟩ * piK hKa ⟨r, hrK⟩ := by
  apply Subtype.ext
  show phi hKa (wbarMk h.B ⟨r, K_le_W h hrK⟩) * phi hKa (abar h) =
    phi hKa (abar h) * phi hKa (wbarMk h.B ⟨r, K_le_W h hrK⟩)
  rw [abar, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  exact Subtype.ext (h.comm_a hrS)

section Ident

variable
  (hZ : center (OddBar h.K) = ⊥) {ι : ↥(NL hKa) →* Equiv.Perm (Fin 8330)}
  (hιinj : Function.Injective ι) (hιP : ∀ γ, ι γ ∈ heP) (hιsurj : ∀ p ∈ heP, ∃ γ, ι γ = p)
  (hαN : phi hKa (abar h) ∈ NL hKa) (hια : ι ⟨phi hKa (abar h), hαN⟩ = heGenPerm 0)
  (hιJ : ∀ γ : ↥(NL hKa), (γ : ↥(GAut hKa)) ∈ Jhat hKa ↔ ι γ ∈ hjJ)

include hZ hιinj hιP hιsurj hια hιJ in
theorem exists_S_not_comm :
    ∃ r ∈ h.S, ∃ hrK : r ∈ h.K, ι (piK hKa ⟨r, hrK⟩) * hjZP ≠ hjZP * ι (piK hKa ⟨r, hrK⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRQ, hRM, R', hR'⟩ := h.sylow_layer
  have hV : layerIn h.W = h.K := h.V_eq_K hKa
  have hMK : layerIn h.W ⊓ normalizer ((GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W :
      Subgroup H) : Set H) ≤ h.K := fun m hm => hV ▸ (mem_inf.mp hm).1
  have hRK : R ≤ h.K := hRM.trans hMK
  have hRS : R ≤ h.S := hRQ.trans inf_le_left
  set fM := (piK hKa).comp (Subgroup.inclusion hMK) with hfM
  have hCle : centralizer ({⟨phi hKa (abar h), hαN⟩} : Set ↥(NL hKa)) ≤ fM.range := by
    intro γ hγ
    obtain ⟨k, rfl⟩ := piK_surjective hKa γ
    have hkN := mem_normalizer_of_comm hKa hZ hιinj hιP hαN hια hιJ
      (mem_centralizer_singleton_iff.mp hγ)
    exact ⟨⟨k, mem_inf.mpr ⟨hV.symm ▸ k.2, hkN⟩⟩, rfl⟩
  have hCcard : Nat.card (centralizer ({⟨phi hKa (abar h), hαN⟩} : Set ↥(NL hKa))) = 161280 := by
    rw [← Subgroup.card_map_of_injective hιinj,
      map_centralizer_ident hKa hιinj hιP hιsurj hαN hια]
    exact card_heP_cent0
  have h512M : 2 ^ 9 ∣ Nat.card ↥(layerIn h.W ⊓ normalizer ((GSLit.fixedLayer h.J h.B ⊔
      oddCoreIn h.W : Subgroup H) : Set H)) := by
    have h1 := Subgroup.card_dvd_of_le hCle
    have h2 : Nat.card fM.range ∣ Nat.card ↥(layerIn h.W ⊓ normalizer ((GSLit.fixedLayer h.J
        h.B ⊔ oddCoreIn h.W : Subgroup H) : Set H)) :=
      Subgroup.card_dvd_of_surjective fM.rangeRestrict_surjective
    rw [hCcard] at h1
    exact dvd_trans (by norm_num) (dvd_trans h1 h2)
  have h512R : 2 ^ 9 ∣ Nat.card R := by
    have := Sylow.pow_dvd_card_of_pow_dvd_card R' h512M
    rwa [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv] at this
  by_contra hno
  push Not at hno
  set fR := ι.comp ((piK hKa).comp (Subgroup.inclusion hRK)) with hfR
  have hfRinj : Function.Injective fR := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : piK hKa (Subgroup.inclusion hRK r) = 1 := hιinj (hr.trans (map_one ι).symm)
    rw [piK_eq_one_iff hKa hZ] at h1
    obtain ⟨n, hn⟩ := h.orderOf_eq_two_pow_of_mem_S (hRS r.2)
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥h.K) h1
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥h.K)) := pPrimeCore_coprime_card
    have hord : orderOf (Subgroup.inclusion hRK r) = 2 ^ n := by
      rw [← Subgroup.orderOf_coe, ← hn]
      rfl
    rw [hord] at hdvd
    have hn0 : n = 0 := by
      by_contra hn0
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      exact absurd (Nat.Coprime.coprime_dvd_right (dvd_trans h2 hdvd) hcop) (by norm_num)
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    exact Subtype.ext hn
  have hle : fR.range ≤ hjJ := by
    rintro _ ⟨r, rfl⟩
    apply mem_hjJ_of_comm
    · exact mem_centralizerIn.2 ⟨hιP _, (comm_iff_of_ident hKa hιinj hαN hια _).1
        (piK_comm_alpha hKa hαN (hRS r.2) (hRK r.2))⟩
    · exact hno _ (hRS r.2) (hRK r.2)
  have hcard := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hfRinj).toEquiv, card_hjJ] at hcard
  have := dvd_trans h512R hcard
  norm_num at this

include hZ hιinj hιP hιsurj hια hιJ in
theorem a_mem_D_of_ident (Ψ : OddBar h.J ≃* ↥hjJ)
    (hΨ : ∀ (j : H) (hjB : j ∈ GSLit.fixedLayer h.J h.B) (hjJ : j ∈ h.J),
      (Ψ (jq h.J ⟨j, hjJ⟩) : Equiv.Perm (Fin 8330)) =
        ι (piK hKa ⟨j, fixedLayer_le_K h hKa hjB⟩)) : h.a ∈ h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : hjL z₁ ∈ center ↥hjJ :=
    ker_hjQ_le_center (by rw [MonoidHom.mem_ker, hjQ_hjL, sigma_z₁])
  have hζc : Ψ.symm (hjL z₁) ∈ center (OddBar h.J) := by
    rw [mem_center_iff]
    intro g
    apply Ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.mp hz (Ψ g)
  have hζ1 : Ψ.symm (hjL z₁) ≠ 1 := by
    intro h1
    have h2 : hjL z₁ = 1 := by rw [← Ψ.apply_symm_apply (hjL z₁), h1, map_one]
    exact hjZP_ne_one (congrArg Subtype.val h2)
  obtain ⟨p, hpD, hpJ, hp⟩ := exists_mem_of_mem_center (isSylowTwoIn_D h) hζc
  have hpP : p ∈ h.P := by
    have hmem := (mem_zStarIn_iff hpJ).2 (hp ▸ hζc)
    rw [zStarIn, map_fusionZStar_eq] at hmem
    exact mem_inf.mpr ⟨h.D_le_S hpD, (mem_inf.mp hmem).2⟩
  have hp1 : p ≠ 1 := by
    rintro rfl
    exact hζ1 (hp.symm.trans (map_one (jq h.J)))
  set N : Subgroup ↥h.S := (h.D ⊓ h.P).subgroupOf h.S with hN
  have hNn : N.Normal := by
    constructor
    intro n hn s
    rw [hN, mem_subgroupOf] at hn ⊢
    simpa using h.conj_mem_D_inf_P s.2 hn
  have hN1 : N ≠ ⊥ := by
    intro hb
    have hpN : (⟨p, h.D_le_S hpD⟩ : ↥h.S) ∈ N := by
      rw [hN, mem_subgroupOf]
      exact mem_inf.mpr ⟨hpD, hpP⟩
    rw [hb] at hpN
    exact hp1 (congrArg Subtype.val (mem_bot.mp hpN))
  have hnil : Group.IsNilpotent ↥h.S := h.isPGroup_S.isNilpotent
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
  have huN' : ((u : ↥h.S) : H) ∈ h.D ⊓ h.P := mem_subgroupOf.mp huN
  obtain ⟨hcD, hcP⟩ := mem_inf.mp huN'
  set c : H := ((u : ↥h.S) : H) with hcdef
  have hc1 : c ≠ 1 := fun he => hu1 (Subtype.ext (Subtype.ext he))
  have hcS : ∀ s ∈ h.S, s * c = c * s := fun s hs =>
    congrArg Subtype.val (mem_center_iff.mp huZ ⟨s, hs⟩)
  have hcJ := h.D_le_J hcD
  have hcB := CF23Diag.D_le_JB h hcD
  have hcK := fixedLayer_le_K h hKa hcB
  have hjqc : jq h.J ⟨c, hcJ⟩ ∈ center (OddBar h.J) := jq_mem_center h hcJ (mem_inf.mp hcP).2
  have hcen : Ψ (jq h.J ⟨c, hcJ⟩) ∈ center ↥hjJ := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := Ψ.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hjqc g']
  have hval := hΨ c hcB hcJ
  have hne1 : (Ψ (jq h.J ⟨c, hcJ⟩) : Equiv.Perm (Fin 8330)) ≠ 1 := by
    intro h1
    have h2 : jq h.J ⟨c, hcJ⟩ = 1 := Ψ.injective (by rw [map_one]; exact Subtype.ext h1)
    exact hc1 (eq_one_of_jq_eq_one h.D_le_J (h.isPGroup_S.to_le h.D_le_S) hcD h2)
  obtain ⟨r, hrS, hrK, hr⟩ := exists_S_not_comm hKa hZ hιinj hιP hιsurj hαN hια hιJ
  have hρrt : ι (piK hKa ⟨r, hrK⟩) * heGenPerm 0 = heGenPerm 0 * ι (piK hKa ⟨r, hrK⟩) :=
    (comm_iff_of_ident hKa hιinj hαN hια _).1 (piK_comm_alpha hKa hαN hrS hrK)
  have hρrc : ι (piK hKa ⟨r, hrK⟩) * (Ψ (jq h.J ⟨c, hcJ⟩) : Equiv.Perm (Fin 8330)) =
      (Ψ (jq h.J ⟨c, hcJ⟩) : Equiv.Perm (Fin 8330)) * ι (piK hKa ⟨r, hrK⟩) := by
    rw [hval, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hcS r hrS)
  have hct : ι (piK hKa ⟨c, hcK⟩) = heGenPerm 0 := by
    rcases center_hjJ_cases hcen with h1 | h1 | h1 | h1
    · exact absurd h1 hne1
    · exfalso
      rw [h1] at hρrc
      exact hr hρrc
    · rw [← hval]
      exact h1
    · exfalso
      rw [h1] at hρrc
      apply hr
      calc ι (piK hKa ⟨r, hrK⟩) * hjZP =
          ι (piK hKa ⟨r, hrK⟩) * (hjZP * heGenPerm 0) * (heGenPerm 0)⁻¹ := by group
        _ = hjZP * heGenPerm 0 * ι (piK hKa ⟨r, hrK⟩) * (heGenPerm 0)⁻¹ := by rw [hρrc]
        _ = hjZP * (heGenPerm 0 * ι (piK hKa ⟨r, hrK⟩)) * (heGenPerm 0)⁻¹ := by group
        _ = hjZP * (ι (piK hKa ⟨r, hrK⟩) * heGenPerm 0) * (heGenPerm 0)⁻¹ := by rw [hρrt]
        _ = hjZP * ι (piK hKa ⟨r, hrK⟩) := by group
  have hpi : piK hKa ⟨c, hcK⟩ = ⟨phi hKa (abar h), hαN⟩ := hιinj (hct.trans hια.symm)
  have hrho : rhoL hKa ⟨c, K_le_W h hcK⟩ = rhoL hKa ⟨h.a, h.a_mem_normalizer⟩ := by
    have h1 := congrArg (fun γ : ↥(NL hKa) => ((γ : ↥(GAut hKa)) : MulAut (LK h))) hpi
    change rhoBar hKa (wbarMk h.B ⟨c, K_le_W h hcK⟩) = rhoBar hKa (abar h) at h1
    rw [abar, rhoBar_mk, rhoBar_mk] at h1
    exact h1
  have hbW : h.a * c⁻¹ ∈ h.W := mul_mem h.a_mem_normalizer (inv_mem (K_le_W h hcK))
  have hbK : h.a * c⁻¹ ∈ coreActionKernel h.K := by
    have h1 : rhoL hKa ⟨h.a * c⁻¹, hbW⟩ = 1 := by
      have e1 : (⟨h.a * c⁻¹, hbW⟩ : ↥h.W) =
          ⟨h.a, h.a_mem_normalizer⟩ * (⟨c, K_le_W h hcK⟩ : ↥h.W)⁻¹ := rfl
      rw [e1, map_mul, map_inv, hrho, mul_inv_cancel]
    exact (rhoL_eq_one_iff hKa _).1 h1
  have hbS : h.a * c⁻¹ ∈ h.S := mul_mem h.a_mem_S (inv_mem (h.D_le_S hcD))
  have hbB : h.a * c⁻¹ ∈ h.B := by
    have hV : layerIn h.W = h.K := h.V_eq_K hKa
    refine mem_of_sylow_of_mem_normalizer h.B_sylow_kernel h.B_le_kernel ?_ hbW
      (h.orderOf_eq_two_pow_of_mem_S hbS)
    exact mem_inf.mpr ⟨hbW, hV.symm ▸ hbK⟩
  have hbx : h.x⁻¹ * (h.a * c⁻¹) * h.x = h.a * c⁻¹ := by
    have h1 : h.x * h.a = h.a * h.x := h.x_comm_a
    have h2 : h.x * c = c * h.x := hcS h.x h.x_mem
    calc h.x⁻¹ * (h.a * c⁻¹) * h.x = h.x⁻¹ * (h.a * (c⁻¹ * h.x)) := by group
      _ = h.x⁻¹ * (h.a * (h.x * c⁻¹)) := by
        rw [show c⁻¹ * h.x = h.x * c⁻¹ by
          calc c⁻¹ * h.x = c⁻¹ * (h.x * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * h.x) * c⁻¹ := by rw [h2]
            _ = h.x * c⁻¹ := by group]
      _ = h.x⁻¹ * ((h.a * h.x) * c⁻¹) := by group
      _ = h.x⁻¹ * ((h.x * h.a) * c⁻¹) := by rw [h1]
      _ = h.a * c⁻¹ := by group
  have hbBx : h.a * c⁻¹ ∈ conjugate h.B h.x := by
    refine ⟨h.a * c⁻¹, hbB, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hbx
  have hb1 : h.a * c⁻¹ = 1 := by
    have := mem_inf.mpr ⟨hbB, hbBx⟩
    rw [h.inf_conjugate_x, mem_bot] at this
    exact this
  have hac : h.a = c := by
    calc h.a = h.a * c⁻¹ * c := by group
      _ = c := by rw [hb1, one_mul]
  rw [hac]
  exact hcD

end Ident

end CFSG.ComponentClassification.GSThmB.CF23L34
