module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316G1a

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fzl_cent_eq_E {P E : Subgroup G} {rho : G} (hrho3 : rho ^ 3 = 1)
    (hcardP : Nat.card P = 64) (hcardE : Nat.card E = 16) (hEP : E ≤ P)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hrP : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P)
    (hrE : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E) (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1)
    (hna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    ∀ g ∈ P, (∀ e ∈ E, g * e = e * g) → g ∈ E := by
  set C : Subgroup G := P ⊓ Subgroup.centralizer (E : Set G) with hC
  have hCmem : ∀ g, g ∈ C ↔ g ∈ P ∧ ∀ e ∈ E, e * g = g * e := by
    intro g
    simp only [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hEC : E ≤ C := by
    intro e he
    rw [hCmem]
    exact ⟨hEP he, fun e' he' => hEcomm e' he' e he⟩
  have hEinv : ∀ e ∈ E, rho⁻¹ * e * rho ∈ E := fzl_inv_conj_mem hrho3 hrE
  have hCin : ∀ c ∈ C, rho * c * rho⁻¹ ∈ C := by
    intro c hc
    obtain ⟨hcP, hccent⟩ := (hCmem c).mp hc
    rw [hCmem]
    refine ⟨hrP c hcP, ?_⟩
    intro e he
    have he' : rho⁻¹ * e * rho ∈ E := hEinv e he
    have hc' : (rho⁻¹ * e * rho) * c = c * (rho⁻¹ * e * rho) := hccent _ he'
    have h1 : (rho * c * rho⁻¹) * e * (rho * c * rho⁻¹)⁻¹ = e := by
      calc (rho * c * rho⁻¹) * e * (rho * c * rho⁻¹)⁻¹
          = rho * (c * (rho⁻¹ * e * rho) * c⁻¹) * rho⁻¹ := by group
        _ = rho * ((rho⁻¹ * e * rho) * c * c⁻¹) * rho⁻¹ := by rw [← hc']
        _ = e := by group
    have h2 : (rho * c * rho⁻¹) * e = e * (rho * c * rho⁻¹) := by
      have := congrArg (· * (rho * c * rho⁻¹)) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have hCfix : ∀ c ∈ C, rho * c * rho⁻¹ = c → c = 1 := by
    intro c hc hfix
    exact hfpf c ((hCmem c).mp hc).1 hfix
  have hCmod : Nat.card C % 3 = 1 := fzl_card_mod3_of_fpf hrho3 hCin hCfix
  have hCP : C ≤ P := fun g hg => ((hCmem g).mp hg).1
  have hC16 : 16 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hEC
    rwa [hcardE] at this
  have hCdiv : Nat.card C ∣ 64 := by
    have := Subgroup.card_dvd_of_le hCP
    rwa [hcardP] at this
  have hCcases : Nat.card C = 16 ∨ Nat.card C = 64 :=
    fzl_card_cases _ (Nat.le_of_dvd (by norm_num) hCdiv)
      (Nat.le_of_dvd Nat.card_pos hC16) hCmod hCdiv
  rcases hCcases with hC16' | hC64'
  · have hCE : C = E := (Subgroup.eq_of_le_of_card_ge (H := E) (K := C) hEC (by omega)).symm
    intro g hgP hgc
    have hgC : g ∈ C := by
      rw [hCmem]
      exact ⟨hgP, fun e he => (hgc e he).symm⟩
    rwa [hCE] at hgC
  · exfalso
    have hCPeq : C = P := Subgroup.eq_of_le_of_card_ge hCP (by omega)
    have hEcent : ∀ e ∈ E, ∀ p ∈ P, p * e = e * p := by
      intro e he p hp
      have hpC : p ∈ C := by rw [hCPeq]; exact hp
      exact (((hCmem p).mp hpC).2 e he).symm
    have hnotPE : ¬ P ≤ E := by
      intro hPE
      have hPEeq : P = E := Subgroup.eq_of_le_of_card_ge hPE (by omega)
      rw [hPEeq, hcardE] at hcardP
      omega
    have hex : ∃ x, x ∈ P ∧ x ∉ E := by
      by_contra h
      apply hnotPE
      intro p hp
      by_contra hpE
      exact h ⟨p, hp, hpE⟩
    obtain ⟨x, hxP, hxE⟩ := hex
    set xp : G := rho * x * rho⁻¹ with hxp
    set xp2 : G := rho ^ 2 * x * (rho ^ 2)⁻¹ with hxp2
    have hxpP : xp ∈ P := hrP x hxP
    have hxp_conj : rho * xp * rho⁻¹ = xp2 := by
      rw [hxp, hxp2]; simp only [pow_two, mul_inv_rev]; group
    have hxp2P : xp2 ∈ P := by rw [← hxp_conj]; exact hrP xp hxpP
    have hxpE : xp ∉ E := by
      intro h
      have h' : rho⁻¹ * xp * rho ∈ E := hEinv xp h
      rw [show rho⁻¹ * xp * rho = x by rw [hxp]; group] at h'
      exact hxE h'
    have hxp2_conj : rho * xp2 * rho⁻¹ = x := by
      rw [hxp2]
      calc rho * (rho ^ 2 * x * (rho ^ 2)⁻¹) * rho⁻¹
          = (rho * rho ^ 2) * x * ((rho ^ 2)⁻¹ * rho⁻¹) := by group
        _ = x := by
              have h1 : rho * rho ^ 2 = 1 := by rw [← pow_succ', hrho3]
              have h2 : (rho ^ 2)⁻¹ * rho⁻¹ = 1 := by rw [← mul_inv_rev, h1, inv_one]
              rw [h1, h2]; simp
    have hxp2E : xp2 ∉ E := by
      intro h
      have h' : rho * xp2 * rho⁻¹ ∈ E := hrE xp2 h
      rw [hxp2_conj] at h'
      exact hxE h'
    have hxpN : xp ∉ E ⊔ Subgroup.closure ({x} : Set G) := by
      intro h
      exact fzl_rho_mem_sup_closure (y := x) hrho3 hcardP hcardE hEP hEcomm hEcent hrP hrE hfpf hna
        hxP hxE h
    set N : Subgroup G := E ⊔ Subgroup.closure ({x} : Set G) with hN
    have hEN : E ≤ N := le_sup_left
    have hxN : x ∈ N := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hNP : N ≤ P := by
      rw [hN]
      refine sup_le hEP ?_
      rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hxP
    have hN16 : 16 ∣ Nat.card N := by
      have := Subgroup.card_dvd_of_le hEN
      rwa [hcardE] at this
    have hNdiv : Nat.card N ∣ 64 := by
      have := Subgroup.card_dvd_of_le hNP
      rwa [hcardP] at this
    have hNne : N ≠ E := by
      intro h
      exact hxE (h ▸ hxN)
    have hNle : Nat.card N ≤ 64 := Nat.le_of_dvd (by norm_num) hNdiv
    have hNgt : 16 < Nat.card N := by
      have hle : 16 ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos hN16
      have hne : Nat.card N ≠ 16 := by
        intro h
        exact hNne (Subgroup.eq_of_le_of_card_ge (H := E) (K := N) hEN (by omega)).symm
      omega
    have hN32 : Nat.card N = 32 := by
      have hne : Nat.card N ≠ 64 := by
        intro h
        have : N = P := Subgroup.eq_of_le_of_card_ge hNP (by omega)
        exact hxpN (this ▸ hxpP)
      exact fzl_card_eq_32 _ hNle hNgt hne hNdiv
    have hNeq : N = Subgroup.closure ((E : Set G) ∪ {x}) := by
      rw [hN, Subgroup.closure_union, Subgroup.closure_eq]
    haveI : IsMulCommutative N := by
      rw [hNeq]
      apply Subgroup.isMulCommutative_closure
      intro a ha b hb _
      simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
      rcases ha with haE | ha_eq
      · rcases hb with hbE | hb_eq
        · exact hEcomm a haE b hbE
        · rw [hb_eq]; exact (hEcent a haE x hxP).symm
      · rw [ha_eq]
        rcases hb with hbE | hb_eq
        · exact hEcent b hbE x hxP
        · rw [hb_eq]
    have hEcent_sub : E.subgroupOf P ≤ Subgroup.center P := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hEcent (z : G) hz (g : G) g.2
    haveI hEnorm : (E.subgroupOf P).Normal := Subgroup.normal_of_le_center hEcent_sub
    have hQcard : Nat.card (P ⧸ (E.subgroupOf P)) = 4 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf P)
      have h2 : Nat.card (E.subgroupOf P) = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
      rw [hcardP, h2, hcardE] at h1
      omega
    haveI hQcomm : IsMulCommutative (P ⧸ (E.subgroupOf P)) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQcard]; norm_num)
    set xP : P := ⟨x, hxP⟩ with hxP'
    set xpP : P := ⟨xp, hxpP⟩ with hxpP'
    set xp2P : P := ⟨xp2, hxp2P⟩ with hxp2P'
    set w : G := x * xp * xp2 with hw
    have hwP : w ∈ P := P.mul_mem (P.mul_mem hxP hxpP) hxp2P
    have hρw : rho * w * rho⁻¹ = xp * xp2 * x := by
      calc rho * w * rho⁻¹ = rho * (x * xp * xp2) * rho⁻¹ := by rw [hw]
        _ = (rho * x * rho⁻¹) * (rho * xp * rho⁻¹) * (rho * xp2 * rho⁻¹) := by group
        _ = xp * xp2 * x := by rw [← hxp, hxp_conj, hxp2_conj]
    have hρwP : rho * w * rho⁻¹ ∈ P := by
      rw [hρw]; exact P.mul_mem (P.mul_mem hxpP hxp2P) hxP
    set wP : P := ⟨w, hwP⟩ with hwPs
    set wρ : P := ⟨rho * w * rho⁻¹, hρwP⟩ with hwρs
    have hπeq : QuotientGroup.mk' (E.subgroupOf P) wρ
        = QuotientGroup.mk' (E.subgroupOf P) wP := by
      have e1 : wρ = xpP * xp2P * xP := by
        apply Subtype.ext
        simpa using hρw
      have e2 : wP = xP * xpP * xp2P := by
        apply Subtype.ext
        simpa using hw.symm
      rw [e1, e2, map_mul, map_mul, map_mul, map_mul]
      calc QuotientGroup.mk' (E.subgroupOf P) xpP * QuotientGroup.mk' (E.subgroupOf P) xp2P
              * QuotientGroup.mk' (E.subgroupOf P) xP
          = QuotientGroup.mk' (E.subgroupOf P) xpP
              * (QuotientGroup.mk' (E.subgroupOf P) xp2P
                * QuotientGroup.mk' (E.subgroupOf P) xP) := by rw [mul_assoc]
        _ = QuotientGroup.mk' (E.subgroupOf P) xpP
              * (QuotientGroup.mk' (E.subgroupOf P) xP
                * QuotientGroup.mk' (E.subgroupOf P) xp2P) := by
              rw [IsMulCommutative.is_comm.comm (QuotientGroup.mk' (E.subgroupOf P) xp2P)
                (QuotientGroup.mk' (E.subgroupOf P) xP)]
        _ = QuotientGroup.mk' (E.subgroupOf P) xpP * QuotientGroup.mk' (E.subgroupOf P) xP
              * QuotientGroup.mk' (E.subgroupOf P) xp2P := by rw [← mul_assoc]
        _ = QuotientGroup.mk' (E.subgroupOf P) xP * QuotientGroup.mk' (E.subgroupOf P) xpP
              * QuotientGroup.mk' (E.subgroupOf P) xp2P := by
              rw [IsMulCommutative.is_comm.comm (QuotientGroup.mk' (E.subgroupOf P) xpP)
                (QuotientGroup.mk' (E.subgroupOf P) xP)]
    have hwE : w ∈ E := by
      apply fzl_mem_of_coset (y := w) hrho3 hcardP hcardE hEP hEcomm hEcent hrP hrE hfpf hna hwP
      have hmem : (wP⁻¹ * wρ : P) ∈ E.subgroupOf P := by
        rw [← QuotientGroup.eq_one_iff]
        change QuotientGroup.mk' (E.subgroupOf P) (wP⁻¹ * wρ) = 1
        rw [map_mul, map_inv, hπeq, inv_mul_cancel]
      simpa [Subgroup.mem_subgroupOf] using hmem
    have hw1 : w = 1 := by
      have hxw : x * (x * xp * xp2) = (x * xp * xp2) * x := by
        have := hEcent w hwE x hxP
        rwa [hw] at this
      have hfix : rho * w * rho⁻¹ = w := by
        rw [hρw, hw]
        have h1 : x * (xp * xp2 * x) = x * (x * xp * xp2) := by
          calc x * (xp * xp2 * x) = x * xp * xp2 * x := by group
            _ = x * (x * xp * xp2) := hxw.symm
        exact mul_left_cancel h1
      exact hfpf w hwP hfix
    have hxp2_eq : xp2 = (x * xp)⁻¹ := by
      have h : x * xp * xp2 = 1 := by rw [← hw, hw1]
      exact eq_inv_of_mul_eq_one_right h
    have hcE : ⁅x, xp⁆ ∈ E := by
      have hmem : (⁅xP, xpP⁆ : P) ∈ E.subgroupOf P := by
        rw [← QuotientGroup.eq_one_iff]
        change QuotientGroup.mk' (E.subgroupOf P) ⁅xP, xpP⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact IsMulCommutative.is_comm.comm _ _
      rwa [Subgroup.mem_subgroupOf] at hmem
    have hcP : ⁅x, xp⁆ ∈ P := by
      have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr (fun a ha b hb => by
        rw [commutatorElement_def]
        exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb))
      exact hle (Subgroup.commutator_mem_commutator hxP hxpP)
    have hc : ⁅x, xp⁆ = 1 := by
      refine hfpf ⁅x, xp⁆ hcP ?_
      have hcent : (x * xp) * ⁅x, xp⁆ = ⁅x, xp⁆ * (x * xp) :=
        hEcent ⁅x, xp⁆ hcE (x * xp) (P.mul_mem hxP hxpP)
      have hkey : ⁅x * xp, xp⁆ = ⁅x, xp⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_self]
        simp only [mul_one]
        group
      have hconj : rho * ⁅x, xp⁆ * rho⁻¹ = ⁅xp, xp2⁆ := by
        rw [conjugate_commutatorElement, ← hxp, hxp_conj]
      rw [hconj, hxp2_eq, commutatorElement_inv_right, hkey]
      calc (x * xp)⁻¹ * ⁅x, xp⁆ * (x * xp)
          = (x * xp)⁻¹ * (⁅x, xp⁆ * (x * xp)) := by group
        _ = (x * xp)⁻¹ * ((x * xp) * ⁅x, xp⁆) := by rw [← hcent]
        _ = ⁅x, xp⁆ := by group
    have hcomm : x * xp = xp * x := commutatorElement_eq_one_iff_mul_comm.mp hc
    have hxp_cent : xp ∈ Subgroup.centralizer (N : Set G) := by
      rw [hNeq, Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      simp only [Set.mem_union, Set.mem_singleton_iff] at hh
      rcases hh with hhE | hh_eq
      · exact (hEcent h hhE xp hxpP).symm
      · rw [hh_eq]; exact hcomm
    set M : Subgroup G := N ⊔ Subgroup.closure ({xp} : Set G) with hM
    have hNM : N ≤ M := le_sup_left
    have hMP : M ≤ P := by
      rw [hM]
      refine sup_le hNP ?_
      rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hxpP
    have hMeq : M = P := by
      by_contra hMPne
      have hle : Nat.card M ≤ 64 := Nat.le_of_dvd (by norm_num) (by
        have := Subgroup.card_dvd_of_le hMP; rwa [hcardP] at this)
      have hge : 32 ≤ Nat.card M := by
        have hd := Subgroup.card_dvd_of_le hNM
        exact Nat.le_of_dvd Nat.card_pos (by rwa [hN32] at hd)
      have hne : Nat.card M ≠ 64 := by
        intro h
        exact hMPne (Subgroup.eq_of_le_of_card_ge hMP (by omega))
      have hM32 : Nat.card M = 32 := by
        have hgt : 16 < Nat.card M := by omega
        exact fzl_card_eq_32 _ hle hgt hne (by
          have := Subgroup.card_dvd_of_le hMP; rwa [hcardP] at this)
      have hNMeq : N = M := Subgroup.eq_of_le_of_card_ge hNM (by omega)
      have hxpM : xp ∈ M := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      exact hxpN (hNMeq.symm ▸ hxpM)
    have hMeq' : M = Subgroup.closure ((N : Set G) ∪ {xp}) := by
      rw [hM, Subgroup.closure_union, Subgroup.closure_eq]
    have hMcomm : IsMulCommutative M := by
      rw [hMeq']
      apply Subgroup.isMulCommutative_closure
      intro a ha b hb _
      simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
      rcases ha with haN | ha_eq
      · rcases hb with hbN | hb_eq
        · exact Subgroup.mul_comm_of_mem_isMulCommutative N haN hbN
        · rw [hb_eq]; exact Subgroup.mem_centralizer_iff.mp hxp_cent a haN
      · rw [ha_eq]
        rcases hb with hbN | hb_eq
        · exact (Subgroup.mem_centralizer_iff.mp hxp_cent b hbN).symm
        · rw [hb_eq]
    obtain ⟨a, haP, b, hbP, hab⟩ := hna
    haveI : IsMulCommutative P := hMeq ▸ hMcomm
    exact hab (Subgroup.mul_comm_of_mem_isMulCommutative P haP hbP)

end CFSG.OddStandard.SmallF3.FritzII
