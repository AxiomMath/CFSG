module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem mem_zpowers_t_eq_one_or (h : Hyp G t L) {p : G} (hp : p ∈ zpowers t) :
    p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht : t * t = 1 := t_mul_self h
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem zpowers_t_sq (h : Hyp G t L) {p : G} (hp : p ∈ zpowers t) : p * p = 1 := by
  rcases mem_zpowers_t_eq_one_or h hp with rfl | rfl
  · rw [one_mul]
  · exact t_mul_self h

private theorem isElemAbelian_sup_zpowers_of_le_invCent {E : Subgroup G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hEH : E ≤ invCent t)
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers t) := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    have hat : Commute a t := mem_invCent_iff.mp (hEH ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (hat.zpow_right k).eq
  refine ⟨?_, ?_⟩
  · exact isMulCommutative_sup_of_commute hcomm hE.1 inferInstance
  · intro x hx
    obtain ⟨v, hv, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
    have hv2 : v ^ 2 = 1 := hE.2 v hv
    have hp2 : p ^ 2 = 1 := by simpa [pow_two] using zpowers_t_sq h.hyp hp
    have hvp : Commute v p := hcomm v hv p hp
    rw [hvp.mul_pow 2, hv2, hp2, mul_one]

private theorem card_sup_zpowers_of_t_not_mem_of_le_invCent {E : Subgroup G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hEH : E ≤ invCent t) (htE : t ∉ E) :
    Nat.card (E ⊔ zpowers t : Subgroup G) = 2 * Nat.card E := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    have hat : Commute a t := mem_invCent_iff.mp (hEH ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (hat.zpow_right k).eq
  have hinf : E ⊓ zpowers t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases mem_zpowers_t_eq_one_or h.hyp hx.2 with hx1 | hxt
    · rw [hx1]
    · exact absurd (hxt ▸ hx.1) htE
  have hcard := card_sup_of_commute (P := E) (Q := zpowers t) hcomm hinf
  rw [hcard, Nat.card_zpowers, h.hyp.ord_t, Nat.mul_comm]

private theorem wreathGrp_le_L (h : Ctx t L S x₁ x₂ lam rho tau) :
    wreathGrp x₁ x₂ lam ≤ L := by
  rw [← h.toCtx0.inf_eq]
  exact inf_le_right

private theorem sup_PT_le_centralizer (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ twoCore t) :
    twoCore t ⊔ wreathGrp x₁ x₂ lam ≤
      centralizer ({p} : Set G) ⊓ centralizer ({t} : Set G) := by
  haveI : IsCyclic (twoCore t) := h.hyp.isCyclic
  have hT_le_L : wreathGrp x₁ x₂ lam ≤ L := wreathGrp_le_L h
  have hT_le_inv : wreathGrp x₁ x₂ lam ≤ invCent t :=
    le_trans hT_le_L (L_le_invCent h.hyp)
  have hP_cent_p : twoCore t ≤ centralizer ({p} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : twoCore t) (⟨p, hp⟩ : twoCore t)))
  have hT_cent_p : wreathGrp x₁ x₂ lam ≤ centralizer ({p} : Set G) := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (twoCore_commute h.hyp p hp b (hT_le_L hb)).symm
  have hP_cent_t : twoCore t ≤ centralizer ({t} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (mem_invCent_iff.mp (twoCore_le_invCent t ha))
  have hT_cent_t : wreathGrp x₁ x₂ lam ≤ centralizer ({t} : Set G) := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (mem_invCent_iff.mp (hT_le_inv hb))
  refine le_inf (sup_le hP_cent_p hT_cent_p) (sup_le hP_cent_t hT_cent_t)

theorem le_PT_of_normal_of_t_not_mem (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ twoCore t) (hpt : p * p = t) (hτ : tau * p * tau⁻¹ = p⁻¹) {V : Subgroup G}
    (hV : NormalIn V S) (htV : t ∉ V) : V ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
  have hT_le_L : wreathGrp x₁ x₂ lam ≤ L := wreathGrp_le_L h
  have hK_le_S : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := by
    refine sup_le ?_ ?_
    · rw [h.S_eq]; exact le_sup_left
    · rw [← h.toCtx0.inf_eq]; exact inf_le_left
  have hK_le_PL : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ twoCore t ⊔ L :=
    sup_le le_sup_left (le_trans hT_le_L le_sup_right)
  have hcent := sup_PT_le_centralizer h hp
  have hcent_p : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ centralizer ({p} : Set G) :=
    le_trans hcent inf_le_left
  have hcent_t : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ centralizer ({t} : Set G) :=
    le_trans hcent inf_le_right
  intro v hv
  rcases mem_or_mem_or_mul_mem_of_relIndex_two (K := twoCore t ⊔ wreathGrp x₁ x₂ lam)
    hK_le_S h.index_PT (hV.1 hv) h.tau_mem with h1 | h2 | h3
  · exact h1
  · exact absurd (hK_le_PL h2) h.tau_not_mem
  · set s : G := v * tau with hs_def
    have hsK : s ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam := h3
    have hv_eq : v = s * tau⁻¹ := by rw [hs_def]; group
    have hs_cent_p : s * p = p * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcent_p hsK)
    have hs_cent_t : s * t = t * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcent_t hsK)
    have hpS : p ∈ S := hK_le_S (Subgroup.mem_sup_left hp)
    have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (t_mul_self h.hyp)
    have hcomm_tau_t : Commute tau t :=
      mem_invCent_iff.mp (h.toCtx0.le_invCent h.tau_mem)
    have htau_inv_t : tau⁻¹ * t = t * tau⁻¹ := hcomm_tau_t.inv_left.eq
    have hptau : p * tau⁻¹ * p⁻¹ = t * tau⁻¹ := by
      calc p * tau⁻¹ * p⁻¹ = tau⁻¹ * (tau * p * tau⁻¹) * p⁻¹ := by group
        _ = tau⁻¹ * p⁻¹ * p⁻¹ := by rw [hτ]
        _ = tau⁻¹ * (p * p)⁻¹ := by group
        _ = tau⁻¹ * t⁻¹ := by rw [hpt]
        _ = tau⁻¹ * t := by rw [ht_inv]
        _ = t * tau⁻¹ := htau_inv_t
    have hpv : p * v * p⁻¹ = t * v := by
      calc p * v * p⁻¹ = p * (s * tau⁻¹) * p⁻¹ := by rw [hv_eq]
        _ = (p * s) * (tau⁻¹ * p⁻¹) := by group
        _ = (s * p) * (tau⁻¹ * p⁻¹) := by rw [← hs_cent_p]
        _ = s * (p * tau⁻¹ * p⁻¹) := by group
        _ = s * (t * tau⁻¹) := by rw [hptau]
        _ = (s * t) * tau⁻¹ := by group
        _ = (t * s) * tau⁻¹ := by rw [hs_cent_t]
        _ = t * (s * tau⁻¹) := by group
        _ = t * v := by rw [hv_eq]
    have hconjV : p * v * p⁻¹ ∈ V := hV.2 p hpS v hv
    have htv : t = (p * v * p⁻¹) * v⁻¹ := by rw [hpv]; group
    exfalso
    exact htV (by rw [htv]; exact V.mul_mem hconjV (V.inv_mem hv))

theorem false_of_elemAbelian_eight_le_PT (h : Ctx t L S x₁ x₂ lam rho tau) {E : Subgroup G}
    (hEPT : E ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEc : Nat.card E = 8) (htE : t ∉ E) : False := by
  have hT_le_inv : wreathGrp x₁ x₂ lam ≤ invCent t :=
    le_trans (wreathGrp_le_L h) (L_le_invCent h.hyp)
  have hE_le_inv : E ≤ invCent t :=
    le_trans hEPT (sup_le (twoCore_le_invCent t) hT_le_inv)
  have hYe : CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers t) :=
    isElemAbelian_sup_zpowers_of_le_invCent h hE_le_inv hEe
  have hYc : Nat.card (E ⊔ zpowers t : Subgroup G) = 2 * Nat.card E :=
    card_sup_zpowers_of_t_not_mem_of_le_invCent h hE_le_inv htE
  have hY_le_PT : E ⊔ zpowers t ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
    sup_le hEPT (le_trans (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore) le_sup_left)
  have hle := h.m2_PT (E ⊔ zpowers t) hY_le_PT hYe
  rw [hYc, hEc] at hle
  omega

theorem false_of_inf_index_two (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ twoCore t) (hpt : p * p = t) {𝒮 E : Subgroup G} (hS𝒮 : S ≤ 𝒮)
    (hC : invCent t ⊓ 𝒮 = S) (hE𝒮 : E ≤ 𝒮) (hEn : (E.subgroupOf 𝒮).Normal)
    (hEe : CFSG.Open.IsElemAbelian 2 E) (hES : ¬ E ≤ S)
    (hV : E ⊓ S ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam) (hidx : (E ⊓ S).relIndex E = 2) :
    False := by
  have hK_le_S : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := by
    refine sup_le ?_ ?_
    · rw [h.S_eq]; exact le_sup_left
    · rw [← h.toCtx0.inf_eq]; exact inf_le_left
  have hpS : p ∈ S := hK_le_S (Subgroup.mem_sup_left hp)
  have hp𝒮 : p ∈ 𝒮 := hS𝒮 hpS
  have hcent_p : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ centralizer ({p} : Set G) :=
    le_trans (sup_PT_le_centralizer h hp) inf_le_left
  have hV_cent : E ⊓ S ≤ centralizer ({p} : Set G) := le_trans hV hcent_p
  have hconjE : ∀ e ∈ E, p * e * p⁻¹ ∈ E := by
    intro e he
    have hn : (⟨e, hE𝒮 he⟩ : ↥𝒮) ∈ E.subgroupOf 𝒮 := by
      rw [Subgroup.mem_subgroupOf]; exact he
    have h := hEn.conj_mem (⟨e, hE𝒮 he⟩ : ↥𝒮) hn (⟨p, hp𝒮⟩ : ↥𝒮)
    simpa using Subgroup.mem_subgroupOf.mp h
  have key : ∀ e ∈ E, ∃ v ∈ E ⊓ S, p * e * p⁻¹ = e * v := by
    intro e he
    by_cases heV : e ∈ E ⊓ S
    · refine ⟨1, (E ⊓ S).one_mem, ?_⟩
      have hec : Commute e p := Subgroup.mem_centralizer_singleton_iff.mp (hV_cent heV)
      rw [← hec.eq, mul_inv_cancel_right, mul_one]
    · have heV' : e⁻¹ ∉ E ⊓ S := by
        intro h
        exact heV (by simpa using (E ⊓ S).inv_mem h)
      have hwE : p * e * p⁻¹ ∈ E := hconjE e he
      have hwV : p * e * p⁻¹ ∉ E ⊓ S := by
        intro hw
        apply heV
        have hwcomm : Commute (p * e * p⁻¹) p :=
          Subgroup.mem_centralizer_singleton_iff.mp (hV_cent hw)
        have hthis : e = p * e * p⁻¹ := by
          calc e = p⁻¹ * (p * e * p⁻¹) * p := by group
            _ = p * e * p⁻¹ := hwcomm.symm.inv_mul_cancel
        rw [hthis]; exact hw
      rcases mem_or_mem_or_mul_mem_of_relIndex_two (K := E ⊓ S) (S := E)
        inf_le_left hidx (E.inv_mem he) hwE with h1 | h2 | h3
      · exact absurd h1 heV'
      · exact absurd h2 hwV
      · exact ⟨e⁻¹ * (p * e * p⁻¹), h3, by group⟩
  have hcent_E : ∀ e ∈ E, t * e * t⁻¹ = e := by
    intro e he
    obtain ⟨v, hvV, hv⟩ := key e he
    have hvE : v ∈ E := (inf_le_left : E ⊓ S ≤ E) hvV
    have hvv : v * v = 1 := by simpa [pow_two] using hEe.2 v hvE
    have hvcent : p * v * p⁻¹ = v := by
      have hcomm : Commute v p := Subgroup.mem_centralizer_singleton_iff.mp (hV_cent hvV)
      rw [hcomm.symm.eq, mul_inv_cancel_right]
    calc t * e * t⁻¹ = p * p * e * p⁻¹ * p⁻¹ := by
          rw [← hpt, mul_inv_rev]; group
      _ = p * (p * e * p⁻¹) * p⁻¹ := by group
      _ = p * (e * v) * p⁻¹ := by rw [hv]
      _ = (p * e * p⁻¹) * (p * v * p⁻¹) := by group
      _ = (e * v) * v := by rw [hv, hvcent]
      _ = e := by rw [mul_assoc, hvv, mul_one]
  have hE_le_inv : E ≤ invCent t := by
    intro e he
    rw [mem_invCent_iff]
    have h := hcent_E e he
    calc e * t = (t * e * t⁻¹) * t := by rw [h]
      _ = t * e := by group
  have hES' : E ≤ S := by
    intro e he
    have hthis : e ∈ invCent t ⊓ 𝒮 := ⟨hE_le_inv he, hE𝒮 he⟩
    rw [hC] at hthis
    exact hthis
  exact hES hES'

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
