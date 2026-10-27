module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Common

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem false_of_inner (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G))
    (hin : ∀ s ∈ N.S, Ch1.InducesInner s N.K) : False := by
  have hf := h.facts2511
  have hzKK := zK_mem_K N h F
  obtain ⟨hzz, -⟩ := z_eq_zK N h F hKt
  obtain ⟨x', hx'P, hx'S, hx'2, hx'c⟩ := exists_xprime N h F hKt
  have htx : x'⁻¹ * t * x' = t * N.z := h.concl2513.1.2 x' hx'P hx'S
  obtain ⟨hRle, hcard, -⟩ := SC_sup_conjugate N h F hx'P hx'S hx'2 hx'c
  have hRcover : ∀ r ∈ centSKz N.S N.K zK, ∃ i : Fin 2, ∃ c ∈ N.SC, r = c * (![1, zK] i) :=
    fun r hr => inner_mem_R_cover N h F hr (hin r (mem_centSKz_iff.mp hr).1)
  have hzR : zK ∈ centSKz N.S N.K zK :=
    mem_centSKz_iff.mpr ⟨(zK_mem_center N hf).1, fun v hv => threeCoreCent_comm hv⟩
  have hg : ∀ i : Fin 2, (![1, zK] i) ∈ centSKz N.S N.K zK := by
    rw [Fin.forall_fin_two]
    exact ⟨by simp, by simpa using hzR⟩
  have hbound : Nat.card ↥(centSKz N.S N.K zK) ≤ 2 * Nat.card N.SC :=
    card_le_mul_of_cover (le_sup_left.trans hRle) ![1, zK] hg hRcover
  have hsq : Nat.card N.SC * Nat.card N.SC ≤ Nat.card ↥(centSKz N.S N.K zK) := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hRle
  have hSC2 : Nat.card N.SC ≤ 2 :=
    Nat.le_of_mul_le_mul_right (hsq.trans hbound) Nat.card_pos
  have hSCeq : N.SC = Subgroup.zpowers t := SC_eq_zpowers N hf hSC2
  obtain ⟨U, HU, E, hpair, hUS, hHU, hU, hESK, hE4, hzE⟩ := exists_pair_E N h F hKt
  refine false_of_normalizes N h F hpair hUS hHU hU hESK hzE hx'P hx'S htx ?_
  intro e he
  have hcm := comm_mem_centSKz N h F hKt (N.SK_le_S (hESK he)) hx'P.2 hx'c
  obtain ⟨i, c, hc, hr⟩ := hRcover _ hcm
  have heq : x'⁻¹ * e * x' = e * (c * ![1, zK] i) := by
    rw [← hr]
    group
  rw [heq]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right he) (Subgroup.mul_mem _ ?_ ?_)
  · rw [hSCeq] at hc
    exact Subgroup.mem_sup_left hc
  · have hzE' : zK ∈ E := hzz ▸ hzE
    have hgE : ∀ j : Fin 2, (![1, zK] j) ∈ Subgroup.zpowers t ⊔ E := by
      rw [Fin.forall_fin_two]
      exact ⟨by simp, by simpa using Subgroup.mem_sup_right hzE'⟩
    exact hgE i

end Config

end CFSG.QuasithinUnique.Unc25K1
