module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L288
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen6

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {L J Py P : Subgroup G} {a w : G}

omit [Finite G] in
theorem mem_normalizer_inf_of_invol {u : G} {Q E : Subgroup G} (huQ : u ∈ Q)
    (huE : u ∈ normalizer (E : Set G)) (hu : u * u = 1) :
    u ∈ normalizer ((Q ⊓ E : Subgroup G) : Set G) := by
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h1 : ∀ r ∈ Q ⊓ E, u * r * u⁻¹ ∈ Q ⊓ E := fun r hr =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem huQ hr.1) (inv_mem huQ),
      (mem_normalizer_iff.mp huE r).mp hr.2⟩
  rw [mem_normalizer_iff]
  intro r
  refine ⟨h1 r, fun h => ?_⟩
  have := h1 _ h
  rwa [hinv, show u * (u * r * u) * u = (u * u) * r * (u * u) by group, hu, one_mul, mul_one]
    at this

theorem lemma_28_9_c (h44 : II4_44) (h327 : IG_3_27) (hs : Setup G x y L J a Py P w)
    {H : Subgroup G} (hH : IsIntrinsic (w * (a⁻¹ * w * a)) H) : y * x ∈ normalizer (H : Set G) := by
  have hFB := hs.hFB
  have hcfg := hFB.cfg
  have hx1 := mul_self_eq_one_of_orderOf_eq_two hcfg.hx
  have hy1 := mul_self_eq_one_of_orderOf_eq_two hcfg.hy
  obtain ⟨u, hu⟩ : ∃ u : G, u = w * (a⁻¹ * w * a) := ⟨_, rfl⟩
  rw [← hu] at hH
  have hu1 : u * u = 1 := by rw [hu]; exact hs.huu
  have hu2 : orderOf u = 2 := by rw [hu]; exact hs.hu2 h44
  have huy : u * y = y * u := by rw [hu]; exact mem_centralizer_singleton_iff.mp hs.hu_cy
  have hyu : y * u = u * y := huy.symm
  have hunJ : u ∉ normalizer (J : Set G) := by rw [hu]; exact hs.hu_not_mem_normalizer_J
  have huP : u ∈ P := by rw [hu]; exact hs.hu_P
  have hJ' : IsIntrinsic y (conjugate J u) := isIntrinsic_conjugate hyu hcfg.hJ
  have hJ'cSec : conjugate J u ≤ cSec J := conjugate_le_cSec hyu hcfg.hJ hunJ
  obtain ⟨m, hm2, hm, hyp⟩ := hFB.exists_pow
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hyp' : y = a ^ (2 ^ (n + 1)) := by
    rw [show n + 2 - 1 = n + 1 by omega] at hyp
    exact hyp
  have ha'mem : u⁻¹ * a * u ∈ conjugate J u := by
    rw [mem_conjugate_iff', show u * (u⁻¹ * a * u) * u⁻¹ = a by group]
    exact hFB.ha
  have ha'P : u⁻¹ * a * u ∈ P := mul_mem (mul_mem (inv_mem huP) hs.haP) huP
  have haa' : a * (u⁻¹ * a * u) = (u⁻¹ * a * u) * a := by
    have hcs := hJ'cSec ha'mem
    have h1 : ⁅a, u⁻¹ * a * u⁆ ∈ pPrimeCoreOf 2 J := hcs.2.2 a hFB.ha
    have h2 : ⁅a, u⁻¹ * a * u⁆ ∈ P := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hs.haP ha'P) (inv_mem hs.haP)) (inv_mem ha'P)
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (eq_one_of_mem_pPrimeCoreOf h1 (isPGroup_zpowers_of_mem hs.hP.2.1 h2))
  set b : G := w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a) with hbdef
  have hbab : b = (u⁻¹ * a * u)⁻¹ * a := by
    have h := hs.hb_formula
    rw [← hu] at h
    rw [hbdef, ← h]
    group
  have hbL : b ∈ L := hs.hb_mem_L
  have hcomm : Commute (u⁻¹ * a * u) a := haa'.symm
  have hyuinv : u⁻¹ * y * u = y := by
    calc u⁻¹ * y * u = u⁻¹ * (y * u) := by group
      _ = u⁻¹ * (u * y) := by rw [hyu]
      _ = y := by group
  have ha'N : (u⁻¹ * a * u) ^ (2 ^ (n + 1)) = y := by
    have h := conj_pow (a := u⁻¹) (b := a) (i := 2 ^ (n + 1))
    rw [inv_inv] at h
    rw [h, ← hyp']
    exact hyuinv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcommb : Commute (u⁻¹ * a * u)⁻¹ a := hcomm.inv_left
  have hbN : b ^ (2 ^ (n + 1)) = 1 := by
    rw [hbab, hcommb.mul_pow, inv_pow, ha'N, ← hyp']
    group
  have hdvdn : 2 ^ n ∣ orderOf a := by
    rw [hm]
    exact pow_dvd_pow 2 (by omega)
  have hz4 : orderOf (a ^ (2 ^ n)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvdn, hm, show 2 ^ (n + 2) = 2 ^ n * 4 by ring]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  have hbn : ¬ b ^ (2 ^ n) = 1 := by
    intro h1
    have h2 : a ^ (2 ^ n) = (u⁻¹ * a * u) ^ (2 ^ n) := by
      rw [hbab, hcommb.mul_pow, inv_pow] at h1
      exact (inv_mul_eq_one.mp h1).symm
    have hzJ : a ^ (2 ^ n) ∈ J := pow_mem hFB.ha _
    have hzJ' : a ^ (2 ^ n) ∈ conjugate J u := by
      rw [h2]
      exact pow_mem ha'mem _
    have hz2 : IsPGroup 2 ↥(zpowers (a ^ (2 ^ n))) :=
      isPGroup_zpowers_of_mem hs.hP.2.1 (pow_mem hs.haP _)
    rcases eq_one_or_eq_of_mem_inf_conjugate h44 hcfg.simple hcfg.hy hyu hcfg.hJ hunJ hzJ hzJ'
      hz2 with h | h
    · rw [h] at hz4
      simp at hz4
    · rw [h, hcfg.hy] at hz4
      norm_num at hz4
  have hbord : orderOf b = 2 ^ (n + 1) := orderOf_eq_prime_pow hbn hbN
  have hbx : b ^ (2 ^ n) = x := by
    have hinv : orderOf (b ^ (2 ^ n)) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hbord]; exact pow_dvd_pow 2 (by omega)),
        hbord, show 2 ^ (n + 1) = 2 ^ n * 2 by ring]
      exact Nat.mul_div_cancel_left 2 (by positivity)
    exact hcfg.hL.eq_of_involution hcfg.hx (pow_mem hbL _) hinv
  have hmain : (a * (u⁻¹ * a * u)) ^ (2 ^ n) = y * x := by
    have hB : b ^ (2 ^ n) = ((u⁻¹ * a * u) ^ (2 ^ n))⁻¹ * a ^ (2 ^ n) := by
      rw [hbab, hcommb.mul_pow, inv_pow]
    have h1 := mul_eq_of_inv_mul_eq (a ^ (2 ^ n)) ((u⁻¹ * a * u) ^ (2 ^ n)) x hx1
      (hB.symm.trans hbx)
    have hcomm' : Commute a (u⁻¹ * a * u) := haa'
    rw [hcomm'.mul_pow, h1, ← pow_add, ← two_mul, ← pow_succ', ← hyp']
  obtain ⟨hI', -, -, h4'⟩ := h327 G hcfg.simple y u hcfg.hy hu2 hyu J hcfg.hJ hunJ
  have huE' : u ∈ normalizer ((J ⊔ conjugate J u : Subgroup G) : Set G) :=
    mem_normalizer_sup_conjugate hu1 J
  have hE'H' : J ⊔ conjugate J u ≤ (J ⊔ conjugate J u) ⊔ zpowers u := le_sup_left
  have hH'N : (J ⊔ conjugate J u) ⊔ zpowers u ≤ normalizer ((J ⊔ conjugate J u : Subgroup G) : Set G) :=
    sup_le (fun z hz => le_normalizer hz) (zpowers_le.mpr huE')
  have hAP : closure ({a, u} : Set G) ≤ P := by
    rw [closure_le]
    rintro g (rfl | hg)
    · exact hs.haP
    · rw [Set.mem_singleton_iff.mp hg]
      exact huP
  have hAp : IsPGroup 2 ↥(closure ({a, u} : Set G)) := hs.hP.2.1.to_le hAP
  have haE' : a ∈ J ⊔ conjugate J u := Subgroup.mem_sup_left hFB.ha
  have hAH' : closure ({a, u} : Set G) ≤ (J ⊔ conjugate J u) ⊔ zpowers u := by
    rw [closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.mem_sup_left haE'
    · rw [Set.mem_singleton_iff.mp hg]
      exact Subgroup.mem_sup_right (mem_zpowers u)
  obtain ⟨Q, hQ, hAQ⟩ := exists_isSylow2In_of_le hAp hAH'
  have hT' : IsSylow2In (Q ⊓ (J ⊔ conjugate J u)) (J ⊔ conjugate J u) :=
    isSylow2In_inf_normal hQ hE'H' hH'N
  have huQ : u ∈ Q := hAQ (subset_closure (Or.inr rfl))
  have haQ : a ∈ Q := hAQ (subset_closure (Or.inl rfl))
  have huT' := mem_normalizer_inf_of_invol huQ huE' hu1
  obtain ⟨S₀, hS₀, hS₀eq⟩ := h4' (Q ⊓ (J ⊔ conjugate J u)) hT' huT'
  have haI' : a * (u⁻¹ * a * u) ∈ IDiag u J := by
    have h1 : a * (u⁻¹ * a * u) ∈ (S₀ : Set G) := by
      rw [hS₀eq]
      exact ⟨a, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨haQ, haE'⟩, hFB.ha⟩, rfl⟩
    exact hS₀.1 h1
  have hyxI : y * x ∈ IDiag u J := by
    have := pow_mem haI' (2 ^ n)
    rwa [hmain] at this
  have hbal := le_pLayerOf_of_isPCompIn_inf (s := y) (t := u) hcfg.hy
    (mem_centralizer_singleton_iff.mpr hyu) hI'
  exact pLayerOf_le_normalizer hH.1 (hbal hyxI)

theorem lemma_28_9_b (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut) (h327 : IG_3_27)
    (hs : Setup G x y L J a Py P w) : ∃ g : G, g⁻¹ * y * g = w * (a⁻¹ * w * a) := by
  have hFB := hs.hFB
  have hcfg := hFB.cfg
  have hx1 := mul_self_eq_one_of_orderOf_eq_two hcfg.hx
  have hy1 := mul_self_eq_one_of_orderOf_eq_two hcfg.hy
  obtain ⟨u, hu⟩ : ∃ u : G, u = w * (a⁻¹ * w * a) := ⟨_, rfl⟩
  rw [← hu]
  have hu1 : u * u = 1 := by rw [hu]; exact hs.huu
  have hu2 : orderOf u = 2 := by rw [hu]; exact hs.hu2 h44
  have huy : u * y = y * u := by rw [hu]; exact mem_centralizer_singleton_iff.mp hs.hu_cy
  have huN : u ∈ normalizer (L : Set G) := by rw [hu]; exact hs.hu_N
  have h88 := lemma_28_8_L hBal h44 hAut h327 hs
  have hay : y * a = a * y := hs.hay.symm
  have h88' : InducesInner y (conjugate L a) ∧ y ∉ cSec (conjugate L a) :=
    ⟨(inducesInner_conjugate_iff hay).mpr h88.1, fun h => h88.2 (by
      have := mem_cSec_conjugate.mp h
      rwa [show a * y * a⁻¹ = y by rw [hs.hay]; group] at this)⟩
  obtain ⟨g, hg1, hg2⟩ := hFB.swap hBal h44 hAut h327
  have hJ' : IsIntrinsic y (conjugate J u) := isIntrinsic_conjugate huy.symm hcfg.hJ
  have hxJJ : x ∈ J ⊔ conjugate J u := by
    have hb : x ∈ zpowers (w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a)) := hs.hx_mem_zpowers_b
    rw [← hs.hb_formula, ← hu] at hb
    have hmem : u⁻¹ * a⁻¹ * u * a ∈ J ⊔ conjugate J u := by
      refine mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hFB.ha)
      rw [mem_conjugate_iff', show u * (u⁻¹ * a⁻¹ * u) * u⁻¹ = a⁻¹ by group]
      exact inv_mem hFB.ha
    exact (zpowers_le.mpr hmem) hb
  have hL₁ : IsIntrinsic x (J.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h := isIntrinsic_map_conj hcfg.hJ g⁻¹
    rwa [show g⁻¹ * y * g⁻¹⁻¹ = x by rw [inv_inv]; exact hg2] at h
  have hL₂ : IsIntrinsic x ((conjugate J u).map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h := isIntrinsic_map_conj hJ' g⁻¹
    rwa [show g⁻¹ * y * g⁻¹⁻¹ = x by rw [inv_inv]; exact hg2] at h
  have hyL₁₂ : y ∈ J.map (MulAut.conj g⁻¹).toMonoidHom ⊔
      (conjugate J u).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← Subgroup.map_sup]
    refine ⟨x, hxJJ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hg1
  have hL' : IsIntrinsic x (conjugate L a) := hs.hL'
  have hLne : L ≠ conjugate L a := (conjugate_ne_of_not_mem_normalizer hFB.haL).symm
  have hyE : y ∈ L ⊔ conjugate L a :=
    mem_sup_of_not_mem_cSec hL₁ hL₂ hcfg.hL hL' hLne hyL₁₂ h88.2 h88'.2
  have huE : u ∈ L ⊔ conjugate L a := by
    rw [hu]
    exact mul_mem (Subgroup.mem_sup_left hs.hwP.2) (Subgroup.mem_sup_right hs.hwa_mem)
  have hw4' : orderOf (a⁻¹ * w * a) = 4 := by
    have := orderOf_conj_eq a⁻¹ w
    rw [inv_inv] at this
    rw [this]
    exact hs.hw4
  have hwcs : w ∈ cSec (conjugate L a) := le_cSec_of_ne hcfg.hL.1 hL'.1 hLne hs.hwP.2
  have hw'cs : a⁻¹ * w * a ∈ cSec L := hs.hL'cSec hs.hwa_mem
  have hdL := diag_inner h44 hAut hcfg.simple hcfg.hx hcfg.hL hs.hwP.2 hs.hw4
    (isPGroup_zpowers_of_mem hs.hP.2.1 hs.hwP.1) hw'cs
  have hdL' := diag_inner h44 hAut hcfg.simple hcfg.hx hL' hs.hwa_mem hw4'
    (isPGroup_zpowers_of_mem hs.hP.2.1 hs.hwa_P) hwcs
  rw [hs.hwwa.symm, ← hu] at hdL'
  rw [← hu] at hdL
  obtain ⟨r, hr⟩ := exists_conj_of_diag h44 hAut hcfg.simple hcfg.hx hcfg.hL hL' hLne hy1 hu1
    hyE huE ⟨h88.1, h88.2⟩ ⟨h88'.1, h88'.2⟩ ⟨hdL.1, hdL.2.1⟩ ⟨hdL'.1, hdL'.2.1⟩
  rcases hr with hr | hr
  · exact ⟨r, hr⟩
  · obtain ⟨S', hS', hS'n⟩ := exists_invariant_sylow
      (isPGroup_zpowers_of_mul_self_eq_one hu1) (zpowers_le.mpr huN)
    have hS'u : ∀ z ∈ S', u * z * u⁻¹ ∈ S' := fun z hz =>
      (mem_normalizer_iff.mp (hS'n (mem_zpowers u)) z).mp hz
    obtain ⟨c, -, -, hc⟩ :=
      fusion_first h44 hAut hcfg.simple hcfg.hx hcfg.hL hu2 huN hdL.2.2 hS' hS'u
    refine ⟨r * c⁻¹, ?_⟩
    calc (r * c⁻¹)⁻¹ * y * (r * c⁻¹) = c * (r⁻¹ * y * r) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hr]
      _ = c * (c⁻¹ * u * c) * c⁻¹ := by rw [hc]
      _ = u := by group

end CFSG.GH74.GLS.Stage1.Thm2.Recip
