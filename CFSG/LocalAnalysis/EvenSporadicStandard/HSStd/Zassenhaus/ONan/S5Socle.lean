module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5Setting
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5

open Subgroup CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

namespace Setting

variable {Y : Type*} [Group Y] [Finite Y] {P : Subgroup Y}

private lemma map_conj_map_conj (J : Subgroup Y) (g h : Y) :
    (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      J.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  congr 1

private lemma exists_mul_ne_of_not_isMulCommutative {H : Type*} [Mul H]
    (h : ¬ IsMulCommutative H) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact h (isMulCommutative_iff.mpr hcon)

private lemma exists_mem_mul_ne_of_not_isMulCommutative {J : Subgroup Y}
    (h : ¬ IsMulCommutative J) : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_not_isMulCommutative h
  exact ⟨a, a.2, b, b.2, fun hh => hab (Subtype.ext hh)⟩

theorem three_dvd_of_mem_lcalOf (h : Setting Y P) {J : Subgroup Y} (hJ : J ∈ lcalOf Y) :
    3 ∣ Nat.card J := by
  classical
  by_contra h3
  have hJcop : Nat.Coprime 3 (Nat.card J) := Nat.prime_three.coprime_iff_not_dvd.mpr h3
  have hJnc : ¬ IsMulCommutative J := hJ.2.2
  let S : Set (Subgroup Y) := {K | ∃ g : Y, K = J.map (MulAut.conj g).toMonoidHom}
  let M : Subgroup Y := sSup S
  have hD0 : IsDirectProduct (lcalOf Y) (CFSG.layer Y) :=
    isDirectProduct_lcalOf_layer h.solvableRadical_eq_bot
  have hSmem : S ⊆ lcalOf Y := by
    rintro K ⟨g, rfl⟩
    exact (map_mem_lcalOf_iff (MulAut.conj g)).mpr hJ
  have hD : IsDirectProduct S M :=
    ⟨fun K hK L hL hne => hD0.commute K (hSmem hK) L (hSmem hL) hne,
      hD0.indep.mono hSmem, rfl⟩
  have hconj : ∀ a : Y, ∀ K ∈ S, K.map (MulAut.conj a).toMonoidHom ∈ S := by
    rintro a K ⟨g, rfl⟩
    exact ⟨a * g, map_conj_map_conj J g a⟩
  have hMnormal : M.Normal :=
    ⟨fun n hn a => hD.conj_mem (hconj a) hn⟩
  have hMcop : Nat.Coprime 3 (Nat.card M) := by
    obtain ⟨e, -⟩ := hD.exists_mulEquiv
    haveI : Fintype S := Fintype.ofFinite S
    have hcard : Nat.card M = ∏ K : S, Nat.card (K : Subgroup Y) := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
    rw [hcard]
    refine Nat.Coprime.prod_right fun K _ => ?_
    obtain ⟨g, hg⟩ := K.2
    rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hJcop
  have hMbot : M = ⊥ := h.eq_bot_of_normal_of_coprime hMnormal hMcop
  have hJS : J ∈ S := ⟨1, by ext x; simp [MulAut.conj_apply]⟩
  have hJbot : J = ⊥ := by
    rw [eq_bot_iff]
    exact (hD.le hJS).trans (le_of_eq hMbot)
  haveI : Subsingleton J := by rw [hJbot]; infer_instance
  exact hJnc (isMulCommutative_iff.mpr fun a b => Subsingleton.elim (a * b) (b * a))

theorem lcalOf_subsingleton (h : Setting Y P) {J₁ J₂ : Subgroup Y} (h₁ : J₁ ∈ lcalOf Y)
    (h₂ : J₂ ∈ lcalOf Y) : J₁ = J₂ := by
  classical
  by_contra hne
  have hD0 : IsDirectProduct (lcalOf Y) (CFSG.layer Y) :=
    isDirectProduct_lcalOf_layer h.solvableRadical_eq_bot
  have h3₁ : 3 ∣ Nat.card J₁ := three_dvd_of_mem_lcalOf h h₁
  have h3₂ : 3 ∣ Nat.card J₂ := three_dvd_of_mem_lcalOf h h₂
  obtain ⟨x₁N, hx₁N⟩ : ∃ x : J₁, orderOf x = 3 := by
    haveI : Fintype J₁ := Fintype.ofFinite J₁
    exact exists_prime_orderOf_dvd_card (G := J₁) 3 (by rwa [Nat.card_eq_fintype_card] at h3₁)
  obtain ⟨x₂N, hx₂N⟩ : ∃ x : J₂, orderOf x = 3 := by
    haveI : Fintype J₂ := Fintype.ofFinite J₂
    exact exists_prime_orderOf_dvd_card (G := J₂) 3 (by rwa [Nat.card_eq_fintype_card] at h3₂)
  have hx₁ : orderOf (x₁N : Y) = 3 := by rw [Subgroup.orderOf_coe, hx₁N]
  have hx₂ : orderOf (x₂N : Y) = 3 := by rw [Subgroup.orderOf_coe, hx₂N]
  have hx₁J₁ : (x₁N : Y) ∈ J₁ := x₁N.2
  have hx₂J₂ : (x₂N : Y) ∈ J₂ := x₂N.2
  have hcomm : Commute (x₁N : Y) (x₂N : Y) :=
    hD0.commute J₁ h₁ J₂ h₂ hne (x₁N : Y) hx₁J₁ (x₂N : Y) hx₂J₂
  let b : Y := (x₁N : Y) * (x₂N : Y)
  have hb : b = (x₁N : Y) * (x₂N : Y) := rfl
  have hb3 : b ^ 3 = 1 := by
    have h1 : (x₁N : Y) ^ 3 = 1 := by rw [← hx₁]; exact pow_orderOf_eq_one (x₁N : Y)
    have h2 : (x₂N : Y) ^ 3 = 1 := by rw [← hx₂]; exact pow_orderOf_eq_one (x₂N : Y)
    rw [hb, hcomm.mul_pow 3, h1, h2, mul_one]
  have hbne : b ≠ 1 := by
    intro hb1
    have hx1eq : (x₁N : Y) = b * (x₂N : Y)⁻¹ := by rw [hb]; group
    have hx1mem2 : (x₁N : Y) ∈ J₂ := by
      rw [hx1eq, hb1, one_mul]
      exact inv_mem hx₂J₂
    have hdisj : J₁ ⊓ sSup (lcalOf Y \ {J₁}) = ⊥ := disjoint_iff.mp (hD0.indep h₁)
    have hx1bot : (x₁N : Y) ∈ (⊥ : Subgroup Y) := by
      have hle : J₂ ≤ sSup (lcalOf Y \ {J₁}) := le_sSup ⟨h₂, fun hh => hne hh.symm⟩
      have hmem : (x₁N : Y) ∈ J₁ ⊓ sSup (lcalOf Y \ {J₁}) :=
        Subgroup.mem_inf.mpr ⟨hx₁J₁, hle hx1mem2⟩
      rwa [hdisj] at hmem
    have : (x₁N : Y) = 1 := Subgroup.mem_bot.mp hx1bot
    have : orderOf (x₁N : Y) = 1 := by rw [this, orderOf_one]
    rw [hx₁] at this; norm_num at this
  have hb_order : orderOf b = 3 := orderOf_eq_prime hb3 hbne
  obtain ⟨K, hKC, hKsimple, hKnc⟩ :=
    exists_simple_le_of_mulEquiv (h.centralizer_equiv hb_order).some
  have hKnc' : ¬ IsMulCommutative K := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hKnc
    exact hxy (congrArg Subtype.val ((isMulCommutative_iff.mp hc) (⟨x, hx⟩ : K) ⟨y, hy⟩))
  have hkey : ∀ k ∈ K, k * (x₁N : Y) * k⁻¹ = b * (k * (x₂N : Y) * k⁻¹)⁻¹ := by
    intro k hk
    have hkb : k * b * k⁻¹ = b := by
      have hcomm' := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
      calc k * b * k⁻¹ = (k * b) * k⁻¹ := rfl
        _ = (b * k) * k⁻¹ := by rw [hcomm']
        _ = b := by group
    have hx1eq : (x₁N : Y) = b * (x₂N : Y)⁻¹ := by rw [hb]; group
    calc k * (x₁N : Y) * k⁻¹ = k * (b * (x₂N : Y)⁻¹) * k⁻¹ := by rw [hx1eq]
      _ = (k * b * k⁻¹) * (k * (x₂N : Y) * k⁻¹)⁻¹ := by group
      _ = b * (k * (x₂N : Y) * k⁻¹)⁻¹ := by rw [hkb]
  have hkey₂ : ∀ k ∈ K, k * (x₂N : Y) * k⁻¹ = b * (k * (x₁N : Y) * k⁻¹)⁻¹ := by
    intro k hk
    have hkb : k * b * k⁻¹ = b := by
      have hcomm' := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
      calc k * b * k⁻¹ = (k * b) * k⁻¹ := rfl
        _ = (b * k) * k⁻¹ := by rw [hcomm']
        _ = b := by group
    have hx2eq : (x₂N : Y) = b * (x₁N : Y)⁻¹ := by rw [hb, hcomm.eq]; group
    calc k * (x₂N : Y) * k⁻¹ = k * (b * (x₁N : Y)⁻¹) * k⁻¹ := by rw [hx2eq]
      _ = (k * b * k⁻¹) * (k * (x₁N : Y) * k⁻¹)⁻¹ := by group
      _ = b * (k * (x₁N : Y) * k⁻¹)⁻¹ := by rw [hkb]
  have hperm₁ : ∀ k : K, J₁.map (MulAut.conj (k : Y)).toMonoidHom = J₁ ∨
      J₁.map (MulAut.conj (k : Y)).toMonoidHom = J₂ := by
    intro k
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    set L : Subgroup Y := J₁.map (MulAut.conj (k : Y)).toMonoidHom with hL
    have hLmem : L ∈ lcalOf Y := by
      rw [hL]; exact (map_mem_lcalOf_iff (MulAut.conj (k : Y))).mpr h₁
    have hLx₁ : (k : Y) * (x₁N : Y) * (k : Y)⁻¹ ∈ L := by
      rw [hL]; exact ⟨(x₁N : Y), hx₁J₁, by simp [MulAut.conj_apply]⟩
    have hb_mem : b ∈ sSup (lcalOf Y \ {L}) := by
      have hJ₁ : J₁ ∈ lcalOf Y \ {L} := ⟨h₁, fun hh => hne1 hh.symm⟩
      have hJ₂ : J₂ ∈ lcalOf Y \ {L} := ⟨h₂, fun hh => hne2 hh.symm⟩
      have h1 : (x₁N : Y) ∈ sSup (lcalOf Y \ {L}) := le_sSup hJ₁ hx₁J₁
      have h2 : (x₂N : Y) ∈ sSup (lcalOf Y \ {L}) := le_sSup hJ₂ hx₂J₂
      have := mul_mem h1 h2
      simpa [hb] using this
    have hx₂_mem : (k : Y) * (x₂N : Y) * (k : Y)⁻¹ ∈ sSup (lcalOf Y \ {L}) := by
      have hψmem : J₂.map (MulAut.conj (k : Y)).toMonoidHom ∈ lcalOf Y \ {L} := by
        refine ⟨(map_mem_lcalOf_iff (MulAut.conj (k : Y))).mpr h₂, ?_⟩
        intro hh
        exact hne (Subgroup.map_injective (MulAut.conj (k : Y)).injective (hh.trans hL)).symm
      exact le_sSup hψmem ⟨(x₂N : Y), hx₂J₂, by simp [MulAut.conj_apply]⟩
    have hR : (k : Y) * (x₁N : Y) * (k : Y)⁻¹ ∈ sSup (lcalOf Y \ {L}) := by
      rw [hkey (k : Y) k.2]
      exact mul_mem hb_mem (inv_mem hx₂_mem)
    have hxbot : (k : Y) * (x₁N : Y) * (k : Y)⁻¹ ∈ (⊥ : Subgroup Y) := by
      have hdisj := hD0.indep hLmem
      rw [disjoint_iff] at hdisj
      rw [← hdisj]
      exact ⟨hLx₁, hR⟩
    have hx1one : (x₁N : Y) = 1 := by
      have h1 : (k : Y) * (x₁N : Y) * (k : Y)⁻¹ = 1 := Subgroup.mem_bot.mp hxbot
      calc (x₁N : Y) = (k : Y)⁻¹ * ((k : Y) * (x₁N : Y) * (k : Y)⁻¹) * (k : Y) := by group
        _ = 1 := by rw [h1]; group
    have hx1ne : (x₁N : Y) ≠ 1 := by
      intro hh; rw [hh, orderOf_one] at hx₁; norm_num at hx₁
    exact hx1ne hx1one
  have hperm₂ : ∀ k : K, J₂.map (MulAut.conj (k : Y)).toMonoidHom = J₁ ∨
      J₂.map (MulAut.conj (k : Y)).toMonoidHom = J₂ := by
    intro k
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    set L : Subgroup Y := J₂.map (MulAut.conj (k : Y)).toMonoidHom with hL
    have hLmem : L ∈ lcalOf Y := by
      rw [hL]; exact (map_mem_lcalOf_iff (MulAut.conj (k : Y))).mpr h₂
    have hLx₂ : (k : Y) * (x₂N : Y) * (k : Y)⁻¹ ∈ L := by
      rw [hL]; exact ⟨(x₂N : Y), hx₂J₂, by simp [MulAut.conj_apply]⟩
    have hb_mem : b ∈ sSup (lcalOf Y \ {L}) := by
      have hJ₁ : J₁ ∈ lcalOf Y \ {L} := ⟨h₁, fun hh => hne1 hh.symm⟩
      have hJ₂ : J₂ ∈ lcalOf Y \ {L} := ⟨h₂, fun hh => hne2 hh.symm⟩
      have h1 : (x₁N : Y) ∈ sSup (lcalOf Y \ {L}) := le_sSup hJ₁ hx₁J₁
      have h2 : (x₂N : Y) ∈ sSup (lcalOf Y \ {L}) := le_sSup hJ₂ hx₂J₂
      have := mul_mem h1 h2
      simpa [hb] using this
    have hx₁_mem : (k : Y) * (x₁N : Y) * (k : Y)⁻¹ ∈ sSup (lcalOf Y \ {L}) := by
      have hφmem : J₁.map (MulAut.conj (k : Y)).toMonoidHom ∈ lcalOf Y \ {L} := by
        refine ⟨(map_mem_lcalOf_iff (MulAut.conj (k : Y))).mpr h₁, ?_⟩
        intro hh
        exact hne (Subgroup.map_injective (MulAut.conj (k : Y)).injective (hh.trans hL))
      exact le_sSup hφmem ⟨(x₁N : Y), hx₁J₁, by simp [MulAut.conj_apply]⟩
    have hR : (k : Y) * (x₂N : Y) * (k : Y)⁻¹ ∈ sSup (lcalOf Y \ {L}) := by
      rw [hkey₂ (k : Y) k.2]
      exact mul_mem hb_mem (inv_mem hx₁_mem)
    have hxbot : (k : Y) * (x₂N : Y) * (k : Y)⁻¹ ∈ (⊥ : Subgroup Y) := by
      have hdisj := hD0.indep hLmem
      rw [disjoint_iff] at hdisj
      rw [← hdisj]
      exact ⟨hLx₂, hR⟩
    have hx2one : (x₂N : Y) = 1 := by
      have h1 : (k : Y) * (x₂N : Y) * (k : Y)⁻¹ = 1 := Subgroup.mem_bot.mp hxbot
      calc (x₂N : Y) = (k : Y)⁻¹ * ((k : Y) * (x₂N : Y) * (k : Y)⁻¹) * (k : Y) := by group
        _ = 1 := by rw [h1]; group
    have hx2ne : (x₂N : Y) ≠ 1 := by
      intro hh; rw [hh, orderOf_one] at hx₂; norm_num at hx₂
    exact hx2ne hx2one
  let H : Subgroup K := (Subgroup.normalizer (J₁ : Set Y)).subgroupOf K
  have hsqg : ∀ x : K, x ^ 2 ∈ H := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    change (x : Y) ^ 2 ∈ Subgroup.normalizer (J₁ : Set Y)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change J₁.map (MulAut.conj ((x : Y) ^ 2)).toMonoidHom = J₁
    have h1 : J₁.map (MulAut.conj ((x : Y) ^ 2)).toMonoidHom =
        (J₁.map (MulAut.conj (x : Y)).toMonoidHom).map
          (MulAut.conj (x : Y)).toMonoidHom := by
      rw [pow_two, ← map_conj_map_conj J₁ (x : Y) (x : Y)]
    rw [h1]
    rcases hperm₁ x with hh | hh
    · rw [hh]; exact hh
    · rw [hh]
      rcases hperm₂ x with hh' | hh'
      · exact hh'
      · exfalso
        exact hne (Subgroup.map_injective (MulAut.conj (x : Y)).injective (hh.trans hh'.symm))
  have hHnormal : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have heq : g * n * g⁻¹ = (g * n) ^ 2 * n⁻¹ * (g⁻¹) ^ 2 := by
      simp only [pow_two]; group
    rw [heq]
    exact mul_mem (mul_mem (hsqg (g * n)) (inv_mem hn)) (hsqg g⁻¹)
  haveI : H.Normal := hHnormal
  haveI : IsSimpleGroup K := hKsimple
  have hKnorm1 : K ≤ Subgroup.normalizer (J₁ : Set Y) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hHbot | hHtop
    · exfalso
      have hKcomm : IsMulCommutative K := by
        rw [isMulCommutative_iff]
        intro a b
        have ha : a ^ 2 = 1 := by
          have := hsqg a; rw [hHbot] at this; exact Subgroup.mem_bot.mp this
        have hb2 : b ^ 2 = 1 := by
          have := hsqg b; rw [hHbot] at this; exact Subgroup.mem_bot.mp this
        have hab : (a * b) ^ 2 = 1 := by
          have := hsqg (a * b); rw [hHbot] at this; exact Subgroup.mem_bot.mp this
        have ha' : a * a = 1 := by simpa [pow_two] using ha
        have hb' : b * b = 1 := by simpa [pow_two] using hb2
        have hab' : (a * b) * (a * b) = 1 := by simpa [pow_two] using hab
        have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha'
        have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb'
        have hab_inv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab'
        calc a * b = (a * b)⁻¹ := hab_inv.symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = b * a := by rw [hb_inv, ha_inv]
      exact hKnc' hKcomm
    · intro k hk
      have hmem : (⟨k, hk⟩ : K) ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hKnorm2 : K ≤ Subgroup.normalizer (J₂ : Set Y) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases hperm₂ ⟨k, hk⟩ with hh | hh
    · exfalso
      have hk1 : J₁.map (MulAut.conj k).toMonoidHom = J₁ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnorm1 hk)
      exact hne (Subgroup.map_injective (MulAut.conj k).injective (hh.trans hk1.symm)).symm
    · exact hh
  have hJ1J2bot : J₁ ⊓ J₂ = ⊥ := by
    have hdisj : J₁ ⊓ sSup (lcalOf Y \ {J₁}) = ⊥ := disjoint_iff.mp (hD0.indep h₁)
    rw [eq_bot_iff, ← hdisj]
    exact inf_le_inf_left _ (le_sSup ⟨h₂, fun hh => hne hh.symm⟩)
  have hKcent₁ : K ≤ Subgroup.centralizer ({(x₁N : Y)} : Set Y) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hknorm : k * (x₁N : Y) * k⁻¹ ∈ J₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKnorm1 hk) (x₁N : Y)).mp hx₁J₁
    have hknorm₂ : k * (x₂N : Y) * k⁻¹ ∈ J₂ :=
      (Subgroup.mem_normalizer_iff.mp (hKnorm2 hk) (x₂N : Y)).mp hx₂J₂
    have heq : (x₁N : Y)⁻¹ * (k * (x₁N : Y) * k⁻¹) =
        (x₂N : Y) * (k * (x₂N : Y) * k⁻¹)⁻¹ := by
      rw [hkey k hk, hb]; group
    have hval : (x₁N : Y)⁻¹ * (k * (x₁N : Y) * k⁻¹) ∈ (⊥ : Subgroup Y) := by
      have hmem₂ : (x₁N : Y)⁻¹ * (k * (x₁N : Y) * k⁻¹) ∈ J₂ := by
        rw [heq]; exact mul_mem hx₂J₂ (inv_mem hknorm₂)
      have hmem : (x₁N : Y)⁻¹ * (k * (x₁N : Y) * k⁻¹) ∈ J₁ ⊓ J₂ :=
        Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx₁J₁) hknorm, hmem₂⟩
      rwa [hJ1J2bot] at hmem
    have hkx : k * (x₁N : Y) * k⁻¹ = (x₁N : Y) :=
      (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hval)).symm
    calc k * (x₁N : Y) = k * (x₁N : Y) * k⁻¹ * k := by group
      _ = (x₁N : Y) * k := by rw [hkx]
  have hKcent₂ : K ≤ Subgroup.centralizer ({(x₂N : Y)} : Set Y) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hknorm : k * (x₂N : Y) * k⁻¹ ∈ J₂ :=
      (Subgroup.mem_normalizer_iff.mp (hKnorm2 hk) (x₂N : Y)).mp hx₂J₂
    have hknorm₁ : k * (x₁N : Y) * k⁻¹ ∈ J₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKnorm1 hk) (x₁N : Y)).mp hx₁J₁
    have heq : (x₂N : Y)⁻¹ * (k * (x₂N : Y) * k⁻¹) =
        (x₁N : Y) * (k * (x₁N : Y) * k⁻¹)⁻¹ := by
      rw [hkey₂ k hk, hb, hcomm.eq]; group
    have hval : (x₂N : Y)⁻¹ * (k * (x₂N : Y) * k⁻¹) ∈ (⊥ : Subgroup Y) := by
      have hmem₁ : (x₂N : Y)⁻¹ * (k * (x₂N : Y) * k⁻¹) ∈ J₁ := by
        rw [heq]; exact mul_mem hx₁J₁ (inv_mem hknorm₁)
      have hmem : (x₂N : Y)⁻¹ * (k * (x₂N : Y) * k⁻¹) ∈ J₁ ⊓ J₂ :=
        Subgroup.mem_inf.mpr ⟨hmem₁, mul_mem (inv_mem hx₂J₂) hknorm⟩
      rwa [hJ1J2bot] at hmem
    have hkx : k * (x₂N : Y) * k⁻¹ = (x₂N : Y) :=
      (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hval)).symm
    calc k * (x₂N : Y) = k * (x₂N : Y) * k⁻¹ * k := by group
      _ = (x₂N : Y) * k := by rw [hkx]
  have hJ2cent : J₂ ≤ Subgroup.centralizer ({(x₁N : Y)} : Set Y) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hD0.commute J₂ h₂ J₁ h₁ (fun hh => hne hh.symm) y hy (x₁N : Y) hx₁J₁).eq
  have hJ1cent : J₁ ≤ Subgroup.centralizer ({(x₂N : Y)} : Set Y) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hD0.commute J₁ h₁ J₂ h₂ hne y hy (x₂N : Y) hx₂J₂).eq
  have hJ1simple : IsSimpleGroup J₁ := h₁.2.1
  have hJ2simple : IsSimpleGroup J₂ := h₂.2.1
  have hJ1nc : ∃ x ∈ J₁, ∃ y ∈ J₁, x * y ≠ y * x :=
    exists_mem_mul_ne_of_not_isMulCommutative h₁.2.2
  have hJ2nc : ∃ x ∈ J₂, ∃ y ∈ J₂, x * y ≠ y * x :=
    exists_mem_mul_ne_of_not_isMulCommutative h₂.2.2
  have hEq2 : J₂ = K :=
    eq_of_simple_le_of_mulEquiv (h.centralizer_equiv hx₁).some
      hJ2cent hKcent₁ hJ2simple hJ2nc hKsimple hKnc
  have hEq1 : J₁ = K :=
    eq_of_simple_le_of_mulEquiv (h.centralizer_equiv hx₂).some
      hJ1cent hKcent₂ hJ1simple hJ1nc hKsimple hKnc
  exact hne (hEq1.trans hEq2.symm)

theorem exists_simple_normal (h : Setting Y P) :
    ∃ N : Subgroup Y, N.Normal ∧ IsSimpleGroup ↥N ∧ (∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) ∧
      centralizer (N : Set Y) = ⊥ ∧ 3 ∣ Nat.card N := by
  have hsol : CFSG.solvableRadical Y = ⊥ := h.solvableRadical_eq_bot
  have hF : CFSG.generalizedFitting Y = CFSG.layer Y :=
    generalizedFitting_eq_layer_of_solvableRadical_eq_bot hsol
  have hlayer_ne : CFSG.layer Y ≠ ⊥ := by
    intro hbot
    have hC := CFSG.centralizer_generalizedFitting_le Y
    rw [hF, hbot] at hC
    have hcentbot : Subgroup.centralizer (((⊥ : Subgroup Y) : Set Y)) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr fun x hx => by
        have hx1 : x = 1 := by simpa using hx
        rw [hx1]
        exact Subgroup.mem_center_iff.mpr fun g => by simp
    rw [hcentbot] at hC
    have hPbot : P = ⊥ := le_bot_iff.mp (le_top.trans hC)
    have hcard1 : Nat.card P = 1 := by rw [hPbot, Subgroup.card_bot]
    rw [h.card] at hcard1
    norm_num at hcard1
  have hlcal_ne : lcalOf Y ≠ ∅ := by
    intro hemp
    apply hlayer_ne
    rw [← (isDirectProduct_lcalOf_layer hsol).sSup_eq, hemp, sSup_empty]
  obtain ⟨J, hJ⟩ := Set.nonempty_iff_ne_empty.mpr hlcal_ne
  have hsingle : lcalOf Y = {J} := by
    ext K
    refine ⟨fun hK => ?_, fun hK => ?_⟩
    · rw [Set.mem_singleton_iff]
      exact lcalOf_subsingleton h hK hJ
    · rw [Set.mem_singleton_iff] at hK
      rwa [hK]
  have hNeq : CFSG.layer Y = J := by
    rw [← (isDirectProduct_lcalOf_layer hsol).sSup_eq, hsingle, sSup_singleton]
  have hJnc : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x :=
    exists_mem_mul_ne_of_not_isMulCommutative hJ.2.2
  haveI : IsSimpleGroup J := hJ.2.1
  refine ⟨CFSG.layer Y, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  · rw [hNeq]; exact hJ.2.1
  · rw [hNeq]; exact hJnc
  · rw [hNeq, eq_bot_iff]
    intro z hz
    have hzF : z ∈ CFSG.generalizedFitting Y :=
      CFSG.centralizer_generalizedFitting_le Y (by rw [hF, hNeq]; exact hz)
    have hzJ : z ∈ J := by
      have := hzF
      rw [hF, hNeq] at this
      exact this
    have hzcenter : (⟨z, hzJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro j
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz j j.2)
    have hcenter : Subgroup.center J = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hh | hh
      · exact hh
      · exfalso
        obtain ⟨a, haJ, b, hbJ, hab⟩ := hJnc
        have hb : (⟨b, hbJ⟩ : J) ∈ Subgroup.center J := by rw [hh]; exact Subgroup.mem_top _
        exact hab (congrArg Subtype.val (Subgroup.mem_center_iff.1 hb (⟨a, haJ⟩ : J)))
    have hzbot : (⟨z, hzJ⟩ : J) ∈ (⊥ : Subgroup J) := by rw [← hcenter]; exact hzcenter
    rw [Subgroup.mem_bot] at hzbot
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzbot)
  · rw [hNeq]; exact three_dvd_of_mem_lcalOf h hJ

theorem le_or_selfCentralizing (h : Setting Y P) {N : Subgroup Y} (hN : N.Normal)
    (h3 : 3 ∣ Nat.card N) :
    P ≤ N ∨ ∃ c ∈ N, orderOf c = 3 ∧ N ⊓ centralizer ({c} : Set Y) = zpowers c := by
  classical
  by_cases hPN : P ≤ N
  · exact Or.inl hPN
  · right
    obtain ⟨xN, hxN⟩ : ∃ x : N, orderOf x = 3 := by
      haveI : Fintype N := Fintype.ofFinite N
      exact exists_prime_orderOf_dvd_card (G := N) 3 (by rwa [Nat.card_eq_fintype_card] at h3)
    have hxNY : orderOf (xN : Y) = 3 := by rw [Subgroup.orderOf_coe, hxN]
    obtain ⟨g, hgP⟩ := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.exists_conj_mem_of_card_eq_pow
      (G := Y) (p := 3) (k := 2) (P := P)
      (by rw [h.card]; norm_num) (by simpa using h.not_dvd) hxNY
    let c : Y := g * (xN : Y) * g⁻¹
    have hcP : c ∈ P := hgP
    have hcN : c ∈ N := hN.conj_mem (xN : Y) xN.2 g
    have hc3 : orderOf c = 3 := by
      have h1 : orderOf ((MulAut.conj g) (xN : Y)) = orderOf (xN : Y) :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (xN : Y)
      rw [MulAut.conj_apply, Subgroup.orderOf_coe, hxN] at h1
      exact h1
    have hcne : c ≠ 1 := by
      intro hh; rw [hh, orderOf_one] at hc3; norm_num at hc3
    let C : Subgroup Y := Subgroup.centralizer ({c} : Set Y)
    have hPC : P ≤ C := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.comm y hy c hcP
    have hcardC : Nat.card ↥C = 360 := h.card_centralizer hcP hcne
    have hcardP : Nat.card P = 9 := h.card
    have hCfac : (Nat.card ↥C).factorization 3 = 2 := by
      rw [hcardC]
      have h9dvd : 3 ^ 2 ∣ 360 := by norm_num
      have h27 : ¬ 3 ^ 3 ∣ 360 := by norm_num
      have hle : 2 ≤ (360).factorization 3 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).mp h9dvd
      have hlt : (360).factorization 3 < 3 := by
        by_contra hcon
        exact h27 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).mpr
          (by omega))
      omega
    have hcardPsub : Nat.card (P.subgroupOf C) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, hcardP]
    have hPsyl : Nat.card (P.subgroupOf C) = 3 ^ (Nat.card ↥C).factorization 3 := by
      rw [hcardPsub, hCfac]; norm_num
    by_cases h9 : 9 ∣ Nat.card ↥(N ⊓ C)
    · exfalso
      obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(N ⊓ C)) 3 (n := 2)
        (by simpa using h9)
      let Q : Subgroup Y := K.map (N ⊓ C).subtype
      have hQcard : Nat.card Q = 9 := by
        dsimp only [Q]
        rw [Subgroup.card_map_of_injective (N ⊓ C).subtype_injective, hKcard]
        norm_num
      have hQle : Q ≤ N ⊓ C := by
        dsimp only [Q]; exact Subgroup.map_subtype_le K
      have hQN : Q ≤ N := hQle.trans inf_le_left
      have hQC : Q ≤ C := hQle.trans inf_le_right
      have hcardQsub : Nat.card (Q.subgroupOf C) = 9 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hQcard]
      have hQsyl : Nat.card (Q.subgroupOf C) = 3 ^ (Nat.card ↥C).factorization 3 := by
        rw [hcardQsub, hCfac]; norm_num
      let Ps : Sylow 3 ↥C := Sylow.ofCard (P.subgroupOf C) hPsyl
      let Qs : Sylow 3 ↥C := Sylow.ofCard (Q.subgroupOf C) hQsyl
      obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥C) Ps Qs
      have hsmul : MulAut.conj k • (P.subgroupOf C) = Q.subgroupOf C := by
        have hh := congrArg (fun S : Sylow 3 ↥C => (S : Subgroup ↥C)) hk
        simpa only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Ps, Qs] using hh
      have hPN' : P ≤ N := by
        intro p hp
        have hpC : p ∈ C := hPC hp
        have hmem : (MulAut.conj k) (⟨p, hpC⟩ : ↥C) ∈ Q.subgroupOf C := by
          rw [← hsmul]
          exact ⟨⟨p, hpC⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
        have hmemN : (((MulAut.conj k) (⟨p, hpC⟩ : ↥C)) : Y) ∈ N :=
          hQN (Subgroup.mem_subgroupOf.mp hmem)
        have hconj_eq : (((MulAut.conj k) (⟨p, hpC⟩ : ↥C)) : Y) = (k : Y) * p * (k : Y)⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hconj_eq] at hmemN
        have hp_eq : p = (k : Y)⁻¹ * ((k : Y) * p * (k : Y)⁻¹) * (k : Y) := by group
        rw [hp_eq]
        simpa using hN.conj_mem ((k : Y) * p * (k : Y)⁻¹) hmemN (k : Y)⁻¹
      exact hPN hPN'
    · refine ⟨c, hcN, hc3, ?_⟩
      exact inf_eq_zpowers_of_mulEquiv (h.centralizer_equiv hc3).some
        (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
        (fun _ hy => Subgroup.mem_centralizer_singleton_iff.mp hy)
        hc3
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hN]; exact le_top)
        hcN (by simpa using h9)

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5
