module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ABasN

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G}

private lemma fzrAux_h_mem {a b h : G} (haP : a ∈ P) (hbP : b ∈ P)
    (hh : h = 1 ∨ h = a ∨ h = b ∨ h = a * b) : h ∈ P := by
  rcases hh with rfl | rfl | rfl | rfl
  · exact P.one_mem
  · exact haP
  · exact hbP
  · exact P.mul_mem haP hbP

private lemma fzrAux_decomp {a b h : G}
    (hh : h = 1 ∨ h = a ∨ h = b ∨ h = a * b) :
    ∃ e f : ℕ, e < 2 ∧ f < 2 ∧ h = a ^ e * b ^ f := by
  rcases hh with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
  · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  · exact ⟨1, 1, by norm_num, by norm_num, by simp⟩

private lemma fzrAux_comm_mul {a b : G} (hab : Commute a b) (e f g h : ℕ) :
    (a ^ e * b ^ f) * (a ^ g * b ^ h) = a ^ (e + g) * b ^ (f + h) := by
  calc (a ^ e * b ^ f) * (a ^ g * b ^ h)
      = a ^ e * (b ^ f * (a ^ g * b ^ h)) := by rw [mul_assoc]
    _ = a ^ e * ((b ^ f * a ^ g) * b ^ h) := by rw [mul_assoc]
    _ = a ^ e * ((a ^ g * b ^ f) * b ^ h) := by
          rw [(show Commute (b ^ f) (a ^ g) from hab.symm.pow_pow f g).eq]
    _ = a ^ e * (a ^ g * (b ^ f * b ^ h)) := by rw [mul_assoc]
    _ = (a ^ e * a ^ g) * (b ^ f * b ^ h) := by rw [← mul_assoc]
    _ = a ^ (e + g) * b ^ (f + h) := by rw [← pow_add, ← pow_add]

private lemma fzrAux_pow_prod {a b : G} (hab : Commute a b) (e f k : ℕ) :
    (a ^ e * b ^ f) ^ k = a ^ (e * k) * b ^ (f * k) := by
  rw [Commute.mul_pow (hab.pow_pow e f) k, ← pow_mul, ← pow_mul]

private lemma fzrAux_prod3 {a b : G} (hab : Commute a b) (e f g h i j : ℕ) :
    (a ^ e * b ^ f) * (a ^ g * b ^ h) * (a ^ i * b ^ j)
      = a ^ (e + g + i) * b ^ (f + h + j) := by
  rw [fzrAux_comm_mul hab e f g h, fzrAux_comm_mul hab (e + g) (f + h) i j]

lemma fzr_a_stepA (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hpf : FzPFacts t tau rho E W Q T P) (hs : FzStr t tau lam rho Z E W Q R T)
    (h8 : FzZ8 Z E P) {a b : G} (haP : a ∈ P) (hbP : b ∈ P)
    (haE : a ∉ E) (hbE : b ∉ E) (habE : a * b ∉ E) (haibE : a⁻¹ * b ∉ E) :
    ∀ p ∈ P, ∃ h : G,
      (h = 1 ∨ h = a ∨ h = b ∨ h = a * b) ∧ ∃ c ∈ P, p = h * c ^ 2 := by
  classical
  haveI : IsMulCommutative ↥P := IsMulCommutative.of_comm fun x y =>
    Subtype.ext (hcomm x.1 x.2 y.1 y.2)
  let H : Subgroup ↥P := E.subgroupOf P
  have hrel : E.relIndex P = 4 := by
    have h := Subgroup.relIndex_mul_card (H := E) (K := P)
    rw [inf_of_le_left hpf.EP, hs.card_E, hpf.card_P] at h
    omega
  have hidx : H.index = 4 := hrel
  have hcardQ : Nat.card (↥P ⧸ H) = 4 := by
    rw [← Subgroup.index_eq_card H]
    exact hidx
  let aH : ↥P := ⟨a, haP⟩
  let bH : ↥P := ⟨b, hbP⟩
  let abH : ↥P := ⟨a * b, P.mul_mem haP hbP⟩
  have hqa1 : (QuotientGroup.mk' H aH : ↥P ⧸ H) ≠ 1 := by
    intro hq
    have hmem : aH ∈ H := (QuotientGroup.eq_one_iff aH).mp hq
    exact haE ((Subgroup.mem_subgroupOf).mp hmem)
  have hqb1 : (QuotientGroup.mk' H bH : ↥P ⧸ H) ≠ 1 := by
    intro hq
    have hmem : bH ∈ H := (QuotientGroup.eq_one_iff bH).mp hq
    exact hbE ((Subgroup.mem_subgroupOf).mp hmem)
  have hqab1 : (QuotientGroup.mk' H abH : ↥P ⧸ H) ≠ 1 := by
    intro hq
    have hmem : abH ∈ H := (QuotientGroup.eq_one_iff abH).mp hq
    exact habE ((Subgroup.mem_subgroupOf).mp hmem)
  have hqa_ne_qb : (QuotientGroup.mk' H aH : ↥P ⧸ H) ≠ QuotientGroup.mk' H bH := by
    intro hq
    rw [QuotientGroup.mk'_eq_mk'] at hq
    obtain ⟨z, hzH, hz⟩ := hq
    have hzE : (z : G) ∈ E := (Subgroup.mem_subgroupOf).mp hzH
    have hzval : a * (z : G) = b := congrArg Subtype.val hz
    have hz_eq : (z : G) = a⁻¹ * b := by rw [← hzval]; group
    exact haibE (hz_eq ▸ hzE)
  have hqa_ne_qab : (QuotientGroup.mk' H aH : ↥P ⧸ H) ≠ QuotientGroup.mk' H abH := by
    intro hq
    rw [QuotientGroup.mk'_eq_mk'] at hq
    obtain ⟨z, hzH, hz⟩ := hq
    have hzE : (z : G) ∈ E := (Subgroup.mem_subgroupOf).mp hzH
    have hzval : a * (z : G) = a * b := congrArg Subtype.val hz
    have hz_eq : (z : G) = b := by
      calc (z : G) = a⁻¹ * (a * (z : G)) := by group
        _ = a⁻¹ * (a * b) := by rw [hzval]
        _ = b := by group
    exact hbE (hz_eq ▸ hzE)
  have hqb_ne_qab : (QuotientGroup.mk' H bH : ↥P ⧸ H) ≠ QuotientGroup.mk' H abH := by
    intro hq
    rw [QuotientGroup.mk'_eq_mk'] at hq
    obtain ⟨z, hzH, hz⟩ := hq
    have hzE : (z : G) ∈ E := (Subgroup.mem_subgroupOf).mp hzH
    have hzval : b * (z : G) = a * b := congrArg Subtype.val hz
    have hz_eq : (z : G) = a := by
      calc (z : G) = b⁻¹ * (b * (z : G)) := by group
        _ = b⁻¹ * (a * b) := by rw [hzval]
        _ = a * (b⁻¹ * b) := by
              rw [← mul_assoc, hcomm b⁻¹ (P.inv_mem hbP) a haP, mul_assoc]
        _ = a := by group
    exact haE (hz_eq ▸ hzE)
  haveI : Finite (↥P ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; norm_num)
  haveI : Fintype (↥P ⧸ H) := Fintype.ofFinite _
  have hcardF : Fintype.card (↥P ⧸ H) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardQ
  have huniv : ({1, QuotientGroup.mk' H aH, QuotientGroup.mk' H bH, QuotientGroup.mk' H abH}
      : Finset (↥P ⧸ H)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcardF, Finset.card_eq_four]
    exact ⟨1, QuotientGroup.mk' H aH, QuotientGroup.mk' H bH, QuotientGroup.mk' H abH,
      hqa1.symm, hqb1.symm, hqab1.symm, hqa_ne_qb, hqa_ne_qab, hqb_ne_qab, rfl⟩
  intro p hp
  let pP : ↥P := ⟨p, hp⟩
  have hmem : (QuotientGroup.mk' H pP : ↥P ⧸ H)
      ∈ ({1, QuotientGroup.mk' H aH, QuotientGroup.mk' H bH, QuotientGroup.mk' H abH}
          : Finset (↥P ⧸ H)) := by
    rw [huniv]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | ha | hb | hab
  · have hpP : pP ∈ H := (QuotientGroup.eq_one_iff pP).mp h0
    have hpE : p ∈ E := (Subgroup.mem_subgroupOf).mp hpP
    obtain ⟨c, hcP, hc2⟩ := h8.sq p hpE
    exact ⟨1, Or.inl rfl, c, hcP, by rw [one_mul, ← hc2]⟩
  · 
    rw [QuotientGroup.mk'_eq_mk'] at ha
    obtain ⟨z, hzH, hz⟩ := ha
    have hzE : (z : G) ∈ E := (Subgroup.mem_subgroupOf).mp hzH
    have hzval : p * (z : G) = a := by simpa using congrArg Subtype.val hz
    have hp_eq : p = a * (z : G)⁻¹ := by rw [← hzval]; group
    have hzinvE : (z : G)⁻¹ ∈ E := E.inv_mem hzE
    obtain ⟨c, hcP, hc2⟩ := h8.sq (z : G)⁻¹ hzinvE
    exact ⟨a, Or.inr (Or.inl rfl), c, hcP, by rw [hp_eq, hc2]⟩
  · 
    rw [QuotientGroup.mk'_eq_mk'] at hb
    obtain ⟨z, hzH, hz⟩ := hb
    have hzE : (z : G) ∈ E := (Subgroup.mem_subgroupOf).mp hzH
    have hzval : p * (z : G) = b := by simpa using congrArg Subtype.val hz
    have hp_eq : p = b * (z : G)⁻¹ := by rw [← hzval]; group
    have hzinvE : (z : G)⁻¹ ∈ E := E.inv_mem hzE
    obtain ⟨c, hcP, hc2⟩ := h8.sq (z : G)⁻¹ hzinvE
    exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), c, hcP, by rw [hp_eq, hc2]⟩
  · 
    rw [QuotientGroup.mk'_eq_mk'] at hab
    obtain ⟨z, hzH, hz⟩ := hab
    have hzE : (z : G) ∈ E := (Subgroup.mem_subgroupOf).mp hzH
    have hzval : p * (z : G) = a * b := by simpa using congrArg Subtype.val hz
    have hp_eq : p = a * b * (z : G)⁻¹ := by rw [← hzval]; group
    have hzinvE : (z : G)⁻¹ ∈ E := E.inv_mem hzE
    obtain ⟨c, hcP, hc2⟩ := h8.sq (z : G)⁻¹ hzinvE
    exact ⟨a * b, Or.inr (Or.inr (Or.inr rfl)), c, hcP, by rw [hp_eq, hc2]⟩

lemma fzr_a_span (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    {a b : G} (haP : a ∈ P) (hbP : b ∈ P) (hab : a * b = b * a)
    (hstepA : ∀ p ∈ P, ∃ h : G,
      (h = 1 ∨ h = a ∨ h = b ∨ h = a * b) ∧ ∃ c ∈ P, p = h * c ^ 2) :
    ∀ p ∈ P, ∃ n, n < 64 ∧ fzrAElt a b n = p := by
  have hcab : Commute a b := hab
  intro p hp
  obtain ⟨h, hh, c, hcP, hp_eq⟩ := hstepA p hp
  obtain ⟨h₁, hh₁, c₁, hc₁P, hc_eq⟩ := hstepA c hcP
  obtain ⟨h₂, hh₂, c₂, hc₂P, hc₁_eq⟩ := hstepA c₁ hc₁P
  have hhP : h ∈ P := fzrAux_h_mem haP hbP hh
  have hh₁P : h₁ ∈ P := fzrAux_h_mem haP hbP hh₁
  have hh₂P : h₂ ∈ P := fzrAux_h_mem haP hbP hh₂
  have hc2pow : c₂ ^ 8 = 1 := fzr_a_pow8 hs hpf hc₂P
  have hc_sq : c ^ 2 = h₁ ^ 2 * c₁ ^ 4 := by
    rw [hc_eq, Commute.mul_pow (hcomm h₁ hh₁P (c₁ ^ 2) (P.pow_mem hc₁P 2)) 2, ← pow_mul]
  have hc1_4 : c₁ ^ 4 = h₂ ^ 4 := by
    have h : c₂ ^ (2 * 4) = (1 : G) := by
      rw [show 2 * 4 = 8 by norm_num, hc2pow]
    rw [hc₁_eq, Commute.mul_pow (hcomm h₂ hh₂P (c₂ ^ 2) (P.pow_mem hc₂P 2)) 4, ← pow_mul,
      h, mul_one]
  have hp_form : p = h * h₁ ^ 2 * h₂ ^ 4 := by
    rw [hp_eq, hc_sq, hc1_4, mul_assoc]
  obtain ⟨e, f, he, hf, hh_d⟩ := fzrAux_decomp hh
  obtain ⟨e₁, f₁, he₁, hf₁, hh₁_d⟩ := fzrAux_decomp hh₁
  obtain ⟨e₂, f₂, he₂, hf₂, hh₂_d⟩ := fzrAux_decomp hh₂
  have hp_form' : p = (a ^ e * b ^ f) * (a ^ e₁ * b ^ f₁) ^ 2 * (a ^ e₂ * b ^ f₂) ^ 4 := by
    rw [hp_form, hh_d, hh₁_d, hh₂_d]
  have hp_pow : p = (a ^ e * b ^ f) * (a ^ (e₁ * 2) * b ^ (f₁ * 2))
      * (a ^ (e₂ * 4) * b ^ (f₂ * 4)) := by
    rw [hp_form', fzrAux_pow_prod hcab e₁ f₁ 2, fzrAux_pow_prod hcab e₂ f₂ 4]
  have hp_collect : p = a ^ (e + e₁ * 2 + e₂ * 4) * b ^ (f + f₁ * 2 + f₂ * 4) := by
    rw [hp_pow, fzrAux_prod3 hcab e f (e₁ * 2) (f₁ * 2) (e₂ * 4) (f₂ * 4)]
  have hx : e + e₁ * 2 + e₂ * 4 < 8 := by omega
  have hy : f + f₁ * 2 + f₂ * 4 < 8 := by omega
  refine ⟨(e + e₁ * 2 + e₂ * 4) + 8 * (f + f₁ * 2 + f₂ * 4), by omega, ?_⟩
  have hn_lo : ((e + e₁ * 2 + e₂ * 4) + 8 * (f + f₁ * 2 + f₂ * 4)) % 8
      = e + e₁ * 2 + e₂ * 4 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hn_hi : ((e + e₁ * 2 + e₂ * 4) + 8 * (f + f₁ * 2 + f₂ * 4)) / 8 % 8
      = f + f₁ * 2 + f₂ * 4 := by
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 8), Nat.div_eq_of_lt hx, Nat.zero_add,
      Nat.mod_eq_of_lt hy]
  rw [fzrAElt, hn_lo, hn_hi]
  exact hp_collect.symm

private lemma fzrAux_elt_mem {a b : G} (haP : a ∈ P) (hbP : b ∈ P) (n : ℕ) :
    fzrAElt a b n ∈ P := by
  rw [fzrAElt]
  exact P.mul_mem (P.pow_mem haP _) (P.pow_mem hbP _)

lemma fzr_a_inj_of_span (hpf : FzPFacts t tau rho E W Q T P) {a b : G}
    (haP : a ∈ P) (hbP : b ∈ P)
    (hspan : ∀ p ∈ P, ∃ n, n < 64 ∧ fzrAElt a b n = p) :
    ∀ n m, n < 64 → m < 64 → fzrAElt a b n = fzrAElt a b m → n = m := by
  have hcard : Nat.card ↥P = 64 := hpf.card_P
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ↥P := Fintype.ofFinite _
  have hcardF : Fintype.card (Fin 64) = Fintype.card ↥P := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  have he : Fin 64 ≃ ↥P := (Fintype.card_eq.mp hcardF).some
  have hsurj : Function.Surjective
      (fun n : Fin 64 => (⟨fzrAElt a b n.1, fzrAux_elt_mem haP hbP n.1⟩ : ↥P)) := by
    intro q
    obtain ⟨n, hn, hn_eq⟩ := hspan q.1 q.2
    exact ⟨⟨n, hn⟩, Subtype.ext hn_eq⟩
  have hinj : Function.Injective
      (fun n : Fin 64 => (⟨fzrAElt a b n.1, fzrAux_elt_mem haP hbP n.1⟩ : ↥P)) :=
    (Finite.injective_iff_surjective_of_equiv he).mpr hsurj
  intro n m hn hm h
  have hfin : (fun k : Fin 64 => (⟨fzrAElt a b k.1, fzrAux_elt_mem haP hbP k.1⟩ : ↥P)) ⟨n, hn⟩
      = (fun k : Fin 64 => (⟨fzrAElt a b k.1, fzrAux_elt_mem haP hbP k.1⟩ : ↥P)) ⟨m, hm⟩ :=
    Subtype.ext h
  exact congrArg Fin.val (hinj hfin)

end CFSG.OddStandard.SmallF3.FritzII
