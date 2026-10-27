module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen4
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L285

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma_28_6_core (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut)
    (h327 : IG_3_27) {x y : G} {L J : Subgroup G} (cfg : RecipCfg G x y L J)
    (hxJ : x ∈ normalizer (J : Set G)) (hyL : y ∉ normalizer (L : Set G))
    (hfx : ¬ InducesFAut x J) {T : Subgroup G} (hT : IsSylow2In T (L ⊔ conjugate L y)) {a : G}
    (haT : a ∈ T ⊓ L) (hcomm : a * (y⁻¹ * a * y) = (y⁻¹ * a * y) * a)
    (hu1 : orderOf (a * (y⁻¹ * a * y)) = 2) (huI : a * (y⁻¹ * a * y) ∈ IDiag y L) :
    ∃ g : G, g⁻¹ * (a * (y⁻¹ * a * y)) * g = x ∧ g⁻¹ * x * g = a * (y⁻¹ * a * y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 := mul_self_eq_one_of_orderOf_eq_two cfg.hx
  have hy1 := mul_self_eq_one_of_orderOf_eq_two cfg.hy
  have hxy : x * y = y * x := cfg.comm
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  obtain ⟨hIcomp, -, -, -⟩ := h327 G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL hyL
  set b : G := y⁻¹ * a * y with hb
  have haL : a ∈ L := haT.2
  have haTT : a ∈ T := haT.1
  have hTp : IsPGroup 2 ↥T := hT.2.1
  have hL' : IsIntrinsic x (conjugate L y) := isIntrinsic_conjugate hxy cfg.hL
  have hbL' : b ∈ conjugate L y := by
    rw [mem_conjugate_iff']
    have : y * b * y⁻¹ = a := by simp only [hb]; group
    rw [this]
    exact haL
  have hbc : b ∈ cSec L := conjugate_le_cSec hxy cfg.hL hyL hbL'
  have hbN : b ∈ normalizer (L : Set G) := hbc.1
  have haN : a ∈ normalizer (L : Set G) := le_normalizer haL
  have huN : a * b ∈ normalizer (L : Set G) := mul_mem haN hbN
  have huu : (a * b) * (a * b) = 1 := mul_self_eq_one_of_orderOf_eq_two hu1
  have ha2L : a * a ∈ L := mul_mem haL haL
  have hbb : b * b = y⁻¹ * (a * a) * y := by simp only [hb]; group
  have ha2L' : a * a ∈ conjugate L y := by
    have h1 : a * a * (b * b) = 1 := by
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [hcomm]
        _ = (a * b) * (a * b) := by group
        _ = 1 := huu
    have h2 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact inv_mem (mul_mem hbL' hbL')
  have hz2 : IsPGroup 2 ↥(zpowers (a * a)) := isPGroup_zpowers_of_mem hTp (mul_mem haTT haTT)
  have hF := eq_one_or_eq_of_mem_inf_conjugate h44 cfg.simple cfg.hx hxy cfg.hL hyL ha2L ha2L' hz2
  have hxbx : y⁻¹ * x * y = x := by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [hxy]
      _ = x := by group
  have haax : a * a = x := by
    rcases hF with h | h
    · exfalso
      have hu_ne : a * b ≠ 1 := by
        intro h1
        rw [h1] at hu1
        simp at hu1
      by_cases ha1 : a = 1
      · apply hu_ne
        simp [hb, ha1]
      · have ha2 : orderOf a = 2 := orderOf_eq_two_of_mul_self_eq_one h ha1
        have hax : a = x := cfg.hL.eq_of_involution cfg.hx haL ha2
        apply hu_ne
        have : b = x := by rw [hb, hax]; exact hxbx
        rw [this, hax, hx1]
    · exact h
  have ha4 : orderOf a = 4 := by
    have h1 : ¬ a ^ (2 ^ 1) = 1 := by
      rw [pow_one, pow_two, haax]
      exact ne_one_of_orderOf_eq_two cfg.hx
    have h2 : a ^ (2 ^ (1 + 1)) = 1 := by
      have e : a ^ (2 ^ (1 + 1)) = (a * a) * (a * a) := by
        rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two a, pow_two (a * a)]
      rw [e, haax, hx1]
    have := orderOf_eq_prime_pow h1 h2
    simpa using this
  have hbbx : b * b = x := by
    rw [hbb, haax]
    exact hxbx
  have hphi_u : phi L (a * b) huN = MulAut.conj (hatMk L ⟨a, haL⟩) := by
    have h1 : phi L (a * b) (mul_mem haN hbN) = phi L a haN * phi L b hbN := phi_mul L haN hbN
    have h2 : phi L b hbN = 1 := (phi_eq_one_iff L hbN).mpr hbc
    have h3 : phi L a haN = MulAut.conj (hatMk L ⟨a, haL⟩) := phi_of_mem L haL
    rw [h1, h2, h3, mul_one]
  have hQ := h44 G cfg.simple x cfg.hx L cfg.hL.1 cfg.hL.2.1
  have hA := (hAut (Hat L) hQ).1
  have hxc : hatMk L ⟨x, cfg.hL.2.2⟩ ∈ center (Hat L) :=
    hatMk_mem_center cfg.hL.2.2 cfg.hL.mem_cSec
  have hac2 : hatMk L ⟨a, haL⟩ * hatMk L ⟨a, haL⟩ = hatMk L ⟨x, cfg.hL.2.2⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext haax
  have hpa : IsPGroup 2 ↥(zpowers a) := isPGroup_zpowers_of_mem hTp haTT
  have hac4 : orderOf (hatMk L ⟨a, haL⟩) = 4 := by
    have := orderOf_hatMk (K := L) (S := zpowers a) (zpowers_le.mpr haL) hpa (mem_zpowers a)
    rw [this, ha4]
  have hacn : hatMk L ⟨a, haL⟩ ∉ center (Hat L) := by
    intro hc
    have h1 : orderOf (⟨hatMk L ⟨a, haL⟩, hc⟩ : center (Hat L)) ∣ Nat.card (center (Hat L)) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hac4, hQ.2] at h1
    norm_num at h1
  have hnf_u : ¬ InducesFAut (a * b) L := by
    rintro ⟨hN', hF'⟩
    have hphi' : inducedQuotAut L (pPrimeCore 2 ↥L) ⟨a * b, hN'⟩ =
        MulAut.conj (hatMk L ⟨a, haL⟩) := hphi_u
    rw [hphi'] at hF'
    exact hA _ hacn (by rw [hac2]; exact hxc) hF'
  have huxy := hIcomp.1 huI
  have huC : a * b * x = x * (a * b) := mem_centralizer_singleton_iff.mp huxy.1
  have hucJ : a * b ∈ cSec J := I_le_cSec h327 cfg hxJ hyL huI
  have hxu_pg : IsPGroup 2 ↥(closure ({x, a * b} : Set G)) :=
    isPGroup_closure_pair hx1 huu huC.symm
  have hA_le : closure ({x, a * b} : Set G) ≤ normalizer (J : Set G) := by
    rw [closure_le]
    rintro g (rfl | hg)
    · exact hxJ
    · rw [Set.mem_singleton_iff.mp hg]
      exact hucJ.1
  obtain ⟨R, hR, hRn⟩ := exists_invariant_sylow hxu_pg hA_le
  have hRx : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (mem_normalizer_iff.mp (hRn (subset_closure (Or.inl rfl))) r).mp hr
  have hRu : ∀ r ∈ R, (a * b) * r * (a * b)⁻¹ ∈ R := fun r hr =>
    (mem_normalizer_iff.mp (hRn (subset_closure (Or.inr rfl))) r).mp hr
  obtain ⟨c₁, hc₁R, -, hc₁⟩ :=
    fusion_first h44 hAut cfg.simple cfg.hy cfg.hJ cfg.hx hxJ hfx hR hRx
  have hc₁u : (a * b) * c₁ = c₁ * (a * b) := by
    have := conj_eq_of_mem_cSec hR hucJ hRu hc₁R
    calc (a * b) * c₁ = (a * b) * c₁ * (a * b)⁻¹ * (a * b) := by group
      _ = c₁ * (a * b) := by rw [this]
  have hc₁' : c₁⁻¹ * (a * b) * c₁ = a * b := by
    calc c₁⁻¹ * (a * b) * c₁ = c₁⁻¹ * ((a * b) * c₁) := by group
      _ = c₁⁻¹ * (c₁ * (a * b)) := by rw [hc₁u]
      _ = a * b := by group
  obtain ⟨S', hS', hS'n⟩ := exists_invariant_sylow (isPGroup_zpowers_of_mul_self_eq_one huu)
    (zpowers_le.mpr huN)
  have hS'u : ∀ r ∈ S', (a * b) * r * (a * b)⁻¹ ∈ S' := fun r hr =>
    (mem_normalizer_iff.mp (hS'n (mem_zpowers _)) r).mp hr
  obtain ⟨c₂, hc₂S, -, hc₂⟩ :=
    fusion_first h44 hAut cfg.simple cfg.hx cfg.hL hu1 huN hnf_u hS' hS'u
  have hy' : y * x * y = x := by
    calc y * x * y = x * y * y := by rw [← hxy]
      _ = x := by rw [mul_assoc, hy1, mul_one]
  have key : b * x * y * a = y := by
    calc b * x * y * a = y⁻¹ * a * (y * x * y) * a := by simp only [hb]; group
      _ = y⁻¹ * a * x * a := by rw [hy']
      _ = y⁻¹ * ((a * a) * (a * a)) := by rw [← haax]; group
      _ = y := by rw [haax, hx1, mul_one, hyinv]
  obtain ⟨g₀, hg0⟩ : ∃ g₀ : G, g₀⁻¹ * (a * b) * g₀ = y := by
    refine ⟨c₂ * c₁ * a, ?_⟩
    calc (c₂ * c₁ * a)⁻¹ * (a * b) * (c₂ * c₁ * a)
        = a⁻¹ * (c₁⁻¹ * (c₂⁻¹ * (a * b) * c₂) * c₁) * a := by group
      _ = a⁻¹ * (c₁⁻¹ * ((a * b) * x) * c₁) * a := by rw [hc₂]
      _ = a⁻¹ * ((c₁⁻¹ * (a * b) * c₁) * (c₁⁻¹ * x * c₁)) * a := by group
      _ = a⁻¹ * ((a * b) * (x * y)) * a := by rw [hc₁, hc₁']
      _ = b * x * y * a := by group
      _ = y := key
  have hH : IsIntrinsic (a * b) (J.map (MulAut.conj g₀).toMonoidHom) := by
    have h1 := isIntrinsic_map_conj cfg.hJ g₀
    have e : g₀ * y * g₀⁻¹ = a * b := by
      calc g₀ * y * g₀⁻¹ = g₀ * (g₀⁻¹ * (a * b) * g₀) * g₀⁻¹ := by rw [hg0]
        _ = a * b := by group
    rwa [e] at h1
  have cfg' : RecipCfg G (a * b) x (J.map (MulAut.conj g₀).toMonoidHom) L :=
    ⟨cfg.simple, hu1, cfg.hx, huC, hH, cfg.hL⟩
  have hau : a * (a * b) = (a * b) * a := by
    calc a * (a * b) = a * (b * a) := by rw [hcomm]
      _ = (a * b) * a := by group
  have hxH : x ∈ normalizer ((J.map (MulAut.conj g₀).toMonoidHom : Subgroup G) : Set G) := by
    by_contra hxH
    exact not_commute_of_orderOf_four h327 cfg' huN hxH haL ha4 hau
  have hnfx : ¬ InducesFAut x (J.map (MulAut.conj g₀).toMonoidHom) := by
    intro hf
    have h3 := lemma_28_3 hBal G (a * b) x _ L cfg' (Or.inr hf)
    have hucs : a * b ∈ cSec L := h3.2.1
    have h1 := (phi_eq_one_iff L huN).mpr hucs
    rw [hphi_u] at h1
    exact hacn (mem_center_of_conj_eq_one h1)
  obtain ⟨g, h1, h2⟩ :=
    ((lemma_28_4 h44 hAut G cfg.simple x cfg.hx L cfg.hL (a * b) hu1 huN hnf_u).2 _ hH hxH hnfx)
  exact ⟨g, h2, h1⟩

theorem lemma_28_6 (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut) (h327 : IG_3_27) :
    ∀ (G : Type) [Group G] [Finite G] (x y : G) (L J : Subgroup G), RecipCfg G x y L J →
      x ∈ normalizer (J : Set G) → y ∉ normalizer (L : Set G) →
      ¬ InducesFAut x J → ¬ InducesFAut y L →
        ∀ u ∈ IDiag y L, orderOf u = 2 → ∃ g : G, g⁻¹ * u * g = x ∧ g⁻¹ * x * g = u := by
  intro G _ _ x y L J cfg hxJ hyL hfx _ u hu hu2
  have hx1 := mul_self_eq_one_of_orderOf_eq_two cfg.hx
  have hy1 := mul_self_eq_one_of_orderOf_eq_two cfg.hy
  obtain ⟨T, hT, hTn⟩ := exists_invariant_sylow (isPGroup_zpowers_of_mul_self_eq_one hy1)
    (zpowers_le.mpr (mem_normalizer_sup_conjugate hy1 L))
  have hyT : y ∈ normalizer (T : Set G) := hTn (mem_zpowers y)
  obtain ⟨hIcomp, -, -, h4⟩ := h327 G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL hyL
  obtain ⟨S₀, hS₀, hS₀eq⟩ := h4 T hT hyT
  have hupow : ∃ n : ℕ, u ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    have := pow_orderOf_eq_one u
    rw [hu2] at this
    simpa using this
  obtain ⟨i, hiI, hi⟩ := exists_conj_mem_of_isSylow2In hS₀ hu hupow
  have hi' : i⁻¹ * u * i ∈ (S₀ : Set G) := hi
  rw [hS₀eq] at hi'
  obtain ⟨a, haTL, hae⟩ := hi'
  have hae' : a * (y⁻¹ * a * y) = i⁻¹ * u * i := hae
  have hu1' : orderOf (a * (y⁻¹ * a * y)) = 2 := by
    rw [hae']
    have := orderOf_conj_eq i⁻¹ u
    rw [inv_inv] at this
    rw [this, hu2]
  have huI' : a * (y⁻¹ * a * y) ∈ IDiag y L := by
    rw [hae']
    exact mul_mem (mul_mem (inv_mem hiI) hu) hiI
  obtain ⟨g', hg1, hg2⟩ := lemma_28_6_core hBal h44 hAut h327 cfg hxJ hyL hfx hT haTL
    (comm_of_mem_sylow_inf cfg.comm cfg.hL hyL hT.2.1 hyT haTL haTL) hu1' huI'
  have hix : i * x = x * i := mem_centralizer_singleton_iff.mp (hIcomp.1 hiI).1
  have hix' : i * x * i⁻¹ = x := by rw [hix]; group
  have hix'' : i⁻¹ * x * i = x := by
    calc i⁻¹ * x * i = i⁻¹ * (x * i) := by group
      _ = i⁻¹ * (i * x) := by rw [hix]
      _ = x := by group
  rw [hae'] at hg1 hg2
  refine ⟨i * g' * i⁻¹, ?_, ?_⟩
  · calc (i * g' * i⁻¹)⁻¹ * u * (i * g' * i⁻¹) = i * (g'⁻¹ * (i⁻¹ * u * i) * g') * i⁻¹ := by group
      _ = i * x * i⁻¹ := by rw [hg1]
      _ = x := hix'
  · calc (i * g' * i⁻¹)⁻¹ * x * (i * g' * i⁻¹) = i * (g'⁻¹ * (i⁻¹ * x * i) * g') * i⁻¹ := by group
      _ = i * (g'⁻¹ * x * g') * i⁻¹ := by rw [hix'']
      _ = i * (i⁻¹ * u * i) * i⁻¹ := by rw [hg2]
      _ = u := by group

end CFSG.GH74.GLS.Stage1.Thm2.Recip
