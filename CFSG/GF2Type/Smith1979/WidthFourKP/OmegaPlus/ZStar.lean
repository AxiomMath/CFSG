module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Component
public import CFSG.GH74.KGH
public import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_conj_ne_commute (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hfaith : ∀ l ∈ S.Lbar g, (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype,
      l * y = y * l) → l = 1) :
    ∃ e ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype,
      e * t * e⁻¹ ≠ t ∧ (e * t * e⁻¹) * t = t * (e * t * e⁻¹) := by
  let E : Subgroup S.O := (timmesfeldLayer S.Mbar).map S.Mbar.subtype
  by_contra hcon
  have hno : ∀ e ∈ E, e * t * e⁻¹ ≠ t → (e * t * e⁻¹) * t ≠ t * (e * t * e⁻¹) := by
    intro e he hne hcomm
    exact hcon ⟨e, he, hne, hcomm⟩
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have hEnorm : S.Mbar ≤ Subgroup.normalizer (E : Set S.O) := Mbar_le_normalizer_layer S
  let Y : Subgroup S.O := E ⊔ Subgroup.zpowers t
  have hE_le_Y : E ≤ Y := le_sup_left
  have htY : t ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  let tY : Y := ⟨t, htY⟩
  have htY2 : tY * tY = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S H.conj_mem ht)
  have htY1 : tY ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hzpow_norm : Subgroup.zpowers t ≤ Subgroup.normalizer (E : Set S.O) :=
    Subgroup.zpowers_le.mpr (hEnorm htM)
  have hisolated : ∀ y : Y, (y * tY * y⁻¹) * tY = tY * (y * tY * y⁻¹) →
      y * tY * y⁻¹ = tY := by
    intro y hy
    have hy' : (y : S.O) ∈ (E ⊔ Subgroup.zpowers t : Subgroup S.O) := by
      simpa only [Y] using y.2
    have hmem : (y : S.O) ∈ (E : Set S.O) * (Subgroup.zpowers t : Set S.O) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left E (Subgroup.zpowers t) hzpow_norm]
      exact hy'
    obtain ⟨e, heE, z, hz, hez⟩ := hmem
    have hz1 : z = 1 ∨ z = t :=
      S8.eq_one_or_eq_of_mem_zpowers (S4.mul_self_of_mem_Lbar S H.conj_mem ht) hz
    have hval : ((y * tY * y⁻¹ : Y) : S.O) = e * t * e⁻¹ := by
      show (y : S.O) * t * (y : S.O)⁻¹ = e * t * e⁻¹
      rw [← hez]
      rcases hz1 with rfl | rfl <;> group
    have hcommS : (e * t * e⁻¹) * t = t * (e * t * e⁻¹) := by
      have h := congrArg Subtype.val hy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, tY] at h
      rw [← hez] at h
      rcases hz1 with rfl | rfl <;> simpa [mul_assoc] using h
    have het : e * t * e⁻¹ = t := by
      by_contra hne
      exact hno e heE hne hcommS
    exact Subtype.ext (by rw [hval, het])
  letI : Fintype Y := Fintype.ofFinite Y
  obtain ⟨N, hNnormal, hNodd, hNmem⟩ :=
    CFSG.ZStar.glauberman_zStar Y tY htY1 htY2 hisolated
  have hE_le_Mbar : E ≤ S.Mbar := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hY_le_Mbar : Y ≤ S.Mbar :=
    sup_le hE_le_Mbar (Subgroup.zpowers_le.mpr htM)
  have hEnormY : (E.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgM : (g : S.O) ∈ S.Mbar := hY_le_Mbar g.2
    exact (Subgroup.mem_normalizer_iff.mp (hEnorm hgM) (n : S.O)).mp hn
  let NE : Subgroup Y := N ⊓ E.subgroupOf Y
  have hNE_normal : NE.Normal := by
    haveI : N.Normal := hNnormal
    refine ⟨fun n hn g => ⟨hNnormal.conj_mem n hn.1 g, hEnormY.conj_mem n hn.2 g⟩⟩
  let A : Subgroup S.O := NE.map Y.subtype
  have hA_le_E : A ≤ E := by
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hn.2
  have hAnormE : (A.subgroupOf E).Normal := by
    refine ⟨fun a ha e => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨n, hnNE, hnval⟩ := Subgroup.mem_map.mp ha
    have heY : (e : S.O) ∈ Y := hE_le_Y e.2
    have hconj : (⟨e, heY⟩ : Y) * n * (⟨e, heY⟩ : Y)⁻¹ ∈ NE :=
      hNE_normal.conj_mem n hnNE ⟨e, heY⟩
    refine Subgroup.mem_map.mpr ⟨_, hconj, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
    rw [show (n : S.O) = a from hnval]
  have hqE : CFSG.Open.IsQuasisimple ↥E := by
    let e := (timmesfeldLayer S.Mbar).equivMapOfInjective S.Mbar.subtype S.Mbar.subtype_injective
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq
  have hEeven : Even (Nat.card ↥E) := by
    have hnonab :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥E hqE
    haveI : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hqE.2
    have heven_quot : Even (Nat.card (↥E ⧸ Subgroup.center ↥E)) :=
      CFSG.GH74.even_card_of_nonabelian_simple hnonab
    exact even_iff_two_dvd.mpr
      (dvd_trans (even_iff_two_dvd.mp heven_quot) (Subgroup.card_quotient_dvd_card _))
  have hAodd : Odd (Nat.card A) := by
    have hAN : A ≤ N.map Y.subtype := by
      rintro _ ⟨n, hn, rfl⟩
      exact ⟨n, hn.1, rfl⟩
    have hmap : Nat.card ↥(N.map Y.subtype) = Nat.card ↥N :=
      Subgroup.card_map_of_injective Y.subtype_injective
    have hdvd : Nat.card A ∣ Nat.card ↥N := by
      rw [← hmap]
      exact Subgroup.card_dvd_of_le hAN
    exact Odd.of_dvd_nat hNodd hdvd
  have hproper : (A.subgroupOf E) ≠ ⊤ := by
    intro htop
    have hEA : E ≤ A := by
      intro e he
      let eE : ↥E := ⟨e, he⟩
      have hmem : eE ∈ (⊤ : Subgroup ↥E) := Subgroup.mem_top eE
      rw [← htop] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have hAE : A = E := le_antisymm hA_le_E hEA
    have hoddE : Odd (Nat.card E) := by rw [← hAE]; exact hAodd
    exact (Nat.not_even_iff_odd.mpr hoddE) hEeven
  haveI : (A.subgroupOf E).Normal := hAnormE
  have hAcenter : (A.subgroupOf E) ≤ Subgroup.center ↥E :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hqE _ hproper
  have hcenter_of_mem : ∀ e ∈ E,
      e * t * e⁻¹ * t⁻¹ ∈ (Subgroup.center ↥E).map E.subtype := by
    intro e he
    have hEcomm : e * t * e⁻¹ * t⁻¹ ∈ E := by
      have ht_norm : t ∈ Subgroup.normalizer (E : Set S.O) := hEnorm htM
      have h1 : t * e⁻¹ * t⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp ht_norm (e⁻¹)).mp (E.inv_mem he)
      have h2 : e * (t * e⁻¹ * t⁻¹) ∈ E := E.mul_mem he h1
      simpa [mul_assoc] using h2
    have hAcomm : e * t * e⁻¹ * t⁻¹ ∈ A := by
      have hmemN : (⟨e, hE_le_Y he⟩ : Y) * tY * (⟨e, hE_le_Y he⟩ : Y)⁻¹ * tY⁻¹ ∈ N :=
        hNmem ⟨e, hE_le_Y he⟩
      have hmemE : (⟨e, hE_le_Y he⟩ : Y) * tY * (⟨e, hE_le_Y he⟩ : Y)⁻¹ * tY⁻¹ ∈
          E.subgroupOf Y := by
        rw [Subgroup.mem_subgroupOf]
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, tY] using hEcomm
      exact Subgroup.mem_map.mpr ⟨_, ⟨hmemN, hmemE⟩, by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype, tY]⟩
    have hsub : (⟨e * t * e⁻¹ * t⁻¹, hEcomm⟩ : ↥E) ∈ A.subgroupOf E := by
      rw [Subgroup.mem_subgroupOf]
      exact hAcomm
    have hcent : (⟨e * t * e⁻¹ * t⁻¹, hEcomm⟩ : ↥E) ∈ Subgroup.center ↥E :=
      hAcenter hsub
    exact ⟨⟨e * t * e⁻¹ * t⁻¹, hEcomm⟩, hcent, rfl⟩
  have hJ : Group.IsPerfect ↥E := (Group.isPerfect_def).2 hqE.1
  have hcentE : t ∈ Subgroup.centralizer (E : Set S.O) := by
    refine CFSG.mem_centralizer_of_commutator_mem_center hJ (hEnorm htM) ?_
    intro j hj
    have h := hcenter_of_mem j hj
    have hEq : t * j * t⁻¹ * j⁻¹ = (j * t * j⁻¹ * t⁻¹)⁻¹ := by group
    rw [hEq]
    exact (Subgroup.map E.subtype (Subgroup.center ↥E)).inv_mem h
  have hcommE : ∀ y ∈ E, t * y = y * t := by
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp hcentE) y hy).symm
  exact ht1 (hfaith t ht hcommE)


theorem exists_mem_layer_not_center (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hfaith : ∀ l ∈ S.Lbar g, (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype,
      l * y = y * l) → l = 1)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P)
    (hKP : ∀ c ∈ S14.Ct S t, (∃ k : ℕ, c ^ 2 ^ k = 1) → (∀ x ∈ P, c * x = x * c) →
      ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hKc : ∀ σ ∈ S14.Ct S t, (∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      ∀ m ∈ S.Mbar, σ = m * t * m⁻¹ → σ = t) :
    ∃ e : timmesfeldLayer S.Mbar, ((e : S.Mbar) : S.O) ∈ P ∧
      e ∉ center (timmesfeldLayer S.Mbar) := by
  let E : Subgroup S.O := (timmesfeldLayer S.Mbar).map S.Mbar.subtype
  have hE_le_Mbar : E ≤ S.Mbar := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨e₀, he₀E, he₀ne, he₀comm⟩ := exists_conj_ne_commute H ht ht1 hq hfaith
  have he₀M : e₀ ∈ S.Mbar := hE_le_Mbar he₀E
  let t' : S.O := e₀ * t * e₀⁻¹
  let c : S.O := t * t'
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have ht2 : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have htt_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht'M : t' ∈ S.Mbar := S.Mbar.mul_mem (S.Mbar.mul_mem he₀M htM) (S.Mbar.inv_mem he₀M)
  have ht'2 : t' * t' = 1 := by
    change (e₀ * t * e₀⁻¹) * (e₀ * t * e₀⁻¹) = 1
    calc (e₀ * t * e₀⁻¹) * (e₀ * t * e₀⁻¹)
        = e₀ * (t * (e₀⁻¹ * e₀) * t) * e₀⁻¹ := by group
      _ = e₀ * (t * t) * e₀⁻¹ := by rw [inv_mul_cancel, mul_one]
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have ht'comm : t' * t = t * t' := he₀comm
  have hcM : c ∈ S.Mbar := S.Mbar.mul_mem htM ht'M
  have hct : c * t = t * c := by
    show (t * t') * t = t * (t * t')
    rw [mul_assoc, ht'comm, ← mul_assoc, ht2, one_mul]
  have hcCt : c ∈ S14.Ct S t := (S8.mem_CMt).mpr ⟨hcM, hct⟩
  have hc2 : c * c = 1 := by
    show (t * t') * (t * t') = 1
    calc (t * t') * (t * t') = t * (t' * t) * t' := by group
      _ = t * (t * t') * t' := by rw [ht'comm]
      _ = (t * t) * (t' * t') := by group
      _ = 1 := by rw [ht2, ht'2, one_mul]
  have hcE : c ∈ E := by
    have h1 : t * e₀ * t⁻¹ ∈ E := by
      have hnorm : t ∈ Subgroup.normalizer (E : Set S.O) :=
        Mbar_le_normalizer_layer S htM
      exact (Subgroup.mem_normalizer_iff.mp hnorm e₀).mp he₀E
    have h2 : (t * e₀ * t⁻¹) * e₀⁻¹ ∈ E := E.mul_mem h1 (E.inv_mem he₀E)
    have heq : c = (t * e₀ * t⁻¹) * e₀⁻¹ := by
      show t * (e₀ * t * e₀⁻¹) = (t * e₀ * t⁻¹) * e₀⁻¹
      rw [htt_inv]
      group
    rwa [heq]
  have hex : ∃ p ∈ P, c * p ≠ p * c := by
    by_contra h
    have hcommP : ∀ x ∈ P, c * x = x * c := by
      intro x hx
      by_contra hne
      exact h ⟨x, hx, hne⟩
    have hcV : ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
      hKP c hcCt ⟨1, by show c ^ 2 = 1; rw [pow_two]; exact hc2⟩ hcommP
    have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro v hv
      exact (mem_Nbar.mp (S6.self_mem_Nbar H ht)).2 v hv
    have ht'V : ∀ v ∈ Vt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro v hv
      have hval : t' = t * c := by
        show e₀ * t * e₀⁻¹ = t * (t * (e₀ * t * e₀⁻¹))
        rw [← mul_assoc t t, ht2, one_mul]
      rw [hval]
      change (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
      rw [hcV v hv, htV v hv]
    have ht'Ct : t' ∈ S14.Ct S t := (S8.mem_CMt).mpr ⟨ht'M, ht'comm⟩
    have hteq : t' = t := hKc t' ht'Ct ht'V e₀ he₀M rfl
    exact he₀ne hteq
  obtain ⟨p, hpP, hpc⟩ := hex
  let b : S.O := p⁻¹ * c * p * c⁻¹
  have hpM : p ∈ S.Mbar := Rbar_le_Mbar (hPR hpP)
  have hbP : b ∈ P := by
    have h1 : c * p * c⁻¹ ∈ P := hPn c hcCt p hpP
    have h2 : p⁻¹ * (c * p * c⁻¹) ∈ P := P.mul_mem (P.inv_mem hpP) h1
    have heq : b = p⁻¹ * (c * p * c⁻¹) := by
      show p⁻¹ * c * p * c⁻¹ = p⁻¹ * (c * p * c⁻¹)
      group
    rwa [heq]
  have hbE : b ∈ E := by
    have h1 : p⁻¹ * c * p ∈ E := by
      have hnorm : p⁻¹ ∈ Subgroup.normalizer (E : Set S.O) :=
        Mbar_le_normalizer_layer S (S.Mbar.inv_mem hpM)
      exact (Subgroup.mem_normalizer_iff.mp hnorm c).mp hcE
    have h2 : (p⁻¹ * c * p) * c⁻¹ ∈ E := E.mul_mem h1 (E.inv_mem hcE)
    have heq : b = (p⁻¹ * c * p) * c⁻¹ := rfl
    rwa [heq]
  have hb_ne : b ≠ 1 := by
    intro hb1
    apply hpc
    have h : p⁻¹ * c * p * c⁻¹ = 1 := hb1
    calc c * p = (p * (p⁻¹ * c * p * c⁻¹)) * c := by group
      _ = p * c := by rw [h]; group
  have hcc : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hbc : c * b * c⁻¹ = b⁻¹ := by
    show c * (p⁻¹ * c * p * c⁻¹) * c⁻¹ = (p⁻¹ * c * p * c⁻¹)⁻¹
    calc c * (p⁻¹ * c * p * c⁻¹) * c⁻¹
        = c * p⁻¹ * c * p * (c⁻¹ * c⁻¹) := by group
      _ = c * p⁻¹ * c * p * (c * c) := by rw [hcc]
      _ = c * p⁻¹ * c * p * 1 := by rw [hc2]
      _ = c * p⁻¹ * c * p := by group
      _ = c * p⁻¹ * c⁻¹ * p := by rw [hcc]
      _ = (p⁻¹ * c * p * c⁻¹)⁻¹ := by group
  have hb_ne_inv : b ≠ b⁻¹ := by
    intro hbinv
    have hb2 : b * b = 1 := by
      have := congrArg (fun x => x * b) hbinv
      simpa [mul_assoc] using this
    have hb3 : b ^ 3 = 1 := hP3 b hbP
    have hb1 : b = 1 := by
      have h : b ^ 3 = b := by rw [pow_succ, pow_two, hb2, one_mul]
      rw [hb3] at h
      exact h.symm
    exact hb_ne hb1
  let φ := (timmesfeldLayer S.Mbar).equivMapOfInjective S.Mbar.subtype
    S.Mbar.subtype_injective
  let e : ↥(timmesfeldLayer S.Mbar) := φ.symm ⟨b, hbE⟩
  have heval : (e : S.Mbar) = b :=
    congrArg Subtype.val (φ.apply_symm_apply ⟨b, hbE⟩)
  let c0 : ↥(timmesfeldLayer S.Mbar) := φ.symm ⟨c, hcE⟩
  have hc0val : (c0 : S.Mbar) = c :=
    congrArg Subtype.val (φ.apply_symm_apply ⟨c, hcE⟩)
  refine ⟨e, ?_, ?_⟩
  · rw [heval]
    exact hbP
  · intro hcenter
    have hcommE0 : e * c0 = c0 * e := (Subgroup.mem_center_iff.mp hcenter c0).symm
    have hcomm : b * c = c * b := by
      have h := congrArg (fun x : ↥(timmesfeldLayer S.Mbar) => ((x : S.Mbar) : S.O)) hcommE0
      simpa [← heval, ← hc0val] using h
    have hcb : c * b * c⁻¹ = b := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    apply hb_ne_inv
    rw [← hbc, hcb]
end CFSG.GF2Type.Smith1979.OmegaPlus
