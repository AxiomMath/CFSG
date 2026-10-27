module

public import CFSG.LargeExtraspecial.S111SIMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4 CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def invCentre {H : Type*} [Group H] (F : Subgroup H) : Subgroup H where
  carrier := {z | z ∈ F ⊓ centralizer (F : Set H) ∧ z * z = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hab : b * a = a * b := (mem_centralizer_iff.mp hb.2 a ha.1).symm
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨one_mem _, mul_one 1⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    exact ⟨inv_mem ha, by rw [← mul_inv_rev, ha2, inv_one]⟩

theorem isPGroup_invCentre {H : Type*} [Group H] (F : Subgroup H) : IsPGroup 2 (invCentre F) :=
  fun z => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact z.2.2)⟩

theorem normal_invCentre {H : Type*} [Group H] {F : Subgroup H} (hF : F.Normal) :
    (invCentre F).Normal := by
  refine ⟨fun z hz x => ⟨⟨hF.conj_mem z hz.1.1 x, ?_⟩, ?_⟩⟩
  · have := (Subgroup.normal_centralizer (H := F)).conj_mem z hz.1.2 x
    exact this
  · calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz.2]; group

theorem eq_one_of_mem_centralizer_fstar {v : S.Mbar} (hv2 : v * v = 1)
    (hv : v ∈ centralizer (GeneralizedFitting.subgroup S.Mbar : Set S.Mbar)) : v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvF : v ∈ GeneralizedFitting.subgroup S.Mbar := GeneralizedFitting.centralizer_le S.Mbar hv
  have hΩn := normal_invCentre (GeneralizedFitting.normal S.Mbar)
  have hsub : IsSubnormal ((invCentre (GeneralizedFitting.subgroup S.Mbar)).map S.Mbar.subtype)
      S.Mbar := by
    refine CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf (map_subtype_le _) ?_
    have e : ((invCentre (GeneralizedFitting.subgroup S.Mbar)).map S.Mbar.subtype).subgroupOf
        S.Mbar = invCentre (GeneralizedFitting.subgroup S.Mbar) :=
      comap_map_eq_self_of_injective S.Mbar.subtype_injective _
    rw [e]
    exact hΩn
  have h0 := S5.eq_bot_of_isSubnormal_Mbar S hsub
    ((isPGroup_invCentre _).map S.Mbar.subtype)
  have hvΩ : (v : S.O) ∈ (invCentre (GeneralizedFitting.subgroup S.Mbar)).map S.Mbar.subtype :=
    ⟨v, ⟨⟨hvF, hv⟩, hv2⟩, rfl⟩
  rw [h0, mem_bot] at hvΩ
  exact Subtype.ext hvΩ

omit [Finite G] in
theorem commute_of_mem_zpowers {H : Type*} [Group H] {x y o : H} (hxy : x * y * x⁻¹ = y)
    (ho : o ∈ zpowers y) : o * x = x * o := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ho
  have hc : Commute x y := by
    show x * y = y * x
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hxy]
  exact ((hc.zpow_right k).eq).symm

theorem not_centralizes_layer_aux {H : Type*} [Group H] [Finite H] {O E F : Subgroup H}
    (hON : O.Normal) (hEn : E.Normal) (h3 : Nat.card O ∣ 3) (hF : F = O ⊔ E)
    (hFc : ∀ v : H, v * v = 1 → v ∈ centralizer (F : Set H) → v = 1)
    {t : H} (ht2 : t * t = 1) (ht1 : t ≠ 1) (hni : ∃ s ∈ wclSet t, s ≠ t) :
    ¬ ∀ e ∈ E, e * t = t * e := by
  intro hE
  obtain ⟨_, ⟨m, rfl, hst⟩, hne⟩ := hni
  set s := m * t * m⁻¹ with hs
  have hsE : ∀ e ∈ E, e * s = s * e := by
    intro e he
    have he' : m⁻¹ * e * m ∈ E := by
      have := hEn.conj_mem e he m⁻¹
      simpa using this
    have h1 := hE _ he'
    calc e * s = m * ((m⁻¹ * e * m) * t) * m⁻¹ := by rw [hs]; group
      _ = m * (t * (m⁻¹ * e * m)) * m⁻¹ := by rw [h1]
      _ = s * e := by rw [hs]; group
  have hs2 : s * s = 1 := by
    calc s * s = m * (t * t) * m⁻¹ := by rw [hs]; group
      _ = 1 := by rw [ht2]; group
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    calc t = m⁻¹ * s * m := by rw [hs]; group
      _ = 1 := by rw [h]; group
  obtain ⟨v, hv2, hv1, hvE, hvO⟩ : ∃ v : H, v * v = 1 ∧ v ≠ 1 ∧
      (∀ e ∈ E, e * v = v * e) ∧
      ∀ o ∈ O, o * v = v * o := by
    have htsE : ∀ e ∈ E, e * (t * s) = (t * s) * e := by
      intro e he
      calc e * (t * s) = (e * t) * s := by group
        _ = t * (e * s) := by rw [hE e he]; group
        _ = t * s * e := by rw [hsE e he]; group
    have hts2 : (t * s) * (t * s) = 1 := by
      calc (t * s) * (t * s) = t * (s * t) * s := by group
        _ = t * (t * s) * s := by rw [hst]
        _ = (t * t) * (s * s) := by group
        _ = 1 := by rw [ht2, hs2, one_mul]
    have hts1 : t * s ≠ 1 := by
      intro h
      apply hne
      calc s = t⁻¹ * (t * s) := by group
        _ = t⁻¹ := by rw [h, mul_one]
        _ = t := (eq_inv_of_mul_eq_one_left ht2).symm
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · refine ⟨t, ht2, ht1, hE, fun o ho => ?_⟩
      rw [Subgroup.card_eq_one.mp h1, mem_bot] at ho
      subst ho
      simp
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hNb : O ≠ ⊥ := by
        intro h
        rw [h, card_bot] at h1
        omega
      obtain ⟨⟨y, hyN⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
      have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
      have hyo : orderOf y = 3 := by
        have hdvd : orderOf y ∣ 3 := h1 ▸ Subgroup.orderOf_dvd_natCard _ hyN
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hy1'
        · exact h
      have hNy : O = zpowers y := by
        refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyN) ?_).symm
        rw [Nat.card_zpowers, hyo, h1]
      have hcases : ∀ x : H, x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹ := by
        intro x
        rcases eq_one_or_eq_or_eq_inv_of_orderOf_eq_three hyo
          (hNy ▸ hON.conj_mem y hyN x) with h | h | h
        · exfalso
          apply hy1'
          calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
            _ = 1 := by rw [h]; group
        · exact Or.inl h
        · exact Or.inr h
      rcases hcases t with h | ht'
      · exact ⟨t, ht2, ht1, hE, fun o ho => commute_of_mem_zpowers h (hNy ▸ ho)⟩
      rcases hcases s with h | hs'
      · exact ⟨s, hs2, hs1, hsE, fun o ho => commute_of_mem_zpowers h (hNy ▸ ho)⟩
      refine ⟨t * s, hts2, hts1, htsE, fun o ho => commute_of_mem_zpowers ?_ (hNy ▸ ho)⟩
      calc t * s * y * (t * s)⁻¹ = t * (s * y * s⁻¹) * t⁻¹ := by group
        _ = (t * y * t⁻¹)⁻¹ := by rw [hs']; group
        _ = y := by rw [ht', inv_inv]
  apply hv1
  refine hFc v hv2 (mem_centralizer_iff.mpr fun f hf => ?_)
  have hle : O ⊔ E ≤ centralizer ({v} : Set H) :=
    sup_le (fun o ho => mem_centralizer_singleton_iff.mpr (hvO o ho))
      (fun e he => mem_centralizer_singleton_iff.mpr (hvE e he))
  rw [hF] at hf
  exact mem_centralizer_singleton_iff.mp (hle hf)


theorem not_centralizes_layer (h3 : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hF : timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar)
    {t : S.Mbar} (ht2 : t * t = 1) (ht1 : t ≠ 1) (hni : ∃ s ∈ wclSet t, s ≠ t) :
    ¬ ∀ e ∈ timmesfeldLayer S.Mbar, e * t = t * e :=
  not_centralizes_layer_aux (S5.timmesfeldOddCore_normal S.Mbar) (Layer.normal S.Mbar) h3 hF
    (fun _ hv2 hv => eq_one_of_mem_centralizer_fstar hv2 hv) ht2 ht1 hni

@[expose] def ShultF6ResidualE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → 6 ≤ S.width →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.Mbar), (t : S.O) ∈ S.Lbar g → t ≠ 1 →
      t ∈ (P : Subgroup S.Mbar) → (∀ x ∈ (P : Subgroup S.Mbar), x * t = t * x) →
      IsMulCommutative (wcl t) → wcl t ≤ P →
      (∀ a ∈ wcl t, ∀ x : S.Mbar, x⁻¹ * a * x ∈ (P : Subgroup S.Mbar) → x⁻¹ * a * x ∈ wcl t) →
      GoldschmidtConcl S.Mbar P (wcl t) →
      (Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
        timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) →
      (∃ s ∈ wclSet t, s ≠ t) →
      (¬ ∀ e ∈ timmesfeldLayer S.Mbar, e * t = t * e) →
      False

theorem shultF6ResidualNI_of (h : ShultF6ResidualE) : ShultF6ResidualNI := by
  intro G _ _ _ S g hy hirr h6 hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni
  have ht2 : t * t = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S hy.hyp4.conj_mem ht)
  exact h G S g hy hirr h6 hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni
    (not_centralizes_layer h55.1 h55.2.2 ht2 ht1 hni)

end CFSG.LargeExtraspecial.S11
