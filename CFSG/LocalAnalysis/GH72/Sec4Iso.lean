module

public import CFSG.LocalAnalysis.GH72.Sec4IsoU
public import CFSG.LocalAnalysis.GH72.Sec4A

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.GorensteinWalter (HasDihedralSylowTwo)

namespace G4b

section Isolated

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_bar_of_isSylowOf {p : ℕ} [Fact p.Prime] {C P W : Subgroup G} (hWC : W ≤ C)
    (h : ABGLocalTools.IsSylowOf p P W) : ABGLocalTools.IsSylowOf p (bar C P) (bar C W) := by
  have h1 : ABGLocalTools.IsSylowOf p (P.subgroupOf C) (W.subgroupOf C) := by
    rw [← ABGLocalTools.isSylowOf_map_subtype_iff C, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.2 (h.le.trans hWC), inf_eq_left.2 hWC]
    exact h
  exact isSylowOf_map_hom h1 _

theorem exists_isMaxInvIn_inf_C {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H A P : Subgroup G}
    {z : G} (hcov : ∀ h ∈ H, ∃ c ∈ H ⊓ C z, c⁻¹ * h ∈ O H) (hAz : A ≤ C z) (hAH : A ≤ H)
    (hA2 : IsPGroup 2 A) (hP : IsMaxInvIn p A H P) :
    ∃ P' : Subgroup G, IsMaxInvIn p A (H ⊓ C z) P' ∧ bar H P' = bar H P := by
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G := H ⊓ C z with hK
  have hAK : A ≤ K := le_inf hAH hAz
  set W : Subgroup G := K ⊓ (P ⊔ O H) with hW
  have hPO : P ≤ normalizer (O H : Set G) := hP.1.trans (le_normalizer_O H)
  have hWodd : Odd (Nat.card W) :=
    odd_card_of_le inf_le_right (odd_card_sup hPO (odd_card_of_isPGroup hp hp2 hP.2.1)
      (card_O_odd H))
  have hAW : A ≤ normalizer (W : Set G) := fun a ha =>
    mem_normalizer_inf (le_normalizer (hAK ha))
      (mem_normalizer_sup (hP.2.2.1 ha) (le_normalizer_O H (hAH ha)))
  obtain ⟨T, hT, -⟩ := exists_isMaxInvIn_ge (A := A) (H := W) bot_le IsPGroup.of_bot
    (by rw [normalizer_eq_top_iff.2 inferInstance]; exact le_top)
  have hTsyl := isSylowOf_of_isMaxInvIn hp hA2 hT hT.1 le_rfl hWodd hAW
  obtain ⟨P', hP', hTP'⟩ := exists_isMaxInvIn_ge (hT.1.trans inf_le_left) hT.2.1 hT.2.2.1
  refine ⟨P', hP', ?_⟩
  have hWP : bar H W = bar H P := by
    apply le_antisymm
    · refine (bar_mono inf_le_right).trans ?_
      rw [bar_sup hP.1 (O_le_self H), bar_O, sup_bot_eq]
    · rintro _ ⟨⟨x, hxH⟩, hx, rfl⟩
      have hx' : x ∈ P := hx
      obtain ⟨c, hc, hcx⟩ := hcov x hxH
      have hcH : c ∈ H := (mem_inf.1 hc).1
      have hcW : c ∈ W := by
        refine mem_inf.2 ⟨hc, ?_⟩
        have e : c = x * (c⁻¹ * x)⁻¹ := by group
        rw [e]
        exact mul_mem (mem_sup_left hx') (mem_sup_right (inv_mem hcx))
      have he : QuotientGroup.mk' (CFSG.oddCore H) ⟨x, hxH⟩ =
          QuotientGroup.mk' (CFSG.oddCore H) ⟨c, hcH⟩ := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        have : (⟨x, hxH⟩ : H)⁻¹ * ⟨c, hcH⟩ = (⟨c⁻¹ * x, mul_mem (inv_mem hcH) hxH⟩ : H)⁻¹ :=
          Subtype.ext (by simp)
        rw [this]
        exact inv_mem ((mem_oddCore_iff _).2 hcx)
      rw [he]
      exact mk_mem_bar hcH hcW
  have hTbar : bar H T = bar H P := by
    have h := isSylowOf_bar_of_isSylowOf (C := H) (inf_le_left.trans inf_le_left) hTsyl
    rw [hWP] at h
    exact (h.eq_of_le h.le le_rfl ((hP.2.1.comap_subtype (K := H)).map _)).symm
  have hmax := (isMaxInvIn_bar hp hp2 le_rfl hAH hA2 hP).2.2.2
  exact hmax (bar H P') (bar_mono (hP'.1.trans inf_le_left)) ((hP'.2.1.comap_subtype).map _)
    (bar_le_normalizer_bar hP'.2.2.1) (hTbar ▸ bar_mono hTP')

theorem exists_conj_of_covers_C {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H A : Subgroup G}
    {z : G} (hcov : ∀ h ∈ H, ∃ c ∈ H ⊓ C z, c⁻¹ * h ∈ O H) (hAz : A ≤ C z) (hAH : A ≤ H)
    (hA2 : IsPGroup 2 A)
    (hK : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A (H ⊓ C z) P₁ → IsMaxInvIn p A (H ⊓ C z) P₂ →
      ∃ k ∈ (H ⊓ C z) ⊓ normalizer (A : Set G), P₁.map (MulAut.conj k).toMonoidHom = P₂)
    {P₁ P₂ : Subgroup G} (h₁ : IsMaxInvIn p A H P₁) (h₂ : IsMaxInvIn p A H P₂) :
    ∃ g ∈ H ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  obtain ⟨P₁', hP₁', hb₁⟩ := exists_isMaxInvIn_inf_C hp hp2 hcov hAz hAH hA2 h₁
  obtain ⟨P₂', hP₂', hb₂⟩ := exists_isMaxInvIn_inf_C hp hp2 hcov hAz hAH hA2 h₂
  obtain ⟨k, hk, hkP⟩ := hK P₁' P₂' hP₁' hP₂'
  obtain ⟨hkK, hkA⟩ := mem_inf.1 hk
  have hkH : k ∈ H := (mem_inf.1 hkK).1
  refine exists_conj_of_bar hp hp2 le_rfl hAH hA2 h₁ h₂
    (y := QuotientGroup.mk' (CFSG.oddCore H) ⟨k, hkH⟩) ?_ ?_
  · rw [bar_self]
    exact mem_inf.2 ⟨mem_top _, bar_le_normalizer_bar le_rfl (mk_mem_bar hkH hkA)⟩
  · rw [← hb₁, ← bar_map_conj hkH, hkP, hb₂]

end Isolated

section Side

variable {G : Type} [Group G] [Finite G] {z : G} {P Q : Subgroup G} {H₁ : Subgroup (Bar (C z))}

theorem IsDih.of_mulEquiv {X Y : Type} [Group X] [Group Y] {D : Subgroup X} {E : Subgroup Y}
    (hD : IsDih D) (e : D ≃* E) : IsDih E := by
  obtain ⟨a, ha, ⟨e₀⟩⟩ := hD
  exact ⟨a, ha, ⟨e.symm.trans e₀⟩⟩

theorem hasDihedralSylowTwo_of_le_H₁ (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆)
    (hQD : IsDih Q) {U V : Subgroup (Bar (C z))} (hUH : U ≤ H₁) (hVU : V ≤ U)
    (hV : IsKleinFour V) : HasDihedralSylowTwo U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := hS.isPGroup.to_le le_sup_right
  have hQsyl := isSylowOf_bar hS hQP hPQ h₁ h₃ h₄
  obtain ⟨eQ⟩ := nonempty_mulEquiv_bar (le_sup_right.trans hS.le) hQ2
  have hQbar : IsDih (bar (C z) Q) := IsDih.of_mulEquiv hQD eQ
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  intro T
  set T' : Subgroup (Bar (C z)) := (T : Subgroup U).map U.subtype with hT'
  have hT'syl : ABGLocalTools.IsSylowOf 2 T' U := ⟨T, rfl⟩
  obtain ⟨c, hcU, hcV⟩ := exists_mem_map_conj_le_of_isSylowOf hT'syl hVU hV2
  obtain ⟨h, hhH, hhT⟩ := exists_mem_map_conj_le_of_isSylowOf hQsyl
    (hT'syl.le.trans hUH) hT'syl.isPGroup
  have hfour : CFSG.CGT.Foote81L6.TStruct.IsFourIn (bar (C z) Q)
      ((V.map (MulAut.conj c).toMonoidHom).map (MulAut.conj h).toMonoidHom) := by
    refine ⟨(map_mono hcV).trans hhT, ?_, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hv2 : v * v = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : V))
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h * (c * v * c⁻¹) * h⁻¹ * (h * (c * v * c⁻¹) * h⁻¹) = h * c * (v * v) * c⁻¹ * h⁻¹ := by
            group
        _ = 1 := by rw [hv2]; group
    · rw [card_map_of_injective (MulAut.conj h).injective,
        card_map_of_injective (MulAut.conj c).injective, hV.card_four]
  have hTD : IsDih (T'.map (MulAut.conj h).toMonoidHom) := hQbar.of_le hhT hfour (map_mono hcV)
  obtain ⟨a, ha, ⟨e⟩⟩ := hTD
  have e₁ : (T : Subgroup U) ≃* T' := (T : Subgroup U).equivMapOfInjective U.subtype
    U.subtype_injective
  have e₂ : T' ≃* T'.map (MulAut.conj h).toMonoidHom :=
    T'.equivMapOfInjective _ (MulAut.conj h).injective
  exact ⟨a, ha, ⟨(e₁.trans e₂).trans e⟩⟩


theorem exists_conj_of_le_C (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆) (hQD : IsDih Q) {A W V : Subgroup G} (hA : W ⊔ V = A)
    (hWP : W ≤ P) (hVQ : V ≤ Q) (hV : IsKleinFour V) (hA2 : IsPGroup 2 A) {K : Subgroup G}
    (hKz : K ≤ C z) (hAK : A ≤ K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P₁ P₂ : Subgroup G}
    (hP₁ : IsMaxInvIn p A K P₁) (hP₂ : IsMaxInvIn p A K P₂) :
    ∃ g ∈ K ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hPz : P ≤ C z := le_sup_left.trans hS.le
  have hQz : Q ≤ C z := le_sup_right.trans hS.le
  have hWz : W ≤ C z := hWP.trans hPz
  have hVz : V ≤ C z := hVQ.trans hQz
  have hAWV : bar (C z) A = bar (C z) W ⊔ bar (C z) V := by rw [← hA, bar_sup hWz hVz]
  set U : Subgroup (Bar (C z)) := bar (C z) K ⊓ H₁ with hU
  have hVbU : bar (C z) V ≤ U :=
    le_inf (bar_mono ((le_sup_right.trans hA.le).trans hAK))
      ((bar_mono hVQ).trans (h₄.trans (commutator_le_self H₁)))
  have hPbH : bar (C z) P ≤ centralizer (H₁ : Set (Bar (C z))) := le_centralizer_iff.1 h₃
  have hWbC : bar (C z) W ≤ centralizer (H₁ : Set (Bar (C z))) := (bar_mono hWP).trans hPbH
  have hbar : ∀ {R : Subgroup G}, IsMaxInvIn p A K R → IsMaxInvIn p (bar (C z) V) U (bar (C z) R) := by
    intro R hR
    have hR' := isMaxInvIn_bar hp hp2 hKz hAK hA2 hR
    have hRH : bar (C z) R ≤ H₁ := fun y hy => mem_H₁_of_odd hP h₁ h₂ h₃
      (Odd.of_dvd_nat (odd_card_of_isPGroup hp hp2 hR'.2.1) (Subgroup.orderOf_dvd_natCard _ hy))
    refine ⟨le_inf hR'.1 hRH, hR'.2.1, (le_sup_right.trans hAWV.ge).trans hR'.2.2.1,
      fun Q' hQ'U hQ'p hVQ' hRQ' => hR'.2.2.2 Q' (hQ'U.trans inf_le_left) hQ'p ?_ hRQ'⟩
    rw [hAWV]
    exact sup_le ((hWbC.trans (centralizer_le (SetLike.coe_subset_coe.2
      (hQ'U.trans inf_le_right)))).trans (centralizer_le_normalizer _)) hVQ'
  have hDU := hasDihedralSylowTwo_of_le_H₁ hS hQP hPQ h₁ h₃ h₄ hQD inf_le_right hVbU
    (isKleinFour_bar hVz hV)
  obtain ⟨u, hu, huP⟩ := exists_conj_of_hasDihedralSylowTwo hVbU (isKleinFour_bar hVz hV) hDU
    hp hp2 (hbar hP₁) (hbar hP₂)
  obtain ⟨huU, huV⟩ := mem_inf.1 hu
  refine exists_conj_of_bar hp hp2 hKz hAK hA2 hP₁ hP₂ (y := u) ?_ huP
  refine mem_inf.2 ⟨(mem_inf.1 huU).1, ?_⟩
  rw [hAWV]
  exact mem_normalizer_sup (centralizer_le_normalizer _
    (centralizer_le (SetLike.coe_subset_coe.2 (bar_mono hWP)) (h₃ (mem_inf.1 huU).2))) huV

end Side

end G4b

namespace Sec4Setting

open G4b

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem exists_isIsolatedIn_mem {H A : Subgroup G} (hAH : A ≤ H) (hAS : A ≤ 𝔖.S)
    (hA : IsE16 A) (hsyl : ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) {t₀ : G}
    (ht₀ : IsIsolatedIn H t₀) : ∃ t ∈ A, IsIsolatedIn H t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (zpowers t₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht₀.2.1, pow_one])
  obtain ⟨c, hcH, hct⟩ := exists_mem_conj_mem_of_isSylowOf hsyl ht₀.1 hT
  have ht : IsIsolatedIn H (c * t₀ * c⁻¹) := by
    have h := ht₀.map_conj c
    rwa [mem_normalizer_iff_map_conj_eq'.1 (le_normalizer hcH)] at h
  set t := c * t₀ * c⁻¹ with htdef
  have htS : t ∈ (𝔖.S : Subgroup G) := (mem_inf.1 hct).1
  have hS2 : IsPGroup 2 (𝔖.S : Subgroup G) := 𝔖.S.isPGroup'
  have hcomm : ∀ a ∈ A, a * t = t * a := by
    intro a ha
    have h1 := ht.conj_mul_inv_mem_O (hAH ha)
    have h2 : a * t * a⁻¹ * t⁻¹ ∈ (𝔖.S : Subgroup G) :=
      mul_mem (mul_mem (mul_mem (hAS ha) htS) (inv_mem (hAS ha))) (inv_mem htS)
    have h3 := eq_one_of_mem_of_mem hS2 (card_O_odd H) h2 h1
    calc a * t = (a * t * a⁻¹ * t⁻¹) * t * a := by group
      _ = t * a := by rw [h3, one_mul]
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht.2.1, pow_two] at h
  have hA2 : ∀ x ∈ A, x * x = 1 := CFSG.CGT.Foote81L6.TStruct.isElemAbelian_two_iff.1 hA.1
  have hZ2 : ∀ y ∈ zpowers t, y * y = 1 := fun y hy => by
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers htt hy with rfl | rfl
    · exact mul_one 1
    · exact htt
  have hc : ∀ x ∈ A, ∀ y ∈ zpowers t, x * y = y * x := fun x hx y hy => by
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers htt hy with rfl | rfl
    · rw [mul_one, one_mul]
    · exact hcomm x hx
  have hE2 : ∀ x ∈ A ⊔ zpowers t, x * x = 1 := fun x hx =>
    CFSG.CGT.Foote81L6.TStruct.mul_self_of_mem_sup hA2 hZ2 hc hx
  have hES : A ⊔ zpowers t ≤ 𝔖.S := sup_le hAS (zpowers_le.2 htS)
  have hEcard := 𝔖.decomp.card_le_sixteen hES
    (CFSG.CGT.Foote81L6.TStruct.isElemAbelian_two_iff.2 hE2)
  have hAE : A = A ⊔ zpowers t := eq_of_le_of_card_ge le_sup_left (by rw [hA.2]; exact hEcard)
  exact ⟨t, hAE ▸ mem_sup_right (mem_zpowers t), ht⟩


theorem lemma_4_5_iso_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (H A : Subgroup G) (hAH : A ≤ H) (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (hsyl : ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) {t₀ : G}
    (ht₀ : IsIsolatedIn H t₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (P₁ P₂ : Subgroup G)
    (h₁ : IsMaxInvIn p A H P₁) (h₂ : IsMaxInvIn p A H P₂) :
    ∃ g ∈ H ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  obtain ⟨t, htA, ht⟩ := exists_isIsolatedIn_mem 𝔖 hAH hAS hA hsyl ht₀
  have ht1 : t ≠ 1 := fun h => by
    have := ht.2.1
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have htS : t ∈ (𝔖.S : Subgroup G) := hAS htA
  have hAC : ∀ {z : G}, z ∈ A → A ≤ C z := fun hz a ha =>
    mem_centralizer_singleton_iff.2 (comm_of_isE16 hA ha hz)
  have step : ∀ {z n : G}, n ∈ normalizer (A : Set G) → n * z * n⁻¹ = t → z ∈ A →
      (∀ K : Subgroup G, K ≤ C z → A ≤ K → ∀ Q₁ Q₂ : Subgroup G, IsMaxInvIn p A K Q₁ →
        IsMaxInvIn p A K Q₂ → ∃ k ∈ K ⊓ normalizer (A : Set G),
          Q₁.map (MulAut.conj k).toMonoidHom = Q₂) →
      ∃ g ∈ H ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
    intro z n hnA hnz hzA hside
    have hAn : A.map (MulAut.conj n⁻¹).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq'.1 (inv_mem hnA)
    refine G4b.exists_conj_of_map_conj (x := n⁻¹) ?_ h₁ h₂
    rw [hAn]
    intro Q₁ Q₂ hQ₁ hQ₂
    have hz' : IsIsolatedIn (H.map (MulAut.conj n⁻¹).toMonoidHom) z := by
      have h := ht.map_conj n⁻¹
      have e : n⁻¹ * t * n⁻¹⁻¹ = z := by rw [← hnz]; group
      rwa [e] at h
    have hAH' : A ≤ H.map (MulAut.conj n⁻¹).toMonoidHom := hAn ▸ map_mono hAH
    exact exists_conj_of_covers_C hp hp2 (fun h hh => hz'.exists_mem_C hh) (hAC hzA) hAH' hA2
      (fun Q₁' Q₂' hQ₁' hQ₂' => hside _ inf_le_right (le_inf hAH' (hAC hzA)) Q₁' Q₂' hQ₁' hQ₂')
      hQ₁ hQ₂
  obtain ⟨⟨H₁, h₁', h₂', h₃', h₄', -⟩, ⟨K₁, k₁, k₂, k₃, k₄, -⟩⟩ :=
    h315 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  by_cases htX : t ∈ 𝔖.X A
  · obtain ⟨n, hnA, hnt⟩ := exists_mem_normalizer_conj_eq_of_mem_X 𝔖 hAS hA htX ht1
    have hS : ABGLocalTools.IsSylowOf 2 (𝔖.S₁ ⊔ 𝔖.S₂) (C 𝔖.z₁) := by
      rw [𝔖.decomp.sup_eq]
      exact isSylowOf_of_sylow_le 𝔖.S 𝔖.S_le_C_z₁
    exact step hnA hnt (X_le_A 𝔖 (z₁_mem_X 𝔖 hAS hA)) fun K hKz hAK Q₁ Q₂ hQ₁ hQ₂ =>
      exists_conj_of_le_C hS (S₂_le_centralizer_S₁ 𝔖) 𝔖.decomp.inf_eq h₁' h₂' h₃' h₄'
        𝔖.decomp.isDih₂ (X_sup_Y 𝔖 hAS hA) (X_le_S₁ 𝔖) (Y_le_S₂ 𝔖) (isKleinFour_Y 𝔖 hAS hA)
        hA2 hKz hAK hp hp2 hQ₁ hQ₂
  by_cases htY : t ∈ 𝔖.Y A
  · obtain ⟨n, hnA, hnt⟩ := exists_mem_normalizer_conj_eq_of_mem_Y 𝔖 hAS hA htY ht1
    have hS : ABGLocalTools.IsSylowOf 2 (𝔖.S₂ ⊔ 𝔖.S₁) (C 𝔖.z₂) := by
      rw [sup_comm, 𝔖.decomp.sup_eq]
      exact isSylowOf_of_sylow_le 𝔖.S (S_le_C_z₂ 𝔖)
    have hPQ : 𝔖.S₂ ⊓ 𝔖.S₁ = ⊥ := by
      rw [inf_comm]
      exact 𝔖.decomp.inf_eq
    have hA' : 𝔖.Y A ⊔ 𝔖.X A = A := by
      rw [sup_comm]
      exact X_sup_Y 𝔖 hAS hA
    exact step hnA hnt (Y_le_A 𝔖 (z₂_mem_Y 𝔖 hAS hA)) fun K hKz hAK Q₁ Q₂ hQ₁ hQ₂ =>
      exists_conj_of_le_C hS (S₁_le_centralizer_S₂ 𝔖) hPQ k₁ k₂ k₃ k₄ 𝔖.decomp.dih₁ hA'
        (Y_le_S₂ 𝔖) (X_le_S₁ 𝔖) (isKleinFour_X 𝔖 hAS hA) hA2 hKz hAK hp hp2 hQ₁ hQ₂
  have hc : IsConj t (𝔖.z₁ * 𝔖.z₂) := by
    rcases 𝔖.isConj_z ht.2.1 with hc | hc | hc
    · exact absurd (mem_inf.2 ⟨htA, mem_S₁_of_isConj 𝔖 𝔖.hz₁.1 htS 𝔖.hz₁.2.1 hc.symm⟩) htX
    · exact absurd (mem_inf.2 ⟨htA, mem_S₂_of_isConj 𝔖 𝔖.hz₂.1 htS 𝔖.hz₂.2.1 hc.symm⟩) htY
    · exact hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  obtain ⟨Kc, hKC, hKn, hKodd, m, hm⟩ := h317 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have hcov : ∀ h ∈ H, ∃ c ∈ H ⊓ C t, c⁻¹ * h ∈ O H := fun h hh => ht.exists_mem_C hh
  have hconjC : ∀ q ∈ H ⊓ C t, g * q * g⁻¹ ∈ C (𝔖.z₁ * 𝔖.z₂) := by
    intro q hq
    rw [← hg, mem_centralizer_singleton_iff]
    have hqt : q * t = t * q := mem_centralizer_singleton_iff.1 (mem_inf.1 hq).2
    calc g * q * g⁻¹ * (g * t * g⁻¹) = g * (q * t) * g⁻¹ := by group
      _ = g * (t * q) * g⁻¹ := by rw [hqt]
      _ = g * t * g⁻¹ * (g * q * g⁻¹) := by group
  let Xc := H ⊓ C t
  let φ : Xc →* G := (MulAut.conj g).toMonoidHom.comp Xc.subtype
  have hφC : ∀ x : Xc, φ x ∈ C (𝔖.z₁ * 𝔖.z₂) := fun x => hconjC x x.2
  have hφinj : Function.Injective φ := (MulAut.conj g).injective.comp Xc.subtype_injective
  let N : Subgroup Xc := Kc.comap φ
  have hNn : N.Normal := by
    constructor
    intro a ha b
    have h1 := hKn.conj_mem ⟨φ a, hKC ha⟩ ha ⟨φ b, hφC b⟩
    show φ (b * a * b⁻¹) ∈ Kc
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hNodd : Odd (Nat.card N) := by
    have hle : N.map φ ≤ Kc := map_le_iff_le_comap.2 le_rfl
    rw [← card_map_of_injective hφinj]
    exact Odd.of_dvd_nat hKodd (card_dvd_of_le hle)
  have hpow : ∀ x : Xc, ∃ k : ℕ, x ^ 2 ^ k ∈ N := fun x =>
    ⟨m, by
      show φ (x ^ 2 ^ m) ∈ Kc
      rw [map_pow]
      exact pow_mem_of_relIndex_eq hKn hm (hφC x)⟩
  have h2 : IsPGroup 2 (Bar H) :=
    isPGroup_of_surjective_of_odd_normal (oddCore_quotient_oddCore_eq_bot H) _
      (surjective_of_covers inf_le_left hcov) N hNn hNodd hpow
  have hbot : ∀ {P : Subgroup G}, IsMaxInvIn p A H P → bar H P = ⊥ := by
    intro P hP
    refine eq_bot_iff.2 fun y hy => (mem_bot).2 ?_
    exact eq_one_of_mem_of_mem (A := ⊤) (h2.to_subgroup ⊤)
      (odd_card_of_isPGroup hp hp2 ((hP.2.1.comap_subtype (K := H)).map _)) (mem_top y) hy
  refine exists_conj_of_bar hp hp2 le_rfl hAH hA2 h₁ h₂ (y := 1) ?_ ?_
  · rw [bar_self]
    exact mem_inf.2 ⟨mem_top _, one_mem _⟩
  · rw [map_conj_one, hbot h₁, hbot h₂]

theorem lemma_4_5_of
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h44J : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → A ≤ 𝔖.S → IsE16 A →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A)))
        (O2 H ⊔ A))
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (H : Subgroup G) (hH : H ≠ ⊤) (A : Subgroup G) (hAH : A ≤ H) (hA : IsE16 A)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P₁ P₂ : Subgroup G) (h₁ : IsMaxInvIn p A H P₁)
    (h₂ : IsMaxInvIn p A H P₂) :
    ∃ g ∈ H ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  obtain ⟨x, hAx, hsylx⟩ := exists_map_conj_sylow 𝔖 H A hAH hA
  refine G4b.exists_conj_of_map_conj x (fun Q₁ Q₂ hQ₁ hQ₂ => ?_) h₁ h₂
  have hH' : H.map (MulAut.conj x).toMonoidHom ≠ ⊤ := by
    intro h
    apply hH
    rw [← map_conj_inv_map_conj H x, h, map_top_of_surjective _ (MulAut.conj x⁻¹).surjective]
  by_cases hiso : ∀ t, ¬ IsIsolatedIn (H.map (MulAut.conj x).toMonoidHom) t
  · exact lemma_4_5_noniso_of 𝔖 h44 h44J _ hH' hiso _ (map_mono hAH) hAx (G4b.IsE16.map hA _)
      hsylx hp hp2 Q₁ Q₂ hQ₁ hQ₂
  · obtain ⟨t₀, ht₀⟩ := not_forall_not.1 hiso
    exact lemma_4_5_iso_of 𝔖 h315 h317 _ _ (map_mono hAH) hAx (G4b.IsE16.map hA _) hsylx ht₀ hp
      hp2 Q₁ Q₂ hQ₁ hQ₂

end Sec4Setting

end CFSG.GH72
