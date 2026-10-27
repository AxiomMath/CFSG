module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxSix3
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinGroup

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxSix

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS.Six

@[expose] def nineP : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 3 4, swap 0 1 * swap 3 5, swap 0 1 * swap 4 5,
   swap 0 2 * swap 3 4, swap 0 2 * swap 3 5, swap 0 2 * swap 4 5,
   swap 1 2 * swap 3 4, swap 1 2 * swap 3 5, swap 1 2 * swap 4 5]

theorem nineN_eq : nineN = nineP.map enc := by decide +kernel

theorem mem_nineP_iff (s : Perm (Fin 6)) : s ∈ nineSet ↔ s ∈ nineP := by
  constructor
  · rintro ⟨a, b, d, e, ha, hb, hd, he, hab, hde, rfl⟩
    revert a b d e
    decide +kernel
  · intro h
    simp only [nineP, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨0, 1, 3, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨0, 1, 4, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨0, 2, 3, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨0, 2, 4, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨1, 2, 3, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
    · exact ⟨1, 2, 4, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

theorem mem_nineN_iff (s : Perm (Fin 6)) : s ∈ nineSet ↔ enc s ∈ nineN := by
  rw [mem_nineP_iff, nineN_eq, List.mem_map_of_injective enc_injective]

theorem exists_of_mem_nineN {u : ℕ} (h : u ∈ nineN) : ∃ s ∈ nineSet, enc s = u := by
  rw [nineN_eq] at h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
  exact ⟨s, (mem_nineP_iff s).2 hs, rfl⟩

theorem step1 {Q : Type} [Group Q] (ι : Q →* Perm (Fin 6)) (hι : Function.Injective ι) (D : Set Q)
    (hinv : ∀ d ∈ D, d * d = 1 ∧ d ≠ 1) (hconj : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D)
    (hP : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → ¬ IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set Q))) :
    ∀ d ∈ D, ∀ e ∈ D, d ≠ e → orderOf (d * e) = 3 ∨ orderOf (d * e) = 5 := by
  intro d hd e he hde
  have hd2 := (hinv d hd).1
  have he2 := (hinv e he).1
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hpow : (d * e) ^ 4 = 1 ∨ (d * e) ^ 5 = 1 ∨ (d * e) ^ 6 = 1 := by
    have lift : ∀ k : ℕ, (ι (d * e)) ^ k = 1 → (d * e) ^ k = 1 := fun k h =>
      hι (by rw [map_pow, map_one]; exact h)
    rcases order_pow (ι (d * e)) with h | h | h
    · exact Or.inl (lift 4 h)
    · exact Or.inr (Or.inl (lift 5 h))
    · exact Or.inr (Or.inr (lift 6 h))
  have h4 : (d * e) ^ 4 ≠ 1 := fun h4 =>
    hP d hd e he hde (TransFin.isPGroup_closure_pair hd2 he2 h4)
  have hne1 : d * e ≠ 1 := by
    intro h
    exact hde (mul_left_cancel (h.trans hd2.symm)).symm
  rcases hpow with h | h | h
  · exact absurd h h4
  · right
    have hdvd : orderOf (d * e) ∣ 5 := orderOf_dvd_of_pow_eq_one h
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.1 h1) hne1
    · exact h5
  · have hdvd : orderOf (d * e) ∣ 6 := orderOf_dvd_of_pow_eq_one h
    have hpos : 0 < orderOf (d * e) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    have hle : orderOf (d * e) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : orderOf (d * e) ≠ 2 := by
      intro h2
      apply h4
      have := pow_orderOf_eq_one (d * e)
      rw [h2] at this
      calc (d * e) ^ 4 = ((d * e) ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [this, one_pow]
    have h1 : orderOf (d * e) ≠ 1 := fun h1 => hne1 (orderOf_eq_one_iff.1 h1)
    have h45 : orderOf (d * e) ≠ 4 ∧ orderOf (d * e) ≠ 5 := by
      constructor <;> intro hh <;> rw [hh] at hdvd <;> omega
    by_cases h3 : orderOf (d * e) = 3
    · exact Or.inl h3
    · exfalso
      have h6 : orderOf (d * e) = 6 := by omega
      have hr3 : (d * e) ^ 3 ≠ 1 := by
        intro h3'
        have := orderOf_dvd_of_pow_eq_one h3'
        rw [h6] at this
        omega
      set c := (d * e)⁻¹ * e * (d * e) with hc
      have hcD : c ∈ D := by
        have := hconj (d * e)⁻¹ e he
        rwa [inv_inv] at this
      have hsame : (d * e) ^ 3 = (e * d) ^ 3 := by
        have h33 : (d * e) ^ 3 * (d * e) ^ 3 = 1 := by rw [← pow_add]; exact h
        have := eq_inv_of_mul_eq_one_left h33
        rw [this, ← inv_pow, mul_inv_rev, hei, hdi]
      have e1 : c * d = (e * d) ^ 3 := by
        rw [hc, mul_inv_rev, hei, hdi]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have hcd : c * d = d * c := by
        have e2 : d * c = (d * e) ^ 3 := by
          rw [hc, mul_inv_rev, hei, hdi]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [e1, e2, hsame]
      have hdc : d ≠ c := by
        intro hdc
        have : c * d = 1 := by rw [← hdc]; exact hd2
        rw [e1, ← hsame] at this
        exact hr3 this
      refine hP d hd c hcD hdc ?_
      refine TransFin.isPGroup_closure_of_comm (I := {d, c}) ?_ ?_
      · rintro u (rfl | rfl)
        · exact hd2
        · exact (hinv c hcD).1
      · rintro u (rfl | rfl) v (rfl | rfl)
        · rfl
        · exact hcd.symm
        · exact hcd
        · rfl

theorem false_of_ncard_one {Q : Type} [Group Q]
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) (D : Set Q)
    (hinv : ∀ d ∈ D, d * d = 1 ∧ d ≠ 1) (hconj : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D)
    (h1 : D.ncard = 1) : False := by
  obtain ⟨d, rfl⟩ := Set.ncard_eq_one.1 h1
  obtain ⟨hd2, hd1⟩ := hinv d rfl
  have hcen : ∀ q : Q, q * d * q⁻¹ = d := fun q => hconj q d rfl
  have hN : (Subgroup.zpowers d).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [← conj_zpow, hcen g]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) k
  have hP : IsPGroup 2 (Subgroup.zpowers d) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1]
    norm_num
  have := hO2 _ hN hP
  exact hd1 (Subgroup.mem_bot.1 (this ▸ Subgroup.mem_zpowers d))

theorem ncard_eq_length {D : Set (Perm (Fin 6))} {S : List ℕ} (hS : S.Nodup) (hsub : SubN D S)
    (hall : ∀ x ∈ D, enc x ∈ S) : D.ncard = S.length := by
  have h1 : enc '' D = {t | t ∈ S} := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hall x hx
    · intro ht
      obtain ⟨x, hx, rfl⟩ := hsub t ht
      exact ⟨x, hx, rfl⟩
  rw [← Set.ncard_image_of_injective D enc_injective, h1]
  rw [show {t | t ∈ S} = ↑S.toFinset by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hS]

theorem classify_hom {Q : Type} [Group Q] (ι : Q →* Perm (Fin 6)) (hι : Function.Injective ι)
    (D : Set Q) (hinv : ∀ d ∈ D, d * d = 1 ∧ d ≠ 1) (hconj : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D)
    (hord : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → orderOf (d * e) = 3 ∨ orderOf (d * e) = 5)
    (d₀ : Q) (hd₀ : d₀ ∈ D)
    (ha : enc (ι d₀) = 181889 ∨ enc (ι d₀) = 181441 ∨ enc (ι d₀) = 152769) :
    ∃ S ∈ goodSetsAll, SubN (ι '' D) S ∧ ∀ x ∈ ι '' D, enc x ∈ S := by
  have hc : ∀ s ∈ ι '' D, ∀ t ∈ ι '' D, s * t * s⁻¹ ∈ ι '' D := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨d * e * d⁻¹, hconj d e he, by rw [map_mul, map_mul, map_inv]⟩
  have hi : ∀ s ∈ ι '' D, s * s = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, (hinv d hd).1, map_one]
  have ho : ∀ s ∈ ι '' D, ∀ t ∈ ι '' D, s ≠ t → OrdOkN (mulN (enc s) (enc t)) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ hne
    rw [← enc_mul, ← map_mul]
    refine ordOkN_of_orderOf ?_
    rw [orderOf_injective ι hι]
    exact hord d hd e he (fun h => hne (by rw [h]))
  have hdm : ∃ x ∈ ι '' D, enc x = enc (ι d₀) := ⟨ι d₀, ⟨d₀, hd₀, rfl⟩, rfl⟩
  rcases ha with ha | ha | ha
  · obtain ⟨S, hS, h⟩ := search_classify cert2 hc hi ho (ha ▸ hdm)
    exact ⟨S, mem_goodSetsAll_of_mem (Or.inl hS), h⟩
  · obtain ⟨S, hS, h⟩ := search_classify cert4 hc hi ho (ha ▸ hdm)
    exact ⟨S, mem_goodSetsAll_of_mem (Or.inr (Or.inl hS)), h⟩
  · obtain ⟨S, hS, h⟩ := search_classify cert6 hc hi ho (ha ▸ hdm)
    exact ⟨S, mem_goodSetsAll_of_mem (Or.inr (Or.inr hS)), h⟩

theorem noY_transfer {Q : Type} [Group Q] [Finite Q] (ι : Q →* Perm (Fin 6))
    (hι : Function.Injective ι) (D : Set Q) (hconj : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D)
    {S : List ℕ} (hsub : SubN (ι '' D) S) (hall : ∀ x ∈ ι '' D, enc x ∈ S) (hno : NoYN S) :
    ¬ HasYStmt D := by
  rintro ⟨Y, hcomm, hsq, hcard, hfaith⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h12⟩ :
      ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ := by
    classical
    haveI : Fintype Y := Fintype.ofFinite Y
    have h5 : 1 < (Finset.univ.erase (1 : Y)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h5
    rw [Finset.mem_erase] at ha hb
    refine ⟨a, a.2, b, b.2, fun h => ha.1 (Subtype.ext h), fun h => hb.1 (Subtype.ext h), ?_⟩
    intro h
    exact hab (Subtype.ext h)
  have hinvι : ∀ y ∈ Y, ι y * ι y = 1 := fun y hy => by
    rw [← map_mul, hsq y hy, map_one]
  have hnrm : ∀ y ∈ Y, enc (ι y) ∈ NrmN S := by
    intro y hy
    simp only [NrmN, List.mem_filter, decide_eq_true_eq]
    refine ⟨mem_invsN (hinvι y hy), fun t ht => ?_⟩
    obtain ⟨x, ⟨d, hd, rfl⟩, rfl⟩ := hsub t ht
    rw [← enc_conj (hinvι y hy), ← map_inv, ← map_mul, ← map_mul]
    exact hall _ ⟨y * d * y⁻¹, hconj y d hd, rfl⟩
  have hcent : ∀ y ∈ Y, CentN S (enc (ι y)) → ∀ d ∈ D, y * d = d * y := by
    intro y hy h d hd
    have := h _ (hall _ ⟨d, hd, rfl⟩)
    rw [← enc_mul, ← enc_mul, enc_injective.eq_iff, ← map_mul, ← map_mul] at this
    exact hι this
  have hne : enc (ι y₁) ≠ enc (ι y₂) := fun h => h12 (hι (enc_injective h))
  have hcm : mulN (enc (ι y₁)) (enc (ι y₂)) = mulN (enc (ι y₂)) (enc (ι y₁)) := by
    rw [← enc_mul, ← enc_mul, ← map_mul, ← map_mul, hcomm y₁ hy₁ y₂ hy₂]
  rcases hno _ (hnrm y₁ hy₁) _ (hnrm y₂ hy₂) hne hcm with h | h | h
  · exact h1 (hfaith y₁ hy₁ (hcent y₁ hy₁ h))
  · exact h2 (hfaith y₂ hy₂ (hcent y₂ hy₂ h))
  · have hy12 : y₁ * y₂ ∈ Y := Y.mul_mem hy₁ hy₂
    have h' : CentN S (enc (ι (y₁ * y₂))) := by rw [map_mul, enc_mul]; exact h
    have h0 := hfaith _ hy12 (hcent _ hy12 h')
    have hy1i : y₁ = y₂⁻¹ := eq_inv_of_mul_eq_one_left h0
    have hy2i : y₂⁻¹ = y₂ := inv_eq_of_mul_eq_one_right (hsq y₂ hy₂)
    exact h12 (hy1i.trans hy2i)

theorem nine_transfer {Q : Type} [Group Q] (ι : Q →* Perm (Fin 6)) (D : Set Q)
    {S : List ℕ} (hsub : SubN (ι '' D) S) (hall : ∀ x ∈ ι '' D, enc x ∈ S) (hnine : NineN S) :
    ConjNine ι D := by
  obtain ⟨σc, hσ, h1, h2⟩ := hnine
  obtain ⟨σ, rfl⟩ := exists_of_mem_allN hσ
  refine ⟨σ, fun d hd => ?_, fun s hs => ?_⟩
  · obtain ⟨u, hu, hu'⟩ := h1 _ (hall _ ⟨d, hd, rfl⟩)
    obtain ⟨s', hs', rfl⟩ := exists_of_mem_nineN hu
    rw [(conj_eq_iff σ (ι d) s').2 hu']
    exact hs'
  · obtain ⟨t, ht, ht'⟩ := h2 _ ((mem_nineN_iff s).1 hs)
    obtain ⟨x, ⟨d, hd, rfl⟩, rfl⟩ := hsub t ht
    exact ⟨d, hd, (conj_eq_iff σ (ι d) s).2 ht'⟩

theorem conjNine_of_conj {Q : Type} [Group Q] (ι : Q →* Perm (Fin 6)) (σ₀ : Perm (Fin 6))
    (D : Set Q) (h : ConjNine ((MulAut.conj σ₀).toMonoidHom.comp ι) D) : ConjNine ι D := by
  obtain ⟨σ, h1, h2⟩ := h
  have e : ∀ d : Q, σ * ((MulAut.conj σ₀).toMonoidHom.comp ι) d * σ⁻¹ =
      (σ * σ₀) * ι d * (σ * σ₀)⁻¹ := fun d => by
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, mul_inv_rev, mul_assoc]
  refine ⟨σ * σ₀, fun d hd => ?_, fun s hs => ?_⟩
  · rw [← e]; exact h1 d hd
  · obtain ⟨d, hd, hd'⟩ := h2 s hs
    exact ⟨d, hd, by rw [← e]; exact hd'⟩

theorem dispatch {Q : Type} [Group Q] [Finite Q]
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) (ι : Q →* Perm (Fin 6))
    (hι : Function.Injective ι) (D : Set Q) (hinv : ∀ d ∈ D, d * d = 1 ∧ d ≠ 1)
    (hconj : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D) {S : List ℕ} (hS : S ∈ goodSetsAll)
    (hsub : SubN (ι '' D) S) (hall : ∀ x ∈ ι '' D, enc x ∈ S) :
    ((D.ncard = 3 ∨ D.ncard = 5) ∧ ¬ HasYStmt D) ∨ (D.ncard = 9 ∧ ConjNine ι D) := by
  obtain ⟨hnd, h1 | ⟨h35, hno⟩ | ⟨h9, hnine⟩⟩ := goodS_all S hS
  · exact absurd (by rw [← Set.ncard_image_of_injective D hι, ncard_eq_length hnd hsub hall, h1])
      (fun h => false_of_ncard_one hO2 D hinv hconj h)
  · have hcard : D.ncard = S.length := by
      rw [← Set.ncard_image_of_injective D hι, ncard_eq_length hnd hsub hall]
    exact Or.inl ⟨by rw [hcard]; exact h35, noY_transfer ι hι D hconj hsub hall hno⟩
  · have hcard : D.ncard = S.length := by
      rw [← Set.ncard_image_of_injective D hι, ncard_eq_length hnd hsub hall]
    exact Or.inr ⟨by rw [hcard]; exact h9, nine_transfer ι D hsub hall hnine⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxSix

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open Equiv CruxSix

theorem cruxSix_holds : CruxSixStmt := by
  intro Q _ _ ι hι hO2 D hne hinv hconj hP
  have hord := step1 ι hι D hinv hconj hP
  refine ⟨hord, ?_⟩
  obtain ⟨d₀, hd₀⟩ := hne
  have hd2 : ι d₀ * ι d₀ = 1 := by rw [← map_mul, (hinv d₀ hd₀).1, map_one]
  have hx : enc (ι d₀) ∈ invsN := mem_invsN hd2
  have hx1 : enc (ι d₀) ≠ oneN := by
    intro h
    rw [← enc_one] at h
    exact (hinv d₀ hd₀).2 (hι (by rw [enc_injective h, map_one]))
  obtain ⟨σc, hσc, a, ha, haN, hrel⟩ := canon_check _ hx hx1
  obtain ⟨σ₀, rfl⟩ := exists_of_mem_allN hσc
  obtain ⟨τ, rfl⟩ := exists_of_mem_allN haN
  let ι₀ : Q →* Perm (Fin 6) := (MulAut.conj σ₀).toMonoidHom.comp ι
  have hι₀ : Function.Injective ι₀ := (MulAut.conj σ₀).injective.comp hι
  have hcode : ι₀ d₀ = τ := by
    have : σ₀ * ι d₀ * σ₀⁻¹ = τ := (conj_eq_iff σ₀ (ι d₀) τ).2 hrel
    simpa [ι₀, MulAut.conj_apply] using this
  obtain ⟨S, hS, hsub, hall⟩ := classify_hom ι₀ hι₀ D hinv hconj hord d₀ hd₀
    (by rw [hcode]; simpa using ha)
  rcases dispatch hO2 ι₀ hι₀ D hinv hconj hS hsub hall with h | ⟨h9, hnine⟩
  · exact Or.inl h
  · exact Or.inr ⟨h9, conjNine_of_conj ι σ₀ D hnine⟩

end CFSG.GF2Type.Aschbacher1976Full.HS
