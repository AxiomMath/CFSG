module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Spor
public import CFSG.GH74.Generic.S45.LSporM12Data
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Blueprint

theorem false_of_card_dvd {N q c : ℕ} (hc : c = 120 ∨ c = 192 ∨ c = 240 ∨ c = 1920 ∨ c = 7680)
    (hN : N ∣ c) (hq7 : 7 ≤ q) (h16 : 16 ∣ q ^ 2 - 1) (h : N * 2 = q * (q ^ 2 - 1)) : False := by
  have hc0 : 0 < c := by omega
  have hNc : N ≤ c := Nat.le_of_dvd hc0 hN
  have hq25 : q ≤ 25 := by
    by_contra hgt
    push Not at hgt
    have h26 : 26 * (26 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
      apply Nat.mul_le_mul hgt
      have : 26 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hgt 2
      omega
    omega
  have hN2 : N = q * (q ^ 2 - 1) / 2 := by omega
  subst hN2
  interval_cases q <;> norm_num at h16 <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> norm_num at hN

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem card_bar (h : Config G p m τ K) (hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥) :
    ∃ q : ℕ, 7 ≤ q ∧ 16 ∣ q ^ 2 - 1 ∧
      Nat.card ↥(K.map (QuotientGroup.mk' (center G))) * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨-, hL⟩ := h.isComponent_bar hO
  obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
  have hodd := AutL2Facts.isOddPrimePower_of hpP h.ne_two hm1 hF'
  have hsub : Nat.card ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
      (fixedPoints (quotAut τ))) = Nat.card ↥(K.map (QuotientGroup.mk' (center G))) :=
    Nat.card_congr (subgroupOfEquivOfLe h.isTwoComponentIn_bar.1).toEquiv
  refine ⟨p ^ m, h.seven_le, ?_, ?_⟩
  · have := h.sixteen_dvd
    rwa [← pow_mul, mul_comm]
  · rw [← hsub, Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
    have hev : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
      have h2 : 2 ∣ (p ^ m) ^ 2 - 1 := by
        have : 16 ∣ (p ^ m) ^ 2 - 1 := by have := h.sixteen_dvd; rwa [← pow_mul, mul_comm]
        exact (by norm_num : 2 ∣ 16).trans this
      exact h2.mul_left _
    exact Nat.div_mul_cancel hev

theorem card_bar_dvd (h : Config G p m τ K) :
    Nat.card ↥(K.map (QuotientGroup.mk' (center G))) ∣ Nat.card ↥(fixedPoints (quotAut τ)) :=
  Subgroup.card_dvd_of_le h.isTwoComponentIn_bar.1

theorem card_bar_lt (h : Config G p m τ K) (hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥)
    {t : G ⧸ center G} (ht : quotAut τ = MulAut.conj t) :
    Nat.card ↥(K.map (QuotientGroup.mk' (center G))) <
      Nat.card ↥(fixedPoints (quotAut τ)) := by
  have hle := h.isTwoComponentIn_bar.1
  have htC : t ∈ fixedPoints (quotAut τ) := by
    rw [mem_fixedPoints, ht, MulAut.conj_apply]
    group
  have ht1 : t ≠ 1 := by
    rintro rfl
    have h2 := h.orderOf_bar
    rw [ht, map_one, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htK : t ∉ K.map (QuotientGroup.mk' (center G)) := by
    intro htK
    obtain ⟨hB, hL⟩ := h.isComponent_bar hO
    have := isSimpleGroup_of_lieModel_psl2 hL
    have hZ := CatLeaf.center_eq_bot_of_simple (nonabelian_of_lieModel_psl2 hL)
    have hc : (⟨⟨t, htC⟩, htK⟩ : ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
        (fixedPoints (quotAut τ)))) ∈ center _ := by
      rw [mem_center_iff]
      intro w
      apply Subtype.ext
      apply Subtype.ext
      have hw : t * ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) * t⁻¹ =
          ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) := by
        rw [← MulAut.conj_apply, ← ht]
        exact ((w : ↥(fixedPoints (quotAut τ)))).2
      change ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) * t =
        t * ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G)
      calc ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) * t
          = t * ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) * t⁻¹ * t := by rw [hw]
        _ = t * ((w : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) := by group
    rw [hZ, mem_bot] at hc
    have h2 := congrArg Subtype.val (congrArg Subtype.val hc)
    exact ht1 (by simpa using h2)
  exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle fun heq => htK (heq ▸ htC))

end Config

theorem card_fixedPoints_congr' {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z) (τ : MulAut Y) :
    Nat.card (fixedPoints τ) = Nat.card (fixedPoints (MulAut.congr φ τ)) := by
  have hmap : (fixedPoints τ).map φ.toMonoidHom = fixedPoints (MulAut.congr φ τ) := by
    ext z
    rw [Subgroup.mem_map_equiv, mem_fixedPoints, mem_fixedPoints]
    change τ (φ.symm z) = φ.symm z ↔ φ (τ (φ.symm z)) = z
    constructor
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
    · intro h
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      exact h
  rw [← hmap, Subgroup.card_map_of_injective φ.injective]

theorem card_centralizer_congr' {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z) (t : Y) :
    Nat.card (centralizer ({t} : Set Y)) = Nat.card (centralizer ({φ t} : Set Z)) := by
  have hmap : (centralizer ({t} : Set Y)).map φ.toMonoidHom = centralizer ({φ t} : Set Z) := by
    ext z
    rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg φ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · intro h
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h
  rw [← hmap, Subgroup.card_map_of_injective φ.injective]

open Hin in
theorem rowFor_spor_J1 :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .J1 := by
  intro G _ _ p m τ K h ⟨e⟩
  exfalso
  have := h.simple_bar
  set σ := quotAut τ
  let φ : G ⧸ center G ≃* Open.walterJ1 := e.trans Walter.walterJ1EquivNative.symm
  obtain ⟨g, hg⟩ := Walter.J1Props.J3_aut (MulAut.congr φ σ)
  have hσg : σ = MulAut.conj (φ.symm g) := by
    apply (MulAut.congr φ).injective
    rw [hg, congr_conj, MulEquiv.apply_symm_apply]
  set t := φ.symm g
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ (conj_injective_of_center hZ) t, ← hσg]
    exact h.orderOf_bar
  have h120 : Nat.card (centralizer ({t} : Set (G ⧸ center G))) = 120 := by
    rw [card_centralizer_congr' φ t]
    exact Walter.J1Props.card_centralizer_of_orderOf_eq_two (by rwa [MulEquiv.orderOf_eq])
  have hle : Nat.card ↥(K.map (QuotientGroup.mk' (center G))) ≤ 120 := by
    rw [← h120, centralizer_eq_fixedPoints_conj, ← hσg]
    exact Subgroup.card_le_of_le h.isTwoComponentIn_bar.1
  have h168 := le_card_of_lieModel_psl2_sixteen h.ne_two h.sixteen_dvd h.lieModel_bar
  have hq : Nat.card (↥(K.map (QuotientGroup.mk' (center G))) ⧸
      pPrimeCore 2 ↥(K.map (QuotientGroup.mk' (center G)))) ≤
      Nat.card ↥(K.map (QuotientGroup.mk' (center G))) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  omega

open Hin in
theorem rowFor_spor_M12 :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .M12 := by
  intro G _ _ p m τ K h ⟨e₀⟩
  exfalso
  have := h.simple_bar
  set σ := quotAut τ with hσdef
  let e : G ⧸ center G ≃* NativeSporadic.M12 := e₀
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  have hO := h.pPrimeCore_bar_eq_bot CatalogueU.sporadicOddCoreFree_M12 e₀
  obtain ⟨q, hq7, hq16, hq⟩ := h.card_bar hO
  have hsq : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [h.orderOf_bar, pow_two] at this
  by_cases hinn : σ ∈ innAut (G ⧸ center G)
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) t, ht]
      exact h.orderOf_bar
    have hc := GH74.Generic.S45.LAlt.m12_involution_data (e t)
      ((MulEquiv.orderOf_eq e t).trans ht2)
    have hcard : Nat.card ↥(fixedPoints σ) = 192 ∨ Nat.card ↥(fixedPoints σ) = 240 := by
      rw [← ht, ← centralizer_eq_fixedPoints_conj, card_centralizer_congr' e t]
      rcases hc with h1 | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have hd := h.card_bar_dvd
    rcases hcard with h1 | h1 <;> rw [h1] at hd
    · exact false_of_card_dvd (Or.inr (Or.inl rfl)) hd hq7 hq16 hq
    · exact false_of_card_dvd (Or.inr (Or.inr (Or.inl rfl))) hd hq7 hq16 hq
  · have hsq' : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hsq, map_one]
    have hout' : MulAut.congr e σ ∉ OuterAutomorphisms.inner NativeSporadic.M12 := by
      rintro ⟨g, hg⟩
      apply hinn
      refine ⟨e.symm g, (MulAut.congr e).injective ?_⟩
      rw [congr_conj]
      convert hg using 2
      exact e.apply_symm_apply g
    obtain ⟨γ, hγ⟩ := GH74.Generic.S45.LAlt.m12_outer_involution _ hsq' hout'
    have hγβ : MulAut.congr γ M12Cover.beta = γ * M12Cover.beta * γ⁻¹ := by
      ext z
      simp [MulAut.congr_apply, MulAut.mul_apply]
    have h3 : Nat.card (fixedPoints M12Cover.beta) = 120 := by
      rw [← fixSub_eq_fixedPoints]
      exact M12Cover.card_fixSub_beta
    have hcard : Nat.card (fixedPoints σ) = 120 := by
      rw [card_fixedPoints_congr' e σ, hγ, ← hγβ, ← card_fixedPoints_congr' γ, h3]
    have hd := h.card_bar_dvd
    rw [hcard] at hd
    exact false_of_card_dvd (Or.inl rfl) hd hq7 hq16 hq

open Hin in
theorem rowFor_spor_J2 :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .J2 := by
  intro G _ _ p m τ K h ⟨e⟩
  have := h.simple_bar
  set σ := quotAut τ with hσdef
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  by_cases hinn : σ ∈ innAut (G ⧸ center G)
  · exfalso
    have hO := h.pPrimeCore_bar_eq_bot CatalogueU.sporadicOddCoreFree_J2 e
    obtain ⟨q, hq7, hq16, hq⟩ := h.card_bar hO
    obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) t, ht]
      exact h.orderOf_bar
    let φ := e.trans J2Cover.nativeEquivP
    have hc := GH74.Generic.S45.j2_involution_data (p := φ t) (by rwa [MulEquiv.orderOf_eq])
    have hcard : Nat.card ↥(fixedPoints σ) = 240 ∨ Nat.card ↥(fixedPoints σ) = 1920 := by
      rw [← ht, ← centralizer_eq_fixedPoints_conj, card_centralizer_congr' φ t]
      rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have hd := h.card_bar_dvd
    rcases hcard with h1 | h1 <;> rw [h1] at hd
    · exact false_of_card_dvd (Or.inr (Or.inr (Or.inl rfl))) hd hq7 hq16 hq
    · exact false_of_card_dvd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hd hq7 hq16 hq
  ·
    left
    have hZ2 : Nat.card ↥(center G) ≤ 2 :=
      StandardRecognition.m12J2CentralTwoGroupOrderBound G
        ⟨h.quasisimple.1.commutator_eq_top, h.quasisimple.2.1⟩ h.center_isPGroup
        (Or.inr ⟨e⟩)
    have hZ1 : 1 < Nat.card ↥(center G) := by
      rw [Finite.one_lt_card_iff_nontrivial, nontrivial_iff_ne_bot]
      exact h.center_ne_bot
    exact ⟨⟨e⟩, by omega, fun hτ => hinn ((h.bar_mem_innAut_iff).mpr hτ)⟩

end CFSG.ComponentClassification.HarrisLit.N36
