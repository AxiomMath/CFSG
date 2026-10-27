module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut
public import CFSG.GH74.Generic.S45.LSporM12Data
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.GH74.Generic.S45.LSporJ3
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

theorem layer_card_data {Z : Type} [Group Z] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) (hL : Blueprint.LieModel Z .PSL 2 p m) :
    ∃ q : ℕ, 7 ≤ q ∧ 16 ∣ q ^ 2 - 1 ∧ Nat.card Z * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
  have hodd := AutL2Facts.isOddPrimePower_of hpP hp2 hm1 hF'
  refine ⟨p ^ m, seven_le_of_sixteen_dvd hp hp2 hm h16, ?_, ?_⟩
  · rwa [← pow_mul, mul_comm]
  · rw [Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
    have hev : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
      have h2 : 2 ∣ (p ^ m) ^ 2 - 1 := by
        have : 16 ∣ (p ^ m) ^ 2 - 1 := by rwa [← pow_mul, mul_comm]
        exact (by norm_num : 2 ∣ 16).trans this
      exact h2.mul_left _
    exact Nat.div_mul_cancel hev

theorem false_of_layer_dvd {N q c : ℕ} (hc : c = 192 ∨ c = 240 ∨ c = 1920 ∨ c = 2448)
    (hN : N ∣ c) (hlt : N < c) (hq7 : 7 ≤ q) (h16 : 16 ∣ q ^ 2 - 1)
    (h : N * 2 = q * (q ^ 2 - 1)) : False := by
  have hc2448 : c ≤ 2448 := by omega
  have hq16 : q ≤ 16 := by
    by_contra hgt
    push Not at hgt
    have h17 : 17 * (17 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
      apply Nat.mul_le_mul hgt
      have : 17 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hgt 2
      omega
    omega
  have hN2 : N = q * (q ^ 2 - 1) / 2 := by omega
  subst hN2
  interval_cases q <;> norm_num at h16 <;>
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num at hN

theorem card_fixedPoints_congr {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z) (τ : MulAut Y) :
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

theorem card_centralizer_congr {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z) (t : Y) :
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

theorem congr_conj {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z) (y : Y) :
    MulAut.congr φ (MulAut.conj y) = MulAut.conj (φ y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_inner_card {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2) (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m)
    {t : Y} (ht : MulAut.conj t = τ)
    (hc : Nat.card (centralizer ({t} : Set Y)) = 192 ∨
      Nat.card (centralizer ({t} : Set Y)) = 240 ∨ Nat.card (centralizer ({t} : Set Y)) = 1920 ∨
      Nat.card (centralizer ({t} : Set Y)) = 2448) : False := by
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    norm_num at hτ
  have htL := not_mem_layerIn_of_conj hτ1 ht hL
  subst ht
  have hCeq := centralizer_eq_fixedPoints_conj t
  set L := GSThmB.layerIn (fixedPoints (MulAut.conj t))
  have hLC : L ≤ centralizer ({t} : Set Y) := hCeq ▸ map_subtype_le _
  have htC : t ∈ centralizer ({t} : Set Y) := mem_centralizer_singleton_iff.mpr rfl
  have hlt : L < centralizer ({t} : Set Y) := lt_of_le_of_ne hLC fun h => htL (h ▸ htC)
  obtain ⟨q, hq7, hq16, hq⟩ := layer_card_data hp hp2 hm h16 hL
  exact false_of_layer_dvd hc (Subgroup.card_dvd_of_le hLC) (Subgroup.card_lt_of_lt hlt) hq7
    hq16 hq

theorem fixSub_eq_fixedPoints' {Y : Type} [Group Y] (α : MulAut Y) :
    Sporadic.Schreier.fixSub α = fixedPoints α := by
  ext y
  rfl

theorem hinFor_spor_J1 :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .J1 := by
  intro Y _ _ _ ⟨e⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  let φ : Y ≃* Open.walterJ1 := e.trans Walter.walterJ1EquivNative.symm
  obtain ⟨g, hg⟩ := Walter.J1Props.J3_aut (MulAut.congr φ τ)
  have hτg : τ = MulAut.conj (φ.symm g) := by
    apply (MulAut.congr φ).injective
    rw [hg, congr_conj, MulEquiv.apply_symm_apply]
  set t := φ.symm g
  have hZ : center Y = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ (conj_injective_of_center hZ) t, ← hτg]
    exact hτ
  have h120 : Nat.card (centralizer ({t} : Set Y)) = 120 := by
    rw [card_centralizer_congr φ t]
    exact Walter.J1Props.card_centralizer_of_orderOf_eq_two (by rwa [MulEquiv.orderOf_eq])
  have hLC : GSThmB.layerIn (fixedPoints τ) ≤ centralizer ({t} : Set Y) := by
    rw [hτg, centralizer_eq_fixedPoints_conj]
    exact map_subtype_le _
  have := Subgroup.card_le_of_le hLC
  have h168 := le_card_of_lieModel_psl2_sixteen hp2 h16 hL
  omega

theorem hinFor_spor_J2 :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .J2 := by
  intro Y _ _ _ ⟨e⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  by_cases hinn : τ ∈ innAut Y
  · exfalso
    obtain ⟨t, rfl⟩ := hinn
    have hZ : center Y = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) t]
      exact hτ
    let φ := e.trans J2Cover.nativeEquivP
    have hc := GH74.Generic.S45.j2_involution_data (p := φ t) (by rwa [MulEquiv.orderOf_eq])
    refine false_of_inner_card hp hp2 hm h16 hτ hL rfl ?_
    rw [card_centralizer_congr φ t]
    rcases hc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact hinConcl_of_list hinn (Or.inl ⟨e⟩)

theorem autFixed_eq_fixedPoints {Y : Type} [Group Y] (α : MulAut Y) :
    GH74.Uniqueness.Bender.autFixed α = fixedPoints α := by
  ext y
  rfl

theorem hinFor_spor_J3 :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .J3 := by
  intro Y _ _ _ ⟨e⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  by_cases hinn : τ ∈ innAut Y
  · exfalso
    have hsq : τ * τ = 1 := by
      have := pow_orderOf_eq_one τ
      rwa [hτ, pow_two] at this
    have hτ1 : τ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hτ
      norm_num at hτ
    have hc := GH74.Generic.S45.j3_fixed_card e τ hsq hτ1
    obtain ⟨t, rfl⟩ := hinn
    refine false_of_inner_card hp hp2 hm h16 hτ hL rfl ?_
    rw [centralizer_eq_fixedPoints_conj, ← autFixed_eq_fixedPoints]
    rcases hc with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact hinConcl_of_list hinn (Or.inr (Or.inl ⟨e⟩))

theorem hinFor_spor_M12 :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M12 := by
  intro Y _ _ _ ⟨e₀⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  let e : Y ≃* Blueprint.NativeSporadic.M12 := e₀
  have hZ : center Y = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hsq : τ * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ, pow_two] at this
  by_cases hinn : τ ∈ innAut Y
  · obtain ⟨t, rfl⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) t]
      exact hτ
    have hc := GH74.Generic.S45.LAlt.m12_involution_data (e t) ((MulEquiv.orderOf_eq e t).trans ht2)
    refine false_of_inner_card hp hp2 hm h16 hτ hL rfl ?_
    rw [card_centralizer_congr e t]
    rcases hc with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hsq' : MulAut.congr e τ * MulAut.congr e τ = 1 := by rw [← map_mul, hsq, map_one]
    have hout' : MulAut.congr e τ ∉ OuterAutomorphisms.inner Blueprint.NativeSporadic.M12 := by
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
      rw [← fixSub_eq_fixedPoints']
      exact M12Cover.card_fixSub_beta
    have hcard : Nat.card (fixedPoints τ) = 120 := by
      rw [card_fixedPoints_congr e τ, hγ, ← hγβ, ← card_fixedPoints_congr γ, h3]
    have hle := Subgroup.card_le_of_le (map_subtype_le (pLayer ↥(fixedPoints τ) 2))
    have h168 := le_card_of_lieModel_psl2_sixteen hp2 h16 hL
    change 168 ≤ Nat.card ↥((pLayer ↥(fixedPoints τ) 2).map (fixedPoints τ).subtype) at h168
    omega

end CFSG.ComponentClassification.HarrisLit.Hin
