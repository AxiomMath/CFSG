module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Root
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup

theorem exists_involution_lift {X : Type*} [Group X] [Finite X] (H : Subgroup X)
    {y : X ⧸ pPrimeCore 2 X} (hy : y ∈ H.map (QuotientGroup.mk' (pPrimeCore 2 X)))
    (hy2 : y * y = 1) :
    ∃ x ∈ H, x * x = 1 ∧ QuotientGroup.mk' (pPrimeCore 2 X) x = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀, rfl⟩ := hy
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  set f := QuotientGroup.mk' (pPrimeCore 2 X) with hf
  have hfm : f (x₀ ^ m) = f x₀ := by
    obtain ⟨j, rfl⟩ := hm
    rw [map_pow, pow_succ, pow_mul, pow_two, hy2, one_pow, one_mul]
  refine ⟨x₀ ^ m, pow_mem hx₀ m, ?_, hfm⟩
  have hz : x₀ ^ m * x₀ ^ m ∈ pPrimeCore 2 X := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hf, map_mul, hfm, hy2]
  have h1 : orderOf (x₀ ^ m * x₀ ^ m) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_add, ← pow_mul, show (m + m) * 2 ^ k = 2 ^ k * m * 2 by ring, ← hkm, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have h2 : orderOf (x₀ ^ m * x₀ ^ m) ∣ Nat.card (pPrimeCore 2 X) := by
    rw [← orderOf_mk (x₀ ^ m * x₀ ^ m) hz]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 X)) :=
    Nat.Coprime.pow_left k pPrimeCore_coprime_card
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem card_zpowers_sup_eq {G : Type*} [Group G] [Finite G] {x : G} (hx : x * x = 1)
    {H : Subgroup G} (hxH : x ∈ normalizer (H : Set G)) (hxn : x ∉ H) :
    Nat.card ↥(zpowers x ⊔ H) = 2 * Nat.card H := by
  have hle := card_zpowers_sup_le hx hxH
  have hdvd : Nat.card H ∣ Nat.card ↥(zpowers x ⊔ H) := card_dvd_of_le le_sup_right
  have hlt : Nat.card H < Nat.card ↥(zpowers x ⊔ H) := by
    apply card_lt_of_lt
    refine lt_of_le_of_ne le_sup_right fun h => hxn ?_
    rw [h]
    exact mem_sup_left (mem_zpowers x)
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [hc] at hle hlt ⊢
  have hc1 : 1 < c := by
    by_contra h
    push Not at h
    interval_cases c <;> simp_all
  have hc2 : c ≤ 2 := by
    by_contra h
    push Not at h
    have : Nat.card H * 3 ≤ Nat.card H * c := Nat.mul_le_mul_left _ h
    omega
  have : c = 2 := by omega
  rw [this, mul_comm]

theorem exists_four_inf_centralizer {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) :
    ∃ W : Subgroup G, W ≤ L ∧ IsElemTwo W ∧ Nat.card W = 4 ∧
      W ⊓ centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lbar := ↥L ⧸ pPrimeCore 2 ↥L with hLbar
  obtain ⟨e₁⟩ := nonempty_quotient_center_equiv_fusionZStar ↥L
  obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel h
  set π : Lbar →* PSL3Four.S :=
    (e₁.trans ψ).toMonoidHom.comp (QuotientGroup.mk' (center Lbar)) with hπdef
  have hπ : Function.Surjective π :=
    (e₁.trans ψ).surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = center Lbar := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcore : pPrimeCore 2 Lbar = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have h3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    rw [hkerπ] at hz
    have hn : (zpowers z).Normal := ⟨fun n hn g => by
      have hc : g * n = n * g := (mem_center_iff.mp
        (Subgroup.zpowers_le.mpr hz hn)) g
      rw [hc, mul_inv_cancel_right]
      exact hn⟩
    have hcop : Nat.Coprime 2 (Nat.card (zpowers z)) := by
      rw [Nat.card_zpowers]
      have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h1 <;> rw [h1] <;>
        norm_num
    have hbot := (pPrimeCore_eq_bot_iff.mp hcore) _ hn hcop
    exact (zpowers_eq_bot).mp hbot
  obtain ⟨Y, hYK, hYab, y₁, hy₁, y₂, hy₂, h₁, h₂, hne₁, hne₂, hne⟩ :=
    GrS5.exists_four_of_central hπ (hkerπ ▸ le_refl _) h3
  set f := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hf
  obtain ⟨w₁, -, hw₁, hfw₁⟩ := exists_involution_lift (⊤ : Subgroup ↥L)
    (by rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact mem_top y₁) h₁
  have hodd : ¬ 2 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    intro hd
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr hd)
  have hw₁ne : w₁ ≠ 1 := by
    rintro rfl
    exact hne₁ (by rw [← hfw₁, map_one])
  have hw₁2 : IsPGroup 2 (zpowers w₁) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two, hw₁]) hw₁ne
  have hcen := map_centralizer_eq_of_odd_ker f (QuotientGroup.mk'_surjective _) hodd hw₁2
  have hy₂mem : y₂ ∈ (centralizer (zpowers w₁ : Set ↥L)).map f := by
    rw [hcen, MonoidHom.map_zpowers, hfw₁, mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (hYab y₁ hy₁ y₂ hy₂) i).eq
  obtain ⟨w₂, hw₂c, hw₂, hfw₂⟩ := exists_involution_lift _ hy₂mem h₂
  have hcomm : (w₁ : G) * w₂ = w₂ * w₁ := by
    have := mem_centralizer_iff.mp hw₂c w₁ (mem_zpowers w₁)
    exact congrArg Subtype.val this
  have hw₂ne : w₂ ≠ 1 := by
    rintro rfl
    exact hne₂ (by rw [← hfw₂, map_one])
  have hw₁G : (w₁ : G) * w₁ = 1 := by rw [← coe_mul, hw₁, coe_one]
  have hw₂G : (w₂ : G) * w₂ = 1 := by rw [← coe_mul, hw₂, coe_one]
  have ho₁ : orderOf (w₁ : G) = 2 := by
    rw [orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two, hw₁]) hw₁ne
  have ho₂ : orderOf (w₂ : G) = 2 := by
    rw [orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two, hw₂]) hw₂ne
  set W : Subgroup G := zpowers (w₂ : G) ⊔ zpowers (w₁ : G) with hWdef
  have hWL : W ≤ L := sup_le (zpowers_le.mpr w₂.2) (zpowers_le.mpr w₁.2)
  have hW : IsElemTwo W := IsElemTwo.sup (isElemTwo_zpowers hw₂G) (isElemTwo_zpowers hw₁G)
    (by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact ((Commute.zpow_zpow (show Commute (w₂ : G) w₁ from hcomm.symm) i j)).eq)
  have hw₂N : (w₂ : G) ∈ normalizer (zpowers (w₁ : G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have hc : ∀ z ∈ zpowers (w₁ : G), (w₂ : G) * z = z * w₂ := by
      intro z hz
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hz
      exact (Commute.zpow_right (show Commute (w₂ : G) w₁ from hcomm.symm) i).eq
    constructor
    · intro hy
      rw [hc y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 : y = (w₂ : G)⁻¹ * ((w₂ : G) * y * (w₂ : G)⁻¹) * w₂ := by group
      rw [h1, mul_assoc, ← hc _ hy, inv_mul_cancel_left]
      exact hy
  have hw₂n : (w₂ : G) ∉ zpowers (w₁ : G) := by
    intro hm
    rcases (LocalB.mem_zpowers_iff_of_involution (w₁ : G) (w₂ : G) ho₁).mp hm with h1 | h1
    · exact hw₂ne (Subtype.ext h1)
    · exact hne (by rw [← hfw₁, ← hfw₂, Subtype.ext h1])
  have hcard : Nat.card W = 4 := by
    rw [hWdef, card_zpowers_sup_eq hw₂G hw₂N hw₂n, Nat.card_zpowers, ho₁]
  refine ⟨W, hWL, hW, hcard, ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hxW, hxC⟩
  set W' : Subgroup ↥L := zpowers w₂ ⊔ zpowers w₁ with hW'def
  have hWmap : W'.map L.subtype = W := by
    rw [hW'def, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [← hWmap] at hxW
  obtain ⟨x', hx'W, rfl⟩ := hxW
  have hx'cen : x' ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (by rw [coe_mul, coe_mul]; exact (mem_centralizer_iff.mp hxC) g g.2)
  have hfx'Y : f x' ∈ Y := by
    have hle : W'.map f ≤ Y := by
      rw [hW'def, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hfw₁, hfw₂]
      exact sup_le (zpowers_le.mpr hy₂) (zpowers_le.mpr hy₁)
    exact hle ⟨x', hx'W, rfl⟩
  have hfx'K : f x' ∈ π.ker := by
    rw [hkerπ]
    exact map_center_le_center (QuotientGroup.mk'_surjective _) ⟨x', hx'cen, rfl⟩
  have hfx' : f x' = 1 := by
    have hm : f x' ∈ Y ⊓ π.ker := Subgroup.mem_inf.mpr ⟨hfx'Y, hfx'K⟩
    rw [hYK] at hm
    exact mem_bot.mp hm
  have hx'O : x' ∈ pPrimeCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hf]
    exact hfx'
  have hx'2 : x' * x' = 1 := by
    have hxW2 := hW.2 _ (hWmap ▸ ⟨x', hx'W, rfl⟩ : (x' : G) ∈ W)
    exact Subtype.ext (by rw [coe_mul, hxW2, coe_one])
  have h1 : orderOf x' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx'2])
  have h2 : orderOf x' ∣ Nat.card (pPrimeCore 2 ↥L) := by
    rw [← orderOf_mk x' hx'O]
    exact orderOf_dvd_natCard _
  have hx'1 : x' = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes pPrimeCore_coprime_card h1 h2)
  rw [hx'1]
  exact mem_bot.mpr rfl

end CFSG.ComponentClassification.GrSLit.GrS5
