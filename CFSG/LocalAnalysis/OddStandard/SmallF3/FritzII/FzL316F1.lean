module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY5

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G] [Finite G]

private def fzl_omega (P : Subgroup G)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Subgroup G where
  carrier := {p | p ∈ P ∧ p ^ 2 = 1}
  mul_mem' := by
    rintro a b ⟨haP, ha2⟩ ⟨hbP, hb2⟩
    exact ⟨P.mul_mem haP hbP, by
      have hc : Commute a b := hcomm a haP b hbP
      rw [hc.mul_pow, ha2, hb2, one_mul]⟩
  one_mem' := ⟨P.one_mem, one_pow 2⟩
  inv_mem' := by
    rintro a ⟨haP, ha2⟩
    exact ⟨P.inv_mem haP, by rw [inv_pow, ha2, inv_one]⟩

private lemma fzl_mem_omega {P : Subgroup G}
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {x : G} :
    x ∈ fzl_omega P hcomm ↔ x ∈ P ∧ x ^ 2 = 1 := Iff.rfl

private theorem fzl_prod_sup_equiv {H₁ H₂ : Subgroup G}
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) (hdisj : H₁ ⊓ H₂ = ⊥) :
    Nonempty ((H₁ × H₂) ≃* (H₁ ⊔ H₂ : Subgroup G)) := by
  have hc : ∀ (x : H₁) (y : H₂), Commute (H₁.subtype x) (H₂.subtype y) :=
    fun x y => hcomm x x.2 y y.2
  have hf : Function.Injective (MonoidHom.noncommCoprod H₁.subtype H₂.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H₁.subtype_injective, H₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hdisj
  have hrange : (MonoidHom.noncommCoprod H₁.subtype H₂.subtype hc).range = H₁ ⊔ H₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)⟩

private lemma fzl_mem_sup_iff_of_commute {J L : Subgroup G}
    (h : ∀ x ∈ J, ∀ y ∈ L, Commute x y) {z : G} :
    z ∈ J ⊔ L ↔ ∃ j ∈ J, ∃ l ∈ L, j * l = z := by
  constructor
  · intro hz
    let P : Subgroup G :=
      { carrier := {z | ∃ j ∈ J, ∃ l ∈ L, j * l = z}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
        mul_mem' := by
          rintro _ _ ⟨j₁, hj₁, l₁, hl₁, rfl⟩ ⟨j₂, hj₂, l₂, hl₂, rfl⟩
          refine ⟨j₁ * j₂, mul_mem hj₁ hj₂, l₁ * l₂, mul_mem hl₁ hl₂, ?_⟩
          have := (h j₂ hj₂ l₁ hl₁).eq
          calc j₁ * j₂ * (l₁ * l₂) = j₁ * (j₂ * l₁) * l₂ := by group
            _ = j₁ * (l₁ * j₂) * l₂ := by rw [this]
            _ = j₁ * l₁ * (j₂ * l₂) := by group
        inv_mem' := by
          rintro _ ⟨j, hj, l, hl, rfl⟩
          refine ⟨j⁻¹, inv_mem hj, l⁻¹, inv_mem hl, ?_⟩
          have := (h j hj l hl).eq
          calc j⁻¹ * l⁻¹ = (l * j)⁻¹ := by group
            _ = (j * l)⁻¹ := by rw [this] }
    have hle : J ⊔ L ≤ P := sup_le (fun j hj => ⟨j, hj, 1, one_mem _, mul_one j⟩)
      (fun l hl => ⟨1, one_mem _, l, hl, one_mul l⟩)
    exact hle hz
  · rintro ⟨j, hj, l, hl, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hl)

private lemma fzl_orderOf_eq_two {y : G} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    orderOf y = 2 := by
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hy1
  · exact h

private lemma fzl_mem_zpowers_pair {y x : G} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    x ∈ zpowers y ↔ x = 1 ∨ x = y := by
  have hord : orderOf y = 2 := fzl_orderOf_eq_two hy2 hy1
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hi : i % (orderOf y : ℤ) = i % (2 : ℤ) := by rw [hord]; norm_num
    rw [(zpow_mod_orderOf y i).symm, hi]
    rcases Int.emod_two_eq_zero_or_one i with h | h <;> rw [h]
    · exact Or.inl (zpow_zero y)
    · exact Or.inr (zpow_one y)
  · rintro (h | h)
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers y

theorem fzl_equiv_Z4422 {P E Z : Subgroup G}
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hcard : Nat.card P = 64) (hZE : Z ≤ E)
    (hEP : E ≤ P) (hcE : Nat.card E = 16) (hcZ : Nat.card Z = 4)
    (hEZ : ∀ e ∈ E, e ^ 2 = 1 → e ∈ Z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hEeq : Nonempty (↥E ≃* Z4Z4))
    (hΩ : Nat.card {p : G // p ∈ P ∧ p ^ 2 = 1} = 16) : Nonempty (↥P ≃* FzZ4422) := by
  let Ω : Subgroup G := fzl_omega P hcomm
  have hΩcard : Nat.card Ω = 16 := by
    show Nat.card (fzl_omega P hcomm) = 16
    simpa [fzl_omega] using hΩ
  have hΩP : Ω ≤ P := fun x hx => (fzl_mem_omega hcomm).mp hx |>.1
  have hZΩ : Z ≤ Ω := fun z hz =>
    (fzl_mem_omega hcomm).mpr ⟨hEP (hZE hz), hZ2 z hz⟩
  have hex1 : ∃ y : G, y ∈ Ω ∧ y ∉ Z := by
    by_contra h
    push Not at h
    have hle : Nat.card Ω ≤ Nat.card Z := Subgroup.card_le_of_le fun x hx => h x hx
    rw [hΩcard, hcZ] at hle
    norm_num at hle
  obtain ⟨y₁, hy1Ω, hy1Z⟩ := hex1
  have hy1_2 : y₁ ^ 2 = 1 := (fzl_mem_omega hcomm).mp hy1Ω |>.2
  have hy1_ne : y₁ ≠ 1 := fun h => hy1Z (h ▸ Z.one_mem)
  have hord1 : orderOf y₁ = 2 := fzl_orderOf_eq_two hy1_2 hy1_ne
  let A : Subgroup G := Z ⊔ zpowers y₁
  have hdisjZ1 : Z ⊓ zpowers y₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxZ, hx1⟩
    rcases (fzl_mem_zpowers_pair hy1_2 hy1_ne).mp hx1 with h | h
    · exact h
    · exact absurd (h ▸ hxZ) hy1Z
  have hcZ1 : ∀ a ∈ Z, ∀ b ∈ zpowers y₁, Commute a b :=
    fun a ha b hb => hcomm a (hEP (hZE ha)) b (hΩP (Subgroup.zpowers_le.mpr hy1Ω hb))
  have hAcard : Nat.card A = 8 := by
    obtain ⟨e⟩ := fzl_prod_sup_equiv (H₁ := Z) (H₂ := zpowers y₁) hcZ1 hdisjZ1
    have h1 : Nat.card A = Nat.card Z * Nat.card (zpowers y₁) := by
      calc Nat.card A = Nat.card (Z × zpowers y₁) := (Nat.card_congr e.toEquiv).symm
        _ = Nat.card Z * Nat.card (zpowers y₁) := Nat.card_prod _ _
    rw [h1, hcZ, Nat.card_zpowers, hord1]
  have hex2 : ∃ y : G, y ∈ Ω ∧ y ∉ A := by
    by_contra h
    push Not at h
    have hle : Nat.card Ω ≤ Nat.card A := Subgroup.card_le_of_le fun x hx => h x hx
    rw [hΩcard, hAcard] at hle
    norm_num at hle
  obtain ⟨y₂, hy2Ω, hy2A⟩ := hex2
  have hy2_2 : y₂ ^ 2 = 1 := (fzl_mem_omega hcomm).mp hy2Ω |>.2
  have hy2_ne : y₂ ≠ 1 := fun h => hy2A (h ▸ A.one_mem)
  have hord2 : orderOf y₂ = 2 := fzl_orderOf_eq_two hy2_2 hy2_ne
  let Y : Subgroup G := zpowers y₁ ⊔ zpowers y₂
  have hYΩ : Y ≤ Ω := sup_le (Subgroup.zpowers_le.mpr hy1Ω) (Subgroup.zpowers_le.mpr hy2Ω)
  have hYP : Y ≤ P := fun x hx => hΩP (hYΩ hx)
  have hc12 : ∀ a ∈ zpowers y₁, ∀ b ∈ zpowers y₂, Commute a b :=
    fun a ha b hb => hcomm a (hΩP (Subgroup.zpowers_le.mpr hy1Ω ha)) b
      (hΩP (Subgroup.zpowers_le.mpr hy2Ω hb))
  have hmem12 : ∀ x ∈ Y, x = 1 ∨ x = y₁ ∨ x = y₂ ∨ x = y₁ * y₂ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hxab⟩ := (fzl_mem_sup_iff_of_commute hc12).mp hx
    rw [← hxab]
    rcases (fzl_mem_zpowers_pair hy1_2 hy1_ne).mp ha with h1 | h1 <;>
      rcases (fzl_mem_zpowers_pair hy2_2 hy2_ne).mp hb with h2 | h2 <;>
      rw [h1, h2] <;> simp
  have hZY : Z ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxZ, hxY⟩
    rcases hmem12 x hxY with h | h | h | h
    · exact h
    · exact absurd (h ▸ hxZ) hy1Z
    · refine absurd ?_ hy2A
      rw [← h]
      exact Subgroup.mem_sup_left hxZ
    · refine absurd ?_ hy2A
      have h2 : y₂ = y₁ * x := by
        rw [h, ← mul_assoc, ← pow_two, hy1_2, one_mul]
      rw [h2]
      exact A.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁))
        (Subgroup.mem_sup_left hxZ)
  have hdisj12 : zpowers y₁ ⊓ zpowers y₂ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hx1, hx2⟩
    rcases (fzl_mem_zpowers_pair hy1_2 hy1_ne).mp hx1 with h | h
    · exact h
    · rw [h] at hx2 ⊢
      rcases (fzl_mem_zpowers_pair hy2_2 hy2_ne).mp hx2 with h2 | h2
      · exact absurd h2 hy1_ne
      · refine absurd ?_ hy2A
        rw [← h2]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁)
  have hYcard : Nat.card Y = 4 := by
    obtain ⟨e⟩ := fzl_prod_sup_equiv (H₁ := zpowers y₁) (H₂ := zpowers y₂) hc12 hdisj12
    have h1 : Nat.card Y = Nat.card (zpowers y₁) * Nat.card (zpowers y₂) := by
      calc Nat.card Y = Nat.card (zpowers y₁ × zpowers y₂) := (Nat.card_congr e.toEquiv).symm
        _ = Nat.card (zpowers y₁) * Nat.card (zpowers y₂) := Nat.card_prod _ _
    rw [h1, Nat.card_zpowers, Nat.card_zpowers, hord1, hord2]
  have hEY : E ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxE, hxY⟩
    have hxZ : x ∈ Z := hEZ x hxE ((fzl_mem_omega hcomm).mp (hYΩ hxY)).2
    have hx : x ∈ Z ⊓ Y := ⟨hxZ, hxY⟩
    rwa [hZY, Subgroup.mem_bot] at hx
  have hcEY : ∀ a ∈ E, ∀ b ∈ Y, Commute a b :=
    fun a ha b hb => hcomm a (hEP ha) b (hYP hb)
  have hEYcard : Nat.card (E ⊔ Y : Subgroup G) = Nat.card E * Nat.card Y := by
    obtain ⟨e⟩ := fzl_prod_sup_equiv (H₁ := E) (H₂ := Y) hcEY hEY
    calc Nat.card (E ⊔ Y : Subgroup G) = Nat.card (E × Y) := (Nat.card_congr e.toEquiv).symm
      _ = Nat.card E * Nat.card Y := Nat.card_prod _ _
  have hsupP : E ⊔ Y = P := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hEP hYP) ?_
    rw [hEYcard, hcE, hYcard, hcard]
  obtain ⟨eE⟩ := hEeq
  obtain ⟨eP⟩ := fzl_prod_sup_equiv (H₁ := E) (H₂ := Y) hcEY hEY
  have heP : (↥E × ↥Y) ≃* ↥P := eP.trans (MulEquiv.subgroupCongr hsupP)
  let ζ1 : Multiplicative (ZMod 2) ≃* ↥(zpowers y₁) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, hord1, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card])
  let ζ2 : Multiplicative (ZMod 2) ≃* ↥(zpowers y₂) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, hord2, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card])
  let eY : ↥Y ≃* Multiplicative (ZMod 2 × ZMod 2) :=
    (((MulEquiv.prodCongr ζ1 ζ2).trans
      (fzl_prod_sup_equiv (H₁ := zpowers y₁) (H₂ := zpowers y₂) hc12 hdisj12).some).symm).trans
      (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2)).symm
  let pA : Z4Z4 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
    MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4)
  let pB : Multiplicative (ZMod 4) × Multiplicative (ZMod 2 × ZMod 2) ≃*
      Multiplicative (ZMod 4 × (ZMod 2 × ZMod 2)) :=
    (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 2 × ZMod 2)).symm
  let q1 : FzZ4422 ≃* Multiplicative (ZMod 4) ×
      Multiplicative (ZMod 4 × (ZMod 2 × ZMod 2)) :=
    MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4 × (ZMod 2 × ZMod 2))
  let g : Z4Z4 × Multiplicative (ZMod 2 × ZMod 2) ≃* FzZ4422 :=
    (MulEquiv.prodCongr pA (MulEquiv.refl _)).trans
      (MulEquiv.prodAssoc.trans ((MulEquiv.prodCongr (MulEquiv.refl _) pB).trans q1.symm))
  exact ⟨heP.symm.trans ((MulEquiv.prodCongr eE eY).trans g)⟩

end CFSG.OddStandard.SmallF3.FritzII
