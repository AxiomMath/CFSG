module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Facts

public section

namespace CFSG.ComponentClassification.HarrisLit.Q81

open CFSG Subgroup

variable {G : Type} [Group G]

@[expose] def oddPart (H : Subgroup G) : Subgroup G := closure {g | g ∈ H ∧ Odd (orderOf g)}

theorem oddPart_le (H : Subgroup G) : oddPart H ≤ H :=
  (closure_le H).mpr fun _ hg => hg.1

theorem mem_oddPart {H : Subgroup G} {g : G} (hg : g ∈ H) (hodd : Odd (orderOf g)) :
    g ∈ oddPart H :=
  subset_closure ⟨hg, hodd⟩

theorem mem_normalizer_oddPart {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer (oddPart H : Set G) := by
  have key : ∀ x : G, x ∈ normalizer (H : Set G) → ∀ y ∈ oddPart H, x * y * x⁻¹ ∈ oddPart H := by
    intro x hx y hy
    have h1 : (oddPart H).map (MulAut.conj x).toMonoidHom ≤ oddPart H := by
      rw [oddPart, MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, ⟨hy, hodd⟩, rfl⟩
      have e : (MulAut.conj x).toMonoidHom y = x * y * x⁻¹ := rfl
      rw [e]
      refine mem_oddPart ((mem_normalizer_iff.mp hx y).mp hy) ?_
      rw [← e, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hodd
    exact h1 (mem_map_of_mem _ hy)
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h1

variable [Finite G]

omit [Finite G] in
theorem mem_of_odd_orderOf {I : Subgroup G} [hIn : I.Normal] (hI : Group.IsPerfect ↥I)
    (hP : Blueprint.LieModel (↥I ⧸ center ↥I) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥I ⧸ center ↥I) .PSU 4 3 1)
    (hC : IsPGroup 2 ↥(centralizer (I : Set G))) {g : G} (hg : Odd (orderOf g)) : g ∈ I := by
  have hgN : g ∈ normalizer (I : Set G) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top g
  obtain ⟨q, hq, hc⟩ := exists_pow_eight_mem_centralizer hI hP hgN
  obtain ⟨a, ha⟩ := hC ⟨_, hc⟩
  have ha' : (q⁻¹ * g ^ 8) ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hcomm : Commute q (q⁻¹ * g ^ 8) := by
    have h1 := mem_centralizer_iff.mp hc q hq
    exact h1
  have hpow : g ^ (8 * 2 ^ a) = q ^ 2 ^ a := by
    have h1 : g ^ 8 = q * (q⁻¹ * g ^ 8) := by group
    rw [pow_mul, h1, hcomm.mul_pow, ha', mul_one]
  have hmem : g ^ (8 * 2 ^ a) ∈ I := by rw [hpow]; exact pow_mem hq _
  have hcop : (8 * 2 ^ a).gcd (orderOf g) = 1 := by
    have h8 : 8 * 2 ^ a = 2 ^ (a + 3) := by ring
    rw [h8]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg)
  have hz := mem_zpowers_pow_iff.mpr hcop
  exact (zpowers_le.mpr hmem) hz

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers_two {z x : G} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem card_center_le_two {Y : Type} [Group Y] (hY : IsSLTwoOver 3 Y) :
    Nat.card ↥(center Y) ≤ 2 := by
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := hY
  have h1 : Nat.card ↥(center Y) = Nat.card ↥(center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Nat.card_congr ((Subgroup.centerCongr e).toEquiv)
  rw [h1, Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
    Fintype.card_fin]
  exact card_rootsOfUnity F 2

theorem center_eq_zpowers {H : Subgroup G} (hH : IsSLTwoOver 3 ↥H) {z : G} (hz : z ∈ H)
    (hzc : ∀ y ∈ H, y * z = z * y) (hz2 : orderOf z = 2) :
    ∀ y ∈ H, (∀ x ∈ H, y * x = x * y) → y ∈ zpowers z := by
  intro y hy hyc
  set zH : ↥H := ⟨z, hz⟩
  have hzH : zH ∈ center ↥H := mem_center_iff.mpr fun x => Subtype.ext (hzc x x.2)
  have hyH : (⟨y, hy⟩ : ↥H) ∈ center ↥H :=
    mem_center_iff.mpr fun x => Subtype.ext (hyc x x.2).symm
  have hle : zpowers zH ≤ center ↥H := zpowers_le.mpr hzH
  have hcard : Nat.card ↥(zpowers zH) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2]
  have heq : zpowers zH = center ↥H := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard]
    exact card_center_le_two hH
  rw [← heq] at hyH
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyH
  refine mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa [zH] using this

theorem oddPart_centralizer_eq (hF : L4U4ThreeInvolutionFacts) {I : Subgroup G} [I.Normal]
    (hI : IsQuasisimple ↥I)
    (hP : Blueprint.LieModel (↥I ⧸ center ↥I) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥I ⧸ center ↥I) .PSU 4 3 1)
    (hZ : Nat.card ↥(center ↥I) ∣ 2) (hC : IsPGroup 2 ↥(centralizer (I : Set G)))
    {z : G} (hz : z ∈ I) (hz2 : orderOf z = 2) {X₁ X₂ : Subgroup G} (hne : X₁ ≠ X₂)
    (h₁ : X₁ ≤ I ⊓ centralizer {z}) (h₂ : X₂ ≤ I ⊓ centralizer {z})
    (hs₁ : (X₁.subgroupOf (I ⊓ centralizer {z})).IsSubnormal)
    (hs₂ : (X₂.subgroupOf (I ⊓ centralizer {z})).IsSubnormal)
    (hc : X₁ ≤ centralizer (X₂ : Set G)) (hi : X₁ ⊓ X₂ = zpowers z)
    (hX₁ : IsSLTwoOver 3 ↥X₁) (hX₂ : IsSLTwoOver 3 ↥X₂) :
    oddPart (centralizer {z}) = X₁ ⊔ X₂ := by
  rw [hF.cent G I hI hP hZ z hz hz2 X₁ X₂ hne h₁ h₂ hs₁ hs₂ hc hi hX₁ hX₂, oddPart]
  congr 1
  ext g
  refine ⟨fun ⟨hg, hodd⟩ => ⟨⟨mem_of_odd_orderOf hI.1 hP hC hodd, hg⟩, hodd⟩,
    fun ⟨hg, hodd⟩ => ⟨hg.2, hodd⟩⟩

omit [Finite G] in
theorem exists_mul_of_mem_sup {X₁ X₂ : Subgroup G} (hc : X₁ ≤ centralizer (X₂ : Set G))
    {y : G} (hy : y ∈ X₁ ⊔ X₂) : ∃ x₁ ∈ X₁, ∃ x₂ ∈ X₂, x₁ * x₂ = y := by
  have hN : X₁ ≤ normalizer (X₂ : Set G) := hc.trans (centralizer_le_normalizer _)
  have h1 : y ∈ ((X₁ ⊔ X₂ : Subgroup G) : Set G) := hy
  rw [coe_mul_of_left_le_normalizer_right X₁ X₂ hN] at h1
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h1
  exact ⟨x₁, hx₁, x₂, hx₂, rfl⟩

theorem mem_zpowers_of_mem_center_sup {X₁ X₂ : Subgroup G} (hc : X₁ ≤ centralizer (X₂ : Set G))
    {z : G} (hi : X₁ ⊓ X₂ = zpowers z) (hz2 : orderOf z = 2) (hX₁ : IsSLTwoOver 3 ↥X₁)
    (hX₂ : IsSLTwoOver 3 ↥X₂) {y : G} (hy : y ∈ X₁ ⊔ X₂)
    (hyc : ∀ x ∈ X₁ ⊔ X₂, y * x = x * y) : y ∈ zpowers z := by
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup hc hy
  have hz : z ∈ X₁ ⊓ X₂ := by rw [hi]; exact mem_zpowers z
  have hcomm₁ : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hc ha) b hb).symm
  have h1 : ∀ a ∈ X₁, x₁ * a = a * x₁ := by
    intro a ha
    have h := hyc a (mem_sup_left ha)
    have hx₂a : x₂ * a = a * x₂ := (hcomm₁ a ha x₂ hx₂).symm
    have h' : x₁ * a * x₂ = a * x₁ * x₂ := by
      calc x₁ * a * x₂ = x₁ * (x₂ * a) := by rw [hx₂a, mul_assoc]
        _ = x₁ * x₂ * a := by rw [mul_assoc]
        _ = a * (x₁ * x₂) := h
        _ = a * x₁ * x₂ := by rw [mul_assoc]
    exact mul_right_cancel h'
  have h2 : ∀ b ∈ X₂, x₂ * b = b * x₂ := by
    intro b hb
    have h := hyc b (mem_sup_right hb)
    have hx₁b : x₁ * b = b * x₁ := hcomm₁ x₁ hx₁ b hb
    have : x₁ * (x₂ * b) = x₁ * (b * x₂) := by
      rw [← mul_assoc, h, ← mul_assoc, ← mul_assoc, ← hx₁b]
    exact mul_left_cancel this
  have hz₁ := center_eq_zpowers hX₁ (mem_inf.mp hz).1
    (fun a ha => (hcomm₁ a ha z (mem_inf.mp hz).2)) hz2 x₁ hx₁ h1
  have hz₂ := center_eq_zpowers hX₂ (mem_inf.mp hz).2
    (fun b hb => (hcomm₁ z (mem_inf.mp hz).1 b hb).symm) hz2 x₂ hx₂ h2
  exact mul_mem hz₁ hz₂

end CFSG.ComponentClassification.HarrisLit.Q81
