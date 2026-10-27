module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallOutChar

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup
open scoped commutatorElement

@[expose] def HasCommProp (Y : Type*) [Group Y] : Prop :=
  ∀ T : Sylow 2 Y, ∀ X : Subgroup (MulAut Y), IsPGroup 2 X →
    (∀ σ ∈ X, σ ∈ (MulAut.conj : Y →* MulAut Y).range →
      ∃ t ∈ (T : Subgroup Y), σ = MulAut.conj t) →
    (∀ t ∈ (T : Subgroup Y), MulAut.conj t ∈ X) →
    ∃ t ∈ (T : Subgroup Y), (∀ σ ∈ X, σ t ∈ zpowers t) ∧
      ∀ σ₁ ∈ X, ∀ σ₂ ∈ X, ⁅σ₁, σ₂⁆ ∈ zpowers (MulAut.conj t)

theorem zpow_one_or_self_of_sq {G : Type*} [Group G] {s : G} (hs : s * s = 1) (k : ℤ) :
    s ^ k = 1 ∨ s ^ k = s := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  induction k using Int.induction_on with
  | zero => exact Or.inl (zpow_zero s)
  | succ i ih =>
    rw [zpow_add_one]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (one_mul s)
    · exact Or.inl hs
  | pred i ih =>
    rw [zpow_sub_one, hinv]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (one_mul s)
    · exact Or.inl hs

theorem exists_central_of_card_le_eight {G : Type*} [Group G] [Finite G] (h2 : IsPGroup 2 G)
    (h8 : Nat.card G ≤ 8) :
    ∃ z : G, z * z = 1 ∧ (∀ g, g * z = z * g) ∧ ∀ a b : G, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · refine ⟨1, one_mul 1, fun g => by simp, fun a b => Or.inl ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a b
  push Not at hcomm
  obtain ⟨a₀, b₀, hab₀⟩ := hcomm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  have hnle : n ≤ 3 := by
    have hle : 2 ^ n ≤ 2 ^ 3 := by rw [← hn]; exact h8
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hn3 : n = 3 := by
    by_contra hne
    have hc : ∀ a b : G, a * b = b * a := by
      interval_cases n
      · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by rw [hn]; rfl)).1
        exact fun a b => Subsingleton.elim _ _
      · have : IsCyclic G := isCyclic_of_prime_card (p := 2) (by rw [hn]; rfl)
        exact fun a b => (IsCyclic.isMulCommutative (α := G)).is_comm.comm a b
      · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
        exact fun a b => this.is_comm.comm a b
      · exact absurd rfl hne
    exact hab₀ (hc a₀ b₀)
  subst hn3
  have hnotcyc : ¬ IsCyclic (G ⧸ center G) := fun hcyc =>
    hab₀ ((MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (center G)) (by rw [QuotientGroup.ker_mk'])).is_comm.comm a₀ b₀)
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hn (by norm_num)
  have hidx : (center G).index * 2 ^ k = 2 ^ 3 := by rw [← hk, index_mul_card, hn]
  have hk1 : k = 1 := by
    have hk3 : k ≤ 3 := by
      have h1 : 2 ^ k ∣ 2 ^ 3 := ⟨(center G).index, by rw [← hidx, mul_comm]⟩
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    interval_cases k
    · rfl
    · exfalso
      have hi : (center G).index = 2 := by omega
      exact hnotcyc (isCyclic_of_prime_card (p := 2) (by rw [← index_eq_card, hi]))
    · exfalso
      have hi : (center G).index = 1 := by omega
      have : Subsingleton (G ⧸ center G) :=
        (Nat.card_eq_one_iff_unique.1 (by rw [← index_eq_card, hi])).1
      exact hnotcyc isCyclic_of_subsingleton
  subst hk1
  have hZ2 : Nat.card (center G) = 2 := by rw [hk]; rfl
  have : Nontrivial (center G) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hZ2]; norm_num)
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := exists_ne (1 : center G)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzo : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard (center G) hzZ
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1'
    · exact h
  have hzz : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
  have hZeq : zpowers z = center G := by
    refine eq_of_le_of_card_ge (zpowers_le.2 hzZ) ?_
    rw [hZ2, Nat.card_zpowers, hzo]
  have hquot : Nat.card (G ⧸ center G) = 2 ^ 2 := by
    rw [← index_eq_card]
    omega
  have hqc := IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot
  refine ⟨z, hzz, fun g => (mem_center_iff.1 hzZ g), fun a b => ?_⟩
  have hab : ⁅a, b⁆ ∈ center G := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hqc.is_comm.comm _ _
  rw [← hZeq] at hab
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hab
  rw [← hj]
  exact zpow_one_or_self_of_sq hzz j


section Inner

variable {Y : Type*} [Group Y]

theorem eq_of_conj_eq (hZ : center Y = ⊥) {a b : Y} (h : MulAut.conj a = MulAut.conj b) :
    a = b := by
  have hc : b⁻¹ * a ∈ center Y := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut Y => φ g) h
    simp only [MulAut.conj_apply] at h1
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * g := by group
  rw [hZ, mem_bot] at hc
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hc, mul_one]

theorem conj_map (σ : MulAut Y) (t : Y) : MulAut.conj (σ t) = σ * MulAut.conj t * σ⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem commProp_dihedral (hZ : center Y = ⊥) {T : Subgroup Y} {n : ℕ} (hn : 2 ≤ n)
    (φ : T ≃* DihedralGroup (2 ^ n)) (X : Subgroup (MulAut Y))
    (hinn : ∀ σ ∈ X, σ ∈ (MulAut.conj : Y →* MulAut Y).range → ∃ t ∈ T, σ = MulAut.conj t)
    (hTX : ∀ t ∈ T, MulAut.conj t ∈ X)
    (hcomm : ∀ σ₁ ∈ X, ∀ σ₂ ∈ X, ⁅σ₁, σ₂⁆ ∈ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ t ∈ T, (∀ σ ∈ X, σ t ∈ zpowers t) ∧
      ∀ σ₁ ∈ X, ∀ σ₂ ∈ X, ⁅σ₁, σ₂⁆ ∈ zpowers (MulAut.conj t) := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  set c₀ : T := φ.symm (DihedralGroup.r 1) with hc₀
  have hφc : φ c₀ = DihedralGroup.r 1 := by rw [hc₀, MulEquiv.apply_symm_apply]
  have hcT : (c₀ : Y) ∈ T := c₀.2
  have hσT : ∀ σ ∈ X, ∀ t ∈ T, σ t ∈ T := by
    intro σ hσ t ht
    have hmem : σ * MulAut.conj t * σ⁻¹ ∈ X := mul_mem (mul_mem hσ (hTX t ht)) (inv_mem hσ)
    obtain ⟨t', ht', heq⟩ := hinn _ hmem ⟨σ t, conj_map σ t⟩
    rw [← conj_map] at heq
    rw [eq_of_conj_eq hZ heq]
    exact ht'
  have hrot1 : ∀ u : DihedralGroup (2 ^ n), orderOf u = 2 ^ n →
      ∃ i : ℕ, u = DihedralGroup.r 1 ^ i := by
    intro u hu
    cases u with
    | r i => exact ⟨i.val, by rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩
    | sr i =>
      rw [DihedralGroup.orderOf_sr] at hu
      omega
  have hrot2 : ∀ u : DihedralGroup (2 ^ n), u * DihedralGroup.r 1 = DihedralGroup.r 1 * u →
      ∃ i : ℕ, u = DihedralGroup.r 1 ^ i := by
    intro u hu
    cases u with
    | r i => exact ⟨i.val, by rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩
    | sr i =>
      exfalso
      rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at hu
      have h1 : i + 1 = i - 1 := DihedralGroup.sr.inj hu
      have h2 : ((2 : ℕ) : ZMod (2 ^ n)) = 0 := by
        have : ((2 : ℕ) : ZMod (2 ^ n)) = (i + 1) - (i - 1) := by push_cast; ring
        rw [this, h1, sub_self]
      have h3 := (ZMod.natCast_eq_zero_iff 2 (2 ^ n)).1 h2
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  have hord : orderOf (c₀ : Y) = 2 ^ n := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ, hφc, DihedralGroup.orderOf_r_one]
  have hi : ∀ σ ∈ X, σ c₀ ∈ zpowers (c₀ : Y) := by
    intro σ hσ
    set u : T := ⟨σ c₀, hσT σ hσ c₀ hcT⟩
    have hu : orderOf (φ u) = 2 ^ n := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hord]
    obtain ⟨i, hi⟩ := hrot1 _ hu
    have h1 : u = c₀ ^ i := by
      apply φ.injective
      rw [hi, map_pow, hφc]
    have h2 : σ c₀ = (c₀ : Y) ^ i := congrArg Subtype.val h1
    rw [h2]
    exact pow_mem (mem_zpowers _) i
  have hexp : ∀ σ ∈ X, ∃ a : ℤ, ∀ k : ℤ, σ ((c₀ : Y) ^ k) = (c₀ : Y) ^ (a * k) := by
    intro σ hσ
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (hi σ hσ)
    exact ⟨a, fun k => by rw [map_zpow, ← ha, zpow_mul]⟩
  refine ⟨c₀, hcT, hi, fun σ₁ h₁ σ₂ h₂ => ?_⟩
  obtain ⟨a₁, ha₁⟩ := hexp σ₁ h₁
  obtain ⟨a₂, ha₂⟩ := hexp σ₂ h₂
  obtain ⟨b₁, hb₁⟩ := hexp σ₁⁻¹ (inv_mem h₁)
  obtain ⟨b₂, hb₂⟩ := hexp σ₂⁻¹ (inv_mem h₂)
  have e1 : σ₁⁻¹ (c₀ : Y) = (c₀ : Y) ^ b₁ := by
    have h := hb₁ 1
    rwa [mul_one, zpow_one] at h
  have e2 : σ₂⁻¹ (c₀ : Y) = (c₀ : Y) ^ b₂ := by
    have h := hb₂ 1
    rwa [mul_one, zpow_one] at h
  have hc1 : (c₀ : Y) ^ (a₁ * b₁) = c₀ := by
    have h := ha₁ b₁
    rw [← e1, MulAut.apply_inv_self] at h
    exact h.symm
  have hc2 : (c₀ : Y) ^ (a₂ * b₂) = c₀ := by
    have h := ha₂ b₂
    rw [← e2, MulAut.apply_inv_self] at h
    exact h.symm
  have hfix : ⁅σ₁, σ₂⁆ c₀ = c₀ := by
    rw [commutatorElement_def, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, e2, hb₁,
      ha₂, ha₁]
    have : a₁ * (a₂ * (b₁ * b₂)) = (a₁ * b₁) * (a₂ * b₂) := by ring
    rw [this, zpow_mul, hc1, hc2]
  obtain ⟨t, ht, hteq⟩ := hinn _ (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)) (hcomm σ₁ h₁ σ₂ h₂)
  rw [hteq] at hfix ⊢
  simp only [MulAut.conj_apply] at hfix
  have htc : t * c₀ = c₀ * t := by
    calc t * c₀ = t * c₀ * t⁻¹ * t := by group
      _ = c₀ * t := by rw [hfix]
  set v : T := ⟨t, ht⟩
  have hv : φ v * DihedralGroup.r 1 = DihedralGroup.r 1 * φ v := by
    rw [← hφc, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htc
  obtain ⟨i, hvi⟩ := hrot2 _ hv
  have h1 : v = c₀ ^ i := by
    apply φ.injective
    rw [hvi, map_pow, hφc]
  have h2 : t = (c₀ : Y) ^ i := congrArg Subtype.val h1
  rw [h2, map_pow]
  exact pow_mem (mem_zpowers _) i


@[expose] def HasOuterSign (Y : Type*) [Group Y] : Prop :=
  ∃ ψ : MulAut Y →* Multiplicative (ZMod 2), (∀ y, ψ (MulAut.conj y) = 1) ∧
    ∀ σ : MulAut Y, (∃ k : ℕ, σ ^ 2 ^ k = 1) → ψ σ = 1 →
      σ ∈ (MulAut.conj : Y →* MulAut Y).range

theorem HasOuterSign.of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : HasOuterSign Y') : HasOuterSign Y := by
  obtain ⟨ψ, hinn, hker⟩ := h
  refine ⟨ψ.comp (MulAut.congr e).toMonoidHom, fun y => ?_, fun σ hσ hψ => ?_⟩
  · have : MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
      ext x
      simp [MulAut.congr_apply, MulAut.conj_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, this]
    exact hinn (e y)
  · obtain ⟨k, hk⟩ := hσ
    obtain ⟨y', hy'⟩ := hker (MulAut.congr e σ) ⟨k, by rw [← map_pow, hk, map_one]⟩ hψ
    refine ⟨e.symm y', ?_⟩
    apply (MulAut.congr e).injective
    rw [← hy']
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem hasCommProp_of {Y : Type*} [Group Y] [Finite Y] (hZ : center Y = ⊥)
    (hout : HasOuterChar Y)
    (hT : ∀ T : Sylow 2 Y, (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((T : Subgroup Y) ≃* DihedralGroup (2 ^ n))) ∨
      (Nat.card (T : Subgroup Y) = 4 ∧ HasOuterSign Y)) : HasCommProp Y := by
  intro T X hX2 hinnX hTX
  obtain ⟨m, ψ, -, hψker⟩ := hout
  have hXc : ∀ σ₁ ∈ X, ∀ σ₂ ∈ X, ⁅σ₁, σ₂⁆ ∈ X := fun σ₁ h₁ σ₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have h2elt : ∀ σ ∈ X, ∃ k : ℕ, σ ^ 2 ^ k = 1 := fun σ hσ => by
    obtain ⟨k, hk⟩ := hX2 ⟨σ, hσ⟩
    refine ⟨k, ?_⟩
    have := congrArg X.subtype hk
    rwa [map_pow, map_one] at this
  have hcomm : ∀ σ₁ ∈ X, ∀ σ₂ ∈ X, ⁅σ₁, σ₂⁆ ∈ (MulAut.conj : Y →* MulAut Y).range := by
    intro σ₁ h₁ σ₂ h₂
    refine hψker _ (h2elt _ (hXc σ₁ h₁ σ₂ h₂)) ?_
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rcases hT T with ⟨n, hn, ⟨φ⟩⟩ | ⟨h4, ψ₀, -, hψ₀ker⟩
  · exact commProp_dihedral hZ hn φ X hinnX hTX hcomm
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := fun a b hab =>
    eq_of_conj_eq hZ hab
  set f₀ : X →* Multiplicative (ZMod 2) := ψ₀.comp X.subtype
  have hker : f₀.ker.map X.subtype ≤ (T : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨t, ht, heq⟩ := hinnX σ σ.2 (hψ₀ker σ (h2elt σ σ.2) hσ)
    exact ⟨t, ht, heq.symm⟩
  have hcard_ker : Nat.card f₀.ker ≤ 4 := by
    calc Nat.card f₀.ker = Nat.card (f₀.ker.map X.subtype) :=
          (card_map_of_injective X.subtype_injective).symm
      _ ≤ Nat.card ((T : Subgroup Y).map (MulAut.conj : Y →* MulAut Y)) := card_le_of_le hker
      _ = 4 := by rw [card_map_of_injective hinj, h4]
  have hcard_range : Nat.card f₀.range ≤ 2 := by
    calc Nat.card f₀.range ≤ Nat.card (Multiplicative (ZMod 2)) := card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  have hX8 : Nat.card X ≤ 8 := by
    rw [← f₀.ker.card_mul_index, index_ker]
    calc Nat.card f₀.ker * Nat.card f₀.range ≤ 4 * 2 := Nat.mul_le_mul hcard_ker hcard_range
      _ = 8 := rfl
  obtain ⟨z, -, hzc, hzcomm⟩ := exists_central_of_card_le_eight hX2 hX8
  have hcoe : ∀ σ₁ (h₁ : σ₁ ∈ X) σ₂ (h₂ : σ₂ ∈ X),
      ⁅σ₁, σ₂⁆ = X.subtype ⁅(⟨σ₁, h₁⟩ : X), ⟨σ₂, h₂⟩⁆ := fun σ₁ h₁ σ₂ h₂ =>
    (map_commutatorElement X.subtype ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩).symm
  by_cases hall : ∀ a b : X, ⁅a, b⁆ = 1
  · refine ⟨1, one_mem _, fun σ _ => ?_, fun σ₁ h₁ σ₂ h₂ => ?_⟩
    · rw [map_one]
      exact one_mem _
    · rw [hcoe σ₁ h₁ σ₂ h₂, hall, map_one]
      exact one_mem _
  push Not at hall
  obtain ⟨a, b, hab⟩ := hall
  have hz : ⁅a, b⁆ = z := (hzcomm a b).resolve_left hab
  have hzinn : (z : MulAut Y) ∈ (MulAut.conj : Y →* MulAut Y).range := by
    have h1 := hcomm a a.2 b b.2
    rwa [hcoe a a.2 b b.2, hz] at h1
  obtain ⟨t, ht, hzt⟩ := hinnX z z.2 hzinn
  refine ⟨t, ht, fun σ hσ => ?_, fun σ₁ h₁ σ₂ h₂ => ?_⟩
  · have h1 : MulAut.conj (σ t) = MulAut.conj t := by
      have h2 : σ * (z : MulAut Y) = z * σ := congrArg Subtype.val (hzc ⟨σ, hσ⟩)
      rw [conj_map, ← hzt, h2, mul_inv_cancel_right]
    rw [eq_of_conj_eq hZ h1]
    exact mem_zpowers t
  · rw [hcoe σ₁ h₁ σ₂ h₂]
    rcases hzcomm ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ with h | h
    · rw [h, map_one]
      exact one_mem _
    · rw [h]
      change (z : MulAut Y) ∈ _
      rw [hzt]
      exact mem_zpowers _

end Inner

end CFSG.ComponentClassification.CatFactsSmall
