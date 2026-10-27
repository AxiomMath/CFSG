module

public import CFSG.CharacterTheory.BrauerLinearThree.TenColumnCount
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionColumns

public section

open scoped BigOperators Classical

namespace CFSG.BrauerLinearThree

namespace TenColumn

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G] {W K H : Subgroup G}

@[expose] noncomputable def torusColumn (hWK : W ≤ K) (χ : W →* ℂˣ) : G → ℂ :=
  inducedFunction K (fun k => 1 - (torusTransfer hWK χ k : ℂ))

theorem units_inv_eq_conj_of_pow_eq_one {u : ℂˣ} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    ((u⁻¹ : ℂˣ) : ℂ) = starRingEnd ℂ (u : ℂ) := by
  have hu' : (u : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hnorm : ‖(u : ℂ)‖ = 1 := by
    have h := congrArg (‖·‖) hu'
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h
  have hmul : (u : ℂ) * starRingEnd ℂ (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right hmul

variable (hWK : W ≤ K) (hKH : K ≤ H) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
  (hinv : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
  (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hHK : Nat.card H = 2 * Nat.card K)
  (hTI : ∀ g : G, ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ∈ W → g ∈ H)

include hcent hinv hKn hTI in
theorem torusColumn_summand (χ : W →* ℂˣ) (k : K) (c : G) :
    (if h : c⁻¹ * (k : G) * c ∈ K then 1 - (torusTransfer hWK χ ⟨_, h⟩ : ℂ) else 0) =
      (if c ∈ K then 1 - (torusTransfer hWK χ k : ℂ) else 0) +
      (if c ∈ H ∧ c ∉ K then 1 - (((torusTransfer hWK χ k)⁻¹ : ℂˣ) : ℂ) else 0) := by
  by_cases hcK : c ∈ K
  · have hmem : c⁻¹ * (k : G) * c ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hcK) k.2) hcK
    have hval : torusTransfer hWK χ ⟨_, hmem⟩ = torusTransfer hWK χ k := by
      have h := torusTransfer_conj_of_mem hWK χ k ⟨c, hcK⟩⁻¹
      have e : (⟨c, hcK⟩⁻¹ * k * ⟨c, hcK⟩⁻¹⁻¹ : K) = ⟨_, hmem⟩ := Subtype.ext (by simp)
      rwa [e] at h
    simp only [hmem, hcK, hval, not_true_eq_false, and_false, dite_true, ite_true, ite_false,
      add_zero]
  · by_cases hcH : c ∈ H
    · have hcinvH : c⁻¹ ∈ H := H.inv_mem hcH
      have hcinvK : c⁻¹ ∉ K := fun h => hcK (by simpa using K.inv_mem h)
      have hmem' : c⁻¹ * (k : G) * c⁻¹⁻¹ ∈ K := hKn _ hcinvH _ k.2
      have hmem : c⁻¹ * (k : G) * c ∈ K := by simpa using hmem'
      have hval : torusTransfer hWK χ ⟨_, hmem⟩ = (torusTransfer hWK χ k)⁻¹ := by
        have h := torusTransfer_conj_of_not_mem hWK hcent hinv χ hcinvH hcinvK k hmem'
        have e : (⟨c⁻¹ * (k : G) * c⁻¹⁻¹, hmem'⟩ : K) = ⟨_, hmem⟩ := Subtype.ext (by simp)
        rwa [e] at h
      simp only [hmem, hcK, hcH, hval, not_false_eq_true, and_self, dite_true, ite_true,
        ite_false, zero_add]
    · have hzero : ∀ h : c⁻¹ * (k : G) * c ∈ K,
          1 - (torusTransfer hWK χ ⟨_, h⟩ : ℂ) = 0 := by
        intro h
        by_contra hne
        have hne' : torusTransfer hWK χ ⟨_, h⟩ ≠ 1 := by
          intro h1
          apply hne
          rw [h1, Units.val_one, sub_self]
        have hc : c⁻¹⁻¹ * ((⟨_, h⟩ : K) : G) * c⁻¹ ∈ K := by
          have e : c⁻¹⁻¹ * (c⁻¹ * (k : G) * c) * c⁻¹ = k := by group
          rw [e]
          exact k.2
        have hcinv := mem_of_torusTransfer_conj_ne_one hWK hcent hTI χ hne' c⁻¹ hc
        exact hcH (by simpa using H.inv_mem hcinv)
      by_cases hmem : c⁻¹ * (k : G) * c ∈ K
      · simp only [hmem, hcK, hcH, dite_true, ite_false, false_and, add_zero, hzero hmem]
      · simp only [hmem, hcK, hcH, dite_false, ite_false, false_and, add_zero]

include hKH hcent hinv hKn hHK hTI in
theorem torusColumn_apply_of_mem (χ : W →* ℂˣ) (k : K) :
    torusColumn hWK χ k =
      2 - (torusTransfer hWK χ k : ℂ) - (((torusTransfer hWK χ k)⁻¹ : ℂˣ) : ℂ) := by
  rw [torusColumn, inducedFunction]
  rw [Finset.sum_congr rfl fun c _ => torusColumn_summand hWK hcent hinv hKn hTI χ k c,
    Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcardK : ((Finset.univ.filter fun c : G => c ∈ K).card : ℂ) = Nat.card K := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hcardHK : ((Finset.univ.filter fun c : G => c ∈ H ∧ c ∉ K).card : ℂ) = Nat.card K := by
    have h1 : (Finset.univ.filter fun c : G => c ∈ H ∧ c ∉ K).card +
        (Finset.univ.filter fun c : G => c ∈ K).card =
        (Finset.univ.filter fun c : G => c ∈ H).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext c
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (⟨h, -⟩ | h)
          · exact h
          · exact hKH h
        · intro h
          by_cases hc : c ∈ K
          · exact Or.inr hc
          · exact Or.inl ⟨h, hc⟩
      · rw [Finset.disjoint_filter]
        intro c _ h
        exact h.2
    have hH : (Finset.univ.filter fun c : G => c ∈ H).card = Nat.card H := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    have hK : (Finset.univ.filter fun c : G => c ∈ K).card = Nat.card K := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rw [hH, hK, hHK] at h1
    have h2 : (Finset.univ.filter fun c : G => c ∈ H ∧ c ∉ K).card = Nat.card K := by omega
    rw [h2]
  rw [hcardK, hcardHK]
  have hK0 : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  ring

omit [Fintype G] in
theorem sum_units_hom_eq_zero {Q : Type*} [Group Q] [Fintype Q] (φ : Q →* ℂˣ) {q₀ : Q}
    (hq₀ : φ q₀ ≠ 1) : ∑ q : Q, (φ q : ℂ) = 0 := by
  have hshift : ∑ q : Q, (φ q : ℂ) = (φ q₀ : ℂ) * ∑ q : Q, (φ q : ℂ) := by
    rw [Finset.mul_sum]
    exact (Fintype.sum_equiv (Equiv.mulLeft q₀) _ _ fun q => by
      simp [map_mul]).symm
  have h1 : (1 - (φ q₀ : ℂ)) * ∑ q : Q, (φ q : ℂ) = 0 := by
    rw [sub_mul, one_mul, ← hshift, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exfalso
    apply hq₀
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.mp h).symm
  · exact h

include hKH hcent hinv hKn hHK hTI in
theorem torusColumn_norm (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {k₀ : K}
    (hk₀ : torusTransfer hWK χ k₀ ≠ 1) :
    characterPairing (torusColumn hWK χ) (torusColumn hWK χ) = 3 := by
  set φ := torusTransfer hWK χ with hφ
  rw [torusColumn, characterPairing_inducedFunction_left K _ _
    (inducedFunction_conjugate K _), ← torusColumn]
  unfold characterPairing
  have hval : ∀ k : K, (1 - (φ k : ℂ)) * torusColumn hWK χ ((k⁻¹ : K) : G) =
      3 - 3 * (φ k : ℂ) - ((φ⁻¹ k : ℂˣ) : ℂ) + ((φ ^ 2) k : ℂˣ) := by
    intro k
    rw [torusColumn_apply_of_mem hWK hKH hcent hinv hKn hHK hTI χ k⁻¹, map_inv, inv_inv,
      MonoidHom.inv_apply, MonoidHom.pow_apply]
    have hk0 : (φ k : ℂ) ≠ 0 := Units.ne_zero _
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hval k]
  have hφ2 : (φ ^ 2) k₀ ≠ 1 := by
    rw [MonoidHom.pow_apply]
    intro h
    exact hk₀ (torusTransfer_eq_one_of_eq_inv hWK hcent χ hχ
      (eq_inv_of_mul_eq_one_left (by rw [← sq]; exact h)))
  have hφinv : φ⁻¹ k₀ ≠ 1 := by
    rw [MonoidHom.inv_apply]
    exact fun h => hk₀ (inv_eq_one.mp h)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_units_hom_eq_zero φ hk₀, sum_units_hom_eq_zero (φ⁻¹) hφinv,
    sum_units_hom_eq_zero (φ ^ 2) hφ2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_zero, sub_zero, add_zero]
  rw [← Nat.card_eq_fintype_card]
  have hK0 : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

theorem torusColumn_principal (χ : W →* ℂˣ) {k₀ : K} (hk₀ : torusTransfer hWK χ k₀ ≠ 1) :
    characterPairing (torusColumn hWK χ) 1 = 1 := by
  rw [torusColumn, characterPairing_inducedFunction_principal]
  unfold characterPairing
  simp only [Pi.one_apply, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, sum_units_hom_eq_zero _ hk₀, sub_zero]
  rw [← Nat.card_eq_fintype_card]
  have hK0 : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

include hKH hcent hinv hKn hHK hTI in
theorem torusColumn_one (χ : W →* ℂˣ) : torusColumn hWK χ 1 = 0 := by
  have h := torusColumn_apply_of_mem hWK hKH hcent hinv hKn hHK hTI χ 1
  rw [map_one, inv_one, Units.val_one] at h
  rw [show ((1 : K) : G) = 1 from rfl] at h
  rw [h]
  ring

theorem torusColumn_eq_zero_of_coprime (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (χ : W →* ℂˣ) {g : G} (hg : Nat.Coprime (orderOf g) (orderOf χ)) :
    torusColumn hWK χ g = 0 := by
  rw [torusColumn, inducedFunction]
  rw [Finset.sum_eq_zero, mul_zero]
  intro c _
  split_ifs with hc
  · set x : K := ⟨c⁻¹ * g * c, hc⟩ with hxdef
    have hxo : orderOf x = orderOf g := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (c⁻¹ * g * c) = orderOf g
      have e : c⁻¹ * g * c = MulAut.conj c⁻¹ g := by simp
      rw [e, MulEquiv.orderOf_eq]
    have h1 := torusTransfer_pow_orderOf hWK hcent χ x
    have h2 : (torusTransfer hWK χ x) ^ orderOf g = 1 := by
      rw [← map_pow, ← hxo, pow_orderOf_eq_one, map_one]
    have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
    rw [Nat.Coprime.gcd_eq_one hg, pow_one] at h3
    rw [h3, Units.val_one, sub_self]
  · rfl

include hKH hcent hinv hKn hHK hTI in
theorem torusColumn_star (χ : W →* ℂˣ) (g : G) :
    starRingEnd ℂ (torusColumn hWK χ g) = torusColumn hWK χ g := by
  by_cases hg : ∃ c : G, c⁻¹ * g * c ∈ K
  · obtain ⟨c, hc⟩ := hg
    have hT : torusColumn hWK χ g = torusColumn hWK χ (c⁻¹ * g * c) := by
      have h := inducedFunction_conjugate K (fun k => 1 - (torusTransfer hWK χ k : ℂ)) g c⁻¹
      rw [inv_inv] at h
      exact h.symm
    rw [hT, show c⁻¹ * g * c = ((⟨c⁻¹ * g * c, hc⟩ : K) : G) from rfl,
      torusColumn_apply_of_mem hWK hKH hcent hinv hKn hHK hTI χ]
    have hpos : 0 < orderOf χ := orderOf_pos χ
    have hconj := units_inv_eq_conj_of_pow_eq_one hpos
      (torusTransfer_pow_orderOf hWK hcent χ ⟨c⁻¹ * g * c, hc⟩)
    rw [map_sub, map_sub, hconj, Complex.conj_conj, map_ofNat]
    ring
  · push Not at hg
    rw [torusColumn, inducedFunction, Finset.sum_eq_zero, mul_zero, map_zero]
    intro c _
    rw [dite_eq_right (hg c)]

theorem exists_nat_pairing (basis : FiniteIrreducibleCharacterBasis G)
    (data : FiniteComplexRepresentation G) (θ : basis.index) :
    ∃ m : ℕ, characterPairing data.character (basis.representation θ).character = m :=
  CFSG.Semidihedral.Principal.CyclicInversion.character_pairing_nat basis data θ

theorem torusColumn_pairing_int (χ : W →* ℂˣ) (basis : FiniteIrreducibleCharacterBasis G)
    (θ : basis.index) :
    ∃ z : ℤ, characterPairing (torusColumn hWK χ) (basis.representation θ).character = z := by
  let line : FiniteComplexRepresentation K :=
    { vector := ℂ
      representation := CFSG.TwoRankLowerBound.Helpers.scalarHomRepresentation
        ((Units.coeHom ℂ).comp (torusTransfer hWK χ)) }
  have hline : line.character = fun k => (torusTransfer hWK χ k : ℂ) := by
    have h := CFSG.TwoRankLowerBound.Helpers.scalarHomRepresentation_character
      ((Units.coeHom ℂ).comp (torusTransfer hWK χ))
    funext k
    exact congrFun h k
  have htriv := principalFiniteComplexRepresentation_character K
  have hT : torusColumn hWK χ =
      (coinducedFiniteComplexRepresentation K (principalFiniteComplexRepresentation K)).character -
        (coinducedFiniteComplexRepresentation K line).character := by
    funext g
    rw [Pi.sub_apply, coinducedFiniteComplexRepresentation_character,
      coinducedFiniteComplexRepresentation_character, htriv, hline, torusColumn]
    have h := congrFun (CFSG.Semidihedral.Principal.CyclicInversion.inducedFunction_sub K 1
      (fun k => (torusTransfer hWK χ k : ℂ))) g
    rw [Pi.sub_apply] at h
    rw [← h]
    rfl
  obtain ⟨m₁, hm₁⟩ := exists_nat_pairing basis
    (coinducedFiniteComplexRepresentation K (principalFiniteComplexRepresentation K)) θ
  obtain ⟨m₂, hm₂⟩ := exists_nat_pairing basis (coinducedFiniteComplexRepresentation K line) θ
  refine ⟨(m₁ : ℤ) - m₂, ?_⟩
  rw [hT, characterPairing_sub_left, hm₁, hm₂]
  push_cast
  ring

omit [Fintype G] in
theorem norm_three_single {X : Type*} [Fintype X] [DecidableEq X] (o : X) (d : X → ℤ)
    (hd : ∀ x, 0 < d x) (hdo : d o = 1) (v : X → ℤ) (hvo : v o = 1)
    (hnorm : ∑ x, v x ^ 2 = 3) (hdeg : ∑ x, d x * v x = 0) :
    ∃ a b : X, a ≠ o ∧ b ≠ o ∧ a ≠ b ∧ ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      (∀ x, v x = (if x = o then 1 else 0) + δ * (if x = a then 1 else 0) -
        δ * (if x = b then 1 else 0)) ∧ d b = d a + δ := by
  let u : X → ℤ := fun x => if x = o then 0 else v x
  have huo : u o = 0 := by simp [u]
  have huv : ∀ x, x ≠ o → u x = v x := fun x hx => by simp [u, hx]
  have hvu : ∀ x, v x = (if x = o then 1 else 0) + u x := by
    intro x
    by_cases hx : x = o
    · subst hx
      simp [u, hvo]
    · simp [u, hx]
  have hunorm : ∑ x, u x * u x = 2 := by
    have h : ∑ x, v x ^ 2 = ∑ x, u x * u x + 1 := by
      rw [Fintype.sum_eq_add_sum_compl o (fun x => v x ^ 2),
        Fintype.sum_eq_add_sum_compl o (fun x => u x * u x)]
      simp only [huo, hvo, mul_zero, zero_add]
      have : ∑ x ∈ ({o}ᶜ : Finset X), v x ^ 2 = ∑ x ∈ ({o}ᶜ : Finset X), u x * u x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxo : x ≠ o := by simpa using hx
        rw [huv x hxo, sq]
      rw [this]
      ring
    linarith
  have hu1 : ∀ x, u x = -1 ∨ u x = 0 ∨ u x = 1 := by
    intro x
    have hle : u x * u x ≤ 2 := by
      rw [← hunorm]
      exact Finset.single_le_sum (f := fun y => u y * u y) (fun y _ => mul_self_nonneg (u y))
        (Finset.mem_univ x)
    exact CFSG.Semidihedral.Principal.NormThreeGram.int_cases_of_mul_self_le_two hle
  have hcard := CFSG.Semidihedral.Principal.NormThreeGram.support_card_of_norm_two u hu1 hunorm
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ x, u x ≠ 0 ↔ x = a ∨ x = b := by
    intro x
    have h := congrArg (fun s : Finset X => x ∈ s) hS
    simpa using h
  have hua : u a ≠ 0 := (hmem a).mpr (Or.inl rfl)
  have hub : u b ≠ 0 := (hmem b).mpr (Or.inr rfl)
  have hao : a ≠ o := fun h => hua (h ▸ huo)
  have hbo : b ≠ o := fun h => hub (h ▸ huo)
  have hzero : ∀ x, x ≠ a → x ≠ b → u x = 0 := by
    intro x hxa hxb
    by_contra h
    rcases (hmem x).mp h with h' | h'
    · exact hxa h'
    · exact hxb h'
  have hdeg' : 1 + d a * u a + d b * u b = 0 := by
    have h : ∑ x, d x * v x = d o + ∑ x, d x * u x := by
      simp_rw [hvu, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [h, hdo, CFSG.Semidihedral.Principal.NormThreeGram.sum_mul_of_support_pair d u hab
      (fun x hx => (hmem x).mp hx)] at hdeg
    linarith
  have hua' : u a = 1 ∨ u a = -1 := by
    rcases hu1 a with h | h | h
    · exact Or.inr h
    · exact absurd h hua
    · exact Or.inl h
  have hub' : u b = 1 ∨ u b = -1 := by
    rcases hu1 b with h | h | h
    · exact Or.inr h
    · exact absurd h hub
    · exact Or.inl h
  have hda := hd a
  have hdb := hd b
  have hsign : u b = -u a := by
    rcases hua' with h1 | h1 <;> rcases hub' with h2 | h2 <;> rw [h1, h2] at hdeg' ⊢ <;>
      first | rfl | (exfalso; linarith)
  refine ⟨a, b, hao, hbo, hab, u a, hua', fun x => ?_, ?_⟩
  · rw [hvu x]
    by_cases hxa : x = a
    · subst hxa
      simp [hao, hab]
    · by_cases hxb : x = b
      · subst hxb
        simp [hbo, Ne.symm hab, hsign]
      · simp [hxa, hxb, hzero x hxa hxb]
  · rw [hsign] at hdeg'
    rcases hua' with h1 | h1 <;> rw [h1] at hdeg' ⊢ <;> linarith

include hKH hcent hinv hKn hHK hTI in
theorem torusColumn_decomposition (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {k₀ : K}
    (hk₀ : torusTransfer hWK χ k₀ ≠ 1) (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    ∃ (ρ τ : basis.index) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧ ρ ≠ principal ∧ τ ≠ principal ∧
      ρ ≠ τ ∧
      (∀ g, torusColumn hWK χ g = 1 + δ * (basis.representation ρ).character g -
        δ * (basis.representation τ).character g) ∧
      (Module.finrank ℂ (basis.representation τ).vector : ℤ) =
        Module.finrank ℂ (basis.representation ρ).vector + δ ∧
      (∀ g, starRingEnd ℂ ((basis.representation ρ).character g) =
        (basis.representation ρ).character g) ∧
      (∀ g, starRingEnd ℂ ((basis.representation τ).character g) =
        (basis.representation τ).character g) := by
  set T := torusColumn hWK χ with hTdef
  have hclass : ∀ x c : G, T (c * x * c⁻¹) = T x := fun x c =>
    inducedFunction_conjugate K _ x c
  choose c hc using fun θ => torusColumn_pairing_int hWK χ basis θ
  have hexp : ∀ g, T g = ∑ θ, (c θ : ℂ) * (basis.representation θ).character g := by
    intro g
    rw [finiteIrreducibleCharacterBasis_reconstruction basis T hclass g]
    exact Finset.sum_congr rfl fun θ _ => by rw [hc θ]
  have hco : c principal = 1 := by
    have h := hc principal
    rw [hprincipal, torusColumn_principal hWK χ hk₀] at h
    exact_mod_cast h.symm
  have hnorm : ∑ θ, c θ ^ 2 = 3 := by
    have h := CFSG.Semidihedral.Principal.CyclicInversion.characterPairing_eq_sum_coefficients
      basis T T hclass hclass c c hc hc
    rw [torusColumn_norm hWK hKH hcent hinv hKn hHK hTI χ hχ hk₀] at h
    have h' : ((∑ θ, c θ * c θ : ℤ) : ℂ) = ((3 : ℤ) : ℂ) := by rw [← h]; norm_num
    simp_rw [sq]
    exact_mod_cast h'
  let d : basis.index → ℤ := fun θ => Module.finrank ℂ (basis.representation θ).vector
  have hdpos : ∀ θ, 0 < d θ := fun θ => by
    have h := irreducible_character_degree_ne_zero _ (basis.irreducible θ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have : Module.finrank ℂ (basis.representation θ).vector ≠ 0 := by exact_mod_cast h
    simp only [d]
    omega
  have hdo : d principal = 1 := by
    have h := congrFun hprincipal 1
    rw [FiniteComplexRepresentation.character, Representation.char_one, Pi.one_apply] at h
    simp only [d]
    exact_mod_cast h
  have hdeg : ∑ θ, d θ * c θ = 0 := by
    have h := hexp 1
    rw [hTdef, torusColumn_one hWK hKH hcent hinv hKn hHK hTI χ] at h
    have h' : ((∑ θ, d θ * c θ : ℤ) : ℂ) = 0 := by
      push_cast
      rw [h]
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [d, FiniteComplexRepresentation.character, Representation.char_one]
      push_cast
      ring
    exact_mod_cast h'
  obtain ⟨ρ, τ, hρo, hτo, hρτ, δ, hδ, hval, hdτ⟩ :=
    norm_three_single principal d hdpos hdo c hco hnorm hdeg
  have hδne : δ ≠ 0 := by rcases hδ with h | h <;> omega
  have hcρ : c ρ = δ := by rw [hval]; simp [hρo, hρτ]
  have hcτ : c τ = -δ := by rw [hval]; simp [hτo, Ne.symm hρτ]
  have hsupp : ∀ θ, c θ ≠ 0 → θ = principal ∨ θ = ρ ∨ θ = τ := by
    intro θ hθ
    by_contra hcon
    push Not at hcon
    apply hθ
    rw [hval]
    simp [hcon.1, hcon.2.1, hcon.2.2]
  have hTval : ∀ g, T g = 1 + δ * (basis.representation ρ).character g -
      δ * (basis.representation τ).character g := by
    intro g
    rw [hexp g]
    simp_rw [hval]
    push_cast
    simp only [add_mul, sub_mul, ite_mul, one_mul, zero_mul, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, hprincipal, Pi.one_apply]
  have hTreal := torusColumn_star hWK hKH hcent hinv hKn hHK hTI χ
  have hconj : ∀ θ θ', (∀ g, (basis.representation θ').character g =
      starRingEnd ℂ ((basis.representation θ).character g)) → c θ' = c θ := by
    intro θ θ' hθ'
    have h1 : characterPairing T (basis.representation θ').character =
        starRingEnd ℂ (characterPairing T (basis.representation θ).character) := by
      unfold characterPairing
      rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, hTreal, hθ']
    rw [hc θ', hc θ, map_intCast] at h1
    exact_mod_cast h1
  have hreal : ∀ θ, θ ≠ principal → c θ ≠ 0 →
      (∀ θ', c θ' = c θ → θ' = principal ∨ θ' = θ) →
      ∀ g, starRingEnd ℂ ((basis.representation θ).character g) =
        (basis.representation θ).character g := by
    intro θ hθo hθ0 huniq g
    obtain ⟨θ', hθ'⟩ := CFSG.Semidihedral.Principal.CyclicInversion.exists_conj_label basis θ
    have hc' := hconj θ θ' hθ'
    rcases huniq θ' hc' with h | h
    · exfalso
      apply hθo
      apply basis.distinct
      change (basis.representation θ).character = (basis.representation principal).character
      funext x
      have h2 := hθ' x
      rw [h, hprincipal, Pi.one_apply] at h2
      rw [hprincipal, Pi.one_apply]
      have h3 := congrArg (starRingEnd ℂ) h2
      rw [map_one, Complex.conj_conj] at h3
      exact h3.symm
    · rw [← hθ' g, h]
  refine ⟨ρ, τ, δ, hδ, hρo, hτo, hρτ, hTval, hdτ, ?_, ?_⟩
  · refine hreal ρ hρo (by rw [hcρ]; exact hδne) fun θ' hθ' => ?_
    rcases hsupp θ' (by rw [hθ', hcρ]; exact hδne) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h, hcτ, hcρ] at hθ'
      rcases hδ with h' | h' <;> omega
  · refine hreal τ hτo (by rw [hcτ]; exact neg_ne_zero.mpr hδne) fun θ' hθ' => ?_
    rcases hsupp θ' (by rw [hθ', hcτ]; exact neg_ne_zero.mpr hδne) with h | h | h
    · exact Or.inl h
    · exfalso
      rw [h, hcρ, hcτ] at hθ'
      rcases hδ with h' | h' <;> omega
    · exact Or.inr h

end TenColumn

end CFSG.BrauerLinearThree
