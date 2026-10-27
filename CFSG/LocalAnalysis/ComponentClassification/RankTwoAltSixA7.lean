module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixGW

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

theorem exists_perm_castLE_of_fix {m n : ℕ} (h : m ≤ n) {π : Perm (Fin n)}
    (hπ : ∀ i : Fin n, m ≤ (i : ℕ) → π i = i) :
    ∃ π' : Perm (Fin m), viaEmbeddingHom (Fin.castLEEmb h) π' = π := by
  have hlt : ∀ σ : Perm (Fin n), (∀ i : Fin n, m ≤ (i : ℕ) → σ i = i) →
      ∀ i : Fin n, (i : ℕ) < m → (σ i : ℕ) < m := by
    intro σ hσ i hi
    by_contra hge
    push Not at hge
    have := hσ (σ i) hge
    have hii : σ i = i := σ.injective this
    rw [hii] at hge
    omega
  have hπinv : ∀ i : Fin n, m ≤ (i : ℕ) → π⁻¹ i = i := fun i hi =>
    (Perm.inv_eq_iff_eq).mpr (hπ i hi).symm
  let f : Fin m → Fin m := fun j => ⟨π (Fin.castLEEmb h j), hlt π hπ _ (by simp)⟩
  let g : Fin m → Fin m := fun j => ⟨π⁻¹ (Fin.castLEEmb h j), hlt π⁻¹ hπinv _ (by simp)⟩
  have hemb : ∀ j : Fin m, Fin.castLEEmb h (f j) = π (Fin.castLEEmb h j) := fun j => Fin.ext (by
    simp [f])
  have hemb' : ∀ j : Fin m, Fin.castLEEmb h (g j) = π⁻¹ (Fin.castLEEmb h j) := fun j =>
    Fin.ext (by simp [g])
  let π' : Perm (Fin m) :=
    { toFun := f
      invFun := g
      left_inv := fun j => (Fin.castLEEmb h).injective (by rw [hemb', hemb]; simp)
      right_inv := fun j => (Fin.castLEEmb h).injective (by rw [hemb, hemb']; simp) }
  refine ⟨π', Equiv.ext fun i => ?_⟩
  by_cases hi : (i : ℕ) < m
  · have hi' : Fin.castLEEmb h ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← hi', viaEmbeddingHom_apply_image]
    exact hemb ⟨i, hi⟩
  · have hnot : i ∉ Set.range (Fin.castLEEmb h) := by
      rintro ⟨j, rfl⟩
      exact hi (by simp)
    rw [viaEmbeddingHom_apply_of_notMem _ _ hnot, hπ i (by omega)]

theorem isThreeCycle_of_fixed_six {x : Perm (Fin 6)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) {j : Fin 6}
    (hj : x j = j) : x.IsThreeCycle := by
  have hord : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  obtain ⟨k, hk⟩ := cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hk
  have hsum := sum_cycleType x
  have hsub : x.support ⊆ Finset.univ.erase j := fun y hy =>
    Finset.mem_erase.mpr ⟨fun h => (mem_support.mp hy) (h ▸ hj), Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hle
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk0 : k = 0 := by omega
  rw [IsThreeCycle, hk, hk0]
  rfl

@[expose] noncomputable def ι67 : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  ((viaEmbeddingHom (Fin.castLEEmb (by norm_num : 6 ≤ 7))).comp
    (alternatingGroup (Fin 6)).subtype).codRestrict (alternatingGroup (Fin 7)) fun σ => by
      rw [MonoidHom.comp_apply, mem_alternatingGroup, sign_viaEmbeddingHom]
      exact σ.2

theorem coe_ι67 (σ : alternatingGroup (Fin 6)) :
    ((ι67 σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      viaEmbeddingHom (Fin.castLEEmb (by norm_num : 6 ≤ 7)) (σ : Perm (Fin 6)) := rfl

theorem ι67_injective : Function.Injective ι67 := fun _ _ h =>
  Subtype.ext (viaEmbeddingHom_injective _ (congrArg Subtype.val h :))

theorem ι67_apply_six (σ : alternatingGroup (Fin 6)) : ((ι67 σ : alternatingGroup (Fin 7)) :
    Perm (Fin 7)) 6 = 6 := by
  rw [coe_ι67, viaEmbeddingHom_apply_of_notMem]
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  simp at this
  omega

theorem mem_range_ι67 {x : alternatingGroup (Fin 7)} (hx : (x : Perm (Fin 7)) 6 = 6) :
    x ∈ ι67.range := by
  obtain ⟨π', hπ'⟩ := exists_perm_castLE_of_fix (by norm_num : 6 ≤ 7) (π := (x : Perm (Fin 7)))
    (fun i hi => by
      have : i = 6 := Fin.ext (by have := i.isLt; omega)
      rw [this, hx])
  have hs : π' ∈ alternatingGroup (Fin 6) := by
    rw [mem_alternatingGroup, ← sign_viaEmbeddingHom (Fin.castLEEmb (by norm_num : 6 ≤ 7)), hπ']
    exact x.2
  exact ⟨⟨π', hs⟩, Subtype.ext (by rw [coe_ι67]; exact hπ')⟩

@[expose] def t012 : Perm (Fin 7) := swap 0 1 * swap 1 2

@[expose] def t013 : Perm (Fin 7) := swap 0 1 * swap 1 3

@[expose] def t450 : Perm (Fin 7) := swap 4 5 * swap 5 0

@[expose] def t456 : Perm (Fin 7) := swap 4 5 * swap 5 6

theorem ι67_a6c012 : ((ι67 a6c012 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = t012 := by
  rw [coe_ι67]
  show viaEmbeddingHom _ (swap 0 1 * swap 1 2) = _
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem ι67_a6c013 : ((ι67 a6c013 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = t013 := by
  rw [coe_ι67]
  show viaEmbeddingHom _ (swap 0 1 * swap 1 3) = _
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem ι67_e450 : ((ι67 e450 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = t450 := by
  rw [coe_ι67]
  show viaEmbeddingHom _ (swap 4 5 * swap 5 0) = _
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem fix_of_commute_t012_t013 {X : Perm (Fin 7)} (h1 : X * t012 = t012 * X)
    (h2 : X * t013 = t013 * X) : X 0 = 0 ∧ X 1 = 1 ∧ X 2 = 2 ∧ X 3 = 3 := by
  have hp : ∀ c : Perm (Fin 7), X * c = c * X → ∀ y, X (c y) = c (X y) := fun c hc y => by
    have := congrArg (fun f : Perm (Fin 7) => f y) hc
    simpa only [Perm.mul_apply] using this
  have e1 : X 1 = t012 (X 0) := by rw [← hp t012 h1]; rfl
  have e2 : X 1 = t013 (X 0) := by rw [← hp t013 h2]; rfl
  have key : ∀ y : Fin 7, t012 y = t013 y → y = 0 ∨ 4 ≤ (y : ℕ) := by decide
  have hfix : ∀ y : Fin 7, 4 ≤ (y : ℕ) → t012 y = y := by decide
  rcases key (X 0) (e1.symm.trans e2) with h0 | h0
  · have hX1 : X 1 = 1 := by rw [e1, h0]; rfl
    have hX2 : X 2 = 2 := by
      rw [show (2 : Fin 7) = t012 1 by decide, hp t012 h1, hX1]
    have hX3 : X 3 = 3 := by
      rw [show (3 : Fin 7) = t013 1 by decide, hp t013 h2, hX1]
    exact ⟨h0, hX1, hX2, hX3⟩
  · exfalso
    have : X 1 = X 0 := by rw [e1, hfix _ h0]
    exact absurd (X.injective this) (by decide)

theorem eq_t456_of_fix {X : Perm (Fin 7)} (hfix : X 0 = 0 ∧ X 1 = 1 ∧ X 2 = 2 ∧ X 3 = 3)
    (h3 : X ^ 3 = 1) (h1 : X ≠ 1) : X = t456 ∨ X = t456⁻¹ := by
  obtain ⟨f0, f1, f2, f3⟩ := hfix
  set κ : Perm (Fin 7) := swap 0 4 * swap 1 5 * swap 2 6 with hκ
  have hκi : κ⁻¹ = κ := by rw [hκ]; decide
  set X' := κ * X * κ⁻¹ with hX'
  have hX'fix : ∀ i : Fin 7, 4 ≤ (i : ℕ) → X' i = i := by
    intro i hi
    have h7 := i.isLt
    rcases (by omega : (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6) with h | h | h
    · rw [show i = 4 from Fin.ext h, hX', Perm.mul_apply, Perm.mul_apply, hκi,
        show κ 4 = 0 by rw [hκ]; decide, f0]
      rw [hκ]; decide
    · rw [show i = 5 from Fin.ext h, hX', Perm.mul_apply, Perm.mul_apply, hκi,
        show κ 5 = 1 by rw [hκ]; decide, f1]
      rw [hκ]; decide
    · rw [show i = 6 from Fin.ext h, hX', Perm.mul_apply, Perm.mul_apply, hκi,
        show κ 6 = 2 by rw [hκ]; decide, f2]
      rw [hκ]; decide
  obtain ⟨π', hπ'⟩ := exists_perm_four_of_fix (by norm_num : 4 ≤ 7) hX'fix
  have hπ'3 : π' 3 = 3 := by
    have e : X' 3 = 3 := by
      rw [hX', Perm.mul_apply, Perm.mul_apply, hκi, show κ 3 = 3 by rw [hκ]; decide, f3]
      rw [hκ]; decide
    have e2 := viaEmbeddingHom_apply_image (fourEmb (by norm_num : 4 ≤ 7)) π' 3
    rw [hπ', show fourEmb (by norm_num : 4 ≤ 7) 3 = (3 : Fin 7) from rfl, e] at e2
    exact (fourEmb (by norm_num : 4 ≤ 7)).injective e2.symm
  have hcube : π' ^ 3 = 1 := by
    apply viaEmbeddingHom_injective (fourEmb (by norm_num : 4 ≤ 7))
    rw [map_pow, hπ', hX', show (κ * X * κ⁻¹) ^ 3 = κ * X ^ 3 * κ⁻¹ from conj_pow, h3, mul_one,
      mul_inv_cancel, map_one]
  have hne : π' ≠ 1 := by
    rintro rfl
    apply h1
    have : X' = 1 := by rw [← hπ', map_one]
    calc X = κ⁻¹ * X' * κ := by rw [hX']; group
      _ = 1 := by rw [this]; group
  have key : ∀ π : Perm (Fin 4), π 3 = 3 → π ^ 3 = 1 → π ≠ 1 →
      π = swap 0 1 * swap 1 2 ∨ π = (swap 0 1 * swap 1 2)⁻¹ := by decide
  have hback : X = κ⁻¹ * viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) π' * κ := by
    rw [hπ', hX']
    group
  have hv : viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) (swap 0 1 * swap 1 2) =
      swap 0 1 * swap 1 2 := by
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl
  have hk1 : κ * (swap 0 1 * swap 1 2) * κ = t456 := by rw [hκ]; decide
  have hk2 : κ * (swap 0 1 * swap 1 2)⁻¹ * κ = t456⁻¹ := by rw [hκ]; decide
  rcases key π' hπ'3 hcube hne with h | h
  · left
    rw [hback, h, hv, hκi, hk1]
  · right
    rw [hback, h, map_inv, hv, hκi, hk2]

theorem t456_t450_sq : (t456 * t450) ^ 2 = 1 := by decide

theorem t456_t450_inv_sq : (t456⁻¹ * t450⁻¹) ^ 2 = 1 := by decide

theorem fix_of_commute_six {X : Perm (Fin 6)} (h1 : X * (a6c012 : Perm (Fin 6)) = a6c012 * X)
    (h2 : X * (a6c013 : Perm (Fin 6)) = a6c013 * X) : X 0 = 0 ∧ X 1 = 1 ∧ X 2 = 2 ∧ X 3 = 3 := by
  have hp : ∀ c : Perm (Fin 6), X * c = c * X → ∀ y, X (c y) = c (X y) := fun c hc y => by
    have := congrArg (fun f : Perm (Fin 6) => f y) hc
    simpa only [Perm.mul_apply] using this
  have e1 : X 1 = (a6c012 : Perm (Fin 6)) (X 0) := by rw [← hp _ h1]; rfl
  have e2 : X 1 = (a6c013 : Perm (Fin 6)) (X 0) := by rw [← hp _ h2]; rfl
  have key : ∀ y : Fin 6, (a6c012 : Perm (Fin 6)) y = (a6c013 : Perm (Fin 6)) y →
      y = 0 ∨ 4 ≤ (y : ℕ) := by decide
  have hfix : ∀ y : Fin 6, 4 ≤ (y : ℕ) → (a6c012 : Perm (Fin 6)) y = y := by decide
  rcases key (X 0) (e1.symm.trans e2) with h0 | h0
  · have hX1 : X 1 = 1 := by rw [e1, h0]; rfl
    have hX2 : X 2 = 2 := by
      rw [show (2 : Fin 6) = (a6c012 : Perm (Fin 6)) 1 by decide, hp _ h1, hX1]
    have hX3 : X 3 = 3 := by
      rw [show (3 : Fin 6) = (a6c013 : Perm (Fin 6)) 1 by decide, hp _ h2, hX1]
    exact ⟨h0, hX1, hX2, hX3⟩
  · exfalso
    have : X 1 = X 0 := by rw [e1, hfix _ h0]
    exact absurd (X.injective this) (by decide)

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

namespace Six

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}

@[expose] noncomputable def toQ (hco : AltCoords 6 A B ψA ψB) :
    B →* H ψA ⧸ pPrimeCore 2 (H ψA) :=
  (QuotientGroup.mk' (pPrimeCore 2 (H ψA))).comp (inclusion (B_le_H hco))

theorem toQ_apply (hco : AltCoords 6 A B ψA ψB) (b : B) :
    toQ hco b = ((⟨b, B_le_H hco b.2⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) := rfl

theorem toQ_injective [Finite G] (hco : AltCoords 6 A B ψA ψB) : Function.Injective (toQ hco) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : Nontrivial B := ⟨⟨1, ⟨y0 ψB, y0_mem⟩, fun h => by
    have h1 : ψB.symm e4523 = 1 := Subtype.ext (congrArg Subtype.val h).symm
    have h2 := congrArg Subtype.val (ψB.symm.injective (h1.trans (map_one _).symm))
    exact absurd h2 (by decide)⟩⟩
  have hsimp : IsSimpleGroup B :=
    IsSimpleGroup.isSimpleGroup_of_surjective ψB.symm.toMonoidHom ψB.symm.surjective
  rcases hsimp.eq_bot_or_eq_top_of_normal (toQ hco).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    have hy : (⟨y0 ψB, y0_mem⟩ : B) ∈ (toQ hco).ker := h ▸ mem_top _
    rw [MonoidHom.mem_ker, toQ_apply, QuotientGroup.eq_one_iff] at hy
    have h1 := eq_one_of_mem_pPrimeCore_of_mul_self (K := H ψA)
      (h := ⟨y0 ψB, B_le_H hco y0_mem⟩) (Subtype.ext y0_mul_self) hy
    have h2' : y0 ψB = 1 := congrArg Subtype.val h1
    have h2 : ψB.symm e4523 = 1 := Subtype.ext h2'
    have h3 := congrArg Subtype.val (ψB.symm.injective (h2.trans (map_one _).symm))
    exact absurd h3 (by decide)

theorem commute_c1bar (hco : AltCoords 6 A B ψA ψB) {σ : alternatingGroup (Fin 6)}
    (hσ : σ ∈ rootAlt 6) :
    ((⟨c1 ψA, c1_mem_H⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) * toQ hco (ψB.symm σ) =
      toQ hco (ψB.symm σ) * ((⟨c1 ψA, c1_mem_H⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) := by
  have hy : ((ψB.symm σ : B) : G) ∈ centralizer (A : Set G) :=
    hco.2.2.2.1 ⟨ψB.symm σ, ⟨σ, hσ, rfl⟩, rfl⟩
  rw [toQ_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext ((mem_centralizer_iff.mp hy) _ (c1_mem (ψA := ψA)))

theorem exists_label
    [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G)) :
    ∃ θ : (H ψA ⧸ pPrimeCore 2 (H ψA)) ≃* alternatingGroup (Fin 7),
      ∀ σ : alternatingGroup (Fin 6), θ (toQ hco (ψB.symm σ)) = ι67 σ := by
  obtain ⟨θ⟩ := nonempty_quot_equiv_alt7 hco hN ht1A
  set j := (toQ hco).comp ψB.symm.toMonoidHom with hjdef
  have hj : Function.Injective j := (toQ_injective hco).comp ψB.symm.injective
  set f := (alternatingGroup (Fin 7)).subtype.comp (θ.toMonoidHom.comp j) with hfdef
  have hfi : Function.Injective f := Subtype.coe_injective.comp (θ.injective.comp hj)
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hFcard : Nat.card f.range = 360 := by
    rw [← card_alt6]
    exact (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).symm
  have : Nontrivial f.range := Finite.one_lt_card_iff_nontrivial.mp (by rw [hFcard]; norm_num)
  have : IsSimpleGroup f.range :=
    IsSimpleGroup.isSimpleGroup_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨p, hp⟩ := exists_fixed_of_card_eq_360 (Fintype.card_fin 7) f.range hFcard
  set θ₁ := θ.trans (conjPerm 7 (swap p 6)) with hθ₁def
  have hθ₁ : ∀ q, ((θ₁ q : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      swap p 6 * θ q * (swap p 6)⁻¹ := fun q => by
    rw [hθ₁def, MulEquiv.trans_apply, conjPerm_apply]
  have hfix6 : ∀ σ, ((θ₁ (j σ) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 6 := by
    intro σ
    have hpσ : ((θ (j σ) : alternatingGroup (Fin 7)) : Perm (Fin 7)) p = p := hp _ ⟨σ, rfl⟩
    rw [hθ₁, Perm.mul_apply, Perm.mul_apply, swap_inv, swap_apply_right, hpσ, swap_apply_left]
  set f₁ := θ₁.toMonoidHom.comp j with hf₁def
  have hf₁ : Function.Injective f₁ := θ₁.injective.comp hj
  have hrange : f₁.range = ι67.range := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨σ, rfl⟩
      exact mem_range_ι67 (hfix6 σ)
    · rw [← Nat.card_congr (MonoidHom.ofInjective ι67_injective).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective hf₁).toEquiv]
  set ε : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) :=
    (MonoidHom.ofInjective hf₁).trans ((MulEquiv.subgroupCongr hrange).trans
      (MonoidHom.ofInjective ι67_injective).symm) with hεdef
  have hε : ∀ σ, ι67 (ε σ) = f₁ σ := by
    intro σ
    have h1 := MonoidHom.ofInjective_apply ι67_injective (x := ε σ)
    rw [← h1, hεdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hc1 := c1_not_mem_core hco hN ht1A
  set cb := ((⟨c1 ψA, c1_mem_H⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) with hcb
  have hcb1 : cb ≠ 1 := fun h => hc1 ((QuotientGroup.eq_one_iff _).mp h)
  have hcomm : ∀ σ ∈ rootAlt 6, cb * j σ = j σ * cb := fun σ hσ => commute_c1bar hco hσ
  set X := ((θ₁ cb : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hX
  have hXt : ∀ σ ∈ rootAlt 6,
      X * ((f₁ σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        ((f₁ σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) * X := by
    intro σ hσ
    have h1 := congrArg (fun q => ((θ₁ q : alternatingGroup (Fin 7)) : Perm (Fin 7)))
      (hcomm σ hσ)
    simp only [map_mul, Subgroup.coe_mul] at h1
    exact h1
  have hX6 : X 6 ≠ 6 := by
    intro h6
    have hmem : θ₁ cb ∈ f₁.range := hrange ▸ mem_range_ι67 h6
    obtain ⟨σ, hσ⟩ := hmem
    have hjσ : j σ = cb := θ₁.injective hσ
    have hc : ∀ τ ∈ rootAlt 6, σ * τ = τ * σ := by
      intro τ hτ
      apply hj
      rw [map_mul, map_mul, hjσ]
      exact hcomm τ hτ
    obtain ⟨f0, f1, f2, f3⟩ := fix_of_commute_six (congrArg Subtype.val (hc _ a6c012_mem_rootAlt))
      (congrArg Subtype.val (hc _ a6c013_mem_rootAlt))
    have hσ1 : σ = 1 := Subtype.ext (eq_one_of_fix_four (mem_alternatingGroup.mp σ.2) f0 f1 f2 f3)
    rw [hσ1, map_one] at hjσ
    exact hcb1 hjσ.symm
  have hfp : ∃ i : Fin 6, ((ε a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)) i = i := by
    by_contra hno
    push Not at hno
    have ht := congrArg (fun g : Perm (Fin 7) => g 6) (hXt a6c012 a6c012_mem_rootAlt)
    simp only [Perm.mul_apply] at ht
    rw [← hε, ι67_apply_six] at ht
    have hlt : (X 6 : ℕ) < 6 := by
      have h7 := (X 6).isLt
      have : (X 6 : ℕ) ≠ 6 := fun h => hX6 (Fin.ext h)
      omega
    have hi : Fin.castLEEmb (by norm_num : 6 ≤ 7) ⟨X 6, hlt⟩ = X 6 := Fin.ext rfl
    rw [coe_ι67, ← hi, viaEmbeddingHom_apply_image] at ht
    exact hno _ ((Fin.castLEEmb _).injective ht).symm
  obtain ⟨i0, hi0⟩ := hfp
  have h3c : ((ε a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)).IsThreeCycle := by
    refine isThreeCycle_of_fixed_six ?_ ?_ hi0
    · rw [← Subgroup.coe_pow, ← map_pow, show a6c012 ^ 3 = 1 from Subtype.ext (by decide),
        map_one, Subgroup.coe_one]
    · intro h
      have h1 : ε a6c012 = ε 1 := by rw [map_one]; exact Subtype.ext h
      have h2 := congrArg Subtype.val (ε.injective h1)
      exact absurd h2 (by decide)
  obtain ⟨π, hπ⟩ := exists_perm_of_isThreeCycle ε h3c
  set πe := viaEmbeddingHom (Fin.castLEEmb (by norm_num : 6 ≤ 7)) π with hπe
  refine ⟨θ₁.trans (conjPerm 7 πe⁻¹), fun σ => Subtype.ext ?_⟩
  rw [MulEquiv.trans_apply, conjPerm_apply]
  change πe⁻¹ * ((f₁ σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) * πe⁻¹⁻¹ =
    ((ι67 σ : alternatingGroup (Fin 7)) : Perm (Fin 7))
  rw [← hε, coe_ι67, coe_ι67, hπ σ, map_mul, map_mul, map_inv, ← hπe]
  group

end Six

end CFSG.ComponentClassification.RankTwoAlt
