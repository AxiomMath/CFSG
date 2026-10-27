module

public import CFSG.GH74.GLS.IVK.Lifted.FCent
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.IVK.Lifted (isQuasisimple_sl2' nonscalar_of_not_mem_center
  comm_of_commute_matrix sq_eq_one_of_mem_center_sl2 sylow_exists_noncomm)
open CFSG.LocalAnalysis.ComponentInitial (sl2Upper sl2Lower sl2Upper_add sl2Lower_add sl2Upper_zero
  sl2Lower_zero sl2_closure_upper_lower)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped Pointwise

theorem kabs_sl2Upper_pow {F : Type} [Field F] (c : F) (m : ℕ) :
    sl2Upper F c ^ m = sl2Upper F (m • c) := by
  induction m with
  | zero => simp [sl2Upper_zero]
  | succ m ih => rw [pow_succ, ih, succ_nsmul, sl2Upper_add]

theorem kabs_sl2Lower_pow {F : Type} [Field F] (c : F) (m : ℕ) :
    sl2Lower F c ^ m = sl2Lower F (m • c) := by
  induction m with
  | zero => simp [sl2Lower_zero]
  | succ m ih => rw [pow_succ, ih, succ_nsmul, sl2Lower_add]

theorem hasSL2_le_oResidual {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (e : ↥A ≃* StatedSL 2 F) : A ≤ oResidual 2 Y := by
  intro a ha
  let φ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥A :=
    (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F →* Y := A.subtype.comp φ.toMonoidHom
  have hgen : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g ^ Nat.card F = 1 →
      ψ g ∈ oResidual 2 Y := by
    intro g hg
    refine Subgroup.subset_closure ?_
    have h1 : orderOf (ψ g) ∣ Nat.card F :=
      (orderOf_map_dvd ψ g).trans (orderOf_dvd_of_pow_eq_one hg)
    exact Nat.coprime_two_right.2 (hodd.of_dvd_nat h1)
  have hle : Subgroup.closure (Set.range (sl2Upper F) ∪ Set.range (sl2Lower F)) ≤
      (oResidual 2 Y).comap ψ := by
    rw [Subgroup.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · apply hgen
      rw [kabs_sl2Upper_pow, card_nsmul_eq_zero', sl2Upper_zero]
    · apply hgen
      rw [kabs_sl2Lower_pow, card_nsmul_eq_zero', sl2Lower_zero]
  have htop : φ.symm ⟨a, ha⟩ ∈ (oResidual 2 Y).comap ψ :=
    hle (by rw [sl2_closure_upper_lower]; exact Subgroup.mem_top _)
  have hψ : ψ (φ.symm ⟨a, ha⟩) = a := by simp [ψ]
  rw [← hψ]
  exact htop

theorem card_sup_mul_two {Y : Type} [Group Y] [Finite Y] {K₁ K₂ : Subgroup Y}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2) :
    Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card ↥K₁ * Nat.card ↥K₂ := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hc).1
  rwa [hinf] at h

theorem kabs_two_ne_zero {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have := Fintype.ofFinite F
  refine Ring.two_ne_zero fun h => ?_
  have h1 := (FiniteField.even_card_iff_char_two (F := F)).1 h
  rw [← Nat.card_eq_fintype_card] at h1
  have := Nat.odd_iff.1 hodd
  omega

theorem kabs_eq_of_orderOf_two {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (ε : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {u v : K}
    (hu : orderOf u = 2) (hv : orderOf v = 2) : u = v := by
  have hsq : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F, orderOf s = 2 → s ^ 2 = 1 ∧ s ≠ 1 := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have := pow_orderOf_eq_one s
      rwa [hs] at this
    · rintro rfl
      simp at hs
  have hu' : orderOf (ε u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hv' : orderOf (ε v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨hu1, hu2⟩ := hsq _ hu'
  obtain ⟨hv1, hv2⟩ := hsq _ hv'
  have h2 := kabs_two_ne_zero hodd
  apply ε.injective
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ hu1 hu2,
      CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ hv1 hv2]

theorem kabs_center_cases {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (ε : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {t : K}
    (ht : orderOf t = 2) {k : K} (hk : k ∈ Subgroup.center K) : k = 1 ∨ k = t := by
  have hεk : ε k ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff] at hk ⊢
    intro g
    apply ε.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact hk (ε.symm g)
  have hsq : k * k = 1 := by
    apply ε.injective
    rw [map_mul, map_one]
    exact sq_eq_one_of_mem_center_sl2 hεk
  have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact Or.inl (orderOf_eq_one_iff.1 h)
  · exact Or.inr (kabs_eq_of_orderOf_two hodd ε h ht)

theorem kabs_mem_center_of_noncomm {K : Type} [Group K] {F : Type} [Field F]
    (ε : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {a b : K} (hab : a * b ≠ b * a) {k : K}
    (ha : a * k = k * a) (hb : b * k = k * b) : k ∈ Subgroup.center K := by
  by_contra hk
  have hεk : ε k ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro h
    apply hk
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    apply ε.injective
    rw [map_mul, map_mul]
    exact h (ε g)
  have hG := nonscalar_of_not_mem_center (ε k) hεk
  have hcomm : ∀ x : K, x * k = k * x → ((ε x : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) * (ε k : Matrix (Fin 2) (Fin 2) F) =
      (ε k : Matrix (Fin 2) (Fin 2) F) * (ε x : Matrix (Fin 2) (Fin 2) F) := by
    intro x hx
    have := congrArg (fun z : K => ((ε z : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) hx
    simpa only [map_mul, Matrix.SpecialLinearGroup.coe_mul] using this
  apply hab
  apply ε.injective
  rw [map_mul, map_mul]
  exact comm_of_commute_matrix _ hG _ _ (hcomm a ha) (hcomm b hb)

theorem inv_central_unique {Y : Type} [Group Y] [Finite Y]
    {K₁ K₂ R : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂] {n : ℕ}
    (hodd₁ : Odd (Nat.card F₁)) (h5 : 5 ≤ Nat.card F₁) (hodd₂ : Odd (Nat.card F₂))
    (hv₁ : (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = n + 1)
    (hv₂ : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = n + 1)
    (e₁ : ↥K₁ ≃* StatedSL 2 F₁) (e₂ : ↥K₂ ≃* StatedSL 2 F₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2)
    (hRK : R ≤ K₁ ⊔ K₂) (hRcard : Nat.card ↥R = 2 ^ (2 * n + 1)) :
    ∀ u ∈ K₁ ⊔ K₂, orderOf u = 2 → (∀ r ∈ R, r * u = u * r) →
    ∀ u' ∈ K₁ ⊔ K₂, orderOf u' = 2 → (∀ r ∈ R, r * u' = u' * r) → u = u' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ε₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    e₁.trans (specialLinearGroupEquivStatedSL 2 F₁).symm
  let ε₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂ :=
    e₂.trans (specialLinearGroupEquivStatedSL 2 F₂).symm
  have hK₁card : Nat.card ↥K₁ = Nat.card ↥(StatedSL 2 F₁) := Nat.card_congr e₁.toEquiv
  have hK₂card : Nat.card ↥K₂ = Nat.card ↥(StatedSL 2 F₂) := Nat.card_congr e₂.toEquiv
  have hmul := card_sup_mul_two hc hinf
  have hfac : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 = 2 * n + 1 := by
    have h : (Nat.card ↥(K₁ ⊔ K₂) * 2).factorization 2 =
        (Nat.card ↥K₁ * Nat.card ↥K₂).factorization 2 := by rw [hmul]
    rw [Nat.factorization_mul Nat.card_pos.ne' two_ne_zero,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', hK₁card, hK₂card] at h
    simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, hv₁, hv₂] at h
    omega
  have hSyl : IsSylowOf 2 R (K₁ ⊔ K₂) := isSylowOf_of_card hRK (by rw [hRcard, hfac])
  have hnorm : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set Y) := by
    refine sup_le Subgroup.le_normalizer (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hc a ha b hb
  obtain ⟨Q, hQ⟩ := hSyl.inf_of_le_normalizer le_sup_left hnorm
  have hq : CFSG.IsQuasisimple ↥K₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ε₁.symm (isQuasisimple_sl2' (by omega))
  have hno : ∀ u v : ↥K₁, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v :=
    fun u v hu hv _ => kabs_eq_of_orderOf_two hodd₁ ε₁ hu hv
  obtain ⟨a, ha, b, hb, hab⟩ := sylow_exists_noncomm hq hno Q
  have hmemR : ∀ x : ↥K₁, x ∈ (Q : Subgroup ↥K₁) → (x : Y) ∈ R := fun x hx => by
    have := Subgroup.mem_map_of_mem K₁.subtype hx
    rw [hQ] at this
    exact this.1
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(K₁ ⊓ K₂)) 2 (by rw [hinf])
  let t : ↥K₁ := ⟨(t₀ : Y), t₀.2.1⟩
  have ht : orderOf t = 2 := by
    rw [orderOf_mk, Subgroup.orderOf_coe]
    exact ht₀
  have hmem : ∀ u ∈ K₁ ⊔ K₂, (∀ r ∈ R, r * u = u * r) → u ∈ K₂ := by
    intro u hu hur
    obtain ⟨x, hx, y, hy, hxy⟩ : u ∈ (K₁ : Set Y) * (K₂ : Set Y) := by
      rw [← (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hc).2]
      exact hu
    have hxy' : x * y = u := hxy
    subst hxy'
    have hcomm : ∀ z : ↥K₁, (z : Y) ∈ R → z * ⟨x, hx⟩ = ⟨x, hx⟩ * z := by
      intro z hz
      apply Subtype.ext
      have h1 := hur _ hz
      have h2 := hc z z.2 y hy
      show (z : Y) * x = x * z
      have h3 : (z : Y) * x * y = x * z * y := by
        calc (z : Y) * x * y = (z : Y) * (x * y) := by rw [mul_assoc]
          _ = (x * y) * z := h1
          _ = x * (y * z) := by rw [mul_assoc]
          _ = x * (z * y) := by rw [← h2]
          _ = x * z * y := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hcen : (⟨x, hx⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ :=
      kabs_mem_center_of_noncomm ε₁ hab (hcomm a (hmemR a ha)) (hcomm b (hmemR b hb))
    have hxK₂ : x ∈ K₂ := by
      rcases kabs_center_cases hodd₁ ε₁ ht hcen with h | h
      · have : x = 1 := congrArg Subtype.val h
        rw [this]
        exact K₂.one_mem
      · have : x = (t₀ : Y) := congrArg Subtype.val h
        rw [this]
        exact t₀.2.2
    exact K₂.mul_mem hxK₂ hy
  intro u hu hu2 hur u' hu' hu'2 hur'
  have h1 := hmem u hu hur
  have h2 := hmem u' hu' hur'
  have h3 : (⟨u, h1⟩ : ↥K₂) = ⟨u', h2⟩ :=
    kabs_eq_of_orderOf_two hodd₂ ε₂ (by rw [orderOf_mk]; exact hu2)
      (by rw [orderOf_mk]; exact hu'2)
  exact congrArg Subtype.val h3

end CFSG.GH74.GLS.Stage1.Main
