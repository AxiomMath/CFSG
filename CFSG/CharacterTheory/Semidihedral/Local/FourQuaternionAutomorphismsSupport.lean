module

public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Semidihedral.Local

open QuaternionGroup

section SymmetricThree

theorem perm_fin_three_central_eq_one :
    ∀ σ : Equiv.Perm (Fin 3), (∀ τ : Equiv.Perm (Fin 3), τ * σ = σ * τ) → σ = 1 := by
  decide

theorem le_center_of_normal_card_two {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (h2 : Nat.card N = 2) : N ≤ Subgroup.center G := by
  intro t ht
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases ht1 : t = 1
  · rw [ht1, mul_one, one_mul]
  have hconj : g * t * g⁻¹ ∈ N := hN.conj_mem t ht g
  have hne : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
    have h' : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [h', h]
    group)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h2
  have h1 : (⟨g * t * g⁻¹, hconj⟩ : N) = y := hy _ fun h => hne (congrArg Subtype.val h)
  have h1' : (⟨t, ht⟩ : N) = y := hy _ fun h => ht1 (congrArg Subtype.val h)
  have hgt : g * t * g⁻¹ = t := congrArg Subtype.val (h1.trans h1'.symm)
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [hgt]

theorem normal_isPGroup_two_eq_bot {G : Type*} [Group G] (ψ : G ≃* Equiv.Perm (Fin 3))
    (N : Subgroup G) (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Finite G := Finite.of_equiv _ ψ.symm.toEquiv
  have hG : Nat.card G = 6 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hdvd : 2 ^ k ∣ 6 := hk ▸ hG ▸ Subgroup.card_subgroup_dvd_card N
  have hk1 : k ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have := Nat.dvd_trans h4 hdvd
    norm_num at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
  · exact Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
  · exfalso
    have hc := le_center_of_normal_card_two hN (by rw [hk, pow_one])
    obtain ⟨t, htN, ht1⟩ : ∃ t ∈ N, t ≠ 1 := by
      rcases N.bot_or_exists_ne_one with hbot | h
      · rw [hbot, Subgroup.card_bot] at hk
        norm_num at hk
      · exact h
    have htc := Subgroup.mem_center_iff.mp (hc htN)
    have hψ : ψ t = 1 := perm_fin_three_central_eq_one (ψ t) fun τ => by
      have h := congrArg ψ (htc (ψ.symm τ))
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
    exact ht1 (ψ.injective (hψ.trans (map_one ψ).symm))

theorem card_eq_or_eq_top_of_le {G : Type*} [Group G] [Finite G] {a : ℕ} (ha : 0 < a)
    (hG : Nat.card G = 3 * a) {H K : Subgroup G} (hKH : K ≤ H) (hK : Nat.card K = a) :
    Nat.card H = a ∨ H = ⊤ := by
  obtain ⟨t, ht⟩ := hK ▸ Subgroup.card_dvd_of_le hKH
  have hdvd := Subgroup.card_subgroup_dvd_card H
  rw [hG, ht, mul_comm 3 a] at hdvd
  have ht3 : t ∣ 3 := Nat.dvd_of_mul_dvd_mul_left ha hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp ht3 with rfl | rfl
  · exact Or.inl (by rw [ht, mul_one])
  · exact Or.inr ((Subgroup.card_eq_iff_eq_top H).mp (by rw [ht, hG, mul_comm]))

end SymmetricThree

section KleinFour

variable {V : Type*} [Group V]

@[expose] def nontrivialPerm (V : Type*) [Group V] : MulAut V →* Equiv.Perm {x : V // x ≠ 1} where
  toFun φ := φ.toEquiv.subtypeEquiv fun _ => (map_ne_one_iff φ φ.injective).symm
  map_one' := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl

theorem nontrivialPerm_apply (φ : MulAut V) (x : {x : V // x ≠ 1}) :
    (nontrivialPerm V φ x : V) = φ x := rfl

theorem nontrivialPerm_bijective [IsKleinFour V] : Function.Bijective (nontrivialPerm V) := by
  classical
  constructor
  · intro φ ψ h
    ext x
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · exact congrArg (fun σ : Equiv.Perm {x : V // x ≠ 1} => (σ ⟨x, hx⟩ : V)) h
  · intro σ
    have hτ1 : Equiv.Perm.ofSubtype σ (1 : V) = 1 :=
      Equiv.Perm.ofSubtype_apply_of_not_mem σ (by simp)
    refine ⟨IsKleinFour.mulEquiv (Equiv.Perm.ofSubtype σ) hτ1, ?_⟩
    ext x
    exact Equiv.Perm.ofSubtype_apply_coe σ x

theorem card_nontrivial [IsKleinFour V] : Nat.card {x : V // x ≠ 1} = 3 := by
  classical
  have : Finite V := IsKleinFour.instFinite
  have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : V))
  rw [Finite.card_option, IsKleinFour.card_four (G := V)] at h
  omega

theorem nonempty_mulAut_equiv_perm_three [IsKleinFour V] :
    Nonempty (MulAut V ≃* Equiv.Perm (Fin 3)) := by
  have : Finite V := IsKleinFour.instFinite
  exact ⟨(MulEquiv.ofBijective _ nontrivialPerm_bijective).trans
    (Finite.equivFinOfCardEq card_nontrivial).permCongrHom⟩

end KleinFour

section Computations

theorem qEight_pow_four : ∀ g : QuaternionGroup 2, g ^ 4 = 1 := by decide

theorem qEight_sq_ne_one : ∀ g : QuaternionGroup 2, g ^ 2 ≠ 1 → g ^ 2 = a 2 := by decide

theorem qEight_conj : ∀ g h : QuaternionGroup 2, g ^ 2 ≠ 1 → h ^ 2 ≠ 1 → h ≠ g → h ≠ g⁻¹ →
    h * g * h⁻¹ = g⁻¹ := by decide

theorem qEight_order_four : ∀ g : QuaternionGroup 2, g ^ 2 ≠ 1 →
    g = a 1 ∨ g = (a 1)⁻¹ ∨ g = xa 0 ∨ g = (xa 0)⁻¹ ∨ g = a 1 * xa 0 ∨ g = (a 1 * xa 0)⁻¹ := by
  decide

theorem qEight_generators :
    (a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧ (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
      (a 1 * xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
      (xa 0 : QuaternionGroup 2) ≠ a 1 ∧ (xa 0 : QuaternionGroup 2) ≠ (a 1)⁻¹ ∧
      (a 1 * xa 0 : QuaternionGroup 2) ≠ a 1 ∧ (a 1 * xa 0 : QuaternionGroup 2) ≠ (a 1)⁻¹ ∧
      (a 1 * xa 0 : QuaternionGroup 2) ≠ xa 0 ∧ (a 1 * xa 0 : QuaternionGroup 2) ≠ (xa 0)⁻¹ := by
  decide

theorem qEight_center : ∀ g : QuaternionGroup 2, (∀ h, h * g = g * h) ↔ g = 1 ∨ g = a 2 := by
  decide

theorem qEight_pairs : (Finset.univ.filter (fun p : QuaternionGroup 2 × QuaternionGroup 2 =>
    p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹)).card = 24 := by decide

end Computations

section QuaternionEight

variable {Q : Type*} [Group Q] (e : Q ≃* QuaternionGroup 2)

theorem map_sq_ne_one_of_equiv {g : Q} (hg : g ^ 2 ≠ 1) : e g ^ 2 ≠ 1 := fun h =>
  hg (e.injective (by rw [map_pow, h, map_one]))

include e in
theorem pow_four_of_equiv (g : Q) : g ^ 4 = 1 :=
  e.injective (by rw [map_pow, map_one, qEight_pow_four])

include e in
theorem sq_eq_sq_of_equiv {g h : Q} (hg : g ^ 2 ≠ 1) (hh : h ^ 2 ≠ 1) : g ^ 2 = h ^ 2 :=
  e.injective (by
    rw [map_pow, map_pow, qEight_sq_ne_one _ (map_sq_ne_one_of_equiv e hg),
      qEight_sq_ne_one _ (map_sq_ne_one_of_equiv e hh)])

include e in
theorem conj_eq_inv_of_equiv {g h : Q} (hg : g ^ 2 ≠ 1) (hh : h ^ 2 ≠ 1) (hhg : h ≠ g)
    (hhg' : h ≠ g⁻¹) : h * g * h⁻¹ = g⁻¹ :=
  e.injective (by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact qEight_conj _ _ (map_sq_ne_one_of_equiv e hg) (map_sq_ne_one_of_equiv e hh)
      (e.injective.ne hhg) (by rw [← map_inv]; exact e.injective.ne hhg'))

theorem eq_of_sq_ne_one_of_equiv {g : Q} (hg : g ^ 2 ≠ 1) :
    g = e.symm (a 1) ∨ g = (e.symm (a 1))⁻¹ ∨ g = e.symm (xa 0) ∨ g = (e.symm (xa 0))⁻¹ ∨
      g = e.symm (a 1) * e.symm (xa 0) ∨ g = (e.symm (a 1) * e.symm (xa 0))⁻¹ := by
  have h := qEight_order_four (e g) (map_sq_ne_one_of_equiv e hg)
  simp only [← map_inv, ← map_mul, ← MulEquiv.eq_symm_apply] at h ⊢
  exact h

theorem generators_of_equiv :
    e.symm (a 1) ^ 2 ≠ 1 ∧ e.symm (xa 0) ^ 2 ≠ 1 ∧ (e.symm (a 1) * e.symm (xa 0)) ^ 2 ≠ 1 ∧
      e.symm (xa 0) ≠ e.symm (a 1) ∧ e.symm (xa 0) ≠ (e.symm (a 1))⁻¹ ∧
      e.symm (a 1) * e.symm (xa 0) ≠ e.symm (a 1) ∧
      e.symm (a 1) * e.symm (xa 0) ≠ (e.symm (a 1))⁻¹ ∧
      e.symm (a 1) * e.symm (xa 0) ≠ e.symm (xa 0) ∧
      e.symm (a 1) * e.symm (xa 0) ≠ (e.symm (xa 0))⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := qEight_generators
  simp only [← map_inv, ← map_mul, ← map_pow, ne_eq, MulEquivClass.map_eq_one_iff,
    EmbeddingLike.apply_eq_iff_eq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

include e in
theorem card_of_equiv : Nat.card Q = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

include e in
theorem finite_of_equiv : Finite Q := Finite.of_equiv _ e.symm.toEquiv

include e in
theorem orderOf_eq_four_of_equiv {g : Q} (hg : g ^ 2 ≠ 1) : orderOf g = 2 * 2 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) (by simpa using hg)
    (by simpa using pow_four_of_equiv e g)
  simpa using h

include e in
theorem eq_or_eq_inv_of_mem_zpowers {g y : Q} (hy : y ∈ Subgroup.zpowers g) (hy2 : y ^ 2 ≠ 1) :
    y = g ∨ y = g⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hg4 : g ^ (4 : ℕ) = 1 := pow_four_of_equiv e g
  rw [zpow_eq_zpow_emod' k hg4] at hy2 ⊢
  have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have h1 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c, k % ((4 : ℕ) : ℤ) = c := ⟨_, rfl⟩
  rw [hc] at hy2 h0 h1 ⊢
  interval_cases c
  · exact absurd (by rw [zpow_zero, one_pow]) hy2
  · exact Or.inl (zpow_one g)
  · exfalso
    apply hy2
    rw [← zpow_natCast, ← zpow_mul, show (2 : ℤ) * ((2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num,
      zpow_natCast, hg4]
  · refine Or.inr ?_
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (3 : ℤ) + 1 = ((4 : ℕ) : ℤ) by norm_num,
      zpow_natCast, hg4]

include e in
theorem cyclicFour_iff (H : Subgroup Q) :
    (IsCyclic H ∧ Nat.card H = 4) ↔ ∃ g : Q, g ^ 2 ≠ 1 ∧ H = Subgroup.zpowers g := by
  constructor
  · rintro ⟨hcyc, hcard⟩
    obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := H)
    have hH : H = Subgroup.zpowers (b : Q) := by
      refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr b.2)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hb ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
    refine ⟨b, fun h => ?_, hH⟩
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [← Nat.card_zpowers, ← hH, hcard] at hdvd
    norm_num at hdvd
  · rintro ⟨g, hg, rfl⟩
    exact ⟨inferInstance, by rw [Nat.card_zpowers, orderOf_eq_four_of_equiv e hg]⟩

end QuaternionEight

section Automorphisms

variable {Q : Type*} [Group Q]

theorem map_cyclicFour (φ : MulAut Q) (H : {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4}) :
    IsCyclic (H.1.map φ.toMonoidHom) ∧ Nat.card (H.1.map φ.toMonoidHom) = 4 := by
  have ε := H.1.equivMapOfInjective φ.toMonoidHom φ.injective
  have := H.2.1
  exact ⟨isCyclic_of_surjective ε.toMonoidHom ε.surjective,
    by rw [← Nat.card_congr ε.toEquiv, H.2.2]⟩

theorem map_map_symm (φ : MulAut Q) (H : Subgroup Q) :
    (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
  ext x
  simp

@[expose] def cyclicFourAction (Q : Type*) [Group Q] :
    MulAut Q →* Equiv.Perm {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} where
  toFun φ :=
    { toFun := fun H => ⟨H.1.map φ.toMonoidHom, map_cyclicFour φ H⟩
      invFun := fun H => ⟨H.1.map φ.symm.toMonoidHom, map_cyclicFour φ.symm H⟩
      left_inv := fun H => Subtype.ext (map_map_symm φ H.1)
      right_inv := fun H => Subtype.ext (by simpa using map_map_symm φ.symm H.1) }
  map_one' := by
    ext H x
    simp
  map_mul' φ ψ := by
    ext H x
    simp [MulAut.mul_def]

theorem cyclicFourAction_apply (φ : MulAut Q)
    (H : {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4}) :
    (cyclicFourAction Q φ H : Subgroup Q) = H.1.map φ.toMonoidHom := rfl

variable (e : Q ≃* QuaternionGroup 2)

include e in
theorem mulAut_ext_of_equiv {φ ψ : MulAut Q} (h1 : φ (e.symm (a 1)) = ψ (e.symm (a 1)))
    (h2 : φ (e.symm (xa 0)) = ψ (e.symm (xa 0))) : φ = ψ := by
  have h := quaternion_eq_of_generators (m := 2) (e₁ := φ.toMonoidHom.comp e.symm.toMonoidHom)
    (e₂ := ψ.toMonoidHom.comp e.symm.toMonoidHom) h1 h2
  ext x
  have := DFunLike.congr_fun h (e x)
  simpa using this

include e in
theorem closure_pair_eq_top_of_equiv {x y : Q} (hx : x ^ 2 ≠ 1) (hy : y ^ 2 ≠ 1) (hyx : y ≠ x)
    (hyx' : y ≠ x⁻¹) : Subgroup.closure {x, y} = ⊤ := by
  have := finite_of_equiv e
  have hxy : y ∉ Subgroup.zpowers x := fun h => by
    rcases eq_or_eq_inv_of_mem_zpowers e h hy with h | h
    · exact hyx h
    · exact hyx' h
  have hle : Subgroup.zpowers x ≤ Subgroup.closure {x, y} :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  have hlt : Subgroup.zpowers x < Subgroup.closure {x, y} :=
    lt_of_le_of_ne hle fun h => hxy (h ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hcx : Nat.card (Subgroup.zpowers x) = 4 := by
    rw [Nat.card_zpowers, orderOf_eq_four_of_equiv e hx]
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hle
  have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.closure ({x, y} : Set Q))
  rw [card_of_equiv e, ht, hcx] at hdvd
  have hlt' := Subgroup.card_lt_of_lt hlt
  rw [ht, hcx] at hlt'
  have ht2 : t ∣ 2 :=
    Nat.dvd_of_mul_dvd_mul_left (show 0 < 4 by norm_num) (show 4 * t ∣ 4 * 2 by simpa using hdvd)
  have ht1 : t ≠ 1 := fun h => by rw [h] at hlt'; omega
  have htt : t = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ht2 with h | h
    · exact absurd h ht1
    · exact h
  rw [← Subgroup.card_eq_iff_eq_top, ht, hcx, htt, card_of_equiv e]

include e in
theorem card_mulAut_of_equiv : Nat.card (MulAut Q) = 24 := by
  classical
  have := finite_of_equiv e
  obtain ⟨hu, hw, -, hwu, hwu', -⟩ := generators_of_equiv e
  set P := {p : Q × Q // p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹}
  let F : MulAut Q → P := fun φ => ⟨(φ (e.symm (a 1)), φ (e.symm (xa 0))),
    by rw [← map_pow, ne_eq, MulEquivClass.map_eq_one_iff]; exact hu,
    by rw [← map_pow, ne_eq, MulEquivClass.map_eq_one_iff]; exact hw,
    fun h => hwu (φ.injective h),
    fun h => hwu' (φ.injective (by rw [map_inv]; exact h))⟩
  have hF : Function.Bijective F := by
    constructor
    · intro φ ψ h
      have h' := congrArg Subtype.val h
      exact mulAut_ext_of_equiv e (congrArg Prod.fst h') (congrArg Prod.snd h')
    · rintro ⟨⟨x, y⟩, hx, hy, hyx, hyx'⟩
      have hgen := closure_pair_eq_top_of_equiv e hx hy hyx hyx'
      obtain ⟨⟨ε, ⟨hε1, hε2⟩, -⟩, -⟩ := quaternion_normal_form_isomorphism (m := 2)
        (by norm_num) hgen (orderOf_eq_four_of_equiv e hx)
        (fun h => by
          rcases eq_or_eq_inv_of_mem_zpowers e h hy with h | h
          · exact hyx h
          · exact hyx' h)
        (sq_eq_sq_of_equiv e hy hx) (conj_eq_inv_of_equiv e hx hy hyx hyx')
      refine ⟨e.trans ε, Subtype.ext ?_⟩
      simp only [F, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hε1, hε2]
  have hP : Nat.card P = 24 := by
    have hPe : P ≃ {p : QuaternionGroup 2 × QuaternionGroup 2 //
        p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1⁻¹} :=
      (e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun p => by
        simp only [Equiv.prodCongr_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
          Prod.map_fst, Prod.map_snd, ← map_pow, ← map_inv, ne_eq, MulEquivClass.map_eq_one_iff,
          EmbeddingLike.apply_eq_iff_eq]
    rw [Nat.card_congr hPe, Nat.card_eq_fintype_card, Fintype.card_subtype, qEight_pairs]
  rw [Nat.card_congr (Equiv.ofBijective F hF), hP]

include e in
theorem card_center_of_equiv : Nat.card (Subgroup.center Q) = 2 := by
  have hz : Subgroup.center Q = Subgroup.zpowers (e.symm (a 2)) := by
    apply le_antisymm
    · intro g hg
      have h := (qEight_center (e g)).mp fun h' => by
        have := Subgroup.mem_center_iff.mp hg (e.symm h')
        simpa using congrArg e this
      rcases h with h | h
      · rw [(MulEquiv.map_eq_one_iff e).mp h]
        exact Subgroup.one_mem _
      · rw [← MulEquiv.eq_symm_apply] at h
        rw [h]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      have h := (qEight_center (a 2)).mpr (Or.inr rfl) (e g)
      apply e.injective
      simpa using h
  have hz2 : orderOf (e.symm (a 2)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  rw [hz, Nat.card_zpowers, hz2]

include e in
theorem card_inner_of_equiv : Nat.card (MulAut.conj : Q →* MulAut Q).range = 4 := by
  have := finite_of_equiv e
  have hker : (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have := congrArg (fun φ : MulAut Q => φ x) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    · intro h
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← h x]
      group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAut.conj : Q →* MulAut Q).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hker,
    card_center_of_equiv e, card_of_equiv e] at h1
  omega

include e in
theorem inner_le_ker_cyclicFourAction :
    (MulAut.conj : Q →* MulAut Q).range ≤ (cyclicFourAction Q).ker := by
  rintro _ ⟨g, rfl⟩
  rw [MonoidHom.mem_ker]
  ext H : 2
  have hidx : H.1.index = 2 := by
    have h := Subgroup.card_mul_index H.1
    rw [H.2.2, card_of_equiv e] at h
    omega
  have := Subgroup.normal_of_index_eq_two hidx
  exact Subgroup.Normal.map_conj_eq H.1 g

include e in
theorem card_cyclicFour_of_equiv :
    Nat.card {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} = 3 := by
  obtain ⟨hu, hw, huw, hwu, hwu', huwu, huwu', huww, huww'⟩ := generators_of_equiv e
  have hmem : ∀ g : Q, g ^ 2 ≠ 1 →
      (IsCyclic (Subgroup.zpowers g) ∧ Nat.card (Subgroup.zpowers g) = 4) :=
    fun g hg => (cyclicFour_iff e _).mpr ⟨g, hg, rfl⟩
  have hne : ∀ {g h : Q}, h ^ 2 ≠ 1 → h ≠ g → h ≠ g⁻¹ →
      Subgroup.zpowers g ≠ Subgroup.zpowers h := by
    intro g h hh h1 h2 heq
    rcases eq_or_eq_inv_of_mem_zpowers e (heq ▸ Subgroup.mem_zpowers h) hh with h' | h'
    · exact h1 h'
    · exact h2 h'
  let F : Fin 3 → {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} :=
    ![⟨Subgroup.zpowers (e.symm (a 1)), hmem _ hu⟩, ⟨Subgroup.zpowers (e.symm (xa 0)), hmem _ hw⟩,
      ⟨Subgroup.zpowers (e.symm (a 1) * e.symm (xa 0)), hmem _ huw⟩]
  have hF : Function.Bijective F := by
    constructor
    · intro i j hij
      have hv := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd hv (hne hw hwu hwu')
        | exact absurd hv.symm (hne hw hwu hwu')
        | exact absurd hv (hne huw huwu huwu')
        | exact absurd hv.symm (hne huw huwu huwu')
        | exact absurd hv (hne huw huww huww')
        | exact absurd hv.symm (hne huw huww huww')
    · intro H
      obtain ⟨g, hg, hH⟩ := (cyclicFour_iff e H.1).mp H.2
      rcases eq_of_sq_ne_one_of_equiv e hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, Subtype.ext hH.symm⟩
      · exact ⟨0, Subtype.ext (by rw [hH, Subgroup.zpowers_inv]; rfl)⟩
      · exact ⟨1, Subtype.ext hH.symm⟩
      · exact ⟨1, Subtype.ext (by rw [hH, Subgroup.zpowers_inv]; rfl)⟩
      · exact ⟨2, Subtype.ext hH.symm⟩
      · exact ⟨2, Subtype.ext (by rw [hH, Subgroup.zpowers_inv]; rfl)⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fin]

include e in
theorem card_ker_cyclicFourAction_le : Nat.card (cyclicFourAction Q).ker ≤ 4 := by
  classical
  obtain ⟨hu, hw, -⟩ := generators_of_equiv e
  have hfix : ∀ φ ∈ (cyclicFourAction Q).ker, ∀ g : Q, g ^ 2 ≠ 1 → φ g = g ∨ φ g = g⁻¹ := by
    intro φ hφ g hg
    have hX : IsCyclic (Subgroup.zpowers g) ∧ Nat.card (Subgroup.zpowers g) = 4 :=
      (cyclicFour_iff e _).mpr ⟨g, hg, rfl⟩
    have h : (Subgroup.zpowers g).map φ.toMonoidHom = Subgroup.zpowers g :=
      congrArg (fun σ : Equiv.Perm {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} =>
        (σ ⟨Subgroup.zpowers g, hX⟩ : Subgroup Q)) (MonoidHom.mem_ker.mp hφ)
    have hmem : φ g ∈ Subgroup.zpowers g :=
      h ▸ Subgroup.mem_map_of_mem φ.toMonoidHom (Subgroup.mem_zpowers g)
    exact eq_or_eq_inv_of_mem_zpowers e hmem
      (by rw [← map_pow, ne_eq, MulEquivClass.map_eq_one_iff]; exact hg)
  let s : Finset (Q × Q) := ({e.symm (a 1), (e.symm (a 1))⁻¹} : Finset Q) ×ˢ
    ({e.symm (xa 0), (e.symm (xa 0))⁻¹} : Finset Q)
  have hs : s.card ≤ 4 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul (Finset.card_le_two) (Finset.card_le_two)
  let F : (cyclicFourAction Q).ker → s := fun φ =>
    ⟨((φ : MulAut Q) (e.symm (a 1)), (φ : MulAut Q) (e.symm (xa 0))), by
      simp only [s, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hfix φ φ.2 _ hu, hfix φ φ.2 _ hw⟩⟩
  have hF : Function.Injective F := fun φ ψ h =>
    Subtype.ext (mulAut_ext_of_equiv e (congrArg (fun p : s => p.1.1) h)
      (congrArg (fun p : s => p.1.2) h))
  calc Nat.card (cyclicFourAction Q).ker ≤ Nat.card s := Nat.card_le_card_of_injective F hF
    _ = s.card := Nat.card_eq_finsetCard s
    _ ≤ 4 := hs

end Automorphisms

end CFSG.Semidihedral.Local
