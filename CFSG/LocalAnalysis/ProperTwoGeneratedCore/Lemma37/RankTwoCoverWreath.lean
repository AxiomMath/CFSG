module

public import CFSG.CharacterTheory.Wreathed.Generators
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverCommutator

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Wreathed

variable {P : Type*} [Group P] {m : ℕ}

theorem wreath_base_decomp (ψ : P →* Wreath m) {a b g : P} (ha : ψ a = element m 1 0 0)
    (hb : ψ b = element m 0 1 0) (hg : ψ g ∈ baseSubgroup m) :
    ∃ I K : ℤ, ψ ((a ^ I * b ^ K)⁻¹ * g) = 1 := by
  obtain ⟨⟨i, j, e⟩, he⟩ := (coordinateEquiv m).symm.surjective (ψ g)
  change element m i j e = ψ g at he
  have he0 : e = 0 := (element_mem_base m i j e).mp (he ▸ hg)
  obtain ⟨I, hI⟩ := ZMod.intCast_surjective i
  obtain ⟨K, hK⟩ := ZMod.intCast_surjective j
  refine ⟨I, K, ?_⟩
  rw [map_mul, map_inv, map_mul, map_zpow, map_zpow, ha, hb, element_base_zpow,
    element_base_zpow, element_base_mul, ← he, he0, inv_mul_eq_one]
  simp [zsmul_eq_mul, hI, hK]

theorem wreath_swap_sq_conj (ψ : P →* Wreath m) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {a t : P} (ht : ψ t = element m 0 0 1) : t * (t * a * t⁻¹) * t⁻¹ = a := by
  have ht2 : ψ (t * t) = 1 := by
    rw [map_mul, ht, ← pow_two, element_swap_sq]
    simp
  calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t)⁻¹ := by group
    _ = a := by rw [← hcen _ ht2 a, mul_inv_cancel_right]

theorem wreath_not_commute (hm : 0 < m) (ψ : P →* Wreath m) (hψ : Function.Surjective ψ)
    (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g) (hker : ∀ z, ψ z = 1 → z ∈ commutator P)
    {z₀ : P} (hz₀ : ψ z₀ = 1) (hz₀1 : z₀ ≠ 1) {a t : P} (ha : ψ a = element m 1 0 0)
    (ht : ψ t = element m 0 0 1) : a * (t * a * t⁻¹) ≠ (t * a * t⁻¹) * a := by
  intro hab
  obtain ⟨b, hb_def⟩ : ∃ b, b = t * a * t⁻¹ := ⟨_, rfl⟩
  rw [← hb_def] at hab
  have hb : ψ b = element m 0 1 0 := by
    rw [hb_def, map_mul, map_mul, map_inv, ha, ht, conjugate_base_by_swap]
  have htb : t * b * t⁻¹ = a := by rw [hb_def]; exact wreath_swap_sq_conj ψ hcen ht
  set T := (baseSubgroup m).comap ψ
  have hTidx : T.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hψ, base_index_two m hm]
  have hnorm : (baseSubgroup m).Normal := Subgroup.normal_of_index_eq_two (base_index_two m hm)
  have hsT : ∀ g ∈ T, t * g * t⁻¹ ∈ T := fun g hg => by
    change ψ (t * g * t⁻¹) ∈ baseSubgroup m
    rw [map_mul, map_mul, map_inv]
    exact hnorm.conj_mem _ hg _
  have htT : t ∉ T := by
    change ψ t ∉ baseSubgroup m
    rw [ht, element_mem_base]
    decide
  have hdec : ∀ g ∈ T, ∃ I K : ℤ, ∃ c, ψ c = 1 ∧ g = a ^ I * b ^ K * c := fun g hg => by
    obtain ⟨I, K, hc⟩ := wreath_base_decomp ψ ha hb hg
    exact ⟨I, K, _, hc, by group⟩
  have hab' : Commute a b := hab
  have hTab : ∀ g ∈ T, ∀ g' ∈ T, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨I, K, c, hc, rfl⟩ := hdec g hg
    obtain ⟨I', K', c', hc', rfl⟩ := hdec g' hg'
    have hcomm : ∀ (I K I' K' : ℤ), Commute (a ^ I * b ^ K) (a ^ I' * b ^ K') := fun I K I' K' =>
      ((Commute.zpow_zpow_self a I I').mul_right (hab'.zpow_zpow I K')).mul_left
        ((hab'.symm.zpow_zpow K I').mul_right (Commute.zpow_zpow_self b K K'))
    have h1 : Commute (a ^ I * b ^ K * c) (a ^ I' * b ^ K') :=
      (hcomm I K I' K').mul_left (hcen c hc _).symm
    exact (h1.mul_right (hcen c' hc' _)).eq
  have hK : ∀ g ∈ T, g⁻¹ * (t * g * t⁻¹) ∈ Subgroup.zpowers (a⁻¹ * b) := by
    intro g hg
    obtain ⟨I, K, c, hc, rfl⟩ := hdec g hg
    have hconj : t * (a ^ I * b ^ K * c) * t⁻¹ = b ^ I * a ^ K * c := by
      have htc : t * c * t⁻¹ = c := by rw [hcen c hc t, mul_inv_cancel_right]
      calc t * (a ^ I * b ^ K * c) * t⁻¹ =
          (t * a * t⁻¹) ^ I * (t * b * t⁻¹) ^ K * (t * c * t⁻¹) := by
            rw [conj_zpow, conj_zpow]; group
        _ = b ^ I * a ^ K * c := by rw [← hb_def, htb, htc]
    rw [hconj]
    refine Subgroup.mem_zpowers_iff.mpr ⟨I - K, ?_⟩
    have hcc : ∀ y, y * c⁻¹ = c⁻¹ * y := fun y => hcen c⁻¹ (by rw [map_inv, hc, inv_one]) y
    have h1 : (a ^ I)⁻¹ * b ^ I = b ^ I * (a ^ I)⁻¹ := ((hab'.zpow_zpow I I).inv_left).eq
    have hE : (a ^ I * b ^ K * c)⁻¹ * (b ^ I * a ^ K * c) = b ^ (I - K) * a ^ (K - I) := by
      calc (a ^ I * b ^ K * c)⁻¹ * (b ^ I * a ^ K * c) =
          c⁻¹ * ((b ^ K)⁻¹ * ((a ^ I)⁻¹ * b ^ I) * a ^ K) * c := by group
        _ = c⁻¹ * ((b ^ K)⁻¹ * (b ^ I * (a ^ I)⁻¹) * a ^ K) * c := by rw [h1]
        _ = c⁻¹ * (b ^ (I - K) * a ^ (K - I)) * c := by group
        _ = b ^ (I - K) * a ^ (K - I) := by rw [← hcc]; group
    rw [hE, (hab'.inv_left).mul_zpow, inv_zpow', neg_sub]
    exact (hab'.zpow_zpow (K - I) (I - K)).eq

  have hcomm : commutator P ≤ Subgroup.zpowers (a⁻¹ * b) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact commutatorElement_mem_of_abelian T t hTab hsT
      (mem_or_mul_inv_mem_of_index_two hTidx htT) hK x y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcomm (hker z₀ hz₀))
  apply hz₀1
  rw [← hk] at hz₀ ⊢
  have hψv : ψ (a⁻¹ * b) = element m (-1) 1 0 := by
    rw [map_mul, map_inv, ha, hb, element_base_inv, element_base_mul]
    simp
  rw [map_zpow, hψv, element_base_zpow, element_base_eq_one_iff] at hz₀
  have hkm : (m : ℤ) ∣ k := by
    have := hz₀.2
    rw [zsmul_eq_mul, mul_one] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k m).mp this
  obtain ⟨l, rfl⟩ := hkm
  have ham : ψ (a ^ m) = 1 := by rw [map_pow, ha, element_base_pow_modulus]
  have hbm : b ^ m = a ^ m := by
    rw [hb_def, conj_pow, hcen _ ham t, mul_inv_cancel_right]
  rw [zpow_mul, zpow_natCast, (hab'.inv_left).mul_pow, inv_pow, hbm, inv_mul_cancel, one_zpow]

theorem wreath_commutator_ker (ψ : P →* Wreath m) {a b : P} (ha : ψ a = element m 1 0 0)
    (hb : ψ b = element m 0 1 0) : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb, element_base_inv, element_base_inv,
    element_base_mul, element_base_mul, element_base_mul]
  simp

theorem wreath_swap_conj (ψ : P →* Wreath m) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {a b t : P} (ht : ψ t = element m 0 0 1) (hb_def : b = t * a * t⁻¹) :
    t * (a * b) * t⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by
  have htb : t * b * t⁻¹ = a := by rw [hb_def]; exact wreath_swap_sq_conj ψ hcen ht
  calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by rw [← hb_def, htb]; group

theorem wreath_commutator_sq (ψ : P →* Wreath m) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {a b t : P} (ha : ψ a = element m 1 0 0) (ht : ψ t = element m 0 0 1)
    (hb_def : b = t * a * t⁻¹) : (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
  have hb : ψ b = element m 0 1 0 := by
    rw [hb_def, map_mul, map_mul, map_inv, ha, ht, conjugate_base_by_swap]
  have htb : t * b * t⁻¹ = a := by rw [hb_def]; exact wreath_swap_sq_conj ψ hcen ht
  set c := a * b * a⁻¹ * b⁻¹ with hc_def
  have hc : ψ c = 1 := wreath_commutator_ker ψ ha hb
  have htc : t * c * t⁻¹ = c⁻¹ := by
    calc t * c * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by
          rw [hc_def]; group
      _ = c⁻¹ := by rw [← hb_def, htb, hc_def]; group
  rw [hcen c hc t, mul_inv_cancel_right] at htc
  calc c * c = c * c⁻¹ := by rw [← htc]
    _ = 1 := mul_inv_cancel c

theorem pow_central_mul_of_even {c x : P} (hcx : Commute c x) (hcc : c * c = 1) {h : ℕ}
    (hh : Even h) : (c * x) ^ h = x ^ h := by
  obtain ⟨k, rfl⟩ := hh
  rw [hcx.mul_pow, ← two_mul, pow_mul, pow_two, hcc, one_pow, one_mul]

theorem conj_pow_eq_commutator_pow {a b : P} (hc : ∀ g, g * (a * b * a⁻¹ * b⁻¹) =
    (a * b * a⁻¹ * b⁻¹) * g) (k : ℕ) :
    a ^ k * b * (a ^ k)⁻¹ = (a * b * a⁻¹ * b⁻¹) ^ k * b := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc a ^ (k + 1) * b * (a ^ (k + 1))⁻¹ = a * (a ^ k * b * (a ^ k)⁻¹) * a⁻¹ := by
          rw [pow_succ']; group
      _ = a * ((a * b * a⁻¹ * b⁻¹) ^ k * b) * a⁻¹ := by rw [ih]
      _ = (a * b * a⁻¹ * b⁻¹) ^ k * (a * b * a⁻¹ * b⁻¹) * b := by
          rw [← mul_assoc a, (Commute.pow_right (hc a) k).eq]
          group
      _ = (a * b * a⁻¹ * b⁻¹) ^ (k + 1) * b := by rw [pow_succ]

theorem wreath_central_lift (ψ : P →* Wreath m) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {a b t : P} (ha : ψ a = element m 1 0 0) (ht : ψ t = element m 0 0 1)
    (hb_def : b = t * a * t⁻¹) {h : ℕ} (hh : Even h) (g : P) :
    g * (a * b) ^ h = (a * b) ^ h * g := by
  have hb : ψ b = element m 0 1 0 := by
    rw [hb_def, map_mul, map_mul, map_inv, ha, ht, conjugate_base_by_swap]
  set c := a * b * a⁻¹ * b⁻¹ with hc_def
  have hc : ψ c = 1 := wreath_commutator_ker ψ ha hb
  have hcc : c * c = 1 := wreath_commutator_sq ψ hcen ha ht hb_def
  have hcinv : ψ c⁻¹ = 1 := by rw [map_inv, hc, inv_one]
  set C := Subgroup.centralizer {(a * b) ^ h}
  have hmemC : ∀ y, y * (a * b) ^ h * y⁻¹ = (a * b) ^ h → y ∈ C := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (a * b) ^ h = y * (a * b) ^ h * y⁻¹ * y := by group
      _ = (a * b) ^ h * y := by rw [hy]
  have haC : a ∈ C := hmemC a (by
    rw [← conj_pow]
    have : a * (a * b) * a⁻¹ = c * (a * b) := by
      calc a * (a * b) * a⁻¹ = a * c * b := by rw [hc_def]; group
        _ = c * (a * b) := by rw [hcen c hc a]; group
    rw [this, pow_central_mul_of_even (hcen c hc _).symm hcc hh])
  have htC : t ∈ C := hmemC t (by
    rw [← conj_pow, wreath_swap_conj ψ hcen ht hb_def, ← hc_def,
      pow_central_mul_of_even (hcen c⁻¹ hcinv _).symm (by rw [← mul_inv_rev, hcc, inv_one]) hh])
  have hkerC : ∀ z, ψ z = 1 → z ∈ C := fun z hz => hmemC z (by
    rw [← hcen z hz, mul_inv_cancel_right])
  have hmap : C.map ψ = ⊤ := by
    rw [eq_top_iff, ← wreath_eq_generated_s_swap m, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨a, haC, ha⟩
    · exact ⟨t, htC, ht⟩
  obtain ⟨g', hg'C, hg'⟩ : ψ g ∈ C.map ψ := by rw [hmap]; exact Subgroup.mem_top _
  have hgC : g ∈ C := by
    have hz : ψ (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, hg', inv_mul_cancel]
    have := C.mul_mem hg'C (hkerC _ hz)
    rwa [mul_inv_cancel_left] at this
  exact (Subgroup.mem_centralizer_singleton_iff.mp hgC)

theorem wreath_half_commute_base (ψ : P →* Wreath m) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {a b t : P} (ha : ψ a = element m 1 0 0) (ht : ψ t = element m 0 0 1)
    (hb_def : b = t * a * t⁻¹) {h : ℕ} (hh : Even h) {g : P} (hg : ψ g ∈ baseSubgroup m) :
    g * a ^ h = a ^ h * g := by
  have hb : ψ b = element m 0 1 0 := by
    rw [hb_def, map_mul, map_mul, map_inv, ha, ht, conjugate_base_by_swap]
  set c := a * b * a⁻¹ * b⁻¹ with hc_def
  have hc : ψ c = 1 := wreath_commutator_ker ψ ha hb
  have hcc : c * c = 1 := wreath_commutator_sq ψ hcen ha ht hb_def
  have hab : Commute (a ^ h) b := by
    have h1 := conj_pow_eq_commutator_pow (a := a) (b := b) (hcen c hc) h
    obtain ⟨k, rfl⟩ := hh
    have hck : c ^ (k + k) = 1 := by rw [← two_mul, pow_mul, pow_two, hcc, one_pow]
    rw [← hc_def, hck, one_mul] at h1
    calc a ^ (k + k) * b = a ^ (k + k) * b * (a ^ (k + k))⁻¹ * a ^ (k + k) := by group
      _ = b * a ^ (k + k) := by rw [h1]
  obtain ⟨I, K, hc'⟩ := wreath_base_decomp ψ ha hb hg
  set c' := (a ^ I * b ^ K)⁻¹ * g
  have hg' : g = a ^ I * b ^ K * c' := (mul_inv_cancel_left (a ^ I * b ^ K) g).symm
  rw [hg']
  have h1 : Commute (a ^ I * b ^ K) (a ^ h) :=
    ((Commute.zpow_left (Commute.refl a) I).pow_right h).mul_left (hab.symm.zpow_left K)
  exact (h1.mul_left (hcen c' hc' _).symm).eq

end CFSG.ProperTwoGeneratedCore.Lemma37
