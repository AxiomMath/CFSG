module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YF

open Module QuadraticMap

section Count

variable {K : Type} [Field K] [Finite K]

noncomputable def dotLin {m : ℕ} (x : Fin m → K) : (Fin m → K) →ₗ[K] K where
  toFun y := dotProduct x y
  map_add' y z := dotProduct_add x y z
  map_smul' c y := by simp [dotProduct_smul]

theorem card_ker_dotLin {m : ℕ} {x : Fin m → K} (hx : x ≠ 0) :
    Nat.card (LinearMap.ker (dotLin x)) = Nat.card K ^ (m - 1) := by
  classical
  rw [CFSG.LocalAnalysis.GLTheoremA.D4T.card_submodule]
  congr 1
  have hsurj : Function.Surjective (dotLin x) := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    intro c
    refine ⟨Pi.single i (c / x i), ?_⟩
    simp only [dotLin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_single]
    field_simp
  have h1 := LinearMap.finrank_range_add_finrank_ker (dotLin x)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  omega

theorem card_dot_zero {m : ℕ} (hm : 1 ≤ m) :
    Nat.card {p : (Fin m → K) × (Fin m → K) // dotProduct p.1 p.2 = 0} + Nat.card K ^ (m - 1) =
      Nat.card K ^ m + Nat.card K ^ (2 * m - 1) := by
  classical
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun (x y : Fin (k + 1) → K) =>
      dotProduct x y = 0), Nat.card_sigma]
  have hf : ∀ x : Fin (k + 1) → K, Nat.card {y : Fin (k + 1) → K // dotProduct x y = 0} =
      if x = 0 then Nat.card K ^ (k + 1) else Nat.card K ^ k := by
    intro x
    split_ifs with hx
    · subst hx
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun y => zero_dotProduct y)), Nat.card_fun,
        Nat.card_fin]
    · have h := card_ker_dotLin hx
      rw [Nat.add_sub_cancel] at h
      exact (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [dotLin])).trans h
  simp_rw [hf]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0)]
  rw [Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, hcardK]
  simp only [if_true, smul_eq_mul]
  have hpos : 1 ≤ Nat.card K ^ (k + 1) := Nat.one_le_pow _ _ Nat.card_pos
  have e1 : k + 1 - 1 = k := by omega
  have e2 : 2 * (k + 1) - 1 = (k + 1) + k := by omega
  generalize Nat.card K = Q at hpos ⊢
  rw [e1, e2, pow_add Q (k + 1) k]
  obtain ⟨a, ha⟩ : ∃ a, Q ^ (k + 1) = a + 1 := ⟨Q ^ (k + 1) - 1, by omega⟩
  rw [ha, Nat.add_sub_cancel]
  ring

theorem card_singular_coordinate_gen :
    Nat.card {v : Fin (2 * 4) → K // CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus 4 K v = 0} +
      Nat.card K ^ 3 = Nat.card K ^ 4 + Nat.card K ^ 7 := by
  have h := card_dot_zero (K := K) (m := 4) (by norm_num)
  have e : Nat.card {v : Fin (2 * 4) → K // CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus 4 K v = 0} =
      Nat.card {p : (Fin 4 → K) × (Fin 4 → K) // dotProduct p.1 p.2 = 0} := by
    refine Nat.card_congr ?_
    refine (Equiv.subtypeEquiv
      (Equiv.arrowCongr (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv 4).symm (Equiv.refl K))
      (p := fun v => CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus 4 K v = 0)
      (q := fun v : Fin 4 ⊕ Fin 4 → K => ∑ i : Fin 4, v (.inl i) * v (.inr i) = 0) fun v => ?_).trans
      (Equiv.subtypeEquiv (Equiv.sumArrowEquivProdArrow (Fin 4) (Fin 4) K) fun v => ?_)
    · rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus_apply]
      simp [Equiv.arrowCongr_apply]
    · simp [dotProduct, Equiv.sumArrowEquivProdArrow]
  rw [e]
  simpa using h

end Count


section Plane

variable {K : Type} [Field K] [Finite K]

theorem card_plane_zero (c : K) :
    Nat.card {p : K × K // p.1 * (p.1 * c + p.2) = 0} + 1 = 2 * Nat.card K := by
  classical
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun (b a : K) => b * (b * c + a) = 0),
    Nat.card_sigma]
  have hf : ∀ b : K, Nat.card {a : K // b * (b * c + a) = 0} = if b = 0 then Nat.card K else 1 := by
    intro b
    split_ifs with hb
    · subst hb
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun a => by simp))]
    · haveI : Unique {a : K // b * (b * c + a) = 0} :=
        { default := ⟨-(b * c), by ring⟩
          uniq := fun ⟨a, ha⟩ => Subtype.ext (by
            have := (mul_eq_zero.1 ha).resolve_left hb
            linear_combination this) }
      exact Nat.card_unique
  simp_rw [hf]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0)]
  rw [Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardK]
  simp only [if_true, smul_eq_mul, mul_one]
  have : 1 ≤ Nat.card K := Nat.card_pos
  omega

variable [CharP K 2] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem card_sing_plane (Q : QuadraticForm K V) (F : Submodule K V) (hF2 : finrank K F = 2)
    (hFnd : ∀ c ∈ F, (∀ c' ∈ F, polar Q c c' = 0) → c = 0)
    {f : V} (hfF : f ∈ F) (hf0 : f ≠ 0) (hfQ : Q f = 0) :
    ({v : V | Q v = 0} ∩ (F : Set V)).ncard + 1 = 2 * Nat.card K := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨c', hc'F, hc'⟩ : ∃ c' ∈ F, polar Q f c' ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (hFnd f hfF h)
  set g : V := (polar Q f c')⁻¹ • c' with hg
  have hgF : g ∈ F := F.smul_mem _ hc'F
  have hfg : polar Q f g = 1 := by
    rw [hg, polar_smul_right]
    exact inv_mul_cancel₀ hc'
  have hff : polar Q f f = 0 := by
    rw [polar_self, hfQ]
    simp [h2]
  set Φ : K × K → V := fun p => p.2 • f + p.1 • g with hΦ
  have hQΦ : ∀ p : K × K, Q (Φ p) = p.1 * (p.1 * Q g + p.2) := by
    intro p
    simp only [hΦ]
    have hadd : ∀ x y : V, Q (x + y) = Q x + Q y + polar Q x y := fun x y => by
      simp only [polar]; ring
    rw [hadd, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hfg, hfQ]
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one]
    ring
  have hΦF : ∀ p, Φ p ∈ F := fun p => F.add_mem (F.smul_mem _ hfF) (F.smul_mem _ hgF)
  have hΦinj : Function.Injective Φ := by
    intro p p' h
    have h1 : (p.2 - p'.2) • f + (p.1 - p'.1) • g = 0 := by
      simp only [hΦ] at h
      rw [sub_smul, sub_smul]
      have := sub_eq_zero.2 h
      rw [← this]
      abel
    have h3 := congrArg (polar Q f) h1
    rw [polar_add_right, polar_smul_right, polar_smul_right, hff, hfg] at h3
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, polar_zero_right] at h3
    have hb : p.1 = p'.1 := sub_eq_zero.1 h3
    rw [hb, sub_self, zero_smul, add_zero] at h1
    have ha : p.2 = p'.2 := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hf0)
    exact Prod.ext hb ha
  have hΦsurj : ∀ v ∈ F, ∃ p, Φ p = v := by
    classical
    haveI := Fintype.ofFinite K
    let Φ' : K × K → F := fun p => ⟨Φ p, hΦF p⟩
    have hΦ'inj : Function.Injective Φ' := fun p p' h => hΦinj (congrArg Subtype.val h)
    have hcard : Nat.card (K × K) = Nat.card F := by
      rw [Nat.card_prod, CFSG.LocalAnalysis.GLTheoremA.D4T.card_submodule, hF2]
      ring
    haveI : Finite V := Module.finite_of_finite K
    haveI : Finite F := inferInstance
    have hsurj : Function.Surjective Φ' :=
      (Function.Injective.bijective_of_nat_card_le hΦ'inj hcard.ge).2
    intro v hv
    obtain ⟨p, hp⟩ := hsurj ⟨v, hv⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  have hset : ({v : V | Q v = 0} ∩ (F : Set V)) =
      Φ '' {p : K × K | p.1 * (p.1 * Q g + p.2) = 0} := by
    ext v
    constructor
    · rintro ⟨hv0, hvF⟩
      obtain ⟨p, rfl⟩ := hΦsurj v hvF
      exact ⟨p, by simpa [hQΦ] using hv0, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by simpa [hQΦ] using hp, hΦF p⟩
  rw [hset, Set.ncard_image_of_injective _ hΦinj, ← Nat.card_coe_set_eq]
  exact card_plane_zero (Q g)

omit [FiniteDimensional K V] in
theorem no_cube_root {K : Type} [Field K] [Finite K] [CharP K 2] (hQ3 : Nat.card K % 3 = 2) :
    ∀ c : K, c ^ 2 + c + 1 ≠ 0 := by
  intro c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have : (1 : K) ^ 2 + 1 + 1 = 2 + 1 := by ring
    rw [this, h2] at hc
    simp at hc
  set u : Kˣ := Units.mk0 c hc0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [hu] using hc3)
  have hu1 : u ≠ 1 := fun h => hc1 (by simpa [hu] using congrArg Units.val h)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard u
  rw [Nat.card_units] at hdvd
  have : 1 ≤ Nat.card K := Nat.card_pos
  omega

end Plane


end CFSG.LocalAnalysis.GLTheoremA.D4YF
