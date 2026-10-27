module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2Twist
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.Open
  CFSG.SectionRank CFSG.GH74.Filter.Lie


@[expose] def e6W : SepWitness TwistTag.E6.tag 9 where
  word := ![([] : List (Fin 6)), ([3] : List (Fin 6)), ([3, 4, 2, 3] : List (Fin 6)),
    ([5, 3, 4, 1, 3, 2] : List (Fin 6)), ([1, 3, 4, 5, 2, 3, 4, 1, 3, 2] : List (Fin 6)),
    ([4] : List (Fin 6)), ([3] : List (Fin 6)), ([5, 4] : List (Fin 6)), ([3, 2] : List (Fin 6))]
  simple := ![(3 : Fin 6), (1 : Fin 6), (1 : Fin 6), (0 : Fin 6), (0 : Fin 6), (3 : Fin 6),
    (2 : Fin 6), (3 : Fin 6), (0 : Fin 6)]
  sep := ![([3] : List (Fin 6)), ([3, 1] : List (Fin 6)), ([3, 2, 1, 3, 4, 3, 2, 1] : List (Fin 6)),
    ([3, 2, 1, 3, 4, 5, 3, 2, 1, 0] : List (Fin 6)),
    ([0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1] : List (Fin 6)), ([3, 4] : List (Fin 6)),
    ([3, 2] : List (Fin 6)), ([3, 4, 5] : List (Fin 6)), ([3, 2, 0] : List (Fin 6))]

theorem e6W_check : e6W.check = true := by decide +kernel

@[expose] def e6π : Equiv.Perm (Fin 9) := Equiv.swap 5 6 * Equiv.swap 7 8

theorem e6_vec_rho : ∀ i : Fin 9, permLattice TwistTag.E6.perm (e6W.vec i) = e6W.vec (e6π i) := by
  decide +kernel

theorem e6_root_rho (i : Fin 9) : rootTwist TwistTag.E6 (e6W.root i) = e6W.root (e6π i) := by
  apply Subtype.ext
  rw [coe_rootTwist, RootWitness.root_val, RootWitness.root_val]
  exact e6_vec_rho i

theorem e6π_symm_apply (j : Fin 9) : e6π.symm j = ![0, 1, 2, 3, 4, 6, 5, 8, 7] j := by
  revert j
  decide +kernel

theorem card_fixed_ge {K : Type} [Field K] [Finite K] {e m n : ℕ} (hK : Nat.card K = 2 ^ e)
    (σ : K ≃+* K) (hσm : σ ^ m = 1) (hme : e = m * n) (hm : 0 < m) :
    2 ^ n ≤ Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) K) := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso
      have h1 := Finite.one_lt_card (α := K)
      rw [h, pow_zero] at hK
      omega
    · exact h
  obtain ⟨-, -, -, -, -, -, hfix⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 e Nat.prime_two he K hK
  obtain ⟨-, -, hcard, -⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hcard
  rw [hcard]
  have hord : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hσm
  have hpos : 0 < orderOf σ := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_dvd_iff] at hord
    omega
  have hle : orderOf σ ≤ m := Nat.le_of_dvd hm hord
  have h1 : e / m ≤ e / orderOf σ := Nat.div_le_div_left hle hpos
  have h2 : e / m = n := by
    rw [hme, Nat.mul_div_cancel_left _ hm]
  exact Nat.pow_le_pow_right (by norm_num) (h2 ▸ h1)

theorem exists_sq_ne_one (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 2 < Nat.card K) :
    ∃ u : Kˣ, (u : K) ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have hone : ∀ x : K, x ≠ 0 → x = 1 := by
    intro x hx
    have hsq : (x - 1) ^ 2 = 0 := by
      have h := hcon (Units.mk0 x hx)
      simp only [Units.val_mk0] at h
      linear_combination h + (1 - x) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq)
  classical
  let f : K → Bool := fun x => decide (x ≠ 0)
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · rw [hx, hy]
      · exfalso
        simp [f, hx, hy] at hxy
    · by_cases hy : y = 0
      · exfalso
        simp [f, hx, hy] at hxy
      · rw [hone x hx, hone y hy]
  have hle := Nat.card_le_card_of_injective f hinj
  simp at hle
  omega

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def e6Param (σ : K →+* K) (f : Fin 5 → K) (g : Fin 2 → K) : Fin 9 → Multiplicative K :=
  ![Multiplicative.ofAdd (f 0), Multiplicative.ofAdd (f 1), Multiplicative.ofAdd (f 2),
    Multiplicative.ofAdd (f 3), Multiplicative.ofAdd (f 4), Multiplicative.ofAdd (g 0),
    Multiplicative.ofAdd (σ (g 0)), Multiplicative.ofAdd (g 1), Multiplicative.ofAdd (σ (g 1))]

theorem e6Param_mem (σ : K →+* K) (hσ2 : ∀ c, σ (σ c) = c) (f : Fin 5 → K)
    (hf : ∀ j, σ (f j) = f j) (g : Fin 2 → K) :
    e6Param σ f g ∈ MonoidHom.eqLocus (paramTwist σ e6π) (MonoidHom.id _) := by
  show paramTwist σ e6π (e6Param σ f g) = e6Param σ f g
  funext j
  simp only [paramTwist, MonoidHom.coe_mk, OneHom.coe_mk, e6π_symm_apply]
  fin_cases j <;> simp [e6Param, hf, hσ2]

theorem twE6_rank {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ (2 * n))
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hσsurj : Function.Surjective σ)
    (hσ2 : ∀ c, σ (σ c) = c) (hu : ∃ u : Kˣ, (u : K) ^ 2 ≠ 1) :
    9 * n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (commutator (twistFixed TwistTag.E6 K σ))) := by
  classical
  obtain ⟨u, hu⟩ := hu
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ'2 : σ' ^ 2 = 1 := by
    ext c
    show σ' (σ' c) = c
    exact hσ2 c
  have hcardV := card_fixed_ge (e := 2 * n) (m := 2) (n := n) hK σ' hσ'2 (by ring) (by norm_num)
  set V := FixedPoints.subfield (Subgroup.zpowers σ') K with hVdef
  have hVσ : ∀ x : V, σ x.1 = x.1 := by
    intro x
    have hx : ∀ g : Subgroup.zpowers σ', g • x.1 = x.1 := x.2
    exact hx ⟨σ', Subgroup.mem_zpowers σ'⟩
  let E := MonoidHom.eqLocus (paramTwist σ e6π) (MonoidHom.id (Fin 9 → Multiplicative K))
  let ι : (Fin 5 → V) × (Fin 2 → K) → E := fun p =>
    ⟨e6Param σ (fun j => (p.1 j : K)) p.2, e6Param_mem σ hσ2 _ (fun j => hVσ (p.1 j)) p.2⟩
  have hι : Function.Injective ι := by
    rintro ⟨f, g⟩ ⟨f', g'⟩ h
    have h' : e6Param σ (fun j => (f j : K)) g = e6Param σ (fun j => (f' j : K)) g' :=
      congrArg Subtype.val h
    have key : ∀ k : Fin 9, e6Param σ (fun j => (f j : K)) g k =
        e6Param σ (fun j => (f' j : K)) g' k := fun k => congrFun h' k
    have hf : f = f' := by
      funext j
      apply Subtype.ext
      fin_cases j
      · simpa [e6Param] using key 0
      · simpa [e6Param] using key 1
      · simpa [e6Param] using key 2
      · simpa [e6Param] using key 3
      · simpa [e6Param] using key 4
    have hg : g = g' := by
      funext j
      fin_cases j
      · simpa [e6Param] using key 5
      · simpa [e6Param] using key 7
    rw [hf, hg]
  have hcardD : Nat.card ((Fin 5 → V) × (Fin 2 → K)) = (Nat.card V) ^ 5 * (Nat.card K) ^ 2 := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fun]
    simp
  have hEge : 2 ^ (9 * n) ≤ Nat.card E := by
    calc 2 ^ (9 * n) = (2 ^ n) ^ 5 * (2 ^ (2 * n)) ^ 2 := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
      _ ≤ (Nat.card V) ^ 5 * (Nat.card K) ^ 2 := by
          rw [hK]
          exact Nat.mul_le_mul (Nat.pow_le_pow_left hcardV 5) le_rfl
      _ = Nat.card ((Fin 5 → V) × (Fin 2 → K)) := hcardD.symm
      _ ≤ Nat.card E := Nat.card_le_card_of_injective ι hι
  have hEdvd : Nat.card E ∣ 2 ^ (18 * n) := by
    have h1 := Subgroup.card_subgroup_dvd_card E
    have h2 : Nat.card (Fin 9 → Multiplicative K) = 2 ^ (18 * n) := by
      rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K), hK,
        ← pow_mul, Nat.card_eq_fintype_card, Fintype.card_fin]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  obtain ⟨B', hB'⟩ := exists_subgroup_card_two_pow hEdvd hEge
  let B : Subgroup (Fin 9 → Multiplicative K) := B'.map E.subtype
  have hBcard : Nat.card B = 2 ^ (9 * n) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hB'
  have hBle : B ≤ E := Subgroup.map_subtype_le B'
  exact le_pRank_of_twistedWitness (t := TwistTag.E6) σ
    (e6_U_le_twistDerived hσsurj hσ2 hu) e6W e6W_check e6π e6_root_rho B hBle hBcard

end Count

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
