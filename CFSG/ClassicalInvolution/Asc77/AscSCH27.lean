module

public import CFSG.ClassicalInvolution.Asc77.AscSCH26
public import CFSG.ClassicalInvolution.Asc77.AscSCH22

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.RankThree.Classical CFSG.RankThree.CentralLift CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem rhoV_le_normalizer [Finite K] :
    (rhoV : Multiplicative (K × K) →* SL(4, K)).range ≤
      Subgroup.normalizer
        ((rhoR : Multiplicative (K × K × K × K) →* SL(4, K)).range : Set SL(4, K)) := by
  rintro _ ⟨y, rfl⟩
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨x', rfl⟩ := hx
  have := rhoV_conj_rhoR y.toAdd x'.toAdd
  rw [ofAdd_toAdd, ofAdd_toAdd] at this
  rw [this]
  exact ⟨_, rfl⟩

theorem rhoR_inf_rhoV :
    (rhoR : Multiplicative (K × K × K × K) →* SL(4, K)).range ⊓
      (rhoV : Multiplicative (K × K) →* SL(4, K)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
  rw [← ofAdd_toAdd x, ← ofAdd_toAdd y] at hy
  have h1 := congrArg (fun g : SL(4, K) => (g : Matrix (Fin 4) (Fin 4) K)) hy
  simp only [coe_rhoR, coe_rhoV] at h1
  have e02 := congrFun (congrFun h1 0) 2
  have e03 := congrFun (congrFun h1 0) 3
  have e12 := congrFun (congrFun h1 1) 2
  have e13 := congrFun (congrFun h1 1) 3
  simp [Vmat, Rmat] at e02 e03 e12 e13
  have hx : x.toAdd = 0 := Prod.ext e02.symm (Prod.ext e03.symm (Prod.ext e12.symm e13.symm))
  have hx1 : x = 1 := Multiplicative.toAdd.injective hx
  rw [hx1, map_one]
  exact Subgroup.one_mem _

theorem card_rhoR_range [Finite K] :
    Nat.card (rhoR : Multiplicative (K × K × K × K) →* SL(4, K)).range = Nat.card K ^ 4 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective rhoR_injective, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

theorem card_rhoV_range [Finite K] :
    Nat.card (rhoV : Multiplicative (K × K) →* SL(4, K)).range = Nat.card K ^ 2 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective rhoV_injective, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
  ring

theorem card_rhoR_sup_rhoV [Finite K] :
    Nat.card ((rhoR : Multiplicative (K × K × K × K) →* SL(4, K)).range ⊔
      (rhoV : Multiplicative (K × K) →* SL(4, K)).range : Subgroup SL(4, K)) =
      Nat.card K ^ 6 := by
  rw [card_sup_eq_mul rhoV_le_normalizer rhoR_inf_rhoV, card_rhoR_range, card_rhoV_range]
  ring

theorem factorization_card_sl4_three [Finite K] {f : ℕ} (hK : Nat.card K = 3 ^ f) (hf : 1 ≤ f) :
    (Nat.card SL(4, K)).factorization 3 = 6 * f := by
  have hc4 : Nat.card SL(4, K) = Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) *
      (Nat.card K ^ 4 - 1) := by
    rw [Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv, card_statedSL_four]
  have hq3 : Nat.card K % 3 = 0 := by
    rw [hK]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
  have hq : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hn2 : ¬ 3 ∣ Nat.card K ^ 2 - 1 := by
    have : Nat.card K ^ 2 % 3 = 0 := by rw [Nat.pow_mod, hq3]
    have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hn3 : ¬ 3 ∣ Nat.card K ^ 3 - 1 := by
    have : Nat.card K ^ 3 % 3 = 0 := by rw [Nat.pow_mod, hq3]
    have : 1 ≤ Nat.card K ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have hn4 : ¬ 3 ∣ Nat.card K ^ 4 - 1 := by
    have : Nat.card K ^ 4 % 3 = 0 := by rw [Nat.pow_mod, hq3]
    have : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have e2 : Nat.card K ^ 2 - 1 ≠ 0 := by
    have : 2 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have e3 : Nat.card K ^ 3 - 1 ≠ 0 := by
    have : 2 ≤ Nat.card K ^ 3 := by nlinarith [Nat.one_le_pow 2 (Nat.card K) (by omega)]
    omega
  have e4 : Nat.card K ^ 4 - 1 ≠ 0 := by
    have : 2 ≤ Nat.card K ^ 4 := by nlinarith [Nat.one_le_pow 3 (Nat.card K) (by omega)]
    omega
  have e6 : Nat.card K ^ 6 ≠ 0 := by positivity
  rw [hc4, fac_mul (by positivity) e4, fac_mul (by positivity) e3, fac_mul e6 e2, fac_zero hn2,
    fac_zero hn3, fac_zero hn4, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hK,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem dSL_conj_rhoR (τ : Kˣ) (hprod : ∏ i, ((![τ, τ, τ⁻¹, τ⁻¹] i : Kˣ) : K) = 1)
    (x : K × K × K × K) :
    diagSL ![τ, τ, τ⁻¹, τ⁻¹] hprod * rhoR (Multiplicative.ofAdd x) *
        (diagSL ![τ, τ, τ⁻¹, τ⁻¹] hprod)⁻¹ =
      rhoR (Multiplicative.ofAdd ((τ : K) ^ 2 * x.1, (τ : K) ^ 2 * x.2.1, (τ : K) ^ 2 * x.2.2.1,
        (τ : K) ^ 2 * x.2.2.2)) := by
  have hτ0 : (τ : K) ≠ 0 := τ.ne_zero
  have e0 : (![τ, τ, τ⁻¹, τ⁻¹] 0 : Kˣ) = τ := rfl
  have e1 : (![τ, τ, τ⁻¹, τ⁻¹] 1 : Kˣ) = τ := rfl
  have e2 : (![τ, τ, τ⁻¹, τ⁻¹] 2 : Kˣ) = τ⁻¹ := rfl
  have e3 : (![τ, τ, τ⁻¹, τ⁻¹] 3 : Kˣ) = τ⁻¹ := rfl
  have hw : (τ : K) / ((τ⁻¹ : Kˣ) : K) = (τ : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    field_simp
  rw [diagSL_conj_rhoR, e0, e1, e2, e3, hw]

theorem dSL_conj_rhoV (τ : Kˣ) (hprod : ∏ i, ((![τ, τ, τ⁻¹, τ⁻¹] i : Kˣ) : K) = 1)
    (y : K × K) :
    diagSL ![τ, τ, τ⁻¹, τ⁻¹] hprod * rhoV (Multiplicative.ofAdd y) *
        (diagSL ![τ, τ, τ⁻¹, τ⁻¹] hprod)⁻¹ = rhoV (Multiplicative.ofAdd y) := by
  have hτ0 : (τ : K) ≠ 0 := τ.ne_zero
  have e0 : (![τ, τ, τ⁻¹, τ⁻¹] 0 : Kˣ) = τ := rfl
  have e1 : (![τ, τ, τ⁻¹, τ⁻¹] 1 : Kˣ) = τ := rfl
  have e2 : (![τ, τ, τ⁻¹, τ⁻¹] 2 : Kˣ) = τ⁻¹ := rfl
  have e3 : (![τ, τ, τ⁻¹, τ⁻¹] 3 : Kˣ) = τ⁻¹ := rfl
  rw [diagSL_conj_rhoV, e0, e1, e2, e3, div_self hτ0, div_self (τ⁻¹).ne_zero, one_mul, one_mul]

section Main

variable {E : Type*} [Group E]

theorem sl_four_perfect_ker_eq_bot_defining [Finite K] {f : ℕ} (hK : Nat.card K = 3 ^ f)
    (hq : 5 ≤ 3 ^ f) [Finite E] [Group.IsPerfect E] (π : E →* SL(4, K))
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) :
    π.ker = ⊥ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf τ = 3 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_units, hK]
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h2
    have h3 : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have := Nat.le_of_dvd (by norm_num) (hord ▸ h3)
    omega
  have hτ2K : (τ : K) ^ 2 ≠ 1 := fun h1 => hτ2 (Units.ext (by simpa using h1))
  have hprod : ∏ i, ((![τ, τ, τ⁻¹, τ⁻¹] i : Kˣ) : K) = 1 := by
    simp [Fin.prod_univ_four]
  set d : SL(4, K) := diagSL ![τ, τ, τ⁻¹, τ⁻¹] hprod with hd
  have hdcop : Nat.Coprime (orderOf d) 3 := by
    have h1 : d ^ Nat.card Kˣ = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hd, coe_diagSL, Matrix.diagonal_pow,
        Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [← Units.val_pow_eq_pow_val, pow_card_eq_one']
    exact coprime_of_dvd_card_units hp hK hf (orderOf_dvd_of_pow_eq_one h1)
  obtain ⟨a, ha, hacop⟩ := exists_coprime_lift hp π hπ hdcop
  refine ker_eq_bot_of_unipotent π hπ hC hCp
    (rhoR : Multiplicative (K × K × K × K) →* SL(4, K)).range
    (rhoV : Multiplicative (K × K) →* SL(4, K)).range rhoV_le_normalizer
    (fun x hx y hy => mul_comm_of_liftPair_eq_one hπ rhoR hC
      (rhoR_liftPair_eq_one hπ hC τ hCp hτ2) hx hy)
    (fun x hx y hy => mul_comm_of_liftPair_eq_one hπ rhoV hC
      (rhoV_liftPair_eq_one hπ hC hCp τ hτ2) hx hy)
    a hacop ?_ ?_ ?_ ?_
  · rw [ha]
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨x', rfl⟩ := hx
    have := dSL_conj_rhoR τ hprod x'.toAdd
    rw [ofAdd_toAdd] at this
    rw [hd, this]
    exact ⟨_, rfl⟩
  · rintro _ ⟨y, rfl⟩
    rw [ha]
    have := dSL_conj_rhoV τ hprod y.toAdd
    rw [ofAdd_toAdd] at this
    rw [hd, this]
  · intro r hr hrfix
    obtain ⟨x, rfl⟩ := hr
    rw [ha] at hrfix
    have h1 := dSL_conj_rhoR τ hprod x.toAdd
    rw [ofAdd_toAdd] at h1
    rw [hd, h1] at hrfix
    have h2 := congrArg Multiplicative.toAdd (rhoR_injective hrfix)
    have hz : ∀ z : K, (τ : K) ^ 2 * z = z → z = 0 := fun z hz => by
      have h4 : ((τ : K) ^ 2 - 1) * z = 0 := by linear_combination hz
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd (sub_eq_zero.1 h5) hτ2K
      · exact h5
    have h3 : x.toAdd = 0 :=
      Prod.ext (hz _ (congrArg Prod.fst h2)) (Prod.ext (hz _ (congrArg (fun p => p.2.1) h2))
        (Prod.ext (hz _ (congrArg (fun p => p.2.2.1) h2))
          (hz _ (congrArg (fun p => p.2.2.2) h2))))
    have h6 : x = 1 := Multiplicative.toAdd.injective h3
    rw [h6, map_one]
  · rw [card_rhoR_sup_rhoV, factorization_card_sl4_three hK hf, hK, ← pow_mul,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    omega

end Main

theorem defSL : DefSL := by
  intro K _ _ f hK hq E _ _ _ π hπ hC hCp
  let e := (specialLinearGroupEquivStatedSL 4 K).symm
  have hker : (e.toMonoidHom.comp π).ker = π.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  have := sl_four_perfect_ker_eq_bot_defining hK hq (e.toMonoidHom.comp π)
    (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ hCp)
  rwa [hker] at this

end CFSG.ClassicalInvolution.Asc77.SCH
