module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem q8_invol_eq : ∀ q : QuaternionGroup 2, q * q = 1 → q ≠ 1 → q = QuaternionGroup.a 2 := by
  decide +kernel

theorem q8_card_sq : Fintype.card {q : QuaternionGroup 2 // q * q = QuaternionGroup.a 2} = 6 := by
  decide +kernel

theorem aut_fix_involution {Q : Type} [Group Q] (e : Q ≃* QuaternionGroup 2) {z : Q}
    (hz : e z = QuaternionGroup.a 2) (γ : MulAut Q) : γ z = z := by
  have h1 : γ z * γ z = 1 := by
    rw [← map_mul]
    have : z * z = 1 := by
      apply e.injective
      rw [map_mul, hz, map_one]
      decide +kernel
    rw [this, map_one]
  have h2 : γ z ≠ 1 := by
    intro h
    have : z = 1 := γ.injective (h.trans (map_one γ).symm)
    rw [this, map_one] at hz
    revert hz
    decide +kernel
  have h3 := q8_invol_eq (e (γ z)) (by rw [← map_mul, h1, map_one])
    (fun h => h2 (e.injective (h.trans (map_one e).symm)))
  exact e.injective (h3.trans hz.symm)

theorem natCard_sq {Q : Type} [Group Q] (e : Q ≃* QuaternionGroup 2) {z : Q}
    (hz : e z = QuaternionGroup.a 2) :
    Nat.card {q : Q // q * q = z} = 6 := by
  have h : Nat.card {q : Q // q * q = z} = Nat.card {q : QuaternionGroup 2 // q * q = QuaternionGroup.a 2} := by
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun q => ?_)
    constructor
    · intro h
      rw [← hz]
      change e q * e q = e z
      rw [← map_mul, h]
    · intro h
      apply e.injective
      have h' : e q * e q = QuaternionGroup.a 2 := h
      rw [map_mul, h', hz]
  rw [h, Nat.card_eq_fintype_card, q8_card_sq]

@[expose, instance_reducible] def prodAct (Q₁ Q₂ : Type) [Group Q₁] [Group Q₂] :
    MulAction (MulAut Q₁ × MulAut Q₂) (Q₁ × Q₂) where
  smul γ x := (γ.1 x.1, γ.2 x.2)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem exists_eq_of_odd_index {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂]
    (e₁ : Q₁ ≃* QuaternionGroup 2) (e₂ : Q₂ ≃* QuaternionGroup 2) {z₁ : Q₁} {z₂ : Q₂}
    (hz₁ : e₁ z₁ = QuaternionGroup.a 2) (hz₂ : e₂ z₂ = QuaternionGroup.a 2)
    {H : Type} [Group H] [Finite H] (ρ : H →* MulAut Q₁ × MulAut Q₂) (J : Subgroup H)
    (htrans : ∀ a a' : Q₁, ∀ b b' : Q₂, a * a = z₁ → a' * a' = z₁ → b * b = z₂ → b' * b' = z₂ →
      ∃ f ∈ J, (ρ f).1 a = a' ∧ (ρ f).2 b = b')
    (hodd : Odd J.index) : ∀ c : H, ∃ f ∈ J, ρ c = ρ f := by
  letI : MulAction (MulAut Q₁ × MulAut Q₂) (Q₁ × Q₂) := prodAct Q₁ Q₂
  have hΓ : Nat.card (MulAut Q₁ × MulAut Q₂) = 576 := by
    rw [Nat.card_prod, natCard_mulAut_of_quaternion e₁, natCard_mulAut_of_quaternion e₂]
  set SJ : Subgroup (MulAut Q₁ × MulAut Q₂) := J.map ρ with hSJ
  have hsq : ∀ {Q : Type} [Group Q] (e : Q ≃* QuaternionGroup 2) (z : Q),
      e z = QuaternionGroup.a 2 → ∃ a : Q, a * a = z := by
    intro Q _ e z hz
    refine ⟨e.symm (QuaternionGroup.a 1), ?_⟩
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hz]
    decide +kernel
  obtain ⟨a₀, ha₀⟩ := hsq e₁ z₁ hz₁
  obtain ⟨b₀, hb₀⟩ := hsq e₂ z₂ hz₂
  set x₀ : Q₁ × Q₂ := (a₀, b₀) with hx₀
  have horb : MulAction.orbit SJ x₀ = {x : Q₁ × Q₂ | x.1 * x.1 = z₁ ∧ x.2 * x.2 = z₂} := by
    ext x
    constructor
    · rintro ⟨⟨γ, hγ⟩, rfl⟩
      obtain ⟨f, -, rfl⟩ := Subgroup.mem_map.mp hγ
      show (ρ f).1 a₀ * (ρ f).1 a₀ = z₁ ∧ (ρ f).2 b₀ * (ρ f).2 b₀ = z₂
      constructor
      · rw [← map_mul, ha₀, aut_fix_involution e₁ hz₁]
      · rw [← map_mul, hb₀, aut_fix_involution e₂ hz₂]
    · rintro ⟨hx1, hx2⟩
      obtain ⟨f, hfJ, hf1, hf2⟩ := htrans a₀ x.1 b₀ x.2 ha₀ hx1 hb₀ hx2
      refine ⟨⟨ρ f, Subgroup.mem_map_of_mem ρ hfJ⟩, ?_⟩
      show ((ρ f).1 a₀, (ρ f).2 b₀) = x
      rw [hf1, hf2]
  have hT : (({x : Q₁ × Q₂ | x.1 * x.1 = z₁ ∧ x.2 * x.2 = z₂}) : Set (Q₁ × Q₂)).ncard = 36 := by
    have : ({x : Q₁ × Q₂ | x.1 * x.1 = z₁ ∧ x.2 * x.2 = z₂} : Set (Q₁ × Q₂)) =
        {a : Q₁ | a * a = z₁} ×ˢ {b : Q₂ | b * b = z₂} := by
      ext x; simp
    rw [this, Set.ncard_prod, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have h1 : Nat.card ↥({a : Q₁ | a * a = z₁} : Set Q₁) = 6 := natCard_sq e₁ hz₁
    have h2 : Nat.card ↥({b : Q₂ | b * b = z₂} : Set Q₂) = 6 := natCard_sq e₂ hz₂
    rw [h1, h2]
  have h36 : 36 ∣ Nat.card SJ := by
    have h1 := MulAction.index_stabilizer SJ x₀
    rw [horb, hT] at h1
    rw [← h1]
    exact Subgroup.index_dvd_card _
  have hidx : SJ.index ∣ 16 := by
    obtain ⟨m, hm⟩ := h36
    have h2 := Subgroup.card_mul_index SJ
    rw [hΓ, hm] at h2
    have h3 : 36 * (m * SJ.index) = 36 * 16 := by
      calc 36 * (m * SJ.index) = 36 * m * SJ.index := by ring
        _ = 576 := h2
        _ = 36 * 16 := by norm_num
    exact ⟨m, by rw [mul_comm]; exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h3).symm⟩
  have hmap := Subgroup.index_map J ρ
  have hdvd1 : (J ⊔ ρ.ker).index ∣ 16 :=
    (Dvd.intro _ hmap.symm).trans hidx
  have hdvd2 : (J ⊔ ρ.ker).index ∣ J.index := Subgroup.index_dvd_of_le le_sup_left
  have hone : (J ⊔ ρ.ker).index = 1 := by
    have hodd' : Odd (J ⊔ ρ.ker).index := hodd.of_dvd_nat hdvd2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show (J ⊔ ρ.ker).index ∣ 2 ^ 4 by simpa using hdvd1)
    rw [hk']
    rcases k with _ | k
    · rfl
    · exfalso
      have hev : Even (J ⊔ ρ.ker).index := by
        rw [hk']; exact Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero k⟩
      exact (Nat.not_even_iff_odd.2 hodd') hev
  have htop : J ⊔ ρ.ker = ⊤ := Subgroup.index_eq_one.mp hone
  intro c
  have hc : c ∈ J ⊔ ρ.ker := by rw [htop]; exact Subgroup.mem_top c
  obtain ⟨f, hf, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
  refine ⟨f, hf, ?_⟩
  rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec
