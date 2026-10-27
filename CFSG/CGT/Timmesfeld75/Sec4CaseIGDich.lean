module

public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG CFSG.Open CFSG.Goldschmidt

@[expose] def Goldschmidt1974 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X) (_ : A ≤ S)
    (_ : IsMulCommutative A)
    (_ : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A),
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
    pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K)

section OddCore

theorem odd_card_goldschmidtOddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (goldschmidtOddCore H)) := by
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := H))

variable {K : Type} [Group K] [Finite K]

theorem odd_card_oddCoreOf (M : Subgroup K) : Odd (Nat.card (oddCoreOf M)) := by
  have h := odd_card_goldschmidtOddCore ↥M
  have e : Nat.card (oddCoreOf M) = Nat.card (goldschmidtOddCore ↥M) :=
    (Nat.card_congr ((goldschmidtOddCore ↥M).equivMapOfInjective M.subtype
      M.subtype_injective).toEquiv).symm
  rw [e]
  exact h

omit [Finite K] in
theorem oddCoreOf_normal {M : Subgroup K} (hM : M.Normal) : (oddCoreOf M).Normal := by
  refine ⟨fun x hx k => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hchar : (goldschmidtOddCore ↥M).Characteristic := by
    rw [goldschmidtOddCore_eq_pPrimeCore]
    infer_instance
  let φ : MulAut ↥M := MulAut.conjNormal k
  have hmem : y ∈ (goldschmidtOddCore ↥M).comap φ.toMonoidHom := by
    rw [hchar.fixed φ]
    exact hy
  refine ⟨φ y, Subgroup.mem_comap.1 hmem, ?_⟩
  simp [φ]

end OddCore

section Dichotomy

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem exists_pow_two_pow_eq_one_of_mem_sylow (S : Sylow 2 K) {x : K}
    (hx : x ∈ (S : Subgroup K)) : ∃ j : ℕ, x ^ (2 ^ j) = 1 := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨x, hx⟩
  refine ⟨j, ?_⟩
  have h : orderOf x = 2 ^ j := by
    rw [← Subgroup.orderOf_mk x hx]
    exact hj
  rw [← h]
  exact pow_orderOf_eq_one x

omit [Finite K] in
theorem pow_two_pow_eq_one_of_le {x : K} {j e : ℕ} (h : x ^ (2 ^ j) = 1) (hje : j ≤ e) :
    x ^ (2 ^ e) = 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hje
  rw [pow_add, pow_mul, h, one_pow]

theorem normal_of_goldschmidt_of_no_layer (hG : Goldschmidt1974) (S : Sylow 2 K) (A : Subgroup K)
    (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : K, g⁻¹ * a * g ∈ (S : Subgroup K) → g⁻¹ * a * g ∈ A)
    (hlayer : goldschmidtLayer (↥(Subgroup.normalClosure (A : Set K)) ⧸
      goldschmidtOddCore ↥(Subgroup.normalClosure (A : Set K))) = ⊥)
    (hcent : ∀ n ∈ oddCoreOf (Subgroup.normalClosure (A : Set K)),
      ∀ m ∈ Subgroup.normalClosure (A : Set K), m * n = n * m) : A.Normal := by
  set M : Subgroup K := Subgroup.normalClosure (A : Set K) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨ha, hb, -⟩ := hG K S A hAS hAab hcl
  rw [hlayer, sup_bot_eq] at ha
  have hb' : (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) = ⊤ := by
    rw [hb, ha]
    exact top_sup_eq _
  refine ⟨fun x hx k => ?_⟩
  have hxM : x ∈ M := hAM hx
  have hyM : k * x * k⁻¹ ∈ M := hMn.conj_mem x hxM k
  have hπy : QuotientGroup.mk' (goldschmidtOddCore M) ⟨k * x * k⁻¹, hyM⟩ ∈
      (A.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [hb']
    exact Subgroup.mem_top _
  obtain ⟨a, haA, hae⟩ := Subgroup.mem_map.1 hπy
  have hn : a⁻¹ * ⟨k * x * k⁻¹, hyM⟩ ∈ goldschmidtOddCore M := QuotientGroup.eq.1 hae
  have haA' : (a : K) ∈ A := Subgroup.mem_subgroupOf.1 haA
  set n : K := (a : K)⁻¹ * (k * x * k⁻¹) with hndef
  have hnO : n ∈ oddCoreOf M := ⟨_, hn, by simp [hndef]⟩
  have hcomm : Commute (a : K) n := hcent n hnO (a : K) a.2
  have hy : k * x * k⁻¹ = (a : K) * n := by rw [hndef]; group
  obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem_sylow S (hAS hx)
  obtain ⟨i, hi⟩ := exists_pow_two_pow_eq_one_of_mem_sylow S (hAS haA')
  have hxe : x ^ (2 ^ (i + j)) = 1 := pow_two_pow_eq_one_of_le hj (Nat.le_add_left j i)
  have hae' : (a : K) ^ (2 ^ (i + j)) = 1 := pow_two_pow_eq_one_of_le hi (Nat.le_add_right i j)
  have hye : (k * x * k⁻¹) ^ (2 ^ (i + j)) = 1 := by rw [conj_pow, hxe]; group
  have hne : n ^ (2 ^ (i + j)) = 1 := by
    have h1 : ((a : K) * n) ^ (2 ^ (i + j)) = (a : K) ^ (2 ^ (i + j)) * n ^ (2 ^ (i + j)) :=
      hcomm.mul_pow _
    rw [← hy, hye, hae', one_mul] at h1
    exact h1.symm
  have hdvd2 : orderOf n ∣ 2 ^ (i + j) := orderOf_dvd_of_pow_eq_one hne
  have hdvdO : orderOf n ∣ Nat.card (oddCoreOf M) := Subgroup.orderOf_dvd_natCard _ hnO
  have hcop : Nat.Coprime (2 ^ (i + j)) (Nat.card (oddCoreOf M)) :=
    (Nat.coprime_two_left.2 (odd_card_oddCoreOf M)).pow_left _
  have hone : orderOf n ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd2 hdvdO
  have hn1 : n = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hone)
  rw [hy, hn1, mul_one]
  exact haA'

end Dichotomy

end CFSG.CGT.Timmesfeld75
