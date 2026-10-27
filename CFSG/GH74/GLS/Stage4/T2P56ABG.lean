module

public import CFSG.GH74.GLS.Stage4.T2P56Transfer
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.GH74.GLS.LU.Local.L3Cover

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

theorem pow_dvd_card_of_isLnEps {E : Type} [Group E] {p n : ℕ} (hp : p.Prime) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (h : IsLnEps 3 E ε (p ^ n)) : p ^ (3 * n) ∣ Nat.card E := by
  rcases h with ⟨rfl, F, iF, iFin, hF, ⟨e⟩⟩ | ⟨rfl, F, iF, iFin, hF, ⟨e⟩⟩
  ·
    have hE : Nat.card E = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      Nat.card_congr (e.toEquiv.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.toEquiv)
    rw [hE, OrderReductions.LinearOrders.card_projectiveSpecialLinear F 3 (by norm_num), hF]
    have hprod : (∏ i ∈ Finset.Icc 2 3, ((p ^ n) ^ i - 1)) = ((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 - 1) := by
      rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    have hexp : 3 * (3 - 1) / 2 = 3 := by norm_num
    rw [hprod, hexp]
    set q : ℕ := p ^ n with hq
    have hd : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
      refine (Nat.gcd_dvd_right 3 (q - 1)).trans (Dvd.dvd.mul_right ?_ _)
      simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    have : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) =
        q ^ 3 * (((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)) := Nat.mul_div_assoc _ hd
    rw [this, hq, ← pow_mul, mul_comm n 3]
    exact Dvd.intro _ rfl
  ·
    have : Fact p.Prime := ⟨hp⟩
    have : Fintype F := Fintype.ofFinite F
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        rw [hF] at h2
        simp at h2
      · exact hn
    have hchar : CharP F p := charP_of_card_eq_prime_pow (f := 2 * n)
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
    set H : Subgroup (GL (Fin 3) F) := StatedSU 3 (p ^ n) F with hH
    set D : Subgroup ↥H := (StatedScalars (Fin 3) F).subgroupOf H with hD
    have hDn : D.Normal := inferInstance
    have hHcard : Nat.card H = (p ^ n) ^ 3 * ((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 + 1) := by
      rw [← LieType.Steinberg.card_SU_three (F := F) (p := p) (f := n) hF]
      exact (Nat.card_congr (LieType.Universal.Unitary.equivStatedSU (F := F) (p := p) (f := n) hF 3).toEquiv).symm
    have hDcard : Nat.card D = Nat.gcd 3 (p ^ n + 1) :=
      GH74.GLS.LU.Local.card_scalars_statedSU_three hp hn1 hF
    have hEcard : Nat.card E = Nat.card (↥H ⧸ D) :=
      Nat.card_congr (e.toEquiv)
    have hmul : Nat.card H = Nat.card (↥H ⧸ D) * Nat.card D :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup D
    have hcop : Nat.Coprime ((p ^ n) ^ 3) (Nat.card D) := by
      rw [hDcard]
      refine Nat.Coprime.pow_left 3 ?_
      refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (p ^ n + 1)) ?_
      exact (Nat.coprime_self_add_right.2 (Nat.coprime_one_right _))
    have hdvd : (p ^ n) ^ 3 ∣ Nat.card (↥H ⧸ D) * Nat.card D := by
      rw [← hmul, hHcard, mul_assoc]
      exact Dvd.intro _ rfl
    have := hcop.dvd_of_dvd_mul_right hdvd
    rw [hEcard, ← pow_mul, mul_comm n 3] at *
    exact this

theorem abgKFusion_of_layer (hL : SDWreathedLayer) : ABGKFusion := by
  intro G _ _ X hX hS p n hp hp2 h5 z hzX hz K hKX hzK hK hCK hfus
  have : Finite ↥X := inferInstance
  let z' : ↥X := ⟨z, hzX⟩
  have hz'2 : orderOf z' = 2 := by rw [← hz]; exact Subgroup.orderOf_mk z hzX
  let K' : Subgroup ↥X := K.subgroupOf X
  have hzK' : z' ∈ K' := hzK
  have hK' : HasSL2Model ↥K' (fun q => q = p ^ n) := by
    obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := hK
    exact ⟨F, iF, iFin, hF, ⟨(Subgroup.subgroupOfEquivOfLe hKX).trans e⟩⟩
  have hCK' : ∀ c : ↥X, c * z' = z' * c → ∀ k ∈ K', c * k * c⁻¹ ∈ K' := by
    intro c hc k hk
    have hc' : (c : G) * z = z * (c : G) := congrArg Subtype.val hc
    exact hCK c c.2 hc' k hk
  have hfus' : ∃ a : ↥X, a * z' * a⁻¹ ≠ z' ∧ (a * z' * a⁻¹) * z' = z' * (a * z' * a⁻¹) := by
    obtain ⟨a, haX, ha1, ha2⟩ := hfus
    refine ⟨⟨a, haX⟩, ?_, ?_⟩
    · intro h
      exact ha1 (congrArg Subtype.val h)
    · exact Subtype.ext ha2
  obtain ⟨E, -, -, -, hE⟩ := layer_of_quotient hL hX hS hp hp2 (by omega) hz'2 hzK' hK' hCK' hfus'
  have h3 : p ^ (3 * n) ∣ Nat.card E := by
    rcases hE with ⟨ε, hε, hEε⟩ | ⟨h3, -⟩
    · exact pow_dvd_card_of_isLnEps hp hε hEε
    · omega
  have h4 : Nat.card E ∣ Nat.card (↥X ⧸ pPrimeCore 2 ↥X) := Subgroup.card_subgroup_dvd_card E
  have h5' : Nat.card (↥X ⧸ pPrimeCore 2 ↥X) ∣ Nat.card ↥X :=
    ⟨Nat.card (pPrimeCore 2 ↥X), Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  exact h3.trans (h4.trans h5')

end CFSG.GH74.GLS.Stage4.Rest
