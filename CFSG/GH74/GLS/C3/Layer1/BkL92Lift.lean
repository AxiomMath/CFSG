module

public import CFSG.GH74.GLS.C3.Layer1.BkL92Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mem_coset {K Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K) {k : G} (hk : k ∈ K)
    (hQt : ∀ q ∈ Q, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K) :
    ∃ c ∈ K, (∀ q ∈ Q, c * q = q * c) ∧ k⁻¹ * c ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set G := {x | x ∈ K ∧ k⁻¹ * x ∈ pPrimeCoreOf 2 K}
  have hS : ∀ q ∈ Q, ∀ x ∈ S, q * x * q⁻¹ ∈ S := by
    intro q hq x hx
    obtain ⟨hxK, hxO⟩ := hx
    refine ⟨hQK q hq x hxK, ?_⟩
    have hw : (⁅k, q⁆)⁻¹ ∈ pPrimeCoreOf 2 K := (pPrimeCoreOf 2 K).inv_mem (hQt q hq)
    have h1 := TwoThin.pPrimeCoreOf_normalized K (K.inv_mem hk) hw
    have h2 := pPrimeCoreOf_norm hQK hq hxO
    have h3 := (pPrimeCoreOf 2 K).mul_mem h1 h2
    convert h3 using 1
    simp only [commutatorElement_def]
    group
  let inst : MulAction ↥Q ↥S :=
    { smul := fun q x => ⟨(q : G) * x * (q : G)⁻¹, hS q q.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥Q) : G) * x * ((1 : ↥Q) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥Q) : G) * x * ((a * b : ↥Q) : G)⁻¹ =
          (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : ¬ 2 ∣ Nat.card ↥S := by
    let e : ↥(pPrimeCoreOf 2 K) ≃ ↥S :=
      { toFun := fun o => ⟨k * o, K.mul_mem hk (TwoThin.pPrimeCoreOf_le K o.2), by simp⟩
        invFun := fun x => ⟨k⁻¹ * x, x.2.2⟩
        left_inv := fun o => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    rw [← Nat.card_congr e]
    exact fun hd => (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd K))
      (even_iff_two_dvd.2 hd)
  obtain ⟨⟨x, hxK, hxO⟩, hfix⟩ := hQ2.nonempty_fixed_point_of_prime_not_dvd_card ↥S hcard
  refine ⟨x, hxK, fun q hq => ?_, hxO⟩
  have h : q * x * q⁻¹ = x := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨q, hq⟩)
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem exists_comm_mem_coset_of_fixed {K : Subgroup G} {y : G} (hy2 : orderOf y = 2)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) {k : G} (hk : k ∈ K)
    (hfix : y * k * y⁻¹ * k⁻¹ ∈ pPrimeCoreOf 2 K) :
    ∃ c ∈ K, c * y = y * c ∧ k⁻¹ * c ∈ pPrimeCoreOf 2 K := by
  have hZ2 : IsPGroup 2 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  have hq' : ∀ q ∈ zpowers y, q = 1 ∨ q = y := by
    intro q hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hq
    have h := zpow_mod_orderOf y j
    rw [hy2] at h
    push_cast at h
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left
      rw [← h, h0]
      simp
    · right
      rw [← h, h1]
      simp
  have hQK : ∀ q ∈ zpowers y, ∀ l ∈ K, q * l * q⁻¹ ∈ K := by
    intro q hq l hl
    rcases hq' q hq with h | h
    · rw [h]
      simpa using hl
    · rw [h]
      exact hyK l hl
  have hQt : ∀ q ∈ zpowers y, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := by
    intro q hq
    rcases hq' q hq with h | h
    · rw [h]
      simp
    · rw [h]
      have e : ⁅k, y⁆ = (y * k * y⁻¹ * k⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (pPrimeCoreOf 2 K).inv_mem hfix
  obtain ⟨c, hcK, hcQ, hcO⟩ := exists_fixed_mem_coset hZ2 hQK hk hQt
  exact ⟨c, hcK, hcQ y (Subgroup.mem_zpowers y), hcO⟩

theorem exists_mem_gammaIn_of_fixed {L M V : Subgroup G}
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hVM : V ≤ M) {v : G} (hvV : v ∈ V)
    (hv2 : orderOf v = 2) {l : G} (hl : l ∈ L) (hfix : v * l * v⁻¹ * l⁻¹ ∈ pPrimeCoreOf 2 L) :
    ∃ c ∈ gammaIn L V, l⁻¹ * c ∈ pPrimeCoreOf 2 L := by
  have hZ : zpowers v ≤ V := zpowers_le.mpr hvV
  have hZ1 : 1 ≤ pRank 2 ↥(zpowers v) := U1a.one_le_pRank_zpowers hv2
  obtain ⟨c, hcL, hcv, hcO⟩ := exists_comm_mem_coset_of_fixed hv2
    (fun k hk => hLn v (hVM hvV) k hk) hl hfix
  have hcN : c ∈ normalizer ((zpowers v : Subgroup G) : Set G) := by
    refine mem_normalizer_of_commute fun r hr => ?_
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hr
    have : Commute c v := hcv
    exact (this.zpow_right j).eq
  exact ⟨c, le_gammaIn hZ hZ1 ⟨hcN, hcL⟩, hcO⟩

end CFSG.GH74.GLS.C3.Layer1.Bk
