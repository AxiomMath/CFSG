module

public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Basic

variable {Γ : Type*} [Group Γ]

theorem s3l_natCard_comap_of_surjective {E H : Type*} [Group E] [Group H] (f : E →* H)
    (hf : Function.Surjective f) (P : Subgroup H) [Finite E] :
    Nat.card (P.comap f) = Nat.card f.ker * Nat.card P := by
  let g : P.comap f →* P := (f.comp (P.comap f).subtype).codRestrict P (fun x => x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ P
    rw [hx]
    exact y.2
  have hker : g.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change ((g x : P) = 1) ↔ f x = 1
    exact Subtype.ext_iff
  have h1 := Subgroup.card_ker_mul_card_of_surjective hg
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P.ker_le_comap f)).toEquiv] at h1
  exact h1.symm

theorem s3l_natCard_fusionOddCore_odd (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (Open.fusionOddCore X)) := by
  have h : Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem s3l_le_fusionOddCore_of_odd {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ Open.fusionOddCore X :=
  le_sSup ⟨inferInstance, hN⟩

theorem s3l_mem_zpowers_two {w : Γ} (hw : w * w = 1) {x : Γ} (hx : x ∈ zpowers w) :
    x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := hx
  have h2 : w ^ 2 = 1 := by rw [pow_two]; exact hw
  have : w ^ k = w ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    have : (w ^ (2 : ℤ)) = 1 := by exact_mod_cast h2
    rw [this, one_zpow, mul_one]
  show w ^ k = 1 ∨ w ^ k = w
  rw [this]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with h | h <;> rw [h]
  · left; simp
  · right; simp

theorem s3l_normal_zpowers {w : Γ} (hc : ∀ g : Γ, g * w = w * g) : (zpowers w).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  have : Commute g (w ^ k) := (show Commute g w from hc g).zpow_right k
  rw [this.eq]
  simp

end Basic

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem s3l_fusionOddCore_quot_zpowers {w : Γ} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hc : ∀ g : Γ, g * w = w * g) [hN : (zpowers w).Normal]
    (h : Open.fusionOddCore Γ = ⊥) : Open.fusionOddCore (Γ ⧸ zpowers w) = ⊥ := by
  set N : Subgroup Γ := zpowers w with hNdef
  let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = N := QuotientGroup.ker_mk' _
  set K := Open.fusionOddCore (Γ ⧸ N) with hK
  have hcardN : Nat.card N = 2 := by
    have hord : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
    rw [Nat.card_zpowers, hord]
  let M : Subgroup Γ := K.comap π
  have hMn : M.Normal := (inferInstance : K.Normal).comap π
  have hM : Nat.card M = 2 * Nat.card K := by
    rw [s3l_natCard_comap_of_surjective π hπ, hker, hcardN]
  have hKodd : Odd (Nat.card K) := s3l_natCard_fusionOddCore_odd _
  have hNM : N ≤ M := by
    intro x hx
    change π x ∈ K
    have : π x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [this]
    exact one_mem _
  let N' : Subgroup ↥M := N.subgroupOf M
  have hN'n : N'.Normal := Subgroup.Normal.subgroupOf hN M
  have hN'card : Nat.card N' = 2 := by
    rw [← hcardN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hindex : N'.index = Nat.card K := by
    have := N'.card_mul_index
    rw [hN'card, hM] at this
    omega
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, hindex]
    exact hKodd.coprime_two_left
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = Nat.card K := by
    have := hH.card_mul_card
    rw [hN'card, hM] at this
    omega
  have hHodd : Odd (Nat.card H) := hHcard ▸ hKodd
  have hodd_mem : ∀ m : M, Odd (orderOf m) → m ∈ H := by
    intro m hm
    obtain ⟨⟨n, h'⟩, hx, -⟩ := (Subgroup.isComplement_iff_existsUnique.1 hH) m
    have hn : (n : M).1 ∈ N := n.2
    rcases s3l_mem_zpowers_two hw2 hn with h1 | h1
    · have : (n : M) = 1 := Subtype.ext h1
      have hmh : m = (h' : M) := by rw [← hx]; simp [this]
      rw [hmh]
      exact h'.2
    · exfalso
      have hnw : (n : M) = ⟨w, hNM (mem_zpowers w)⟩ := Subtype.ext h1
      have hcomm : Commute (n : M) (h' : M) := by
        rw [hnw]
        exact Subtype.ext (hc _) |>.symm
      have hn2 : (n : M) * (n : M) = 1 := by rw [hnw]; exact Subtype.ext hw2
      have hnc : (n : M) ^ Nat.card H = (n : M) := by
        obtain ⟨j, hj⟩ := hHodd
        rw [hj, pow_succ, pow_mul, pow_two, hn2, one_pow, one_mul]
      have hhc : (h' : M) ^ Nat.card H = 1 := by
        rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
      have hpow : m ^ Nat.card H = (n : M) := by
        rw [← hx, hcomm.mul_pow, hnc, hhc, mul_one]
      have hdvd : orderOf (n : M) ∣ orderOf m := by
        rw [← hpow]
        exact orderOf_pow_dvd _
      have hord2 : orderOf (n : M) = 2 := by
        rw [hnw]
        exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hw2)
          (fun h1 => hw1 (congrArg Subtype.val h1))
      rw [hord2] at hdvd
      obtain ⟨k, hk⟩ := Odd.of_dvd_nat hm hdvd
      omega
  let H' : Subgroup Γ := H.map M.subtype
  have hH'card : Nat.card H' = Nat.card H :=
    Subgroup.card_map_of_injective (Subtype.coe_injective)
  have hH'n : H'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hm, hmH, rfl⟩ := hx
    have hgm : g * (hm : Γ) * g⁻¹ ∈ M := hMn.conj_mem (hm : Γ) hm.2 g
    let m' : M := ⟨g * (hm : Γ) * g⁻¹, hgm⟩
    have hord : orderOf m' = orderOf hm := by
      rw [← Subgroup.orderOf_coe m', ← Subgroup.orderOf_coe hm]
      have := MulEquiv.orderOf_eq (MulAut.conj g) (hm : Γ)
      simpa [MulAut.conj_apply, m'] using this
    have hodd' : Odd (orderOf m') := by
      rw [hord]
      exact Odd.of_dvd_nat hHodd (Subgroup.orderOf_dvd_natCard H hmH)
    exact ⟨m', hodd_mem m' hodd', rfl⟩
  have hH'odd : Odd (Nat.card H') := hH'card ▸ hHodd
  have hle : H' ≤ Open.fusionOddCore Γ := s3l_le_fusionOddCore_of_odd hH'odd
  rw [h, le_bot_iff] at hle
  have h1 : Nat.card H' = 1 := by rw [hle]; exact Subgroup.card_bot
  have hK1 : Nat.card K = 1 := by rw [← hHcard, ← hH'card, h1]
  exact Subgroup.card_eq_one.1 hK1

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
