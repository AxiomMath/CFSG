module

public import CFSG.GH74.GLS.Stage4.T2P56Transfer
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open CFSG.Semidihedral CFSG.Wreathed

theorem not_sd_and_wreathed {S : Type} [Group S] {n m : ℕ} (hn : 4 ≤ n) (hm : 2 ≤ m)
    (hSD : Nonempty (S ≃* CFSG.Open.SemidihedralGroup n))
    (hW : Nonempty (S ≃* CFSG.Open.WreathedTwoGroup m)) : False := by
  obtain ⟨f⟩ := hSD
  obtain ⟨e⟩ := hW
  have hstr := wreath_center_involution_and_quaternion_coordinates m hm
  let ψ : CFSG.Open.SemidihedralGroup n ≃* Wreath (2 ^ m) := f.symm.trans e
  have hc1 : Nat.card (Subgroup.center (CFSG.Open.SemidihedralGroup n)) = 2 := center_card n hn
  have hc2 : Nat.card (Subgroup.center (Wreath (2 ^ m))) = 2 ^ m := by
    rw [hstr.center, Original.Z, Nat.card_zpowers, Original.orderOf_a]
  have hc : Nat.card (Subgroup.center (CFSG.Open.SemidihedralGroup n)) =
      Nat.card (Subgroup.center (Wreath (2 ^ m))) := by
    rw [← Subgroup.map_center_eq ψ, Subgroup.card_map_of_injective ψ.injective]
  rw [hc1, hc2] at hc
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem sylow_le_of_odd_index' {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hN : Odd N.index) (S : Sylow 2 X) : (S : Subgroup X) ≤ N := by
  intro s hs
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hodd : Odd (Nat.card (X ⧸ N)) := by rwa [Subgroup.index] at hN
  have h1 : orderOf (QuotientGroup.mk' N s) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hsn, map_one])
  have h2 : orderOf (QuotientGroup.mk' N s) ∣ Nat.card (X ⧸ N) := orderOf_dvd_natCard _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h3 : QuotientGroup.mk' N s = 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact orderOf_eq_one_iff.1 (by simpa using hi)
    · exfalso
      have h4 : 2 ∣ orderOf (QuotientGroup.mk' N s) := by
        rw [hi]; exact dvd_pow_self 2 hi0.ne'
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h4.trans h2))
  exact (QuotientGroup.eq_one_iff s).mp h3

theorem exists_sylow_of_layer {Y : Type} [Group Y] [Finite Y] {T : Type} [Group T]
    (hY : ∃ S : Sylow 2 Y, Nonempty (↥(S : Subgroup Y) ≃* T))
    (E : Subgroup (Y ⧸ pPrimeCore 2 Y)) [E.Normal] (hE : Odd E.index) :
    ∃ S : Sylow 2 ↥E, Nonempty (↥(S : Subgroup ↥E) ≃* T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card (pPrimeCore 2 Y)) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := Y)
    rwa [Nat.coprime_two_left] at hcop
  have : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  obtain ⟨Sb, ⟨e⟩⟩ := (hasSylowIso_quotient_iff (pPrimeCore 2 Y) hNodd T).1 hY
  have hSE : (Sb : Subgroup (Y ⧸ pPrimeCore 2 Y)) ≤ E := sylow_le_of_odd_index' hE Sb
  refine ⟨Sb.subtype hSE, ⟨?_⟩⟩
  rw [Sylow.coe_subtype]
  exact (Subgroup.subgroupOfEquivOfLe hSE).trans e

theorem eps_eq_one_of_layer {Y : Type} [Group Y] [Finite Y] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (E : Subgroup (Y ⧸ pPrimeCore 2 Y)) [E.Normal] (hEodd : Odd E.index)
    (hE : IsLnEps 3 ↥E ε (p ^ n))
    (hshape : (p ^ n % 4 = 3 ∧ HasSDSylow Y) ∨ (p ^ n % 4 = 1 ∧ HasWreathedSylow Y)) : ε = 1 := by
  rcases hε with h | h
  · exact h
  · exfalso
    subst h
    rcases hshape with ⟨h3, ⟨S, m, hm, ⟨e⟩⟩⟩ | ⟨h1, ⟨S, m, hm, ⟨e⟩⟩⟩
    · obtain ⟨S', ⟨e'⟩⟩ := exists_sylow_of_layer (T := CFSG.Open.SemidihedralGroup m) ⟨S, ⟨e⟩⟩ E hEodd
      have hcong : ((p ^ n : ℕ) : ℤ) ≡ -1 [ZMOD 4] := by
        unfold Int.ModEq; omega
      obtain ⟨m', hm', ⟨e''⟩⟩ := (Proofs2.ivk_4_4b ↥E (-1) p n hp hp2 hE S').2 hcong
      exact not_sd_and_wreathed hm hm' ⟨e'⟩ ⟨e''⟩
    · obtain ⟨S', ⟨e'⟩⟩ := exists_sylow_of_layer (T := CFSG.Open.WreathedTwoGroup m) ⟨S, ⟨e⟩⟩ E hEodd
      have hncong : ¬ ((p ^ n : ℕ) : ℤ) ≡ -1 [ZMOD 4] := by
        unfold Int.ModEq; omega
      obtain ⟨m', ⟨hm', ⟨e''⟩⟩⟩ := (Proofs2.ivk_4_4b ↥E (-1) p n hp hp2 hE S').1 hncong
      exact not_sd_and_wreathed hm' hm ⟨e''⟩ ⟨e'⟩

end CFSG.GH74.GLS.Stage4.Rest
