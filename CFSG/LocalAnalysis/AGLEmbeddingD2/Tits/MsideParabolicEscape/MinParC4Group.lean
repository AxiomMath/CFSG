module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem exists_normalized_sylow_two {Y : Type*} [Group Y] [Finite Y] {N W : Subgroup Y}
    (hN : Group.IsNilpotent ↥N) (hW : W ≤ Subgroup.normalizer (N : Set Y)) :
    ∃ S : Subgroup Y, S ≤ N ∧ IsPGroup 2 S ∧ W ≤ Subgroup.normalizer (S : Set Y) ∧
      ∀ u ∈ N, (∃ k : ℕ, orderOf u = 2 ^ k) → u ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  haveI : (P : Subgroup ↥N).Normal := inferInstance
  haveI : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal P inferInstance
  refine ⟨(P : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map _, ?_, ?_⟩
  · exact hW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  · intro u hu ⟨k, hk⟩
    have hp : IsPGroup 2 (Subgroup.zpowers (⟨u, hu⟩ : ↥N)) := by
      refine IsPGroup.iff_orderOf.2 fun ⟨x, hx⟩ => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hd : orderOf ((⟨u, hu⟩ : ↥N) ^ m) ∣ 2 ^ k := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        have : (⟨u, hu⟩ : ↥N) ^ 2 ^ k = 1 := by
          apply Subtype.ext
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
          rw [← hk]; exact pow_orderOf_eq_one u
        rw [this, one_zpow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
      exact ⟨j, by rw [← hj, ← Subgroup.orderOf_coe]⟩
    obtain ⟨P', hP'⟩ := hp.exists_le_sylow
    haveI : Unique (Sylow 2 ↥N) := Sylow.unique_of_normal P inferInstance
    have : P' = P := Subsingleton.elim _ _
    subst this
    exact ⟨⟨u, hu⟩, hP' (Subgroup.mem_zpowers _), rfl⟩

theorem odd_action_trivial {Y : Type*} [Group Y] {W D S : Subgroup Y}
    (hDW : D ≤ W) (hWD : W ≤ Subgroup.normalizer (D : Set Y))
    (hodd : ∀ x ∈ W, Odd (orderOf x) → x ∈ D)
    (hS : IsPGroup 2 S) (hWS : W ≤ Subgroup.normalizer (S : Set Y))
    (hVD : ⁅pCoreOf 2 D, D⁆ = ⊥)
    {y : Y} (hy : y ∈ W) (hyodd : Odd (orderOf y)) {u : Y} (huS : u ∈ S) (huW : u ∈ W) :
    y * u * y⁻¹ = u := by
  have hyD : y ∈ D := hodd y hy hyodd
  set v : Y := y * u * y⁻¹ * u⁻¹ with hv
  have hvS : v ∈ S := by
    have h1 : y * u * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hWS hy) u).1 huS
    exact S.mul_mem h1 (S.inv_mem huS)
  have hvD : v ∈ D := by
    have h1 : u * y⁻¹ * u⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.1 (hWD huW) y⁻¹).1 (D.inv_mem hyD)
    have : v = y * (u * y⁻¹ * u⁻¹) := by rw [hv]; group
    rw [this]
    exact D.mul_mem hyD h1
  have hnormSD : ∀ d ∈ D, ∀ r ∈ S ⊓ D, d * r * d⁻¹ ∈ S ⊓ D := by
    intro d hd r hr
    obtain ⟨hr1, hr2⟩ := Subgroup.mem_inf.1 hr
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hWS (hDW hd)) r).1 hr1,
      D.mul_mem (D.mul_mem hd hr2) (D.inv_mem hd)⟩
  have hnorm : D ≤ Subgroup.normalizer ((S ⊓ D : Subgroup Y) : Set Y) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnormSD d hd x hx, fun hx => ?_⟩
    have := hnormSD d⁻¹ (D.inv_mem hd) _ hx
    simpa [mul_assoc] using this
  have hvV : v ∈ pCoreOf 2 D :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hS.to_inf_left
      (Subgroup.mem_inf.2 ⟨hvS, hvD⟩)
  have hc : ⁅v, y⁆ ∈ ⁅pCoreOf 2 D, D⁆ := Subgroup.commutator_mem_commutator hvV hyD
  rw [hVD, Subgroup.mem_bot, commutatorElement_def] at hc
  have h1 := mul_inv_eq_one.1 hc
  have hcomm : y * v = v * y := by
    have := congrArg (· * v) h1
    have h2 : v * y = y * v := by simpa [mul_assoc] using this
    exact h2.symm
  have hcm : Commute y v := hcomm
  have hyu : y * u * y⁻¹ = v * u := by rw [hv]; group
  have hpow : ∀ i : ℕ, y ^ i * u * (y ^ i)⁻¹ = v ^ i * u := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e1 : y ^ (i + 1) * u * (y ^ (i + 1))⁻¹ = y * (y ^ i * u * (y ^ i)⁻¹) * y⁻¹ := by
        group
      have e2 : y * v ^ i * y⁻¹ = v ^ i := by
        rw [(hcm.pow_right i).eq]; group
      calc y ^ (i + 1) * u * (y ^ (i + 1))⁻¹ = y * (v ^ i * u) * y⁻¹ := by rw [e1, ih]
        _ = (y * v ^ i * y⁻¹) * (y * u * y⁻¹) := by group
        _ = v ^ i * (v * u) := by rw [e2, hyu]
        _ = v ^ (i + 1) * u := by rw [pow_succ]; group
  have hm := hpow (orderOf y)
  rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at hm
  have hvm : v ^ orderOf y = 1 := by
    have : v ^ orderOf y * u = 1 * u := by rw [← hm, one_mul]
    exact mul_right_cancel this
  obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨v, hvS⟩
  have hs' : orderOf v = 2 ^ s := by rw [← hs, ← Subgroup.orderOf_coe]
  have hdvd : 2 ^ s ∣ orderOf y := hs' ▸ orderOf_dvd_of_pow_eq_one hvm
  have hcop : Nat.Coprime (2 ^ s) (orderOf y) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hyodd)
  have h1' : 2 ^ s = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hv1 : v = 1 := orderOf_eq_one_iff.1 (hs' ▸ h1')
  rw [hyu, hv1, one_mul]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
