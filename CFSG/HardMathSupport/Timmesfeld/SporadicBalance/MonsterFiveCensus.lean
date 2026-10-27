module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterGood
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
public import Certificates.Certificate13680

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus

open _root_.Timmesfeld.PcFive _root_.Timmesfeld.PcReg _root_.Timmesfeld.PcFus CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem lift_wordF_eq {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) (v : Array ℕ) :
    FreeGroup.lift g (wordF n v) = prodAsc g v := by
  unfold wordF prodAsc
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply, dite_eq_left hk', map_pow, FreeGroup.lift_apply_of]

section Census

variable {G : Type} [Group G] [Finite G] (g : Fin 9 → G)
  (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
  (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
  (hz : g 8 ≠ 1)
include hpow hcomm hz

theorem fiveSylow_card : Nat.card (Subgroup.closure (Set.range g)) = 5 ^ 9 :=
  (Certificates.certificate13680 g hpow hcomm hz).1.1

theorem fiveSylow_center : ∀ c ∈ Subgroup.closure (Set.range g),
    (∀ y ∈ Subgroup.closure (Set.range g), c * y = y * c) → c ∈ Subgroup.zpowers (g 8) :=
  (Certificates.certificate13680 g hpow hcomm hz).1.2

theorem fiveCensus {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m)
    (hN : ∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!)) :
    ∀ s : G, orderOf s = 5 → ∃ k < repIdx.size, prodAsc g (digitsOf 5 9 repIdx[k]!) ^ 5 = 1 ∧
      ∃ e : ℕ, 0 < e ∧ e < 5 ∧ ∃ c : G, c * s * c⁻¹ = prodAsc g (digitsOf 5 9 repIdx[k]!) ^ e :=
  (Certificates.certificate13680 g hpow hcomm hz).2 hcard hm hN

end Census

section Cover

variable {G : Type} [Group G] [Finite G]

theorem fiveCover_of_invariant {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m)
    (g : Fin 9 → G) (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1)
    (hN : ∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!))
    {R : G → Prop} (hRc : ∀ x c, R x → R (c * x * c⁻¹))
    (hRp : ∀ x k, x ^ 5 = 1 → Nat.Coprime k 5 → R x → R (x ^ k))
    (hR : ∀ k < repIdx.size, R (prodAsc g (digitsOf 5 9 repIdx[k]!))) :
    ∀ s : G, orderOf s = 5 → R s := by
  intro s hs
  obtain ⟨k, hk, hT, e, he0, he5, c, hc⟩ := fiveCensus g hpow hcomm hz hcard hm hN s hs
  have hcop : Nat.Coprime e 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    omega
  have h1 := hRp _ e hT hcop (hR k hk)
  rw [← hc] at h1
  have h2 := hRc _ c⁻¹ h1
  have e' : c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s := by group
  rwa [e'] at h2

theorem twoATwoCommuting_five_of {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m)
    (g : Fin 9 → G) (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1)
    (hN : ∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!))
    (hgood : ∀ k < repIdx.size, Good (prodAsc g (digitsOf 5 9 repIdx[k]!))) :
    TwoATwoCommuting 5 G := by
  intro s hs hn
  have hg : Good s := fiveCover_of_invariant hcard hm g hpow hcomm hz hN
    (fun x c h => (good_conj_iff x c).2 h)
    (fun x k hx hk h => (good_pow_iff (by norm_num) hx hk).2 h) hgood s hs
  rcases hg with h | h
  · exact absurd h hn
  · exact h

end Cover

theorem rel_of_relSet {G : Type*} [Group G] (g : Fin 9 → G)
    (hg : ∀ r ∈ relSet 5 (pwF 9 pw) (cwF 9 cw), FreeGroup.lift g r = 1) :
    (∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!) ∧
    ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]! := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have h := hg _ (Or.inl ⟨i, rfl⟩)
    simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, pwF, lift_wordF_eq] at h
    exact mul_inv_eq_one.1 h
  · have h := hg _ (Or.inr ⟨i, j, hij, rfl⟩)
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, cwF, lift_wordF_eq] at h
    exact mul_inv_eq_one.1 h

theorem twoATwoCommuting_five_of_rel {G : Type} [Group G]
    [Finite G] {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m) (g : Fin 9 → G)
    (hg : ∀ r ∈ relSet 5 (pwF 9 pw) (cwF 9 cw), FreeGroup.lift g r = 1) (hz : g 8 ≠ 1)
    (V : Array (Array (Array ℕ)))
    (hV : ∀ j < auts.size, ∀ i < 9, digitsOf 5 9 (auts[j]!)[i]! = (V[j]!)[i]!)
    (cN : ℕ → G)
    (hN : ∀ j < auts.size, ∀ (i : ℕ) (hi : i < 9),
      cN j * g ⟨i, hi⟩ * (cN j)⁻¹ = FreeGroup.lift g (wordF 9 (V[j]!)[i]!))
    (hgood : ∀ k < repIdx.size, Good (prodAsc g (digitsOf 5 9 repIdx[k]!))) :
    TwoATwoCommuting 5 G := by
  obtain ⟨hp, hc⟩ := rel_of_relSet g hg
  refine twoATwoCommuting_five_of hcard hm g hp hc hz (fun j hj => ⟨cN j, fun i hi => ?_⟩) hgood
  rw [hN j hj i hi, lift_wordF_eq, hV j hj i hi]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus
