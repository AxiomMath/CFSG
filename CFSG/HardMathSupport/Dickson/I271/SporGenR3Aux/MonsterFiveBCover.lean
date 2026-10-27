module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus
public import CFSG.Certificates.Kernel.MonsterPcFive.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.I271.MonsterFiveB

open _root_.Timmesfeld.PcFive _root_.Timmesfeld.PcReg _root_.Timmesfeld.PcFus CFSG.Sporadic.Th CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus

section Generic

theorem sylowFive_data {G : Type} [Group G] [Finite G] {m : ℕ}
    (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m) (g : Fin 9 → G)
    (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1) :
    ∃ P : Subgroup G, Nat.card P = 5 ^ 9 ∧ orderOf (g 8) = 5 ∧ g 8 ∈ P ∧
      (∀ x ∈ P, x * g 8 = g 8 * x) ∧
      ∀ c ∈ P, (∀ y ∈ P, c * y = y * c) → c ∈ Subgroup.zpowers (g 8) := by
  have H := CFSG.KC.MonPcFive.pcHyp_of_rel hpow hcomm
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨Subgroup.closure (Set.range g), fiveSylow_card g hpow hcomm hz,
    orderOf_eq_prime H.rel.x5 hz, Subgroup.subset_closure ⟨8, rfl⟩,
    fun x hx => CFSG.KC.MonPcFive.comm_last_of_mem H hx, fiveSylow_center g hpow hcomm hz⟩

theorem fiveCover_of_targets {G : Type} [Group G] [Finite G] {m : ℕ}
    (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m) (g : Fin 9 → G)
    (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1)
    (hN : ∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!))
    {R : G → Prop} (hRc : ∀ x c, R x → R (c * x * c⁻¹))
    (hRp : ∀ x k, x ^ 5 = 1 → Nat.Coprime k 5 → R x → R (x ^ k))
    (hR : ∀ k < repIdx.size, R (prodAsc g (digitsOf 5 9 repIdx[k]!))) :
    ∀ s : G, orderOf s = 5 → R s :=
  fiveCover_of_invariant hcard hm g hpow hcomm hz hN hRc hRp hR

end Generic

end CFSG.HardMathSupport.Dickson.I271.MonsterFiveB
