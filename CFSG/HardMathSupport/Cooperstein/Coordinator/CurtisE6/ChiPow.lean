module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Rank1
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTypeE6

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem simpleRep_comp {G' L k V : Type*} [Group G'] [Group L] [Field k] [AddCommGroup V] [Module k V]
    (π : G' →* L) (hπ : Function.Surjective π) {ρ : Representation k L V} (hρ : IsSimpleRep ρ) :
    IsSimpleRep (ρ.comp π) := by
  refine ⟨hρ.1, fun W hW => hρ.2 W fun g w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  exact hW x w hw

theorem fixSub_comp {G' L k V : Type*} [Group G'] [Group L] [Field k] [AddCommGroup V] [Module k V]
    (π : G' →* L) (ρ : Representation k L V) (A : Subgroup G') :
    fixSub (ρ.comp π) A = fixSub ρ (A.map π) := by
  ext v
  simp only [mem_fixSub, Subgroup.mem_map]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem chi_pow_of_entries_cover (δ : ℕ)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    (hent : ∀ s i j, (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i)
    {y : Fin m → k} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (i : N6) (u : Kˣ) :
    χ (e6Data_valid.hm K i u) ^ (2 ^ δ) = χ (e6Data_valid.hm K i u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  set ty : Fin m → k := fun i => (y i) ^ (2 ^ δ) with hty
  have hy : ∀ g, ρ g ty = fun i => (ρ g y i) ^ (2 ^ δ) := fun g => (frob_act δ ρ hent g y).symm
  have hty_fix : ty ∈ (e6CoverData K).datum.fixU ρ := by
    intro x hx
    rw [hy, ht.1 x hx]
  have hty0 : ty ≠ 0 := by
    intro h0
    apply ht.2.1
    funext j
    have := congrFun h0 j
    simp only [hty, Pi.zero_apply] at this
    exact pow_eq_zero_iff (by positivity) |>.1 this
  obtain ⟨c, hc⟩ := (e6CoverData K).datum.fixU_eq_smul hρ hμ hty_fix
  have hh := e6_hm_mem_H (K := K) i u
  have e1 : ρ (e6Data_valid.hm K i u) ty = (χ (e6Data_valid.hm K i u) ^ (2 ^ δ)) • ty := by
    rw [hy, ht.2.2.1 _ hh]
    funext j
    simp [hty, mul_pow]
  have e2 : ρ (e6Data_valid.hm K i u) ty = χ (e6Data_valid.hm K i u) • ty := by
    rw [hc, map_smul, ht.2.2.1 _ hh, smul_comm]
  exact smul_left_injective k hty0 (e1.symm.trans e2)

theorem chi_hm_pow_card {ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)}
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {n : ℕ} (hK : Nat.card K = 2 ^ n) (i : N6)
    (u : Kˣ) : χ (e6Data_valid.hm K i u) ^ (2 ^ n) = χ (e6Data_valid.hm K i u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  have hpow : ∀ N : ℕ, χ (e6Data_valid.hm K i (u ^ N)) = χ (e6Data_valid.hm K i u) ^ N := by
    intro N
    induction N with
    | zero => rw [pow_zero, e6Data_valid.hm_one, pow_zero]; exact hμ.chi_one
    | succ N ih =>
      rw [pow_succ, e6Data_valid.hm_mul, hμ.chi_mul (e6_hm_mem_H i _) (e6_hm_mem_H i _), ih,
        pow_succ]
  have h1 : u ^ (2 ^ n - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := u)
    rwa [Nat.card_units, hK] at this
  have h2 : χ (e6Data_valid.hm K i u) ^ (2 ^ n - 1) = 1 := by
    rw [← hpow, h1, e6Data_valid.hm_one]
    exact hμ.chi_one
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc χ (e6Data_valid.hm K i u) ^ (2 ^ n)
      = χ (e6Data_valid.hm K i u) ^ (2 ^ n - 1) * χ (e6Data_valid.hm K i u) := by
        rw [← pow_succ]; congr 1; omega
    _ = χ (e6Data_valid.hm K i u) := by rw [h2, one_mul]

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
