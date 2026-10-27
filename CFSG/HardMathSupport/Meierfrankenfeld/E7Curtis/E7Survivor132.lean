module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Reduction
public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.Adj132Bound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.BaseChangeModels
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7TorusGen
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.BcInvariants

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
  TensorProduct


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e7SurvivorBound_n1 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    E7SurvivorBound n1 K n := by
  classical
  intro k _ _ _ _ m ρ y χ b hρ hinj ht hb hχ A hA hel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    exact ⟨2 ^ t - 1, by omega⟩
  let ι : K →+* k := (algebraMap K k).comp (iterateFrobenius K 2 b)
  have hιz : ∀ z : K, ι z = algebraMap K k z ^ 2 ^ b := fun z => by
    simp [ι, iterateFrobenius_def, map_pow]
  let alg : Algebra K k := ι.toAlgebra
  have halg : ∀ z : K, @algebraMap K k _ _ alg z = ι z := fun z => rfl
  have htm := adj132_bc_isChevType (K := K) (k := k)
  have hd : ∀ (s : Fin Tag.E7.rank) (t : Kˣ),
      χ (dC .E7 K s t) = (fun g => @algebraMap K k _ _ alg (adjChi132 K g)) (dC .E7 K s t) := by
    intro s t
    simp only [halg, adjChi132_dC]
    by_cases hs : s = e7node10
    · subst hs
      simp only [↓reduceIte, zpow_one]
      rw [hιz]
      exact hχ t
    · simp only [hs, ↓reduceIte, zpow_zero, Units.val_one, map_one]
      have hsJ : s ∈ Finset.univ.erase n1 := Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩
      exact ((ht.2.2.2 s).1 hsJ).1 t
  have htm' : IsChevType .E7 K 2 exists_weyl_neg_E7 (@bcRep K _ k _ alg _ _ _ _ _ (adj132 K))
      (@bcVec K _ k _ alg _ _ _ (adj132Y : RootModule .E7 K ⧸ e7Z K)) χ
      (Finset.univ.erase n1) := by
    have hf := htm.1
    have hne := htm.2.1
    have hH := htm.2.2.1
    have hJ := htm.2.2.2
    refine ⟨hf, hne, fun h hh => ?_, fun i => ?_⟩
    · rw [hH h hh, chi_eq_of_dC_eq hodd ht htm hd h hh]
    · constructor
      · intro hi
        obtain ⟨h1, h2⟩ := (hJ i).1 hi
        exact ⟨fun t => (hd i t).trans (h1 t), h2⟩
      · rintro ⟨h1, h2⟩
        exact (hJ i).2 ⟨fun t => (hd i t).symm.trans (h1 t), h2⟩
  obtain ⟨β, hβ⟩ := iso_of_isChevType hρ (isSimpleRep_bc_adj132 (K := K) (k := k)) ht htm'
  have hm : m = 132 := by
    have h1 := β.finrank_eq
    rw [Module.finrank_fin_fun, Module.finrank_baseChange, finrank_adj132] at h1
    exact h1
  have hdim : Module.finrank k ↥(Representation.invariants (ρ.comp A.subtype)) =
      Module.finrank k ↥(Representation.invariants
        ((@bcRep K _ k _ alg _ _ _ _ _ (adj132 K)).comp A.subtype)) :=
    finrank_invariants_of_linearEquiv _ _ β fun g v => hβ g v
  have h1 : Module.finrank k ↥(Representation.invariants
        ((@bcRep K _ k _ alg _ _ _ _ _ (adj132 K)).comp A.subtype)) ≤
      Module.finrank K ↥(Representation.invariants ((adj132 K).comp A.subtype)) :=
    finrank_invariants_bcRep_le (K := K) (k := k) ((adj132 K).comp A.subtype)
  have h2 := adj132_fix_bound K A hA hel
  have hpow : Nat.card K ^ 132 = Nat.card K ^ m := by rw [hm]
  refine lt_of_le_of_lt ?_ (h2.trans_eq hpow)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Finite.card_pos (hdim ▸ h1))

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
