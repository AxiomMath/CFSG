module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralChevalley
public import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

theorem sum_cartan_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) :
    ∑ i, A k i * (Pi.single j 1 : Fin n → ℤ) i = A k j := by
  simp [Pi.single_apply]

theorem eq_one_of_mem_center_PSp (n p e : ℕ) (hp : p.Prime) (hfund : IsFundTag .PSp)
    (hadm : StatedLieAdmissible .PSp n p e)
    {R : Subgroup (modelUniv .PSp n p e hp).K}
    (hR : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p e hp).D)
    {r : (modelUniv .PSp n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv .PSp n p e hp).K) : r = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ n := hadm.2.2.1
  let k : Fin (modelUniv .PSp n p e hp).D.rank := ⟨n - 1, by show n - 1 < n; omega⟩
  have hk := isLongestRoot_single .PSp n p e hp hfund hadm k (show (n - 1) + 1 = n by omega)
  refine eq_one_of_mem_center_of_longest_node .PSp n p e hp (by simp) (by simp) hk ?_ hfund hadm
    hR hrR hrc
  intro r' hr' hrk
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (rootDatum n (GaloisField p e)).isFiniteType (Dv := (rootDatum n (GaloisField p e)).divisible)
    rfl
  have hE := CFSG.LieType.Steinberg.Sp.chevalleyExtras hn O _
    (CFSG.LieType.Steinberg.Sp.commutatorFormula O)
  let j : Fin n := ⟨n - 2, by omega⟩
  have hβ : (Pi.single j 1 : Fin n → ℤ) ∈ (rootDatum n (GaloisField p e)).roots :=
    Or.inl ⟨1, j, by simp; rfl⟩
  have hodd : Odd (∑ i, (rootDatum n (GaloisField p e)).cartan k i * (Pi.single j 1 : Fin n → ℤ) i) := by
    have h : ∑ i, (rootDatum n (GaloisField p e)).cartan k i * (Pi.single j 1 : Fin n → ℤ) i =
        cartanC n ⟨n - 1, by omega⟩ j := by
      exact sum_cartan_single _ k j
    rw [h]
    have : cartanC n ⟨n - 1, by omega⟩ j = -1 := by
      simp only [cartanC, Matrix.of_apply, j, Fin.ext_iff]
      split_ifs <;> omega
    rw [this]
    exact ⟨-1, by norm_num⟩
  exact eq_one_of_mem_center_of_mem_rankOne_chevalley hE hβ hodd hr' hrk

end CFSG.ClassicalInvolution.ModelFacts
