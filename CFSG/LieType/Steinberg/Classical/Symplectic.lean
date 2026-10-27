module

public import CFSG.LieType.Steinberg.Classical.Symplectic.Commutator
public import CFSG.LieType.Steinberg.Classical.Symplectic.Weyl
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LieType.Steinberg.Classical.Symplectic.Unipotent
public import CFSG.LieType.Steinberg.PartBAssembly
public import CFSG.LieType.Steinberg.Presentation
import all CFSG.LieType.Universal.SymplecticRoots

public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

theorem exists_root_of_stdVec (r : RootSubgroupIndex n) :
    ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = stdVec r := by
  obtain ⟨w, k, hw⟩ := isStdOrbit_stdVec n r
  exact ⟨_, mem_roots_of_stdVec hw.symm, hw⟩

theorem natAbs_commC_one_one {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (hr : α + β ∈ roots (isFiniteType_cartanC n) ∅)
    (h2 : toStd n (α + β) ⬝ᵥ toStd n (α + β) = 2) : (commC α β (1, 1)).natAbs = 1 := by
  obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
  rw [commC_one_one hαβ, Exz_eq hr', Exz_eq hs, entryAt_eq _ ht]
  rcases coeff11_spec (r := r) (s := s) (ht.trans (by rw [toStd_add', hr', hs])) with h | h
  · exact h
  · rw [ht, h2] at h
    exact absurd h.2 (by norm_num)

theorem natAbs_commC_one_two {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (hr : α + 2 • β ∈ roots (isFiniteType_cartanC n) ∅) : (commC α β (1, 2)).natAbs = 1 := by
  obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
  rw [commC_one_two hαβ, Exz_eq hr', Exz_eq hs, entryAt_eq _ ht]
  refine coeff21_spec (r := s) (s := r)
    (ht.trans (by rw [toStd_add', toStd_nsmul', hr', hs, add_comm])) ?_
  rw [hs, hr', add_comm]
  exact toStd_add_ne_zero hαβ

private theorem isUnit_of_natAbs_eq_one {z : ℤ} (h : z.natAbs = 1) : IsUnit (z : F) := by
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl
  · simp
  · simp

theorem rankTwo (hn : 2 ≤ n) {O : CommOrder (Φ n F)}
    {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ} (hC : CommutatorFormula (x n F) O C)
    (i : Fin n) :
    ∃ δ ∈ roots (isFiniteType_cartanC n) ∅, ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, δ + γ ≠ 0 ∧
      ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ (Pi.single i 1 : Fin n → ℤ) = δ + j • γ ∧
        IsUnit (C δ γ (1, j) : F) := by
  have hsingle := (Φ n F).single_mem i
  by_cases hk : i.val + 1 < n
  ·
    set i' : Fin n := ⟨i.val + 1, hk⟩
    obtain ⟨δ, hδ, hδs⟩ := exists_root_of_stdVec (.positiveSum i i' (by
      rw [Fin.lt_def]
      exact Nat.lt_succ_self _))
    obtain ⟨γ, hγ, hγs⟩ := exists_root_of_stdVec (.negativeLong i')
    have hsum : δ + γ = Pi.single i 1 := by
      apply toStd_inj
      rw [toStd_add', hδs, hγs, toStd_single_of_lt' hk]
      simp only [stdVec, two_nsmul]
      abel
    have hne : δ + γ ≠ 0 := by
      rw [hsum]
      exact ne_zero_of_mem_roots hsingle
    have hp : (1, 1) ∈ expPairs (Φ n F) δ γ :=
      ⟨one_pos, one_pos, by rwa [one_smul, one_smul, hsum]⟩
    refine ⟨δ, hδ, γ, hγ, hne, 1, Or.inl rfl, by rw [one_smul, hsum], ?_⟩
    rw [cast_eq_commC hC hδ hγ hne hp]
    refine isUnit_of_natAbs_eq_one (natAbs_commC_one_one hδ hγ hne (hsum ▸ hsingle) ?_)
    rw [hsum, toStd_single_of_lt' hk]
    simp [dotProduct_sub, Fin.ext_iff]
  ·
    have hi : 1 ≤ i.val := by omega
    set k : Fin n := ⟨i.val - 1, by omega⟩
    have hki : k ≠ i := Fin.ne_of_val_ne (by simp only [k]; omega)
    obtain ⟨δ, hδ, hδs⟩ := exists_root_of_stdVec (.positiveLong k)
    obtain ⟨γ, hγ, hγs⟩ := exists_root_of_stdVec (.difference i k hki.symm)
    have hsum : δ + 2 • γ = Pi.single i 1 := by
      apply toStd_inj
      rw [toStd_add', toStd_nsmul', hδs, hγs, toStd_single_of_not_lt' hk]
      simp only [stdVec, two_nsmul]
      abel
    have hne : δ + γ ≠ 0 := by
      intro h
      have h' := congrArg (fun v => toStd n v i) h
      simp only [toStd_add', hδs, hγs, toStd_zero'] at h'
      simp [stdVec, Ne.symm hki] at h'
    have hp : (1, 2) ∈ expPairs (Φ n F) δ γ :=
      ⟨one_pos, two_pos, by rwa [one_smul, hsum]⟩
    refine ⟨δ, hδ, γ, hγ, hne, 2, Or.inr rfl, hsum.symm, ?_⟩
    rw [cast_eq_commC hC hδ hγ hne hp]
    exact isUnit_of_natAbs_eq_one (natAbs_commC_one_two hδ hγ hne (hsum ▸ hsingle))

theorem chevalleyExtras (hn : 2 ≤ n) (O : CommOrder (Φ n F))
    (C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ) (hC : CommutatorFormula (x n F) O C) :
    ChevalleyExtras (rootDatum n F) F (x n F) C O where
  param := isParametrization
  comm := hC
  weyl i _ hβ := weyl i hβ
  rankOne i := rankOne i
  prodInjective f L hL hpos hsort := prodInjective f L hL hpos hsort
  rankTwo i := rankTwo hn hC i

theorem presentationB [Finite F] (hn : 2 ≤ n) : PresentationB (Φ := Φ n F) (x n F) :=
  presentationB_of rfl
    (fun O => ⟨commC, commC_natAbs_mem (F := F), commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras hn O C hC)
    (bijective_stPi_of (isCTGroupDatum n F) (steinbergExtras n F)).2

theorem redundantR2 [Finite F] (hn : 2 ≤ n) : RedundantR2 (Φ n F) (rootDatum n F).rootGroup :=
  redundantR2_of rfl (fun O => ⟨commC, commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras hn O C hC)
    (bijective_stPi_of (isCTGroupDatum n F) (steinbergExtras n F)).2

end CFSG.LieType.Steinberg.Sp
