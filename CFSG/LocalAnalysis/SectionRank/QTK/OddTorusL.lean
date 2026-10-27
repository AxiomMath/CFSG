module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Census (torusSL torusSL_injective coe_torusSL torusEntries
  rootsOfUnity_pow_eq_one card_fun_rootsOfUnity card_rootsOfUnity_of_dvd isElemAbelian_range
  le_localRank_quotient_of_commute diagGL torusEntries_compLeft torusEntries_of_gt prod_torusEntries
  torusEntries_injective)

variable {K : Type} [Field K]

@[expose] def twoSign (n : ℕ) (K : Type) [Field K] : Fin n → K :=
  fun i => if i.val < 2 then -1 else 1

theorem det_diagonal_twoSign {n : ℕ} (hn : 2 ≤ n) : (diagonal (twoSign n K)).det = 1 := by
  rw [det_diagonal]
  simp only [twoSign]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Fin.card_filter_val_lt,
    min_eq_right hn]
  norm_num

theorem twoSign_mul_self {n : ℕ} (i : Fin n) : twoSign n K i * twoSign n K i = 1 := by
  simp only [twoSign]
  split_ifs <;> simp

theorem diagonal_twoSign_mul_self {n : ℕ} :
    diagonal (twoSign n K) * diagonal (twoSign n K) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext twoSign_mul_self)

theorem twoSign_zero_ne_two (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 2 < n) :
    twoSign n K ⟨0, by omega⟩ ≠ twoSign n K ⟨2, hn⟩ := by
  simp only [twoSign]
  norm_num
  intro h
  apply h2
  linear_combination -h

@[expose] def twoSignSL {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] :
    SpecialLinearGroup (Fin n) K :=
  ⟨diagonal (twoSign n K), det_diagonal_twoSign hn⟩

@[expose] def twoSignGL (n : ℕ) (K : Type) [Field K] : GL (Fin n) K :=
  ⟨diagonal (twoSign n K), diagonal (twoSign n K), diagonal_twoSign_mul_self,
    diagonal_twoSign_mul_self⟩

theorem le_localRank_PSL_torus_odd [Finite K] (h2 : (2 : K) ≠ 0) {r m n : ℕ} (hr : r.Prime)
    (hrK : r ∣ Nat.card Kˣ) (hmn : m < n) (h2n : 2 < n) (hcen : m + 1 < n ∨ ¬ r ∣ n) :
    m ≤ localRank r (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set incl := (rootsOfUnity r K).subtype
  set φ := (torusSL m n hmn K).comp (incl.compLeft (Fin m))
  have hφ : Function.Injective φ :=
    (torusSL_injective hmn).comp fun s t hst => funext fun j => Subtype.ext (congrFun hst j)
  have hdiag : ∀ s, ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => ((incl (torusEntries (rootsOfUnity r K) m n s i) : Kˣ) : K) := by
    intro s
    change ((torusSL m n hmn K (incl.compLeft (Fin m) s) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = _
    rw [coe_torusSL, torusEntries_compLeft]
    rfl
  set t := twoSignSL (by omega : 2 ≤ n) K
  refine le_localRank_quotient_of_commute _ hr (E := φ.range)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) φ) ?_ ?_
    (t := t) ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxc⟩
    obtain ⟨c, hcn, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    rw [Fintype.card_fin] at hcn
    have hci : ∀ i, c = ((incl (torusEntries (rootsOfUnity r K) m n s i) : Kˣ) : K) := by
      intro i
      have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hc
      simp only [scalar_apply, diagonal_apply_eq, hdiag] at this
      exact this
    have hc1 : c = 1 := by
      rcases hcen with h | h
      · rw [hci ⟨m + 1, h⟩, torusEntries_of_gt _ (by simp), map_one, Units.val_one]
      · have hcr : c ^ r = 1 := by
          rw [hci ⟨0, by omega⟩, ← Units.val_pow_eq_pow_val, ← map_pow,
            rootsOfUnity_pow_eq_one, map_one, Units.val_one]
        have hg : c ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr h), pow_one]
          at hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hc, hc1, map_one]
    rfl
  · intro htc
    have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center htc (⟨0, by omega⟩ : Fin n)
    have h22 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨2, h2n⟩ ⟨2, h2n⟩) hs
    change scalar (Fin n) (diagonal (twoSign n K) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨2, h2n⟩
      ⟨2, h2n⟩ = diagonal (twoSign n K) ⟨2, h2n⟩ ⟨2, h2n⟩ at h22
    rw [scalar_apply, diagonal_apply_eq, diagonal_apply_eq, diagonal_apply_eq] at h22
    exact twoSign_zero_ne_two h2 h2n h22
  · rw [show t ^ 2 = 1 from Subtype.ext (by
      rw [pow_two]
      exact diagonal_twoSign_mul_self)]
    exact Subgroup.one_mem _
  · rintro _ ⟨s, rfl⟩
    refine Subtype.ext ?_
    change ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      diagonal (twoSign n K) = diagonal (twoSign n K) *
        ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)

end CFSG.SectionRank.QTK
