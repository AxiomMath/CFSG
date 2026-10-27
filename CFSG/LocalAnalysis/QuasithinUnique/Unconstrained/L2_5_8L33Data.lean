module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsTau
public meta import Mathlib
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsTau
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33DataInputs
public import Certificates.Certificate4048

public section

namespace CFSG.QuasithinUnique.Unc25L33

open CFSG.QuasithinUnique.Unc25K1

theorem mem_P0R_iff {x : R9} : x ∈ P0R ↔ ∃ i < 8, ∃ j < 2, x = rmul (rpw sa i) (rpw sb j) := by
  simp only [P0R, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩

theorem small_checks :
    rdet sa = 1 ∧ rdet sb = 1 ∧ rpw sa 8 = rone ∧ rmul sb sb = rone ∧
      rmul sb sa = rmul (rpw sa 3) sb ∧ P0R.Nodup ∧ P0R.length = 16 ∧ rone ∈ P0R ∧ sa ∈ P0R ∧
      sb ∈ P0R ∧ (∀ x ∈ P0R, ∀ y ∈ P0R, rmul x y ∈ P0R) ∧ (∀ x ∈ P0R, rpw x 16 = rone) ∧
      (∀ w ∈ W3, rdet w = 1) ∧
      (∀ t ∈ invsP0, ∀ s ∈ invsP0, t ≠ s → rmul t s = rmul s t →
        ∃ w ∈ W3, rpw w 3 = rone ∧ w ≠ rone ∧
          (∃ u ∈ [rone, t, s, rmul t s], rmul w t = rmul u w) ∧
          (∃ u ∈ [rone, t, s, rmul t s], rmul w s = rmul u w)) :=
  Certificates.certificate4048.1

theorem sa_det : rdet sa = 1 := small_checks.1

theorem sb_det : rdet sb = 1 := small_checks.2.1

theorem sa_pow : rpw sa 8 = rone := small_checks.2.2.1

theorem sb_sq : rmul sb sb = rone := small_checks.2.2.2.1

theorem sb_conj : rmul sb sa = rmul (rpw sa 3) sb := small_checks.2.2.2.2.1

theorem P0R_nodup : P0R.Nodup := small_checks.2.2.2.2.2.1

theorem P0R_length : P0R.length = 16 := small_checks.2.2.2.2.2.2.1

theorem rone_mem_P0R : rone ∈ P0R := small_checks.2.2.2.2.2.2.2.1

theorem sa_mem_P0R : sa ∈ P0R := small_checks.2.2.2.2.2.2.2.2.1

theorem sb_mem_P0R : sb ∈ P0R := small_checks.2.2.2.2.2.2.2.2.2.1

theorem mul_mem_P0R : ∀ x ∈ P0R, ∀ y ∈ P0R, rmul x y ∈ P0R :=
  small_checks.2.2.2.2.2.2.2.2.2.2.1

theorem pow16_check : ∀ x ∈ P0R, rpw x 16 = rone := small_checks.2.2.2.2.2.2.2.2.2.2.2.1

theorem W3_det : ∀ w ∈ W3, rdet w = 1 := small_checks.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem W3_check : ∀ t ∈ invsP0, ∀ s ∈ invsP0, t ≠ s → rmul t s = rmul s t →
    ∃ w ∈ W3, rpw w 3 = rone ∧ w ≠ rone ∧ (∃ u ∈ [rone, t, s, rmul t s], rmul w t = rmul u w) ∧
      (∃ u ∈ [rone, t, s, rmul t s], rmul w s = rmul u w) :=
  small_checks.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem normProp_check : ∀ g ∈ rawList, NormProp g :=
  Certificates.certificate4048.2.1

theorem centProp_check : ∀ g ∈ rawList, CentProp g :=
  Certificates.certificate4048.2.2.1

theorem fixProp_check : ∀ g ∈ rawList, FixProp g :=
  Certificates.certificate4048.2.2.2.1

theorem noFix_check : ∀ g ∈ rawList,
    ¬ (rmul g (rcof sa) = rmul sa g ∧ rmul g (rcof sb) = rmul sb g) :=
  Certificates.certificate4048.2.2.2.2

end CFSG.QuasithinUnique.Unc25L33
