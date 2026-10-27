module

public import CFSG.ClassicalInvolution.Asc77.AscE189Orth
public import CFSG.ClassicalInvolution.Asc77.AscE189Vac
public import CFSG.ClassicalInvolution.Asc77.AscE189SU4
public import CFSG.ClassicalInvolution.Asc77.AscE189D4Model
public import CFSG.ClassicalInvolution.Asc77.AscE189Lift
public import CFSG.ClassicalInvolution.Asc77.AscE189E4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

structure E189Rest (p : ℕ) [Fact p.Prime] : Prop where
  g2 : ∀ e, p ≠ 2 → StatedLieAdmissible .G2 0 p e → E189ModelAt p e .G2 0
  td4 : ∀ e, p ≠ 2 → StatedLieAdmissible .trialityD4 0 p e → E189ModelAt p e .trialityD4 0

variable {p : ℕ} [Fact p.Prime]

theorem e189Model_of_rest {f : ℕ} (h : E189Rest p) : E189Model p f := by
  intro hp hq t n e hfund hadm hexp
  have hef : t ≠ .trialityD4 → e = f := fun ht => hexp.resolve_right fun h' => ht h'.1
  have hq' : t ≠ .trialityD4 → 5 ≤ p ^ e := fun ht => by rw [hef ht]; exact hq
  cases t with
  | PSL =>
    have hq4 := hq' (by decide)
    by_cases hn2 : n = 2
    · subst hn2
      exact e189ModelAt_PSL_two hadm
    by_cases hn4 : n = 4
    · subst hn4
      exact e189ModelAt_psl_four hp hq4
    refine e189ModelAt_of_noTwinRow hp hq4 .PSL n hfund hadm (by decide) (by decide)
      (fun h' => hn2 h'.2) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4, hn4]
  | PSU =>
    have hq4 := hq' (by decide)
    by_cases hn4 : n = 4
    · subst hn4
      exact e189ModelAt_psu_four hp hadm
    refine e189ModelAt_of_noTwinRow hp hq4 .PSU n hfund hadm (by decide) (by decide)
      (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4, hn4]
  | PSp =>
    have hq4 := hq' (by decide)
    by_cases hn2 : n = 2
    · subst hn2
      exact e189ModelAt_psp_two hp hq4 hadm
    refine e189ModelAt_of_noTwinRow hp hq4 .PSp n hfund hadm (by decide) (by decide)
      (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4, hn2]
  | POmegaOdd =>
    exact e189ModelAt_odd hp (hq' (by decide)) hadm
  | POmegaPlus =>
    have hq4 := hq' (by decide)
    by_cases hn4 : n = 4
    · subst hn4
      exact e189ModelAt_plus_four hp hq4 hadm
    · exact e189ModelAt_plus_of_five_le hp hq4 hadm (by have := hadm.2.2; omega)
  | POmegaMinus =>
    exact e189ModelAt_minus hp (hq' (by decide)) hadm
  | G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact h.g2 e hp hadm
  | F4 =>
    refine e189ModelAt_of_noTwinRow hp (hq' (by decide)) .F4 n hfund hadm (by decide)
      (by decide) (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  | E6 =>
    refine e189ModelAt_of_noTwinRow hp (hq' (by decide)) .E6 n hfund hadm (by decide)
      (by decide) (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  | E7 =>
    refine e189ModelAt_of_noTwinRow hp (hq' (by decide)) .E7 n hfund hadm (by decide)
      (by decide) (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  | E8 =>
    refine e189ModelAt_of_noTwinRow hp (hq' (by decide)) .E8 n hfund hadm (by decide)
      (by decide) (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  | twistedE6 =>
    refine e189ModelAt_of_noTwinRow hp (hq' (by decide)) .twistedE6 n hfund hadm (by decide)
      (by decide) (fun h' => absurd h'.1 (by decide)) ?_ (fun h' => absurd h'.1 (by decide))
    simp [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2,
      ShapeTwinTD, ShapeTwinSU4]
  | trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact h.td4 e hp hadm
  | twistedB2 => exact absurd hfund (by simp [IsFundTag])
  | twistedG2 => exact absurd hfund (by simp [IsFundTag])
  | twistedF4 => exact absurd hfund (by simp [IsFundTag])
  | Tits => exact absurd hfund (by simp [IsFundTag])

theorem e189Sect_of_rest {f : ℕ} (h : E189Rest p) : E189Sect p f :=
  e189Sect_of_model (e189Model_of_rest h)

theorem e18_9_of_rest (f : ℕ) (h3 : E18_3 p f) (h6 : E18_6 p f) (h7 : E18_7 p f)
    (h4 : E187E4C p f) (h : E189Rest p) : E18_9 p f :=
  e18_9 p f h3 h6 h7 (E189E4.of_e187 h4) (e189Sect_of_rest h)

end CFSG.ClassicalInvolution.Asc77
