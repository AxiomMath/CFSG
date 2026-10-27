module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharF4
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section S13604


theorem toralCentralizer_eq_toralRootGroup_F4_three (K : Type) [Field K]
    (a : Fin Tag.F4.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    toralCentralizer Tag.F4 K a = toralRootGroup Tag.F4 K a :=
  toralCentralizer_eq_toralRootGroup_of_stabilizer_le _ K a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a h3).le

theorem toral_centralizer_connected_F4_three (k : Type) [Field k] [IsAlgClosed k]
    (a : Fin Tag.F4.rank → kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    IsConnectedAlgebraicSubgroup k (toralCentralizerPointSubgroup Tag.F4 k a) :=
  (toral_centralizer_connected_of_stabilizer_le a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a h3).le).2

theorem toral_centralizer_Lang_F4_three (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [IsAlgClosed k] (hp3 : p ≠ 3) (a : Fin Tag.F4.rank → kˣ)
    (h3 : ∀ i, a i ^ 3 = 1) (e : ℕ) (he : 1 ≤ e) {Q : ModGL Tag.F4 k}
    (hQG : Q ∈ adjointGroup Tag.F4 k) {s : ℕ} (hs : ¬ 3 ∣ s)
    (hQ : Q * rootDiagUnit Tag.F4 a * Q⁻¹ = rootDiagUnit Tag.F4 a ^ s) :
    ∀ c ∈ toralCentralizer Tag.F4 k a, ∃ z ∈ toralCentralizer Tag.F4 k a,
      z⁻¹ * frobTwistGL Tag.F4 k p e Q z = c :=
  toral_centralizer_Lang_of_cube p hp3 a h3
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a h3).le e he hQG hs hQ

end S13604

section S13605


theorem toralCentralizer_eq_toralRootGroup_E7_three (K : Type) [Field K]
    (a : Fin Tag.E7.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    toralCentralizer Tag.E7 K a = toralRootGroup Tag.E7 K a :=
  toralCentralizer_eq_toralRootGroup_of_stabilizer_le _ K a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a h3).le

theorem toral_centralizer_connected_E7_three (k : Type) [Field k] [IsAlgClosed k]
    (a : Fin Tag.E7.rank → kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    IsConnectedAlgebraicSubgroup k (toralCentralizerPointSubgroup Tag.E7 k a) :=
  (toral_centralizer_connected_of_stabilizer_le a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a h3).le).2

theorem toral_centralizer_Lang_E7_three (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [IsAlgClosed k] (hp3 : p ≠ 3) (a : Fin Tag.E7.rank → kˣ)
    (h3 : ∀ i, a i ^ 3 = 1) (e : ℕ) (he : 1 ≤ e) {Q : ModGL Tag.E7 k}
    (hQG : Q ∈ adjointGroup Tag.E7 k) {s : ℕ} (hs : ¬ 3 ∣ s)
    (hQ : Q * rootDiagUnit Tag.E7 a * Q⁻¹ = rootDiagUnit Tag.E7 a ^ s) :
    ∀ c ∈ toralCentralizer Tag.E7 k a, ∃ z ∈ toralCentralizer Tag.E7 k a,
      z⁻¹ * frobTwistGL Tag.E7 k p e Q z = c :=
  toral_centralizer_Lang_of_cube p hp3 a h3
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a h3).le e he hQG hs hQ

end S13605

section S13691


theorem toralCentralizer_eq_toralRootGroup_E8_three (K : Type) [Field K]
    (a : Fin Tag.E8.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    toralCentralizer Tag.E8 K a = toralRootGroup Tag.E8 K a :=
  toralCentralizer_eq_toralRootGroup_of_stabilizer_le _ K a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a h3).le

theorem toral_centralizer_connected_E8_three (k : Type) [Field k] [IsAlgClosed k]
    (a : Fin Tag.E8.rank → kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    IsConnectedAlgebraicSubgroup k (toralCentralizerPointSubgroup Tag.E8 k a) :=
  (toral_centralizer_connected_of_stabilizer_le a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a h3).le).2

theorem toral_centralizer_Lang_E8_three (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [IsAlgClosed k] (hp3 : p ≠ 3) (a : Fin Tag.E8.rank → kˣ)
    (h3 : ∀ i, a i ^ 3 = 1) (e : ℕ) (he : 1 ≤ e) {Q : ModGL Tag.E8 k}
    (hQG : Q ∈ adjointGroup Tag.E8 k) {s : ℕ} (hs : ¬ 3 ∣ s)
    (hQ : Q * rootDiagUnit Tag.E8 a * Q⁻¹ = rootDiagUnit Tag.E8 a ^ s) :
    ∀ c ∈ toralCentralizer Tag.E8 k a, ∃ z ∈ toralCentralizer Tag.E8 k a,
      z⁻¹ * frobTwistGL Tag.E8 k p e Q z = c :=
  toral_centralizer_Lang_of_cube p hp3 a h3
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a h3).le e he hQG hs hQ

end S13691

end CFSG.HardMathSupport.Timmesfeld.Steinberg
