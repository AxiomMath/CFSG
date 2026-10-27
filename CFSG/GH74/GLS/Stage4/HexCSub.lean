module

public import CFSG.GH74.GLS.Stage4.HexCPos
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.GH74.GLS.Stage4.HexClass
public import CFSG.LieType.Steinberg.G2

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

@[expose] def Vsub (root : ℤ → Subgroup G) (i j : ℤ) : Subgroup G := ⨆ k ∈ intList i j, root k

theorem root_le_Vsub {i j k : ℤ} (hk1 : i ≤ k) (hk2 : k ≤ j) : root k ≤ Vsub root i j :=
  le_iSup₂_of_le (f := fun k (_ : k ∈ intList i j) => root k) k (mem_intList_iff.2 ⟨hk1, hk2⟩) le_rfl

theorem Vsub_mono {i j i' j' : ℤ} (h1 : i ≤ i') (h2 : j' ≤ j) :
    Vsub root i' j' ≤ Vsub root i j :=
  iSup₂_le fun k hk => by
    have := mem_intList_iff.1 hk
    exact root_le_Vsub (by omega) (by omega)

theorem Vsub_carrier (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 6) :
    ((Vsub root i j : Subgroup G) : Set G) = chainProd root (intList i j) :=
  (rgd2_octComm R).carrier_eq hi (by exact_mod_cast hj)

theorem Vsub_norm_left (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 < i) (hj : j ≤ 6) {x : G}
    (hx : x ∈ root (i - 1)) {v : G} (hv : v ∈ Vsub root i j) : x * v * x⁻¹ ∈ Vsub root i j :=
  (rgd2_octComm R).conj_mem_left hi (by exact_mod_cast hj) hx hv

theorem Vsub_norm_right (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 ≤ i) (hj : j < 6) {x : G}
    (hx : x ∈ root (j + 1)) {v : G} (hv : v ∈ Vsub root i j) : x * v * x⁻¹ ∈ Vsub root i j :=
  (rgd2_octComm R).conj_mem_right hi (by exact_mod_cast hj) hx hv

theorem r2_mem_Vsub (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 5) {v : G}
    (hv : v ∈ Vsub root i j) : r₂ * v * r₂⁻¹ ∈ Vsub root (6 - j) (6 - i) := by
  refine conj_mem_of_forall_mem (P := {k | k ∈ intList i j}) (X := root)
    (M := Vsub root (6 - j) (6 - i)) (fun k hk y hy => ?_) hv
  have hk' := mem_intList_iff.1 hk
  have := (RGD2.mem_iff_r₂ R (i := k) (by omega) (by omega) y).1 hy
  exact root_le_Vsub (by omega) (by omega) this

theorem r2_inv_mem_Vsub (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 5) {v : G}
    (hv : v ∈ Vsub root i j) : r₂⁻¹ * v * r₂ ∈ Vsub root (6 - j) (6 - i) := by
  have gen : ∀ k ∈ {k : ℤ | k ∈ intList i j}, ∀ y ∈ root k,
      r₂⁻¹ * y * r₂⁻¹⁻¹ ∈ Vsub root (6 - j) (6 - i) := by
    intro k hk y hy
    have hk' := mem_intList_iff.1 hk
    have h6 : 6 - (6 - k) = k := by omega
    have h2 := (RGD2.mem_iff_r₂ R (i := 6 - k) (by omega) (by omega) (r₂⁻¹ * y * r₂)).2
    rw [h6] at h2
    have h3 : r₂ * (r₂⁻¹ * y * r₂) * r₂⁻¹ = y := by group
    rw [h3] at h2
    have hmem : r₂⁻¹ * y * r₂⁻¹⁻¹ ∈ root (6 - k) := by simpa using h2 hy
    exact root_le_Vsub (i := 6 - j) (j := 6 - i) (k := 6 - k) (by omega) (by omega) hmem
  simpa using conj_mem_of_forall_mem (P := {k | k ∈ intList i j}) (X := root) gen hv

end CFSG.GH74.GLS.Stage4.Hex
