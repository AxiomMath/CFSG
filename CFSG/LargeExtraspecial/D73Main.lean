module

public import CFSG.LargeExtraspecial.D73Fusion
public import CFSG.LargeExtraspecial.D73Ident
public import CFSG.LargeExtraspecial.DWTransBNorm
public import CFSG.LargeExtraspecial.DWTransGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.D73

open Subgroup CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem nonempty_mulEquiv_SL_of_maxEA (hNode : NodeStatement) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {N : ℕ} (hN : 6 ≤ N)
    (h2 : 2 ^ (N * (N - 1) / 2) ∣ Nat.card G) (S : Setting G) (hw : S.width = N - 2)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG)
    (hxA : g * S.z * g⁻¹ ∉ A) : Nonempty (G ≃* SL(N, ZMod 2)) := by
  have hn4 : 4 ≤ S.width := by omega
  have := S.isElementaryAbelian_QG_inf_Qa (hA.conj_ne_z hxA)
  have hT := hA.maxEA_inf hM hxQ hxA
  have hTM := hA.M_le_normalizer_inf hM hxQ hxA hn4
  have hsurj := hT.conjLinear_surjective_of_conj (hA.inf_le_closure hM hxQ hxA hn4)
    fun _ hg' => hA.inf_le_Qa hM hxQ hxA hn4 hg'
  have hti := isTI_of_transitive hTM (MaxEA.transitive_of_surjective hT hsurj)
  have hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (N - 1) := by
    rw [hT.card_eq, hw]
    congr 1
    omega
  exact nonempty_mulEquiv_SL_of_ti hNode hnab hN _ hcard (hT.centralizer_eq hTM) hti h2

theorem nonempty_mulEquiv_SL_of_setting (hNode : NodeStatement) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {N : ℕ} (hN : 6 ≤ N) (z : G) (hz : orderOf z = 2)
    (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) {g : G}
    (hgQ : g * z * g⁻¹ ∈ (settingOfCorner hN z hz φ).QG) (hgz : g * z * g⁻¹ ≠ z) :
    Nonempty (G ≃* SL(N, ZMod 2)) := by
  set S := settingOfCorner hN z hz φ
  have hSz : S.z = z := settingOfCorner_z hN z hz φ
  have hw := width_settingOfCorner hN z hz φ
  have hnab := exists_ne_mul_comm hN z φ
  have h2 := two_pow_dvd_card hN z φ
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hx1 : g * z * g⁻¹ ≠ 1 := fun h => by
    have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    simp [hz1] at hz
  have hxQ : g * S.z * g⁻¹ ∈ S.QG := by rw [hSz]; exact hgQ
  by_cases hxA : g * z * g⁻¹ ∈ cornerA hN z φ
  · have hxB : g * S.z * g⁻¹ ∉ cornerB hN z φ := fun hB => by
      rw [hSz] at hB
      have h := (cornerA_inf_cornerB hN z hz φ) ▸ (mem_inf.mpr ⟨hxA, hB⟩)
      rcases (Setting.mem_zpowers_iff_of_mul_self hzz).mp h with h | h
      · exact hx1 h
      · exact hgz h
    exact nonempty_mulEquiv_SL_of_maxEA hNode hnab hN h2 S hw (maxEA_cornerB hN z hz φ)
      (M_le_normalizer_cornerB hN z hz φ) hxQ hxB
  · exact nonempty_mulEquiv_SL_of_maxEA hNode hnab hN h2 S hw (maxEA_cornerA hN z hz φ)
      (M_le_normalizer_cornerA hN z hz φ) hxQ (by rw [hSz]; exact hxA)

theorem dempwolffLn2Input_of (h35 : S14.AschbacherThreeTranspositionCore)
    (hNode : NodeStatement) : DempwolffLn2Input := by
  intro N hN G _ _ _ z hz ⟨φ⟩
  obtain ⟨g, hgQ, hgz⟩ := exists_conj_mem_QG h35 hN z hz φ
  exact nonempty_mulEquiv_SL_of_setting hNode hN z hz φ hgQ hgz

end CFSG.LargeExtraspecial.DW.D73
