module

public import CFSG.GH74.QTGen4.Recog.Ku.NStructB
public import CFSG.GH74.QTGen4.Recog.Ku.PolarityB

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem z_mul_z [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) : z * z = 1 := by
  have h2 := h.isElemAbelian_kuA.2 z h.z_mem_kuA
  rwa [pow_two] at h2

omit [Finite G] in
theorem mem_H_comm (h : KuHyp G T M H P z) {g : G} (hg : g ∈ H) : g * z = z * g := by
  rw [h.hCz, Subgroup.mem_centralizer_singleton_iff] at hg
  exact hg

omit [Finite G] in
theorem conj_H_z (h : KuHyp G T M H P z) {g : G} (hg : g ∈ H) : g * z * g⁻¹ = z := by
  rw [h.mem_H_comm hg]
  simp

omit [Finite G] in
theorem kuPolar_one_right (x : G) : kuPolar P H z x 1 = 0 := by
  unfold kuPolar
  have hp : kuPred P H z x 1 := by
    intro n _ _
    simp
  rw [if_pos hp]

theorem kuPolar_one_left (h : KuHyp G T M H P z) (y : G) : kuPolar P H z 1 y = 0 := by
  apply kuPolar_of_not_orbit
  rintro ⟨n, -, hn⟩
  apply h.z_ne_one
  have h1 : n * z = n * 1 := by
    rw [mul_one]
    exact mul_inv_eq_one.mp hn
  exact mul_left_cancel h1

theorem kuPolar_z_eq_zero_iff (h : KuHyp G T M H P z) (v : G) :
    kuPolar P H z z v = 0 ↔ v ∈ kuW P H := by
  unfold kuPolar
  by_cases hp : kuPred P H z z v
  · rw [if_pos hp]
    exact ⟨fun _ => (h.kuPred_z_iff v).mp hp, fun _ => rfl⟩
  · rw [if_neg hp]
    exact ⟨fun h1 => absurd h1 (by decide), fun hv => absurd ((h.kuPred_z_iff v).mpr hv) hp⟩

theorem exists_kuW_polar_zero [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ∃ z' ∈ kuW P H, z' ∉ Subgroup.zpowers z ∧ kuPolar P H z z' z = 0 := by
  obtain ⟨y, hyL, hyN, -, -, hE, -, -⟩ := h.exists_y
  have hyM : y ∈ M := oTwoUpper_le M hyL
  have hzV2 : z ∈ kuV2 T M := h.z_mem_kuV2
  have hz' : y * z * y⁻¹ ∈ kuV2 T M := (Subgroup.mem_normalizer_iff.mp hyN z).mp hzV2
  have hne1 : y * z * y⁻¹ ≠ 1 := by
    intro e
    apply h.z_ne_one
    have h1 : y * z = y * 1 := by
      rw [mul_one]
      exact mul_inv_eq_one.mp e
    exact mul_left_cancel h1
  have hnez : y * z * y⁻¹ ≠ z := by
    intro e
    exact h.z_ne_one (hE z hzV2 e)
  have hyA : y ∈ kuN P H :=
    h.M_inf_normalizer_V2_le_normalizer_kuA (Subgroup.mem_inf.mpr ⟨hyM, hyN⟩)
  have hz'W : y * z * y⁻¹ ∈ kuW P H := h.kuV2_le_kuW hz'
  have hz'z : y * z * y⁻¹ ∉ Subgroup.zpowers z := fun hc => by
    rcases KuZCore.mem_zpowers_cases h.z_mul_z hc with e | e
    · exact hne1 e
    · exact hnez e
  refine ⟨y * z * y⁻¹, hz'W, hz'z, ?_⟩
  have hyz : y⁻¹ * z * y ∈ kuV2 T M :=
    (Subgroup.mem_normalizer_iff.mp hyN (y⁻¹ * z * y)).mpr (by
      rw [show y * (y⁻¹ * z * y) * y⁻¹ = z by group]
      exact hzV2)
  exact (h.kuPolar_conj_eq_zero_iff hyA z).mpr (h.kuV2_le_kuW hyz)

theorem kuPolar_W_z [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {w : G} (hw : w ∈ kuW P H) :
    kuPolar P H z w z = 0 := by
  by_cases hwz : w ∈ Subgroup.zpowers z
  · rcases KuZCore.mem_zpowers_cases h.z_mul_z hwz with h1 | h1
    · rw [h1]
      exact h.kuPolar_one_left z
    · rw [h1]
      exact h.kuPolar_self z
  · obtain ⟨z', hz'W, hz'z, hz'0⟩ := h.exists_kuW_polar_zero
    obtain ⟨g, hg, hgw⟩ := h.H_transitive_kuW hw hwz hz'W hz'z
    have hgN : g ∈ kuN P H := h.H_le_normalizer_kuA hg
    have key := kuPolar_conj_conj (z := z) hgN w z
    rw [hgw, h.conj_H_z hg] at key
    rw [← key]
    exact hz'0

theorem kuPolar_A_z_eq_zero_iff [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {v : G} (hv : v ∈ kuA P H) :
    kuPolar P H z v z = 0 ↔ v ∈ kuW P H := by
  by_cases hv1 : v = 1
  · subst hv1
    exact ⟨fun _ => (kuW P H).one_mem, fun _ => h.kuPolar_one_left z⟩
  obtain ⟨n, hn, hnv⟩ := h.conj_transitive_kuA hv hv1
  subst hnv
  constructor
  · intro h0
    have h1 : n⁻¹ * z * n ∈ kuW P H := (h.kuPolar_conj_eq_zero_iff hn z).mp h0
    have hn' : n⁻¹ ∈ kuN P H := Subgroup.inv_mem _ hn
    have h2 : kuPolar P H z (n⁻¹ * z * n⁻¹⁻¹) z = 0 := by
      rw [inv_inv]
      exact h.kuPolar_W_z h1
    have h3 := (h.kuPolar_conj_eq_zero_iff hn' z).mp h2
    rw [inv_inv] at h3
    exact h3
  · intro hW
    exact h.kuPolar_W_z hW

theorem kuPolar_z_comm [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {v : G} (hv : v ∈ kuA P H) :
    kuPolar P H z z v = kuPolar P H z v z := by
  have hzero : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact hzero _ _ ((h.kuPolar_z_eq_zero_iff v).trans (h.kuPolar_A_z_eq_zero_iff hv).symm)

theorem kuPolar_symm [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {x y : G} (hx : x ∈ kuA P H) (hy : y ∈ kuA P H) :
    kuPolar P H z x y = kuPolar P H z y x := by
  by_cases hx1 : x = 1
  · subst hx1
    rw [h.kuPolar_one_left y, kuPolar_one_right y]
  obtain ⟨n, hn, hnx⟩ := h.conj_transitive_kuA hx hx1
  have hv : n⁻¹ * y * n ∈ kuA P H := inv_conj_mem_kuA hn hy
  have hyv : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
  have e1 : kuPolar P H z x y = kuPolar P H z z (n⁻¹ * y * n) := by
    have := kuPolar_conj_conj (z := z) hn z (n⁻¹ * y * n)
    rw [hyv, hnx] at this
    exact this
  have e2 : kuPolar P H z y x = kuPolar P H z (n⁻¹ * y * n) z := by
    have := kuPolar_conj_conj (z := z) hn (n⁻¹ * y * n) z
    rw [hyv, hnx] at this
    exact this
  rw [e1, e2]
  exact h.kuPolar_z_comm hv

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
