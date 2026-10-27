module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Intrinsic
public import CFSG.ClassicalInvolution.Phan.StandardPair
public import CFSG.GH74.GLS.LU.StdPairLin
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

open Matrix Module CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem center_pow_three_su (hK : Nat.card K = (p ^ f) ^ 2) (k : Su K p f 3)
    (hk : k ∈ Subgroup.center (Su K p f 3)) : k ^ 3 = 1 := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK)
    (le_refl 3) hk
  have hu' : suMat k = Matrix.scalar (Fin 3) (u : K) := hu
  have hdet : (u : K) * ((u : K) * (u : K)) = 1 := by
    have h1 := det_suMat k
    rw [hu', Matrix.scalar_apply, Matrix.det_diagonal] at h1
    simpa [pow_three] using h1
  apply suMat_injective
  rw [pow_three, suMat_mul, suMat_mul, hu', ← map_mul, ← map_mul, hdet, map_one, suMat_one]


theorem isLongRootSU2_of_involution (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {z : Su K p f 3} (hz : z * z = 1) (hz1 : z ≠ 1) :
    IsLongRootSU2 K p f (by omega : 2 ≤ 3) (longRootGroupSU K p f (suMat z)) z := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hI : suMat z * suMat z = 1 := by rw [← suMat_mul, hz, suMat_one]
  have hdim : finrank K (eigSpace (suMat z) (-1)) = 2 :=
    finrank_eigSpace_neg_one_eq_two_of_det h2 hI (det_suMat z)
      (fun h => hz1 (suMat_injective (by rw [h, suMat_one])))
  obtain ⟨i, hi⟩ := exists_isLongRootSU2_of_nondeg hK hp (by omega : 2 ≤ 3)
    (nondeg_eigSpace_neg_one h2 z hI) hdim (L := longRootGroupSU K p f (suMat z))
    (fun x => by
      rw [perp_eigSpace_neg_one (isUnitaryInvolution_unitaryInvolution hK) h2 z hI]
      exact mem_longRootGroupSU_iff_fix hK hp hI)
  have hzmem : z ∈ longRootGroupSU K p f (suMat z) := by
    rw [mem_longRootGroupSU]
    refine ⟨rfl, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_one, hI, add_comm]
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz) hz1
  have := hi.eq_of_orderOf_eq_two hK hp hzmem hord
  subst this
  exact hi

theorem commutator_mem_longRootGroupSU (hp : p ≠ 2) {z : Su K p f 3} (hz : z * z = 1)
    (hdim : finrank K (eigSpace (suMat z) (-1)) = 2) {x y : Su K p f 3}
    (hx : x ∈ Subgroup.centralizer ({z} : Set (Su K p f 3)))
    (hy : y ∈ Subgroup.centralizer ({z} : Set (Su K p f 3))) :
    ⁅x, y⁆ ∈ longRootGroupSU K p f (suMat z) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hcent : ∀ g ∈ Subgroup.centralizer ({z} : Set (Su K p f 3)),
      suToSL (unitaryInvolution K p f) 3 g ∈
        Subgroup.centralizer ({suToSL (unitaryInvolution K p f) 3 z} : Set SL(3, K)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg z rfl]
  show suToSL (unitaryInvolution K p f) 3 ⁅x, y⁆ ∈ longRootGroup (suMat z)
  rw [map_commutatorElement]
  have hz' : ((suToSL (unitaryInvolution K p f) 3 z : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      suMat z := coe_suToSL z
  have := commutator_mem_longRootGroup h2 (z := suToSL (unitaryInvolution K p f) 3 z)
    (by rw [hz', ← suMat_mul, hz, suMat_one]) (by rw [hz']; exact hdim) (hcent x hx) (hcent y hy)
  rwa [hz'] at this


theorem natCard_su_two_eq {F : Type} [Field F] [Finite F] (hK : Nat.card K = (p ^ f) ^ 2)
    (hF : Nat.card F = p ^ f) : Nat.card (Su K p f 2) = Nat.card SL(2, F) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  have h1 := Nat.card_congr e.toEquiv
  rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, card_fixedSubfield hK] at h1
  rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two F, hF]
  exact h1.symm

theorem eq_map_longRootGroupSU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hF4 : 4 ≤ p ^ f) {X : Type} [Group X]
    (α : Su K p f 3 →* X) (hker : α.ker ≤ Subgroup.center (Su K p f 3)) {z : Su K p f 3}
    (hz : z * z = 1) (hz1 : z ≠ 1) {j : ℕ} (hj : j + 2 ≤ 3) (g : Su K p f 3)
    (hLj : longRootGroupSU K p f (suMat z) =
      (blockEmb K p f 3 2 j hj).range.map (MulAut.conj g).toMonoidHom)
    {U : Subgroup X} (hU : U ≤ α.range) (eU : SL(2, F) ≃* U)
    (haU : ∀ u ∈ U, u * α z = α z * u) :
    U = (longRootGroupSU K p f (suMat z)).map α := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hI : suMat z * suMat z = 1 := by rw [← suMat_mul, hz, suMat_one]
  have hdim : finrank K (eigSpace (suMat z) (-1)) = 2 :=
    finrank_eigSpace_neg_one_eq_two_of_det h2 hI (det_suMat z)
      (fun h => hz1 (suMat_injective (by rw [h, suMat_one])))
  have hperf : ⁅U, U⁆ = U :=
    commutator_eq_self_of_mulEquiv_perfect U
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F (by rw [hF]; exact hF4))
      eU
  have hUC : ∀ u ∈ U, ∃ x ∈ Subgroup.centralizer ({z} : Set (Su K p f 3)), α x = u := by
    intro u hu
    obtain ⟨x, rfl⟩ := hU hu
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_of_involution_lift α hker (center_pow_three_su hK) hz (haU _ hu)).symm
  have hCL : ⁅Subgroup.centralizer ({z} : Set (Su K p f 3)),
      Subgroup.centralizer ({z} : Set (Su K p f 3))⁆ ≤ longRootGroupSU K p f (suMat z) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_longRootGroupSU hp hz hdim hx hy
  have hle := le_map_of_commutator_le α hCL hperf hUC
  set α' : Su K p f 3 →* X := α.comp (MulAut.conj g).toMonoidHom with hα'
  have hinj : Function.Injective (α'.comp (blockEmb K p f 3 2 j hj)) :=
    comp_blockEmb_injective hK (ker_comp_mulEquiv_le_center hker _) hj (by omega) (le_refl 3)
  have hrange : (α'.comp (blockEmb K p f 3 2 j hj)).range =
      (longRootGroupSU K p f (suMat z)).map α := by
    rw [hLj, MonoidHom.range_eq_map, Subgroup.map_map, MonoidHom.range_eq_map, Subgroup.map_map]
  have hcard : Nat.card ↥((longRootGroupSU K p f (suMat z)).map α) =
      Nat.card (Su K p f 2) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfin : Finite ↥((longRootGroupSU K p f (suMat z)).map α) := by
    rw [← hrange]
    exact Finite.of_surjective (MonoidHom.rangeRestrict _) (MonoidHom.rangeRestrict_surjective _)
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [hcard, natCard_su_two_eq hK hF, Nat.card_congr eU.toEquiv])


theorem unitaryBlockStandardPair_of_central_involutions (hK : Nat.card K = (p ^ f) ^ 2)
    (hp : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hF4 : 4 ≤ p ^ f)
    {X : Type} [Group X] (α : Su K p f 3 →* X) (hker : α.ker ≤ Subgroup.center (Su K p f 3))
    {U V : Subgroup X} (hU : U ≤ α.range) (hV : V ≤ α.range) (eU : SL(2, F) ≃* U)
    (eV : SL(2, F) ≃* V) {a b : X} (ha : a ∈ U) (hb : b ∈ V) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (haU : ∀ u ∈ U, u * a = a * u) (hbV : ∀ v ∈ V, v * b = b * v)
    (hab : a ≠ b) (hcomm : a * b = b * a) :
    UnitaryBlockStandardPair K p f α.range U V ∧ ∃ x ∈ U, x * b ≠ b * x := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have ha1 : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
  have hb1 : b * b = 1 := by rw [← sq, ← hb2]; exact pow_orderOf_eq_one b
  obtain ⟨ta, hta2, htaa⟩ := exists_involution_lift α hker (center_pow_three_su hK) (hU ha) ha1
  obtain ⟨tb, htb2, htbb⟩ := exists_involution_lift α hker (center_pow_three_su hK) (hV hb) hb1
  have hta1 : ta ≠ 1 := fun h => by
    rw [h, map_one] at htaa
    rw [← htaa] at ha2
    simp at ha2
  have htb1 : tb ≠ 1 := fun h => by
    rw [h, map_one] at htbb
    rw [← htbb] at hb2
    simp at hb2
  have hc : Commute ta tb :=
    (commute_of_involution_lift α hker (center_pow_three_su hK) hta2 (g := tb)
      (by rw [htaa, htbb]; exact hcomm.symm)).symm
  have hne : ta ≠ tb := fun h => hab (by rw [← htaa, ← htbb, h])
  have h₁ := isLongRootSU2_of_involution hK hp hta2 hta1
  have h₂ := isLongRootSU2_of_involution hK hp htb2 htb1
  rcases inf_eq_bot_or_exists_conj_su hK hp (le_refl 3) h₁ h₂ hc hne with hV0 | ⟨g, e₁, e₂, -, hi₂⟩
  · exfalso
    have d1 := h₁.finrank_minusSpaceSU h2
    have d2 := h₂.finrank_minusSpaceSU h2
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (minusSpaceSU ta) (minusSpaceSU tb)
    rw [hV0, finrank_bot, d1, d2] at hsum
    have : finrank K ↥(minusSpaceSU ta ⊔ minusSpaceSU tb) ≤ 3 :=
      (Submodule.finrank_le _).trans (by simp)
    omega
  · have e₁' : longRootGroupSU K p f (suMat ta) =
        (blockEmb K p f 3 2 0 (by omega)).range.map (MulAut.conj g).toMonoidHom := by
      rw [← e₁, h₁.eq_longRootGroupSU h2]
    have e₂' : longRootGroupSU K p f (suMat tb) =
        (blockEmb K p f 3 2 1 (by omega)).range.map (MulAut.conj g).toMonoidHom := by
      rw [← e₂, h₂.eq_longRootGroupSU h2]
    have hU' := eq_map_longRootGroupSU hK hp hF hF4 α hker hta2 hta1 (by omega : 0 + 2 ≤ 3) g e₁' hU
      eU (by rw [htaa]; exact haU)
    have hV' := eq_map_longRootGroupSU hK hp hF hF4 α hker htb2 htb1 (by omega : 1 + 2 ≤ 3) g e₂' hV
      eV (by rw [htbb]; exact hbV)
    refine ⟨⟨α, g⁻¹, rfl, hker, Or.inl ⟨?_, ?_⟩⟩, ?_⟩
    · rw [inv_inv, B12, embSUid_two_eq_blockEmb, ← e₁', hU']
    · rw [inv_inv, B23, embSUid_zero_eq_blockEmb, ← e₂', hV']
    · obtain ⟨A, hA⟩ := not_comm_blockEmb_zero_one (K := K) (p := p) (f := f) h2 (le_refl 3)
      have hx0 : g * blockEmb K p f 3 2 0 (by omega) A * g⁻¹ ∈
          longRootGroupSU K p f (suMat ta) := by
        rw [e₁']
        exact Subgroup.mem_map.mpr ⟨_, ⟨A, rfl⟩, rfl⟩
      refine ⟨α (g * blockEmb K p f 3 2 0 (by omega) A * g⁻¹), by rw [hU']; exact ⟨_, hx0, rfl⟩,
        fun h => hA ?_⟩
      have h' := commute_of_involution_lift α hker (center_pow_three_su hK) htb2
        (g := g * blockEmb K p f 3 2 0 (by omega) A * g⁻¹) (by rw [htbb]; exact h)
      rw [hi₂] at h'
      calc blockEmb K p f 3 2 0 (by omega) A * blockEmb K p f 3 2 1 (by omega) (negOneSU K p f)
          = g⁻¹ * (g * blockEmb K p f 3 2 0 (by omega) A * g⁻¹ *
              (g * blockEmb K p f 3 2 1 (by omega) (negOneSU K p f) * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * blockEmb K p f 3 2 1 (by omega) (negOneSU K p f) * g⁻¹ *
              (g * blockEmb K p f 3 2 0 (by omega) A * g⁻¹)) * g := by rw [h']
        _ = blockEmb K p f 3 2 1 (by omega) (negOneSU K p f) *
              blockEmb K p f 3 2 0 (by omega) A := by group

end CFSG.GH74.GLS.LU
