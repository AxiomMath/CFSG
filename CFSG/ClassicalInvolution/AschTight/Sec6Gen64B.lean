module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

theorem z_ne_j : z ≠ j := by
  intro h
  subst h
  have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_twin c.hΩ c.hJ c.hK c.hKJ.symm c.hj c.hz
  exact c.notJ ⟨c.hJ, c.hKJ.symm, T, mem_RSet_of_isSylow2In c.hJ c.hT, c.hT.1, c.hT.1.trans hJN⟩

theorem pair : Pair Ω K J z j := ⟨c.hK, c.hJ, c.hz, c.hj, c.z_ne_j⟩

omit [Finite G] in
theorem symm : Cfg64 Ω J K j z v u T R where
  hΩ := c.hΩ
  hK := c.hJ
  hJ := c.hK
  hKJ := c.hKJ.symm
  hz := c.hj
  hj := c.hz
  notJ := c.notK
  notK := c.notJ
  hU := c.hV
  hUK := c.hVJ
  hV := c.hU
  hVJ := c.hUK
  hUV := fun a ha b hb => (c.hUV b hb a ha).symm
  hR := c.hT
  hT := c.hR
  huR := c.hvT
  hvT := c.huR
  hRN := by rw [sup_comm]; exact c.hTN
  hTN := by rw [sup_comm]; exact c.hRN

theorem natCard_R : Nat.card R = 2 * Nat.card (Subgroup.zpowers u) := by
  obtain ⟨R₀, -, K₀, hK₀, hR₀K₀, huR₀, -, hcard, -⟩ := exists_data_of_mem_USet c.hΩ c.hU
  have e : K₀ = K := eq_of_mem_USet c.hΩ c.hU hK₀ c.hK (huR₀.trans hR₀K₀.1) c.hUK
  subst e
  rw [c.hR.natCard_eq hR₀K₀, hcard]

theorem four_le_U : 4 ≤ Nat.card (Subgroup.zpowers u) := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := exists_data_of_mem_USet c.hΩ c.hU
  exact h4

omit [Finite G] in
theorem natCard_R_eq_T : Nat.card R = Nat.card T := natCard_isSylow2In_eq c.hΩ c.hK c.hJ c.hR c.hT

theorem natCard_U_eq_V : Nat.card (Subgroup.zpowers u) = Nat.card (Subgroup.zpowers v) := by
  have h1 := c.natCard_R
  have h2 := c.symm.natCard_R
  have h3 := c.natCard_R_eq_T
  omega

theorem U_isPGroup : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_of_mem_USet c.hΩ c.hU

theorem z_mem_U : z ∈ Subgroup.zpowers u :=
  AscL62.mem_of_uniqueInvolution_of_pGroup c.hz c.hUK c.U_isPGroup (by have := c.four_le_U; omega)

theorem j_mem_V : j ∈ Subgroup.zpowers v := c.symm.z_mem_U

theorem U_le_centralizer : Subgroup.zpowers u ≤ Subgroup.centralizer ({j} : Set G) :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (c.hUV x hx j c.j_mem_V)

theorem U_le_normalizer : Subgroup.zpowers u ≤ Subgroup.normalizer (J : Set G) :=
  le_normalizer_of_le_centralizer c.hΩ c.hJ c.hK c.hKJ.symm c.hj c.hUK c.U_isPGroup
    (by have := c.four_le_U; omega) c.U_le_centralizer

theorem sylow_V : IsSylow2In (Subgroup.zpowers v) (J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := c.symm.U_isPGroup
  have hVle : Subgroup.zpowers v ≤ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    le_inf c.hVJ c.symm.U_le_centralizer
  obtain ⟨V', hV', hVV'⟩ := IsSylow2In.exists_ge hV2 hVle
  have hV4 := c.symm.four_le_U
  have hle := Subgroup.card_le_of_le hVV'
  have hV'U : V' ∈ USet Ω :=
    sylow_cent_mem_USet c.hΩ c.hK c.hJ c.hz c.hj c.z_ne_j c.notJ hV' (hVV' c.j_mem_V)
      (by omega)
  have hcard := natCard_eq_of_mem_USet c.hΩ c.hJ hV'U c.hV (hV'.1.trans inf_le_left) c.hVJ
  have e : Subgroup.zpowers v = V' := Subgroup.eq_of_le_of_card_ge hVV' hcard.le
  exact e ▸ hV'

theorem sylow_U : IsSylow2In (Subgroup.zpowers u) (K ⊓ Subgroup.centralizer ({j} : Set G)) :=
  c.symm.sylow_V

theorem R_inf_centralizer : R ⊓ Subgroup.centralizer ({j} : Set G) = Subgroup.zpowers u := by
  have h2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer ({j} : Set G)) := c.hR.2.1.to_inf_left
  have hle : R ⊓ Subgroup.centralizer ({j} : Set G) ≤ K ⊓ Subgroup.centralizer ({j} : Set G) :=
    inf_le_inf_right _ c.hR.1
  have hcard := c.sylow_U.natCard_le h2 hle
  have hUle : Subgroup.zpowers u ≤ R ⊓ Subgroup.centralizer ({j} : Set G) :=
    le_inf c.huR c.U_le_centralizer
  exact (Subgroup.eq_of_le_of_card_ge hUle hcard).symm

theorem T_inf_centralizer : T ⊓ Subgroup.centralizer ({z} : Set G) = Subgroup.zpowers v :=
  c.symm.R_inf_centralizer

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
