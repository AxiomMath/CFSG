module

public import CFSG.ClassicalInvolution.RouteD.TypeUChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits Module Matrix
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem coe_eq_neg_of_spaces_su (h2 : (2 : K) ≠ 0) {hn2 : 2 ≤ 3 + 1}
    {R₀ R₁ : Subgroup (Su K p f (3 + 1))} {i₀ i₁ : Su K p f (3 + 1)}
    (h₀ : IsLongRootSU2 K p f hn2 R₀ i₀) (h₁ : IsLongRootSU2 K p f hn2 R₁ i₁)
    (hs1 : minusSpaceSU i₀ ≤ fixSpaceSU i₁) (hs2 : minusSpaceSU i₁ ≤ fixSpaceSU i₀) :
    suMat i₀ = -suMat i₁ := by
  have hcompl := isCompl_eigSpace h2 h₁.coe_mul_self
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [Module.finrank_fin_fun] at hsum
  have hd₁ : finrank K (minusSpaceSU i₁) = 2 := h₁.finrank_minusSpaceSU h2
  have hd₀ : finrank K (minusSpaceSU i₀) = 2 := h₀.finrank_minusSpaceSU h2
  have hd₁' : finrank K (eigSpace (suMat i₁) (-1)) = 2 := hd₁
  have hfix : finrank K (fixSpaceSU i₁) = 2 := by
    have : finrank K (eigSpace (suMat i₁) 1) = 2 := by omega
    exact this
  have heq : minusSpaceSU i₀ = fixSpaceSU i₁ := Submodule.eq_of_le_of_finrank_eq hs1 (by omega)
  have hv : ∀ v : Fin (3 + 1) → K, suMat i₀ *ᵥ v = -(suMat i₁ *ᵥ v) := by
    intro v
    have hvt : v ∈ eigSpace (suMat i₁) (-1) ⊔ eigSpace (suMat i₁) 1 := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
    have ha' : suMat i₁ *ᵥ a = -a := mem_eigSpace_neg_one.mp ha
    have hb' : suMat i₁ *ᵥ b = b := mem_eigSpace_one.mp hb
    have ha0 : suMat i₀ *ᵥ a = a := mem_fixSpaceSU.mp (hs2 ha)
    have hb0 : suMat i₀ *ᵥ b = -b := by
      have : b ∈ minusSpaceSU i₀ := by rw [heq]; exact hb
      exact mem_minusSpaceSU.mp this
    rw [Matrix.mulVec_add, Matrix.mulVec_add, ha0, hb0, ha', hb']
    abel
  refine Matrix.ext fun a b => ?_
  have := congrFun (hv (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem exists_partner_one_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn2 : 2 ≤ 3 + 1}
    {R₀ R₁ : Subgroup (Su K p f (3 + 1))} {i₀ i₁ : Su K p f (3 + 1)}
    (h₀ : IsLongRootSU2 K p f hn2 R₀ i₀) (h₁ : IsLongRootSU2 K p f hn2 R₁ i₁) (hne : i₀ ≠ i₁)
    (hR : Commutes R₀ R₁) :
    ∃ (B : Subgroup (Su K p f (3 + 1))) (iB : Su K p f (3 + 1)),
      IsLongRootSU2 K p f hn2 B iB ∧ Commute iB i₀ ∧ iB ≠ i₀ ∧ ¬ Commutes B R₀ ∧
        Commute iB i₁ ∧ iB ≠ i₁ ∧ ¬ Commutes B R₁ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hn3 : 3 ≤ 3 + 1 := by omega
  obtain ⟨hs1, hs2, -⟩ := spaces_of_commutes_su hK hp hn3 h₀ h₁ hne hR
  have hmat := coe_eq_neg_of_spaces_su h2 h₀ h₁ hs1 hs2
  obtain ⟨g, hR1, hi1⟩ := h₁
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
  set Tb : Pair (3 + 1) := natPair (3 + 1) 0 2 (by omega) (by omega) (by omega) with hTb
  have hrootInv : suMat (rootInvSU K p f hn2) = zMat K (3 + 1) T0.1 := by
    rw [suMat_rootInvSU, negBlock_eq_zMat (by omega : 0 + 2 ≤ 3 + 1)]
    rfl
  have hneg : -(negBlock K (3 + 1) 0) = zMat K (3 + 1) T2.1 := by
    rw [negBlock_eq_diagonal, zMat]
    ext a b
    by_cases hab : a = b
    · subst hab
      fin_cases a <;> simp [hT2, nodePair, natPair]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hJ : suMat i₀ * suMat g = suMat g * zMat K (3 + 1) T2.1 := by
    rw [hmat, hi1, suMat_mul, suMat_mul, suMat_rootInvSU, ← hneg, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
  have hcinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hi0 : i₀ = g * zEltU K p f T2 * g⁻¹ := by
    have h' : i₀ * g = g * zEltU K p f T2 := by
      apply suMat_injective
      rw [suMat_mul, suMat_mul, suMat_zEltU]
      exact hJ
    exact eq_mul_inv_iff_mul_eq.mpr h'
  have hR0 : R₀ = (LcU K p f T2).map (MulAut.conj g).toMonoidHom := by
    rw [h₀.eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq g hJ]
    rfl
  have hR1' : R₁ = (LcU K p f T0).map (MulAut.conj g).toMonoidHom := by
    rw [hR1, rootSU2_eq_longRootGroupSU h2 hn2, negBlock_eq_zMat (by omega : 0 + 2 ≤ 3 + 1)]
    rfl
  have hi1' : i₁ = g * zEltU K p f T0 * g⁻¹ := by
    have : rootInvSU K p f hn2 = zEltU K p f T0 := suMat_injective hrootInv
    rw [hi1, this]
  have hcz : ∀ T' : Pair (3 + 1),
      Commute (g * zEltU K p f Tb * g⁻¹) (g * zEltU K p f T' * g⁻¹) := fun T' =>
    commute_conj (signGroupU_comm (zEltU_mem_signGroupU Tb) (zEltU_mem_signGroupU T')) g
  have hmemb : ∀ {T' : Pair (3 + 1)} (x : Fin (3 + 1)), x ∈ Tb.1 → x ∉ T'.1 →
      g * zEltU K p f Tb * g⁻¹ ≠ g * zEltU K p f T' * g⁻¹ := fun {T'} x hx hx' h =>
    typeU_zEltU_ne_of_mem h2 hx hx' (mul_left_cancel (mul_right_cancel h))
  refine ⟨(LcU K p f Tb).map (MulAut.conj g).toMonoidHom, g * zEltU K p f Tb * g⁻¹,
    (isLongRootSU2_LcU h2 hn2 Tb).conj g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi0]
    exact hcz T2
  · rw [hi0]
    exact hmemb ⟨0, by omega⟩ (by simp [hTb, natPair])
      (by simp [hT2, nodePair, natPair, Fin.ext_iff])
  · rw [hR0, commutes_map_iff _ hcinj]
    exact not_commutes_LcU_overlap hK hp hn3 (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩)
      (k := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  · rw [hi1']
    exact hcz T0
  · rw [hi1']
    exact hmemb ⟨2, by omega⟩ (by simp [hTb, natPair])
      (by simp [hT0, nodePair, natPair, Fin.ext_iff])
  · rw [hR1', commutes_map_iff _ hcinj]
    have hswap : LcU K p f Tb = LcU K p f (⟨{⟨2, by omega⟩, ⟨0, by omega⟩},
        Finset.card_pair (by simp)⟩ : Pair (3 + 1)) :=
      typeU_LcU_congr (Finset.pair_comm _ _)
    rw [hswap]
    exact not_commutes_LcU_overlap hK hp hn3 (i := ⟨2, by omega⟩) (j := ⟨0, by omega⟩)
      (k := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) (by simp) (by simp)

end Model

section Partner

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem UCtx.exists_partner_three (c : UCtx p f 3 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β : Subgroup G, β ∈ Ω ∧ (∃ wβ : G, IsClassicalMember p f β wβ) ∧ ¬ Commutes K β ∧
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β) ∧
      ¬ Commutes β (nd.j 0) ∧
      (∃ W : Subgroup G,
        UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β (nd.j 0)) ∧
      Commutes β (nd.j 2) := by
  have h2 := c.h2
  have hMΩ : nd.j 2 ∈ Ω := (nd.mem 2 (by omega)).1
  obtain ⟨g, hg⟩ := hsingle _ hMΩ
  obtain ⟨hK'm, hK'ne, R₀, i₀, hR₀, hKR₀, hy₀, hi₀⟩ := c.exists_rootData_conj hg c.hK
    (nd.commK 2 (by omega)) (nd.ne_K 2 (by omega)).symm c.hz
  obtain ⟨hN0m, hN0ne, R₁, i₁, hR₁, hN0R, hy₁, hi₁⟩ := c.exists_rootData_conj hg
    (nd.mem 0 (by omega)).1 (nd.far 0 (by omega) 2 (by omega) (by omega))
    (nd.inj 0 (by omega) 2 (by omega) (by omega)) (nd.isCl 0 (by omega))
  have hKne : conjSub g⁻¹ K ≠ conjSub g⁻¹ (nd.j 0) := fun h =>
    nd.ne_K 0 (by omega) ((conjSub_injective g⁻¹ h).symm)
  have hne : i₀ ≠ i₁ := c.ne_of_rootInv hK'm hN0m hKne hR₀ hR₁ hKR₀ hN0R
  have hR01 : Commutes R₀ R₁ :=
    (c.commutes_iff_root hK'm hN0m hR₀ hKR₀ hN0R).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.commK 0 (by omega)))
  obtain ⟨B, iB, hB, hc0, hne0, hnc0, hc1, hne1, hnc1⟩ :=
    exists_partner_one_su c.card_eq c.hp2 hR₀ hR₁ hne hR01
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := typeU_exists_member_of_root c.hp2 c.hq c.hm c.hΩ c.hK c.hz
    c.hP1 c.d (R := B) ⟨iB, hB⟩
  obtain ⟨wb, hwb⟩ := c.hΩ.classical β' hβ'm.1
  have hnK' : ¬ Commutes (conjSub g⁻¹ K) β' := fun h =>
    hnc0 ((c.commutes_iff_root hK'm hβ'm hR₀ hKR₀ hβ'img).mp h).symm
  have hn0' : ¬ Commutes β' (conjSub g⁻¹ (nd.j 0)) := fun h =>
    hnc1 ((c.commutes_iff_root hβ'm hN0m hB hβ'img hN0R).mp h)
  obtain ⟨W1, hW1⟩ := c.stdpair_of_root hK'm hβ'm hR₀ hB hKR₀ hβ'img hc0.symm hne0.symm
    (fun h => hnc0 h.symm)
  obtain ⟨W2, hW2⟩ := c.stdpair_of_root hβ'm hN0m hB hR₁ hβ'img hN0R hc1 hne1 hnc1
  have hKβ'M : Commutes K β' :=
    typeU_commutes_K_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d hβ'm hβ'K
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨_, IsClassicalMember.conj hwb g⟩, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro h
    rw [← conjSub_conjSub_inv g K] at h
    exact hnK' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W1, ?_⟩
    have := typeU_standardPair_conjSub hW1 g
    rwa [conjSub_conjSub_inv] at this
  · intro h
    rw [← conjSub_conjSub_inv g (nd.j 0)] at h
    exact hn0' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W2, ?_⟩
    have := typeU_standardPair_conjSub hW2 g
    rwa [conjSub_conjSub_inv] at this
  · rw [hg]
    exact (commutes_conjSub_iff g).mpr hKβ'M.symm

end Partner

end CFSG.ClassicalInvolution.RouteD
