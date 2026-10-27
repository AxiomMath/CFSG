module

public import CFSG.ClassicalInvolution.Q3.Q3URNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups

section Chart

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_chart_of_commuting_roots (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {hn2 : 2 ≤ 3 + 1} {R₀ R₁ : Subgroup (Su K p f (3 + 1))} {i₀ i₁ : Su K p f (3 + 1)}
    (h₀ : IsLongRootSU2 K p f hn2 R₀ i₀) (h₁ : IsLongRootSU2 K p f hn2 R₁ i₁) (hne : i₀ ≠ i₁)
    (hR : Commutes R₀ R₁) :
    ∃ g : Su K p f (3 + 1),
      R₀ = (LcU K p f (nodePair 3 2 (by norm_num))).map (MulAut.conj g).toMonoidHom ∧
      R₁ = (LcU K p f (nodePair 3 0 (by norm_num))).map (MulAut.conj g).toMonoidHom := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hn3 : 3 ≤ 3 + 1 := by omega
  obtain ⟨hs1, hs2, -⟩ := spaces_of_commutes_su hK hp hn3 h₀ h₁ hne hR
  have hmat := coe_eq_neg_of_spaces_su h2 h₀ h₁ hs1 hs2
  obtain ⟨g, hR1, hi1⟩ := h₁
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
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
  have hR0 : R₀ = (LcU K p f T2).map (MulAut.conj g).toMonoidHom := by
    rw [h₀.eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq g hJ]
    rfl
  have hR1' : R₁ = (LcU K p f T0).map (MulAut.conj g).toMonoidHom := by
    rw [hR1, rootSU2_eq_longRootGroupSU h2 hn2, negBlock_eq_zMat (by omega : 0 + 2 ≤ 3 + 1)]
    rfl
  exact ⟨g, hR0, hR1'⟩

end Chart

section Conj

variable {S Y : Type*} [Group S] [Group Y]

theorem ker_comp_conj_le_center (θ : S →* Y) (hker : θ.ker ≤ Subgroup.center S) (g : S) :
    (θ.comp (MulAut.conj g).toMonoidHom).ker ≤ Subgroup.center S := by
  intro x hx
  have h1 : g * x * g⁻¹ ∈ θ.ker := hx
  have h2 := Subgroup.mem_center_iff.mp (hker h1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul]
  exact h2 (g * y * g⁻¹)

theorem range_comp_conj (θ : S →* Y) (g : S) :
    (θ.comp (MulAut.conj g).toMonoidHom).range = θ.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨g⁻¹ * x * g, ?_⟩
    show θ (g * (g⁻¹ * x * g) * g⁻¹) = θ x
    congr 1
    group

end Conj

section Stab

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.locAut_stab (c : UCtx3 m Ω K z) (nd : UNodes3 c) {t : G} (htz : t * z * t⁻¹ = z) :
    ∀ x, locAut c.hΩ.conjInvariant htz (c.d.ψ x) ∈ c.d.ψ.range := by
  classical
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} :=
    fun L hL => conjSub_mem_centralizingMembers3 hconj htz hL
  set σ := locAut hconj htz with hσdef
  set ψ := c.d.ψ with hψ
  have hcK : IsClassicalMember3 (conjSub t K) z := by
    have := c.hz.conj t
    rwa [htz] at this
  have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
    ⟨hconj t K c.hK, isSubnormal_le hcK.subnormal⟩
  have hKt : conjSub t K = K :=
    eq_of_locImg_le_Q₀U3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hmem
      (locImg_self_le_Q₀U3 c.hm (hconj t K c.hK) hcK c.d)
  have hKt' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hKt
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hconjne : ∀ L, conjSub t L ≠ K ↔ L ≠ K := by
    intro L
    constructor
    · intro hne heq
      apply hne
      rw [heq, hKt]
    · intro hne heq
      apply hne
      have := congrArg (conjSub t⁻¹) heq
      rwa [conjSub_inv_conjSub, hKt'] at this
  have hS : (⨆ i : Fin m, (blockEmb2 (GaloisField 3 2) 3 1 m i).range) ≤
      (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨A, rfl⟩
    have hyL : ψ (blockEmb2 (GaloisField 3 2) 3 1 m i A) ∈ locImg Ω z (nd.j i.val) := by
      rw [nd.locImg_eq i.isLt]
      exact ⟨_, ⟨A, rfl⟩, rfl⟩
    have h1 : σ (ψ (blockEmb2 (GaloisField 3 2) 3 1 m i A)) ∈
        locImg Ω z (conjSub t (nd.j i.val)) := by
      rw [← locAut_locImg hconj htz]
      exact ⟨_, hyL, rfl⟩
    obtain ⟨R', -, hR'⟩ := exists_root_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
      (hmemΩz _ (nd.mem i.val i.isLt)) ((hconjne _).mpr (nd.ne_K i.val i.isLt))
    rw [hR'] at h1
    obtain ⟨y', -, hy'⟩ := h1
    exact ⟨y', hy'⟩
  intro x
  have hx : x ∈ ⨆ i : Fin m, (blockEmb2 (GaloisField 3 2) 3 1 m i).range := by
    rw [iSup_range_blockEmb2 card_gf9 (by norm_num : 3 ^ 1 ≠ 2) m]
    exact Subgroup.mem_top x
  exact hS hx

end Stab

section Partner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.exists_partner_three (c : UCtx3 3 Ω K z) (nd : UNodes3 c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β : Subgroup G, β ∈ Ω ∧ (∃ wβ : G, IsClassicalMember3 β wβ) ∧ ¬ Commutes K β ∧
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β) ∧
      ¬ Commutes β (nd.j 0) ∧
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β (nd.j 0)) ∧
      Commutes β (nd.j 2) := by
  have h2 := two_ne_zero_gf9
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
    exists_partner_one_su card_gf9 (by norm_num) hR₀ hR₁ hne hR01
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := exists_member_of_rootU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1
    c.hO3 c.d (R := B) ⟨iB, hB⟩
  obtain ⟨wb, hwb⟩ := c.hΩ.classical β' hβ'm.1
  have hnK' : ¬ Commutes (conjSub g⁻¹ K) β' := fun h =>
    hnc0 ((c.commutes_iff_root hK'm hβ'm hR₀ hKR₀ hβ'img).mp h).symm
  have hn0' : ¬ Commutes β' (conjSub g⁻¹ (nd.j 0)) := fun h =>
    hnc1 ((c.commutes_iff_root hβ'm hN0m hB hβ'img hN0R).mp h)
  obtain ⟨W1, hW1⟩ := c.stdpair_of_root hK'm hβ'm hR₀ hB hKR₀ hβ'img hc0.symm hne0.symm
    (fun h => hnc0 h.symm)
  obtain ⟨W2, hW2⟩ := c.stdpair_of_root hβ'm hN0m hB hR₁ hβ'img hN0R hc1 hne1 hnc1
  have hKβ'M : Commutes K β' :=
    commutes_K_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hβ'm hβ'K
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨_, IsClassicalMember3.conj hwb g⟩, ?_,
    ?_, ?_, ?_, ?_⟩
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

end CFSG.ClassicalInvolution.Q3.Q3W
