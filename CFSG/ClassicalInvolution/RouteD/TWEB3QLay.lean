module

public import CFSG.ClassicalInvolution.RouteD.GapsToralD

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.RouteD.Gaps

set_option linter.unusedSectionVars false

section Group

variable {G : Type} [Group G]

theorem conjSub_inv_conjSub (d : G) (L : Subgroup G) : conjSub d⁻¹ (conjSub d L) = L := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (d : G) (L : Subgroup G) : conjSub d (conjSub d⁻¹ L) = L := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem inv_mul_mul_eq_of_conj {d z : G} (hdz : d * z * d⁻¹ = z) : d⁻¹ * z * d⁻¹⁻¹ = z := by
  rw [inv_inv]
  calc d⁻¹ * z * d = d⁻¹ * (d * z * d⁻¹) * d := by rw [hdz]
    _ = z := by group

end Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem conjSub_twin_eq_of_unit (c : TCtx p f tY nY Ω K z) {d : G} (hdz : d * z * d⁻¹ = z)
    (hKd : conjSub d K = K) {T : Subgroup G} (hT : T ∈ centralizingMembers Ω {z})
    (hTQ : locImg Ω z T ≤ c.d.Q₁) : conjSub d T = T := by
  by_contra hne
  have hΩ := c.hΩ.conjInvariant
  have hdz' := inv_mul_mul_eq_of_conj hdz
  have hKd' : conjSub d⁻¹ K = K := by
    conv_lhs => rw [← hKd]
    exact conjSub_inv_conjSub d K
  have hN₀z : conjSub d T ∈ centralizingMembers Ω {z} :=
    conjSub_mem_centralizingMembers hΩ hdz hT
  have hTK : T ≠ K := by
    rintro rfl
    have h1 : Commutes (locImg Ω z T) (locImg Ω z T) :=
      fun a ha b hb => c.d.comm₀₁ a (c.hQ₀ ha) b (hTQ hb)
    exact not_commutes_self_of_mem c.hΩ hT.1 ((commutes_iff_locImg c.hΩ c.hP1 hT hT).mpr h1)
  have hN₀K : conjSub d T ≠ K := fun h => hTK (by
    have := congrArg (conjSub d⁻¹) h
    rwa [conjSub_inv_conjSub, hKd'] at this)
  have hall : ∀ L ∈ centralizingMembers Ω {z}, L ≠ conjSub d T → Commutes (conjSub d T) L := by
    intro L hL hLN
    have hL' : conjSub d⁻¹ L ∈ centralizingMembers Ω {z} :=
      conjSub_mem_centralizingMembers hΩ hdz' hL
    have hne' : conjSub d⁻¹ L ≠ T := fun h => hLN (by
      rw [← conjSub_conjSub_inv d L, h])
    have h1 := (c.commutes_T_of_ne hT hTQ hL' hne').conjSub d
    rwa [conjSub_conjSub_inv] at h1
  have hN₀Q : ¬ locImg Ω z (conjSub d T) ≤ c.d.Q₁ := fun h =>
    hne (c.eq_of_locImg_le_Q₁ hN₀z hT h hTQ)
  obtain ⟨R₀, hR₀, hR₀eq⟩ := c.exists_fund_of_ne hN₀z hN₀K hN₀Q
  obtain ⟨R', hR', W, hW⟩ := c.hY.std R₀ hR₀
  obtain ⟨N', hN'z, -, -, hN'eq⟩ := c.exists_member_of_fund hR'
  have hnc : ¬ Commutes (conjSub d T) N' := fun h =>
    not_commutes_of_linearBlockStandardPair hW
      ((c.commutes_iff_fund hN₀z hN'z hR₀ hR₀eq hN'eq).mp h)
  have hN'N₀ : N' ≠ conjSub d T := fun h => ne_of_linearBlockStandardPair hW
    (eq_of_map_eq_of_perfect c.d.ψ c.d.ker_le (c.hY.perfR R₀ hR₀) (c.hY.perfR R' hR')
      (by rw [← hR₀eq, ← hN'eq, h]))
  exact hnc (hall N' hN'z hN'N₀)

theorem conjSub_layer_member_of_unit (c : TCtx p f tY nY Ω K z) {d : G}
    (hdz : d * z * d⁻¹ = z) (hKd : conjSub d K = K) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNQ : ¬ locImg Ω z N ≤ c.d.Q₁) :
    conjSub d N ∈ centralizingMembers Ω {z} ∧ conjSub d N ≠ K ∧
      ¬ locImg Ω z (conjSub d N) ≤ c.d.Q₁ := by
  have hΩ := c.hΩ.conjInvariant
  have hKd' : conjSub d⁻¹ K = K := by
    conv_lhs => rw [← hKd]
    exact conjSub_inv_conjSub d K
  have hNz := conjSub_mem_centralizingMembers hΩ hdz hN
  refine ⟨hNz, fun h => hNK ?_, fun h => ?_⟩
  · have := congrArg (conjSub d⁻¹) h
    rwa [conjSub_inv_conjSub, hKd'] at this
  · obtain ⟨T, hT, hTeq⟩ := c.exists_twin
    have hconj := conjSub_twin_eq_of_unit c hdz hKd hT hTeq.le
    have h1 := c.eq_of_locImg_le_Q₁ hNz hT h hTeq.le
    apply hNQ
    have : N = T := by
      rw [← conjSub_inv_conjSub d N, h1]
      conv_lhs => rw [← hconj]
      exact conjSub_inv_conjSub d T
    rw [this, hTeq]

theorem locAut_mem_range_of_unit (c : TCtx p f tY nY Ω K z) {d : G} (hdz : d * z * d⁻¹ = z)
    (hKd : conjSub d K = K)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      R.map c.d.ψ) (k : (modelUniv tY nY p f Fact.out).K) :
    locAut c.hΩ.conjInvariant hdz (c.d.ψ k) ∈ c.d.ψ.range := by
  have hS : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      (R.map c.d.ψ).map (locAut c.hΩ.conjInvariant hdz).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNQ, hNeq⟩ := c.exists_member_of_fund hR
    obtain ⟨hN'z, hN'K, hN'Q⟩ := conjSub_layer_member_of_unit c hdz hKd hNz hNK hNQ
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K hN'Q
    rw [← hNeq, locAut_locImg c.hΩ.conjInvariant hdz, hR'eq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : c.d.ψ.range.map (locAut c.hΩ.conjInvariant hdz).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨k, rfl⟩, rfl⟩

end CFSG.ClassicalInvolution.RouteD.TWE.B3
