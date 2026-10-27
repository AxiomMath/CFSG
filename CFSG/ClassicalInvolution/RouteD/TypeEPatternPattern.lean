module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternToral
public import CFSG.ClassicalInvolution.RouteD.GapsPatternDMain
public import CFSG.ClassicalInvolution.RouteD.TypeEAdapt

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem exists_attached_of_toralNormal (c : ETCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 tY nY Ω z)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    (hfund : CFSG.ClassicalInvolution.ModelFacts.IsFundTag tY)
    (hadm : StatedLieAdmissible tY nY p f)
    (hPat : PatternLemma (modelUniv tY nY p f Fact.out).D.cartan)
    (hLG : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
      (GaloisField p f))
    {adj : Fin (modelUniv tY nY p f Fact.out).D.rank →
      Fin (modelUniv tY nY p f Fact.out).D.rank → Prop}
    (hfar : ∀ a, ∃ b, b ≠ a ∧ ¬ adj b a ∧ ¬ adj a b)
    {j : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G}
    (hj : NodeSystem p f adj Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv tY nY p f Fact.out).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    {m₀ : Fin (modelUniv tY nY p f Fact.out).D.rank} (hβm₀ : Commutes β (j m₀))
    (ht : t * z * t⁻¹ = z) (hT : ToralNormalE c ht) :
    ∃ j' : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G,
      NodeSystem p f adj Ω K z j' ∧ ∃ p₀ : Fin (modelUniv tY nY p f Fact.out).D.rank,
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j' p₀)) ∧
        ∀ a, a ≠ p₀ → Commutes β (j' a) := by
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨W, hW⟩ := hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  obtain ⟨n, H, hct, -⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum tY nY p f Fact.out
    hfund hadm
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNK, hKN, hβN⟩ := c.exists_moved_layer_member hLG hsingle hshape hβ htβ
      ⟨W, hW⟩ (hj.mem m₀).1 (hj.commK m₀) hβm₀
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK
    have hgen := Balance.iSup_rankOneImage_eq_range tY nY p f Fact.out hfund hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, Gaps.locAut hΩ.conjInvariant ht x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv tY nY p f Fact.out).D.roots,
          Balance.rankOneImage (modelUniv tY nY p f Fact.out).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (Gaps.locAut_fixed_iff hΩ c.hP1 ht hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ ⟨W, hW⟩ hNz hNt hKN)
  obtain ⟨y, hy, p₀, hfixed⟩ := Gaps.exists_adapted_y_normal hΩ.conjInvariant c.d.ψ hct hPat ht v
    hv k₀ hTT hjimg
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hj' := hj.conjSub hΩ.conjInvariant hyz (c.locLayer_le_normalizer hy)
  have hmemy : ∀ a, conjSub y (j a) ∈ centralizingMembers Ω {z} := hj'.mem
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} :=
    fun L hL => TypeEPattern.conjSub_mem_centralizingMembers hΩ.conjInvariant ht hL
  have hfix' : ∀ a, a ≠ p₀ → Commutes β (conjSub y (j a)) := fun a ha => by
    have h1 := (hfixed a).1.mpr ha
    have hNt := (Gaps.locAut_fixed_iff hΩ c.hP1 ht (hmemy a)).mpr h1
    exact c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ ⟨W, hW⟩ (hmemy a) hNt
      (hj'.commK a)
  have hmov : ¬ Commutes β (conjSub y (j p₀)) := fun h => by
    have hNt : conjSub y (j p₀) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t htβ.mem n hn).symm
    have := (hfixed p₀).1.mp ((Gaps.locAut_fixed_iff hΩ c.hP1 ht (hmemy p₀)).mp hNt)
    exact this rfl
  have hnorm : conjSub t (conjSub y (j p₀)) = conjSub y (j p₀) := by
    have h1 := (hfixed p₀).2
    rw [Gaps.locAut_locImg hΩ.conjInvariant ht] at h1
    exact locImg_injOn hΩ c.hP1 (hmemt _ (hmemy p₀)) (hmemy p₀) h1
  obtain ⟨b, hbp, hb1, hb2⟩ := hfar p₀
  obtain ⟨wJ, hwJ⟩ := hΩ.classical _ (hmemy p₀).1
  obtain ⟨xb, hxb⟩ := hΩ.classical _ (hmemy b).1
  have hstd := c.scenarioC hLG hsingle hshape hβ htβ ⟨W, hW⟩ (hmemy p₀).1 (hmemy b).1 hwJ hxb
    (hj'.commK p₀) (hj'.commK b) (hfix' b hbp) (hj'.comm b p₀ hbp hb1 hb2).symm hmov hnorm
  exact ⟨fun a => conjSub y (j a), hj', p₀, hstd, hfix'⟩

end ETCtx

end CFSG.ClassicalInvolution.RouteD
