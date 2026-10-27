module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternRows
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclFrame
public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.TypeE8 (ToralNormalAt Rroot)

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_attached_at (c : ETCtx p f .E7 0 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    (hLG : LayerGeom (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
      (GaloisField p f))
    {j : Fin 7 → Subgroup G} (hj : NodeSystem p f (edgeE 7) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    {m₀ : Fin 7} (hβm₀ : Commutes β (j m₀)) (ht : t * z * t⁻¹ = z) (hT : ToralNormalE c ht) :
    ∃ j' : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j' ∧ ∃ p₀ : Fin 7,
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j' p₀)) ∧
      (∀ a, a ≠ p₀ → Commutes β (j' a)) ∧
      ∃ g : (modelUniv .E7 0 p f Fact.out).K, ToralNormalAt p f c ht g p₀ := by
  have hΩ := c.hΩ
  have hp : p.Prime := Fact.out
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr c.hf, rfl⟩
  obtain ⟨W, hW⟩ := hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  obtain ⟨n, H, hct, -⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum .E7 0 p f Fact.out
    trivial hadm
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNK, hKN, hβN⟩ := c.exists_moved_layer_member hLG hsingle hshape hβ htβ
      ⟨W, hW⟩ (hj.mem m₀).1 (hj.commK m₀) hβm₀
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK
    have hgen := Balance.iSup_rankOneImage_eq_range .E7 0 p f Fact.out trivial hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, Gaps.locAut hΩ.conjInvariant ht x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .E7 0 p f Fact.out).D.roots,
          Balance.rankOneImage (modelUniv .E7 0 p f Fact.out).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (Gaps.locAut_fixed_iff hΩ c.hP1 ht hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (c.commutes_partner_of_centralizes hsingle hMFZ hS3 hD4 hβ htβ ⟨W, hW⟩ hNz hNt hKN)
  obtain ⟨y, hy, g, p₀, hjimg', hframe⟩ := Gaps.exists_adapted_frame_normal hΩ.conjInvariant c.d.ψ
    hct TypeEPattern.patternLemma_E7_model ht v hv k₀ hTT hjimg
  have hmap : ∀ S : Subgroup (modelUniv .E7 0 p f Fact.out).K, (conjSub g S).map c.d.ψ =
      S.map (c.d.ψ.comp (MulAut.conj g).toMonoidHom) := fun S => by
    unfold conjSub
    rw [Subgroup.map_map]
  have hTg : ToralNormalAt p f c ht g p₀ := by
    intro γ hγ
    rw [hmap]
    exact hframe γ hγ
  have hfixed : ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), Gaps.locAut hΩ.conjInvariant ht x = x) ↔ a ≠ p₀) ∧
      (locImg Ω z (conjSub y (j a))).map (Gaps.locAut hΩ.conjInvariant ht).toMonoidHom =
        locImg Ω z (conjSub y (j a)) := by
    intro a
    obtain ⟨h1, h2'⟩ := hframe (Pi.single a 1)
      (single_mem_roots (modelUniv .E7 0 p f Fact.out).D a)
    rw [hjimg' a]
    refine ⟨h2'.trans ?_, h1⟩
    by_cases hap : p₀ = a
    · subst hap
      simp
      exact rfl
    · rw [Pi.single_eq_of_ne hap]
      simp
      exact fun h => hap h.symm
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
  obtain ⟨b, hbp, hb1, hb2⟩ := TypeEPattern.edgeE7_far p₀
  obtain ⟨wJ, hwJ⟩ := hΩ.classical _ (hmemy p₀).1
  obtain ⟨xb, hxb⟩ := hΩ.classical _ (hmemy b).1
  have hstd := c.scenarioC hLG hsingle hshape hβ htβ ⟨W, hW⟩ (hmemy p₀).1 (hmemy b).1 hwJ hxb
    (hj'.commK p₀) (hj'.commK b) (hfix' b hbp) (hj'.comm b p₀ hbp hb1 hb2).symm hmov hnorm
  exact ⟨fun a => conjSub y (j a), hj', p₀, hstd, hfix', g, hTg⟩

end ETCtx

end CFSG.ClassicalInvolution.RouteD
