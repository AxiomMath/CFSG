module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Attached

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld

variable {p f : ℕ} [Fact p.Prime]

section Rows

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_partnerAt_E8_at (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 1 .E7 0 Ω z) (hP1 : LocalOddCentral Ω {z})
    (hGeom : LayerGeom (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
      (GaloisField p f))
    (hTor : ∀ c : ETCtx p f .E7 0 Ω K z, ∀ j : Fin 7 → Subgroup G,
      NodeSystem p f (edgeE 7) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, TorusFixedE7 c ht)
    (hExcl : ∀ c : ETCtx p f .E7 0 Ω K z, ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
      ∀ ht : t * z * t⁻¹ = z, ∀ (g : (modelUniv .E7 0 p f Fact.out).K) (p₀ : Fin 7),
        TypeE8.ToralNormalAt p f c ht g p₀ → p₀ = 6) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j ∧ PartnerAt p f Ω j 6 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hadmY : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .E7 0 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_E7 hadmY (by omega) }
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_E7' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := partner_involution_commutes hp2 hz htβ hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := by
    obtain ⟨W, hW⟩ := hKβ
    exact Gaps.conjSub_eq_of_standardPair
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) hW htβ.mem
      htβ.orderOf_eq_two
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hfix0 : ∀ x ∈ (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup
      ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank)).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant ht x = x := by
    rw [← hjimg 0]
    exact c.fixed_of_commutes ht htβ (hj.mem 0) hβ0
  have hTN := c.toralNormal_E7 ht h2t hKt hfix0 (hTor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht)
  obtain ⟨j', hj', p₀, ⟨W, hW⟩, hc, g, hg⟩ := c.exists_attached_at hsingle hshape hMFZ hS3 hD4
    hGeom hj hjimg hβΩ htβ hKβ hβ0 ht hTN
  refine ⟨j', hj', ?_⟩
  rcases hExcl c β hβΩ t htβ hKβ ht g p₀ hg with rfl
  exact ⟨β, hβΩ, ⟨W, hW⟩, hc⟩

end Rows

end CFSG.ClassicalInvolution.RouteD
