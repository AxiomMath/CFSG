module

public import CFSG.ClassicalInvolution.RouteD.TypeEMain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdaptConj
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers LieSystemData ConjInvariant centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem locLayer_le_normalizer (c : ETCtx p f tY nY Ω K z) :
    locLayer Ω z ≤ Subgroup.normalizer (K : Set G) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLK : L = K
  · subst hLK
    exact Subgroup.le_normalizer
  · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer (K : Set G))
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => c.commutes_K_of_ne hL hLK k hk x hx

end ETCtx

section NodeSystems

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem NodeSystem.conjSub {r : ℕ} {adj : Fin r → Fin r → Prop} {j : Fin r → Subgroup G}
    (hj : NodeSystem p f adj Ω K z j) (hΩ : ConjInvariant Ω) {y : G} (hyz : y * z * y⁻¹ = z)
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    NodeSystem p f adj Ω K z (fun a => CFSG.ClassicalInvolution.Generic.conjSub y (j a)) where
  mem a := by
    have := centralizingMembers_conj hΩ y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, hj.mem a, rfl⟩
  ne_K a := by
    intro h
    apply hj.ne_K a
    have := congrArg (CFSG.ClassicalInvolution.Generic.conjSub y⁻¹) h
    rw [CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub,
      conjSub_eq_of_mem_normalizer (inv_mem hyK)] at this
    exact this
  commK a := commutes_conjSub_of_mem_normalizer hyK (hj.commK a)
  comm a b hab h1 h2 := (hj.comm a b hab h1 h2).conjSub y
  pair a b h := by
    obtain ⟨W, hW⟩ := hj.pair a b h
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩

end NodeSystems

section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem ETCtx.exists_nodeSystem_A5' (c : ETCtx p f .PSL 6 Ω K z)
    (hadm : StatedLieAdmissible .PSL 6 p f) :
    ∃ j : Fin 5 → Subgroup G, NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup a).map c.d.ψ := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .PSL 6 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .PSL 6 p f hp trivial hadm
  have hdiv : (modelUniv .PSL 6 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .PSL 6 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 5; decide⟩
  have hA : ∀ a b : Fin 5, a ≠ b → ¬ b.val = a.val + 1 → ¬ a.val = b.val + 1 →
      CartanMatrix.A 5 a b = 0 := by
    intro a b hab h1 h2
    simp only [CartanMatrix.A, Matrix.of_apply]
    split_ifs
    all_goals first | rfl | omega
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 5)
    (fun a => rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (fun a b : Fin 5 => b.val = a.val + 1)
    (fun a b hab h1 h2 => commutes_rankOne_of_cartan_eq_zero _ hext hℓ (hA a b hab h1 h2))
    (fun a b h => stdPair_specialLinear_edge (GaloisField p f) 5 h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

theorem ETCtx.exists_nodeSystem_D6' (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hadm : StatedLieAdmissible .POmegaPlus 6 p f) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadm
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 6)
    (fun a => rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeD 6)
    (fun a b hab h1 h2 => commutes_rankOne_plusDatum (n := 6) (K := GaloisField p f)
      (by norm_num) (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1)
    (fun a b h => standardPair_plusDatum_edge (F := GaloisField p f) (by norm_num) h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

theorem ETCtx.exists_nodeSystem_E7' (c : ETCtx p f .E7 0 Ω K z)
    (hadm : StatedLieAdmissible .E7 0 p f) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadm
  have hdiv : (modelUniv .E7 0 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E7 0 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 7; decide⟩
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 7)
    (fun a => rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeE 7)
    (fun a b hab h1 h2 => commutes_rankOne_of_cartan_eq_zero _ hext hℓ
      ((WeakCT.edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))).2.2.1 a b hab h1 h2).1)
    (fun a b h => stdPair_edge_E7 h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

end Nodes

section Route

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G} {tY : StatedLieTag}
  {nY : ℕ}

@[expose] def ToralRoute (c : ETCtx p f tY nY Ω K z)
    (j : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G) (β : Subgroup G) (t : G)
    (ht : t * z * t⁻¹ = z) (k : Fin (modelUniv tY nY p f Fact.out).D.rank) : Prop :=
  ∃ (k₀ : (modelUniv tY nY p f Fact.out).K)
    (v : Fin (modelUniv tY nY p f Fact.out).D.rank → ZMod 2),
    (∀ γ ∈ (modelUniv tY nY p f Fact.out).D.roots,
      (∀ x ∈ (conjSub k₀ ((modelUniv tY nY p f Fact.out).D.rootGroup γ ⊔
          (modelUniv tY nY p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0) ∧
    CharReach (modelUniv tY nY p f Fact.out).D.cartan v (Pi.single k 1) ∧
    ∀ y ∈ locLayer Ω z,
      (∀ b, (∀ x ∈ locImg Ω z (conjSub y (j b)),
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b ≠ k) →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j k))

variable [Finite G]

theorem ETCtx.partnerAt_of_toral (c : ETCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    (hbd : ModelFacts.HasBruhatDatum (modelUniv tY nY p f Fact.out).D)
    {adj : Fin (modelUniv tY nY p f Fact.out).D.rank →
      Fin (modelUniv tY nY p f Fact.out).D.rank → Prop}
    {j : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G}
    (hj : NodeSystem p f adj Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv tY nY p f Fact.out).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    {k : Fin (modelUniv tY nY p f Fact.out).D.rank}
    (hroute : ∀ ht : t * z * t⁻¹ = z, ToralRoute c j β t ht k) :
    ∃ j' : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G,
      NodeSystem p f adj Ω K z j' ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j' k)) ∧
      ∀ a, a ≠ k → Commutes β (j' a) := by
  obtain ⟨n, H, hct, -⟩ := hbd
  have ht : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz htβ hKβ
  obtain ⟨k₀, v, hT, hE, hS⟩ := hroute ht
  obtain ⟨y, hy, hfix⟩ := exists_adapted_y_of_conj_reach c.hΩ.conjInvariant c.d.ψ hct ht v k₀ hT hE
    hjimg
  have hfix' : ∀ b, (∀ x ∈ locImg Ω z (conjSub y (j b)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b ≠ k := fun b => by
    rw [hfix b, Pi.single_apply]
    by_cases h : b = k
    · simp [h]
    · simp [h]
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hj' := hj.conjSub c.hΩ.conjInvariant hyz (c.locLayer_le_normalizer hy)
  refine ⟨fun a => conjSub y (j a), hj', hS y hy hfix', fun a ha => ?_⟩
  have hmem : conjSub y (j a) ∈ centralizingMembers Ω {z} := hj'.mem a
  have hle : conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G) :=
    (Gaps.locAut_fixed_iff c.hΩ c.hP1 ht hmem).mpr ((hfix' a).mpr ha)
  obtain ⟨z', hz'⟩ := c.hΩ.classical _ hmem.1
  exact commutes_partner_of_perfect_conj c.hp2 c.hq hMFZ hS3 c.hΩ hsingle c.hz hD4 c.hP1 hβ htβ
    hKβ (commutator_eq_of_isClassicalMember hz') hle
    (fun y' hy' x hx => hj'.commK a x hx y' hy')

end Route

section Main

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem routeD_typeE6_of_exists [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .PSL 6 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : ∃ j : Fin 5 → Subgroup G,
      NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z j ∧ PartnerAt p f Ω j 2) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0 := by
  obtain ⟨j, hj, hβ⟩ := hpartner
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE6_of_partner hj hβ
  exact routeD_typeE6_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

theorem routeD_typeE7_of_exists [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : ∃ j : Fin 6 → Subgroup G,
      NodeSystem p f (edgeD 6) Ω K z j ∧ (PartnerAt p f Ω j 4 ∨ PartnerAt p f Ω j 5)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E7 ∧ D.rank i = 0 := by
  obtain ⟨j, hj, hβ⟩ := hpartner
  rcases hβ with h4 | h5
  · obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE7_of_partner hj h4
    exact routeD_typeE7_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair
  · have hj' := hj.comp_equiv (Equiv.swap (4 : Fin 6) 5) edgeD6_swap
    have h5' : PartnerAt p f Ω (j ∘ Equiv.swap (4 : Fin 6) 5) 4 :=
      PartnerAt.comp_equiv (Equiv.swap (4 : Fin 6) 5) (by rwa [Equiv.swap_apply_left])
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE7_of_partner hj' h5'
    exact routeD_typeE7_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

theorem routeD_typeE8_of_exists [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : ∃ j : Fin 7 → Subgroup G,
      NodeSystem p f (edgeE 7) Ω K z j ∧ PartnerAt p f Ω j 6) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E8 ∧ D.rank i = 0 := by
  obtain ⟨j, hj, hβ⟩ := hpartner
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE8_of_partner hj hβ
  exact routeD_typeE8_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

@[expose] def ToralPartners {tY : StatedLieTag} {nY : ℕ} (c : ETCtx p f tY nY Ω K z)
    (j : Fin (modelUniv tY nY p f Fact.out).D.rank → Subgroup G)
    (m₀ : Fin (modelUniv tY nY p f Fact.out).D.rank)
    (ks : Set (Fin (modelUniv tY nY p f Fact.out).D.rank)) : Prop :=
  ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) → Commutes β (j m₀) →
    ∀ ht : t * z * t⁻¹ = z, ∃ k ∈ ks, ToralRoute c j β t ht k

theorem routeD_typeE6_of_toral [Finite G] (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .PSL 6 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (htor : ∀ c : ETCtx p f .PSL 6 Ω K z, ∀ j : Fin 5 → Subgroup G,
      NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .PSL 6 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ToralPartners c j ((0 : Fin 5) : Fin (modelUniv .PSL 6 p f Fact.out).D.rank)
        {((2 : Fin 5) : Fin (modelUniv .PSL 6 p f Fact.out).D.rank)}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hadmY : StatedLieAdmissible .PSL 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num, by simp, by simp⟩
  have hsc : FundamentalSingleClass .PSL (modelUniv .PSL 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .PSL 6 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .PSL 6 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_A5 hadmY (by omega) }
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_A5' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := partner_involution_commutes hp2 hz htβ hKβ
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hbd := ModelFacts.hasBruhatDatum .PSL 6 p f hp trivial hadmY
  obtain ⟨k, hk, hroute⟩ := htor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht
  have hk2 : k = ((2 : Fin 5) : Fin (modelUniv .PSL 6 p f Fact.out).D.rank) := hk
  subst hk2
  obtain ⟨j', hj', hW, hc⟩ := c.partnerAt_of_toral hsingle hMFZ hS3 hD4 hbd hj hjimg hβΩ htβ hKβ
    (fun _ => hroute)
  exact routeD_typeE6_of_exists hp2 hq hΩ hK hsingle hconn hz hshape hP1 ⟨j', hj', β, hβΩ, hW, hc⟩

theorem routeD_typeE7_of_toral [Finite G] (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (htor : ∀ c : ETCtx p f .POmegaPlus 6 Ω K z, ∀ j : Fin 6 → Subgroup G,
      NodeSystem p f (edgeD 6) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ToralPartners c j ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank)
        {((4 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank),
          ((5 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank)}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E7 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num⟩
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .POmegaPlus 6 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_D6 hadmY (by omega) }
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_D6' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := partner_involution_commutes hp2 hz htβ hKβ
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hbd := ModelFacts.hasBruhatDatum .POmegaPlus 6 p f hp trivial hadmY
  obtain ⟨k, hk, hroute⟩ := htor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht
  obtain ⟨j', hj', hW, hc⟩ := c.partnerAt_of_toral hsingle hMFZ hS3 hD4 hbd hj hjimg hβΩ htβ hKβ
    (fun _ => hroute)
  have hk45 : k = ((4 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank) ∨
      k = ((5 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank) := hk
  refine routeD_typeE7_of_exists hp2 hq hΩ hK hsingle hconn hz hshape hP1 ⟨j', hj', ?_⟩
  rcases hk45 with rfl | rfl
  · exact Or.inl ⟨β, hβΩ, hW, hc⟩
  · exact Or.inr ⟨β, hβΩ, hW, hc⟩

theorem routeD_typeE8_of_toral [Finite G] (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (htor : ∀ c : ETCtx p f .E7 0 Ω K z, ∀ j : Fin 7 → Subgroup G,
      NodeSystem p f (edgeE 7) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ToralPartners c j ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank)
        {((6 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank)}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E8 ∧ D.rank i = 0 := by
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
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hbd := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadmY
  obtain ⟨k, hk, hroute⟩ := htor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht
  have hk6 : k = ((6 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank) := hk
  subst hk6
  obtain ⟨j', hj', hW, hc⟩ := c.partnerAt_of_toral hsingle hMFZ hS3 hD4 hbd hj hjimg hβΩ htβ hKβ
    (fun _ => hroute)
  exact routeD_typeE8_of_exists hp2 hq hΩ hK hsingle hconn hz hshape hP1 ⟨j', hj', β, hβΩ, hW, hc⟩

end Main

end CFSG.ClassicalInvolution.RouteD
