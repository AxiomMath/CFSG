module

public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers LieSystemData ConjInvariant centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerPatternD (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin m → Subgroup G, (∀ a, j a ∈ Ω) ∧ (∀ a, Commutes K (j a)) ∧
    (∀ a : Fin m, 1 ≤ a.val → j a ≤ Subgroup.centralizer ({t} : Set G)) ∧
    (∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b)) ∧
    (∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
    (∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a))

theorem PartnerPatternD.of_conj {m : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin m → Subgroup G} (hjΩ : ∀ a, j a ∈ Ω)
    (hjK : ∀ a, Commutes K (j a))
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a : Fin m, 1 ≤ a.val → conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternD p f m Ω K β t :=
  ⟨fun a => conjSub y (j a), fun a => hΩ y _ (hjΩ a),
    fun a => commutes_conjSub_of_mem_normalizer hy (hjK a), hfix,
    fun a b hab h1 h2 => (hjc a b hab h1 h2).conjSub y,
    fun a b h => by
      obtain ⟨W, hW⟩ := hjp a b h
      exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩,
    hpair0⟩

theorem PartnerPatternD.of_locAut [Finite G] {m : ℕ} {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G}
    (c : TCtx p f .POmegaPlus m Ω K z) {j : Fin m → Subgroup G}
    (hj : ∀ a, j a ∈ centralizingMembers Ω {z}) (hjK : ∀ a, Commutes K (j a))
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    {y : G} (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x)
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternD p f m Ω K β t := by
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine PartnerPatternD.of_conj c.hΩ.conjInvariant (fun a => (hj a).1) hjK hjc hjp
    (c.locLayer_le_normalizer hy) (fun a ha => ?_) hpair0
  have hmem : conjSub y (j a) ∈ centralizingMembers Ω {z} := by
    have := centralizingMembers_conj c.hΩ.conjInvariant y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, hj a, rfl⟩
  exact (Gaps.locAut_fixed_iff c.hΩ c.hP1 ht hmem).mpr (hfix a ha)

theorem twinChain_relations_D {m : ℕ} (hm : 4 ≤ m) {K β : Subgroup G} {j : Fin m → Subgroup G}
    (hjK : ∀ a, Commutes K (j a)) (hβj : ∀ a : Fin m, 1 ≤ a.val → Commutes β (j a))
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hβj0 : ∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a)) :
    (∀ i k : Fin (m + 2), i ≠ k → ¬ edgeD (m + 2) i k → ¬ edgeD (m + 2) k i →
      Commutes (twinChain K β j i) (twinChain K β j k)) ∧
    (∀ i k : Fin (m + 2), edgeD (m + 2) i k →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (twinChain K β j i) (twinChain K β j k)) := by
  have shape : ∀ i k : Fin (m + 2), edgeD (m + 2) i k ↔
      ((i.val + 1 = k.val ∧ k.val + 1 < m + 2) ∨ (i.val + 3 = m + 2 ∧ k.val + 1 = m + 2)) :=
    fun i k => Iff.rfl
  constructor
  · intro i k hik h1 h2
    rw [shape] at h1 h2
    have hne : i.val ≠ k.val := fun e => hik (Fin.ext e)
    obtain hi | hi | hi : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
    · obtain hk | hk | hk : k.val = 0 ∨ k.val = 1 ∨ 2 ≤ k.val := by omega
      · omega
      · omega
      · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 := ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by
          simp only; omega⟩
        rw [twinChain_zero K β j hi, twinChain_node K β j hb]
        exact hjK b
    · obtain hk | hk | hk : k.val = 0 ∨ k.val = 1 ∨ 2 ≤ k.val := by omega
      · omega
      · omega
      · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 := ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by
          simp only; omega⟩
        rw [twinChain_one K β j hi, twinChain_node K β j hb]
        exact hβj b (by omega)
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 := ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by
        simp only; omega⟩
      obtain hk | hk | hk : k.val = 0 ∨ k.val = 1 ∨ 2 ≤ k.val := by omega
      · rw [twinChain_node K β j ha, twinChain_zero K β j hk]
        exact (hjK a).symm
      · rw [twinChain_node K β j ha, twinChain_one K β j hk]
        exact (hβj a (by omega)).symm
      · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 := ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by
          simp only; omega⟩
        rw [twinChain_node K β j ha, twinChain_node K β j hb]
        refine hjc a b (fun e => hne (by rw [ha, hb, e])) ?_ ?_
        · intro h
          unfold edgeD at h
          omega
        · intro h
          unfold edgeD at h
          omega
  · intro i k hik
    rw [shape] at hik
    obtain hi | hi | hi : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
    · have hk : k.val = 1 := by omega
      rw [twinChain_zero K β j hi, twinChain_one K β j hk]
      exact hKβ
    · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 := ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by
        simp only; omega⟩
      rw [twinChain_one K β j hi, twinChain_node K β j hb]
      exact hβj0 b (by omega)
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 := ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by
        simp only; omega⟩
      obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 := ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by
        simp only; omega⟩
      rw [twinChain_node K β j ha, twinChain_node K β j hb]
      refine hjp a b ?_
      unfold edgeD
      omega

theorem routeD_typeD [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {m : ℕ} (hm : 4 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hpat : PartnerPatternD p f m Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = m + 2 := by
  obtain ⟨j, hjΩ, hjK, hjt, hjc, hjp, hβj0⟩ := hpat
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hβj : ∀ a : Fin m, 1 ≤ a.val → Commutes β (j a) := fun a ha => by
    obtain ⟨z', hz'⟩ := hΩ.classical (j a) (hjΩ a)
    exact commutes_partner_of_perfect_conj hp2 hq hMFZ hS3 hΩ hsingle hz hD4 hP1 hβ ht hKβ
      (commutator_eq_of_isClassicalMember hz') (hjt a ha) (fun y hy x hx => hjK a x hx y hy)
  obtain ⟨hcomm, hpair⟩ := twinChain_relations_D (p := p) (f := f) hm hjK hβj hjc hjp hKβ hβj0
  have hshape' : LocalShapeT p f 2 .POmegaPlus (m + 2 - 2) Ω z := hshape
  refine routeD_typeD_of_chain hp2 hq (n := m + 2) (by omega) hΩ hK hsingle hconn hz hshape' hP1
    (twinChain K β j) ?_ hcomm hpair
  intro k
  by_cases h0 : k.val = 0
  · rw [twinChain_zero K β j h0]; exact hK
  · by_cases h1 : k.val = 1
    · rw [twinChain_one K β j h1]; exact hβ
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, k.val = a.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha]
      exact hjΩ a

theorem routeD_typeD_of_pattern [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {m : ℕ}
    (hm : 4 ≤ m) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternD p f m Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = m + 2 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf, by show 4 ≤ m; omega⟩
  obtain ⟨c⟩ := TCtx.nonempty_plus hm hp2 hq hΩ hex hK hz hP1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_plus hm hadm hsingle hshape
  exact routeD_typeD hp2 hq hMFZ hS3 hm hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ
    (hpat β hβ t ht hKβ hfix)

theorem routeD_typeD_of_pattern_n [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {n : ℕ}
    (hn : 6 ≤ n) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 2 .POmegaPlus (n - 2) Ω z) (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternD p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m + 2 - 2 = m := by omega
  rw [hm] at hshape hpat
  exact routeD_typeD_of_pattern hp2 hq hMFZ hS3 (by omega) hΩ hex hK hsingle hconn hz hshape hP1
    hpat

end CFSG.ClassicalInvolution.RouteD
