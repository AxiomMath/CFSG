module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub InClass IsClassicalMember LocalOddCentral
  ExactMembers LieSystemData ConjInvariant)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerPatternB (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin m → Subgroup G, (∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) ∧ (∀ a, Commutes K (j a)) ∧
    (∀ a : Fin m, 1 ≤ a.val → ⁅j a, j a⁆ = j a ∧ j a ≤ Subgroup.centralizer ({t} : Set G)) ∧
    (∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b)) ∧
    (∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
    (∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
    (∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a))

theorem PartnerPatternB.of_conj {m : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin m → Subgroup G}
    (hjΩ : ∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) (hjK : ∀ a, Commutes K (j a))
    (hjperf : ∀ a : Fin m, ⁅j a, j a⁆ = j a)
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b))
    {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a : Fin m, 1 ≤ a.val → conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternB p f m Ω K β t := by
  refine ⟨fun a => conjSub y (j a), fun a ha => hΩ y _ (hjΩ a ha),
    fun a => commutes_conjSub_of_mem_normalizer hy (hjK a), fun a ha => ⟨?_, hfix a ha⟩,
    fun a b hab => (hjc a b hab).conjSub y, ?_, ?_, hpair0⟩
  · show ⁅(j a).map (MulAut.conj y).toMonoidHom, (j a).map (MulAut.conj y).toMonoidHom⁆ =
      (j a).map (MulAut.conj y).toMonoidHom
    rw [← Subgroup.map_commutator, hjperf a]
  · intro a b hab hb
    obtain ⟨W, hW⟩ := hjp a b hab hb
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩
  · intro a b ha hb
    obtain ⟨W, hW⟩ := hjsp a b ha hb
    exact ⟨_, CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map hW
      (MulAut.conj y).toMonoidHom (MulAut.conj y).injective⟩

theorem PartnerPatternB.of_locAut [Finite G] {m : ℕ} {Ω : Set (Subgroup G)} {z : G}
    {K β : Subgroup G} (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {z})
    {j : Fin m → Subgroup G} (hjΩ : ∀ a : Fin m, a.val + 1 < m → j a ∈ Ω)
    (hjY : ∀ a, j a ≤ locLayer Ω z) (hjK : ∀ a, Commutes K (j a))
    (hjperf : ∀ a : Fin m, ⁅j a, j a⁆ = j a) (hKY : locLayer Ω z ≤ Subgroup.normalizer (K : Set G))
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b))
    {y : G} (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut hΩ.conjInvariant ht x = x)
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternB p f m Ω K β t := by
  refine PartnerPatternB.of_conj hΩ.conjInvariant hjΩ hjK hjperf hjc hjp hjsp (hKY hy)
    (fun a ha => ?_) hpair0
  have hle : conjSub y (j a) ≤ locLayer Ω z := by
    intro x hx
    have h1 : y⁻¹ * x * y ∈ locLayer Ω z := hjY a (CFSG.ClassicalInvolution.Generic.mem_conjSub_iff.mp hx)
    have := (locLayer Ω z).mul_mem ((locLayer Ω z).mul_mem hy h1) ((locLayer Ω z).inv_mem hy)
    simpa [mul_assoc] using this
  have hperf : conjSub y (j a) ≤ ⁅conjSub y (j a), conjSub y (j a)⁆ := by
    show (j a).map (MulAut.conj y).toMonoidHom ≤ ⁅(j a).map (MulAut.conj y).toMonoidHom,
      (j a).map (MulAut.conj y).toMonoidHom⁆
    rw [← Subgroup.map_commutator, hjperf a]
  exact (locAut_fixed_iff_of_perfect hΩ hP1 ht hle hperf).mpr (hfix a ha)

theorem twinChain_relations_B {m : ℕ} (hm : 3 ≤ m) {K β : Subgroup G} {j : Fin m → Subgroup G}
    (hjK : ∀ a, Commutes K (j a)) (hβj : ∀ a : Fin m, 1 ≤ a.val → Commutes β (j a))
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hβj0 : ∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a)) :
    (∀ i k : Fin (m + 2), i.val + 1 < k.val →
      Commutes (twinChain K β j i) (twinChain K β j k)) ∧
    (∀ i k : Fin (m + 2), i.val + 1 = k.val → k.val + 1 < m + 2 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (twinChain K β j i) (twinChain K β j k)) ∧
    (∀ i k : Fin (m + 2), i.val + 2 = m + 2 → k.val + 1 = m + 2 →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (twinChain K β j i)
        (twinChain K β j k)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k hik
    obtain hi | hi | hi : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
    · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_zero K β j hi, twinChain_node K β j hb]
      exact hjK b
    · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_one K β j hi, twinChain_node K β j hb]
      exact hβj b (by omega)
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 :=
        ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by simp only; omega⟩
      obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha, twinChain_node K β j hb]
      exact hjc a b (by omega)
  · intro i k hik hk1
    obtain hi | hi | hi : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
    · have hk : k.val = 1 := by omega
      rw [twinChain_zero K β j hi, twinChain_one K β j hk]
      exact hKβ
    · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_one K β j hi, twinChain_node K β j hb]
      exact hβj0 b (by omega)
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 :=
        ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by simp only; omega⟩
      obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha, twinChain_node K β j hb]
      exact hjp a b (by omega) (by omega)
  · intro i k hi hk
    obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 :=
      ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by simp only; omega⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
      ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
    rw [twinChain_node K β j ha, twinChain_node K β j hb]
    exact hjsp a b (by omega) (by omega)

theorem routeD_typeB [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {m : ℕ} (hm : 3 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hpat : PartnerPatternB p f m Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = m + 2 := by
  obtain ⟨j, hjΩ, hjK, hjpt, hjc, hjp, hjsp, hβj0⟩ := hpat
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hβj : ∀ a : Fin m, 1 ≤ a.val → Commutes β (j a) := fun a ha =>
    commutes_partner_of_perfect_conj hp2 hq hMFZ hS3 hΩ hsingle hz hD4 hP1 hβ ht hKβ
      (hjpt a ha).1 (hjpt a ha).2 (fun y hy x hx => hjK a x hx y hy)
  obtain ⟨hcomm, hpair, hsp⟩ := twinChain_relations_B (p := p) (f := f) hm hjK hβj hjc hjp hjsp
    hKβ hβj0
  have hshape' : LocalShapeT p f 2 .POmegaOdd (m + 2 - 2) Ω z := hshape
  refine routeD_typeB_of_chain hp2 hq (n := m + 2) (by omega) hΩ hK hsingle hconn hz hshape' hP1
    (twinChain K β j) ?_ hcomm hpair hsp
  intro k hk
  by_cases h0 : k.val = 0
  · rw [twinChain_zero K β j h0]; exact hK
  · by_cases h1 : k.val = 1
    · rw [twinChain_one K β j h1]; exact hβ
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, k.val = a.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha]
      exact hjΩ a (by omega)

theorem routeD_typeB_of_pattern [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {m : ℕ}
    (hm : 3 ≤ m) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternB p f m Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = m + 2 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf, hm, hp2⟩
  obtain ⟨c⟩ := TCtx.nonempty_odd hm hp2 hq hΩ hex hK hz hP1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_odd hm hadm hsingle hshape
  exact routeD_typeB hp2 hq hMFZ hS3 hm hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ
    (hpat β hβ t ht hKβ hfix)

theorem routeD_typeB_of_pattern_n [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {n : ℕ}
    (hn : 5 ≤ n) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 2 .POmegaOdd (n - 2) Ω z) (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternB p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m + 2 - 2 = m := by omega
  rw [hm] at hshape hpat
  exact routeD_typeB_of_pattern hp2 hq hMFZ hS3 (by omega) hΩ hex hK hsingle hconn hz hshape hP1
    hpat

end CFSG.ClassicalInvolution.RouteD
