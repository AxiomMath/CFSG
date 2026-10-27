module

public import CFSG.ClassicalInvolution.RouteD.TwinTenModel
public import CFSG.ClassicalInvolution.RouteD.TypeDChain
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups
  FundamentalSingleClass InClass IsClassicalMember LocalOddCentral ExactMembers
  LieSystemData modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G]

theorem routeD_typeD5_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K₀ z) (hshape : LocalShapeT p f 2 .PSL 4 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin 5 → Subgroup G) (hUΩ : ∀ k, U k ∈ Ω)
    (hcomm : ∀ i j : Fin 5, i ≠ j → ¬ edgeD 5 i j → ¬ edgeD 5 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 5, edgeD 5 i j →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = 5 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ 5 := by omega
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f := ⟨hp.out, hf, by show 4 ≤ 5; omega⟩
  have hadmY : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, hf, by show 2 ≤ 4; omega, fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag .POmegaPlus := trivial
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have hfundY : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .PSL := trivial
  have e1 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 5 p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadm (by decide)
      (by decide)
  have hfinY : Finite (modelUniv .PSL 4 p f hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp.out hfundY hadmY
  obtain ⟨M⟩ := nonempty_extModel_D5 (p := p) (f := f) (by omega)
  obtain ⟨ψ0, hker0, hψ0⟩ := exists_psi_of_chain_plus hadm (by omega) U hcomm hpair
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 5 (GaloisField p f) hn3) := by
    revert hscT; rw [e1]; exact id
  have hΩψ0 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) hn3),
      R.map ψ0 ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (plusDatum 5 (GaloisField p f) hn3).rootGroup
      (zeroD (n := 5) (by omega))) (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ0]
    exact hΩ.conjInvariant _ _ (hUΩ _)
  have hψ : ∃ ψ : (modelUniv .POmegaPlus 5 p f hp.out).K →* G,
      ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 5 p f hp.out).K ∧
      ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 5 p f hp.out).D,
        R.map ψ ∈ Ω := by
    rw [e1]
    exact ⟨ψ0, hker0, hΩψ0⟩
  obtain ⟨ψ, hker, hΩψ⟩ := hψ
  exact routeD_core (by norm_num) hfund hadm hscT (by decide) hfinY M hΩ hK₀ hsingle hconn hz
    hshape hP1 ψ hker hΩψ

theorem twinChain_relations_D_of_three_le {m : ℕ} (hm : 3 ≤ m) {K β : Subgroup G}
    {j : Fin m → Subgroup G} (hjK : ∀ a, Commutes K (j a))
    (hβj : ∀ a : Fin m, 1 ≤ a.val → Commutes β (j a))
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hβj0 : ∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a)) :
    (∀ i k : Fin (m + 2), i ≠ k → ¬ edgeD (m + 2) i k → ¬ edgeD (m + 2) k i →
      Commutes (twinChain K β j i) (twinChain K β j k)) ∧
    (∀ i k : Fin (m + 2), edgeD (m + 2) i k →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (twinChain K β j i)
        (twinChain K β j k)) := by
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
      · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
          ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
        rw [twinChain_zero K β j hi, twinChain_node K β j hb]
        exact hjK b
    · obtain hk | hk | hk : k.val = 0 ∨ k.val = 1 ∨ 2 ≤ k.val := by omega
      · omega
      · omega
      · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
          ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
        rw [twinChain_one K β j hi, twinChain_node K β j hb]
        exact hβj b (by omega)
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 :=
        ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by simp only; omega⟩
      obtain hk | hk | hk : k.val = 0 ∨ k.val = 1 ∨ 2 ≤ k.val := by omega
      · rw [twinChain_node K β j ha, twinChain_zero K β j hk]
        exact (hjK a).symm
      · rw [twinChain_node K β j ha, twinChain_one K β j hk]
        exact (hβj a (by omega)).symm
      · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
          ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
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
    · obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_one K β j hi, twinChain_node K β j hb]
      exact hβj0 b (by omega)
    · obtain ⟨a, ha⟩ : ∃ a : Fin m, i.val = a.val + 2 :=
        ⟨⟨i.val - 2, by have := i.isLt; omega⟩, by simp only; omega⟩
      obtain ⟨b, hb⟩ : ∃ b : Fin m, k.val = b.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha, twinChain_node K β j hb]
      refine hjp a b ?_
      unfold edgeD
      omega

theorem routeD_typeD5 [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .PSL 4 Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hpat : PartnerPatternD p f 3 Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = 5 := by
  obtain ⟨j, hjΩ, hjK, hjt, hjc, hjp, hβj0⟩ := hpat
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hβj : ∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a) := fun a ha => by
    obtain ⟨z', hz'⟩ := hΩ.classical (j a) (hjΩ a)
    exact commutes_partner_of_perfect_conj hp2 hq hMFZ hS3 hΩ hsingle hz hD4 hP1 hβ ht hKβ
      (commutator_eq_of_isClassicalMember hz') (hjt a ha) (fun y hy x hx => hjK a x hx y hy)
  obtain ⟨hcomm, hpair⟩ := twinChain_relations_D_of_three_le (p := p) (f := f) (le_refl 3) hjK
    hβj hjc hjp hKβ hβj0
  refine routeD_typeD5_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 (twinChain K β j) ?_
    hcomm hpair
  intro k
  by_cases h0 : k.val = 0
  · rw [twinChain_zero K β j h0]; exact hK
  · by_cases h1 : k.val = 1
    · rw [twinChain_one K β j h1]; exact hβ
    · obtain ⟨a, ha⟩ : ∃ a : Fin 3, k.val = a.val + 2 :=
        ⟨⟨k.val - 2, by have := k.isLt; omega⟩, by simp only; omega⟩
      rw [twinChain_node K β j ha]
      exact hjΩ a

theorem TCtx.nonempty_A3 [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeT p f 2 .PSL 4 Ω z) : Nonempty (TCtx p f .PSL 4 Ω K z) := by
  have hY := yData_A3 (p := p) (f := f) (by omega : 4 ≤ p ^ f)
  obtain ⟨d⟩ := hshape.nonempty_dictT2 hY.ne_d4 hY.sc hΩ hK hz
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member hY hK hz d
  exact ⟨{
    hp2 := hp2
    hq := hq
    hΩ := hΩ
    hex := hex
    hK := hK
    hz := hz
    hP1 := hP1
    d := d'
    hQ₀ := hQ
    hY := hY }⟩

theorem nonempty_fund_sl4 (hq : 4 ≤ p ^ f) :
    (fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D).Nonempty := by
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hf, by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hl := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .PSL 4 p f hp.out trivial hadm
  exact ⟨_, rankOne_mem_fundamental (t := .PSL) (modelUniv .PSL 4 p f hp.out).D
    (k := ⟨0, by show 0 < 3; decide⟩) (hl ⟨0, by show 0 < 3; decide⟩ trivial)⟩

theorem routeD_typeD5_of_pattern [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .PSL 4 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternD p f 3 Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = 5 := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  obtain ⟨c⟩ := TCtx.nonempty_A3 hp2 hq hΩ hex hK hz hP1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner hsingle hshape
    (nonempty_fund_sl4 (by omega)) c.hY.std
  exact routeD_typeD5 hp2 hq hMFZ hS3 hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ
    (hpat β hβ t ht hKβ hfix)

end CFSG.ClassicalInvolution.RouteD
