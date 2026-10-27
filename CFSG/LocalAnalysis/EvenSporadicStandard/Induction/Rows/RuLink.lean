module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuReachRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowLink

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Assembly.LowTwoRank CFSG.EvenSporadicStandard.RuStd

@[expose] def RuNormalizerFacts : Prop :=
  ∀ (G : Type) [Group G] (L K : Subgroup G) (u : G), IsSporadic ↥L .Ru → RuPair G L K u →
    ∀ R : Subgroup G, R ≤ K → Nat.card ↥R = 2 ^ 6 →
      Nat.card ↥(L ⊓ centralizer ((normalizer (R : Set G) ⊓ K : Subgroup G) : Set G)) = 4

@[expose] def SzCoverFacts : Prop :=
  ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
    SuzukiModel (K₂ ⧸ center K₂) 2 3 → ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
      (∃ E : Subgroup K₂, (∀ x ∈ E, α x = x) ∧ (∀ x ∈ E, x * x = 1) ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 16 ≤ Nat.card ↥E) ∨
      ¬ TwoSubgroupsAbelian ↥(fixSubgroup α)

section RuLink


attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem ru_link_pair (hf : RuLocalFacts) (hS : RuSuzukiModel) (hmult : OddMultTrivial .Ru)
    {G : Type} [Group G] [Finite G] {L K₁ T : Subgroup G} {s : G} (hcov : OddCover .Ru L)
    (h : Sol78Link5bData K₁ L T s) (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKRu (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ ℓ : G, RuPair G L K₁ ℓ ∧ CFSG.oddCore ↥K₁ = ⊥ := by
  have hL : IsSporadic ↥L .Ru := hcov.isSporadic_of_mult hmult
  have hZL : center ↥L = ⊥ := center_eq_bot_of_isSporadic_ru hL
  obtain ⟨-, hc, -, -⟩ := isKRu_data hf hS hIsK
  have hcardK : Nat.card ↥K₁ = 29120 * Nat.card ↥(CFSG.oddCore ↥K₁) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K₁)
    rw [hc] at h1
    exact h1
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥K₁)) := odd_card_oddCore' ↥K₁
  have hcardL : Nat.card ↥L = 145926144000 := ru_pinned_card ↥L hL
  have hne : K₁ ≠ L := by
    intro hKL
    have h1 : Nat.card ↥K₁ = 145926144000 := hKL ▸ hcardL
    obtain ⟨j, hj⟩ := hodd
    omega
  obtain ⟨hKL, σ, hσ1, hσ2, hσapp, hσK⟩ := link5b_aut h hK hne
  obtain ⟨l, hl⟩ := CFSG.EvenSporadicStandard.TwoRu.HypOne.allInner_of_isSporadic hL σ
  have hll : l * l = 1 := by
    have h3 : MulAut.conj (l * l) = (1 : MulAut ↥L) := by
      rw [map_mul, ← hl]
      exact hσ2
    have h2 : l * l ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h4 := congrArg (fun f : MulAut ↥L => f g) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      calc g * (l * l) = (l * l * g * (l * l)⁻¹) * (l * l) := by rw [h4]
        _ = l * l * g := by group
    rw [hZL] at h2
    exact Subgroup.mem_bot.1 h2
  have hl1 : l ≠ 1 := by
    intro h1
    apply hσ1
    rw [hl, h1, map_one]
  have hord : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hll) hl1
  have hℓ2 : orderOf (l : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hord
  have hcomm : ∀ k ∈ K₁, k * (l : G) = (l : G) * k := by
    intro k hk
    have h1 := hσK ⟨k, hKL hk⟩ hk
    rw [hl] at h1
    have h2 : (l : G) * k * (l : G)⁻¹ = k := congrArg Subtype.val h1
    calc k * (l : G) = ((l : G) * k * (l : G)⁻¹) * l := by rw [h2]
      _ = (l : G) * k := by group
  have hcent : K₁.subgroupOf L ≤ centralizer ({l} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm k (Subgroup.mem_subgroupOf.1 hk))
  have hdvd : Nat.card ↥(K₁.subgroupOf L) ∣ Nat.card ↥(centralizer ({l} : Set ↥L)) :=
    Subgroup.card_dvd_of_le hcent
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at hdvd
  have hcc := (ruFacts_of_isSporadic hL).card_centralizer l hord
  have ho1 : Nat.card ↥(CFSG.oddCore ↥K₁) = 1 := by
    rcases hcc with h245 | h116
    · exfalso
      rw [h245, hcardK] at hdvd
      have h29 : 29120 ∣ 245760 := (dvd_mul_right 29120 _).trans hdvd
      omega
    · rw [h116, hcardK] at hdvd
      exact eq_one_of_odd_of_dvd_ru hodd hdvd
  refine ⟨(l : G), ⟨l.2, hℓ2, hKL, hcomm, ?_⟩, Subgroup.eq_bot_of_card_eq _ ho1⟩
  show Nat.card ↥K₁ = 29120
  rw [hcardK, ho1]

theorem ru_std_row (hf : RuLocalFacts) (hS : RuSuzukiModel) (hmult : OddMultTrivial .Ru)
    {G : Type} [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.Ru], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKRu (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ, -⟩ := ru_link_pair hf hS hmult hcov h hK hIsK
  have hloc := solomonLocalQ_ru hf (hcov.isSporadic_of_mult hmult) hQ
  exact ⟨hloc.standard_in_L, hloc.autCentralizer_two⟩

theorem ru_card_autCentralizer_le {H : Type} [Group H] [Finite H] {L N₀ : Subgroup H}
    (hL : IsSporadic ↥L .Ru) (hN₀L : N₀ ≤ L) {c : ℕ}
    (hc : Nat.card ↥(L ⊓ centralizer (N₀ : Set H)) ≤ c) : Nat.card ↥(autCentralizer L N₀) ≤ c := by
  have hinn := CFSG.EvenSporadicStandard.TwoRu.HypOne.allInner_of_isSporadic hL
  have hle := autCentralizer_le_map_centralizer (L := L) (K := N₀) (fun α => by
    obtain ⟨g, hg⟩ := hinn α
    exact ⟨g, fun x => by rw [hg]; rfl⟩)
  have hc' : Nat.card ↥(centralizer ((N₀.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ c := by
    rw [card_centralizer_subgroupOf hN₀L]
    exact hc
  exact (Subgroup.card_le_of_le hle).trans
    ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans hc')

theorem ru_hautC (hf : RuLocalFacts) (hS : RuSuzukiModel) (hmult : OddMultTrivial .Ru)
    (hnorm : RuNormalizerFacts) {G : Type} [Group G] [Finite G] (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.Ru], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKRu (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 2 ∧
      ElemBound 4 ↥(autCentralizer L N₀) ∧
      (True → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  have hLRu := hcov.isSporadic_of_mult hmult
  obtain ⟨ℓ, hQ, hO⟩ := ru_link_pair hf hS hmult hcov h hK hIsK
  have hK1card : Nat.card ↥K₁ = 29120 := hQ.2.2.2.2
  have hsimp := hf.simple G L K₁ ℓ hLRu hQ
  have hZ : center ↥K₁ = ⊥ := center_eq_bot_of_simple_isQuasisimple_row hK
  rcases hcan with ⟨hev, -⟩ | ⟨-, R, -, hRle, hRcard, hN₀⟩
  · exfalso
    rw [hZ, Subgroup.card_bot] at hev
    exact absurd hev (by decide)
  · have hR6 : Nat.card ↥R = 2 ^ 6 := by rw [hRcard, hK1card, factorization_two_29120]
    have h4 := hnorm G L K₁ ℓ hLRu hQ R hRle hR6
    have hN₀L : N₀ ≤ L := by
      rw [hN₀]
      exact inf_le_right.trans hQ.2.2.1
    have hcard : Nat.card ↥(autCentralizer L N₀) ≤ 4 :=
      ru_card_autCentralizer_le hLRu hN₀L (by rw [hN₀]; exact h4.le)
    have hcomm : IsMulCommutative ↥(autCentralizer L N₀) := isMulCommutative_of_card_le_four hcard
    refine ⟨inferInstance, ?_, fun E _ _ => (Subgroup.card_le_card_group E).trans hcard,
      fun _ => ruAut_inner hLRu⟩
    have hdvd : 2 ^ twoAdic (autCentralizer L N₀) ∣ Nat.card ↥(autCentralizer L N₀) :=
      Nat.ordProj_dvd _ _
    by_contra hlt
    push Not at hlt
    have h8 : 2 ^ 3 ≤ 2 ^ twoAdic (autCentralizer L N₀) := Nat.pow_le_pow_right (by norm_num) hlt
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega

theorem ru_hfix (hsz : SzCoverFacts) {K₂ : Type} [Group K₂] [Finite K₂]
    (hperf : Group.IsPerfect K₂) (hS : SuzukiModel (K₂ ⧸ center K₂) 2 3) :
    ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
      ¬ LamProfile True 8 (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
        ((∃ k : K₂, α = MulAut.conj k) → ¬ LamProfile True 8 ↥(fixSubgroup α)) := by
  intro α h1 h2
  rcases hsz K₂ hperf hS α h1 h2 with ⟨E, hEfix, hE2, hEc, hE16⟩ | hna
  · have hle : E ≤ fixSubgroup α := fun x hx => hEfix x hx
    have hcard : Nat.card ↥(E.subgroupOf (fixSubgroup α)) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hnot : ¬ ElemBound 8 ↥(fixSubgroup α) := fun hb => by
      have h := hb (E.subgroupOf (fixSubgroup α))
        (fun x hx => Subtype.ext (hE2 x hx)) (fun x hx y hy => Subtype.ext (hEc x hx y hy))
      omega
    exact ⟨fun hL => hnot (hL.2.1.of_injective (f := MonoidHom.inl _ _)
        (inl_injective' _ _)), fun _ hL => hnot hL.2.1⟩
  · exact ⟨fun hL => hna ((hL.2.2 trivial).of_injective (f := MonoidHom.inl _ _)
        (inl_injective' _ _)), fun _ hL => hna (hL.2.2 trivial)⟩

end RuLink

end CFSG.EvenSporadicStandard.Induction
