module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternBasic
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv
  IsClassicalMember centralizingMembers)
open CFSG.ClassicalInvolution.RouteD

@[expose] def ChainBound1 {KY : Type} [Group KY] (Z : Subgroup KY) (𝓕 : Set (Subgroup KY))
    (d : ℕ) : Prop :=
  ∀ r, 4 ≤ r → ∀ c, IsChain Z 𝓕 r c → ∀ S ∈ 𝓕, (∀ a < r, Commutes S (c a)) →
    2 * (r + 1) + 4 ≤ d

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem chainBound1_model (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) :
    ChainBound1 (scalars K V) (fundSet Q) (Module.finrank K V) := by
  intro r hr c hc S hS hSc
  obtain ⟨i, hi⟩ := exists_chain_inv hc
  obtain ⟨iS, hiS⟩ := hS
  have nc : ∀ a', a' + 1 < r → ¬ Commutes (c a') (c (a' + 1)) := fun a' h' => (hc.adj a' h').2.1
  have horthX : ∀ x ∈ negSpace iS, ∀ y ∈ chainSpan i r, polar Q x y = 0 := by
    intro x hx
    refine polar_chainSpan (fun a ha => ?_)
    rcases orth_or_twin hodd hiS (hi a ha) (hSc a ha) with h | h
    · exact h x hx
    · exfalso
      by_cases h1 : a + 1 < r
      · refine ne_of_distinguish hodd hdim hiS (hi a ha) (hi (a + 1) h1) ?_ ?_ ?_ ?_ ?_ h
        · intro e
          apply nc a h1
          have := hSc a ha
          rw [← e] at this
          exact this.symm
        · exact fun e => (hc.adj a h1).1 e.symm
        · exact modelInvComm_of_commutes hodd (hi (a + 1) h1) hiS (hSc (a + 1) h1).symm
        · exact (ModelInvComm.of_adj (hc.adj a h1)).symm'
        · intro hiff
          exact nc a h1 (hiff.mp (hSc (a + 1) h1).symm).symm
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        refine ne_of_distinguish hodd hdim hiS (hi (a' + 1) ha) (hi a' (by omega)) ?_ ?_ ?_ ?_ ?_ h
        · intro e
          have := hSc (a' + 1) ha
          rw [← e] at this
          exact nc a' (by omega) this
        · exact fun e => (hc.adj a' (by omega)).1 e
        · exact modelInvComm_of_commutes hodd (hi a' (by omega)) hiS (hSc a' (by omega)).symm
        · exact ModelInvComm.of_adj (hc.adj a' (by omega))
        · intro hiff
          exact nc a' (by omega) (hiff.mp (hSc a' (by omega)).symm)
  have hspan := finrank_chainSpan hodd hdim hr hc hi r (by omega) le_rfl
  have hle : negSpace iS ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (chainSpan i r) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show polarBilin Q y x = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact horthX x hx y hy
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ (chainSpan i r)
  have h3 : Module.finrank K ↥(chainSpan i r) ≤ Module.finrank K V := Submodule.finrank_le _
  have h4 := finrank_negSpace hodd hiS
  omega

end Geometry

section Transfer

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot.chainBound1 (h : CentralQuot π 𝓕 𝓕' Z') {d : ℕ} (hb : ChainBound1 Z' 𝓕' d) :
    ChainBound1 (Subgroup.center KY) 𝓕 d := by
  intro r hr c hc S hS hSc
  refine hb r hr (fun a => (c a).map π) ⟨?_, ?_, ?_⟩ (S.map π) (h.map_mem S hS) ?_
  · intro a ha
    exact h.map_mem _ (hc.mem a ha)
  · intro a ha
    exact h.modelAdj (hc.mem a (by omega)) (hc.mem (a + 1) ha) (hc.adj a ha)
  · intro a b hab hb'
    exact (h.commutes_iff (hc.mem a (by omega))).mpr (hc.comm a b hab hb')
  · intro a ha
    exact (h.commutes_iff hS).mpr (hSc a ha)

end Transfer

section Plus

variable {p f m : ℕ} [Fact p.Prime]

theorem chainBound1_plusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound1 (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) (2 * m) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hb := chainBound1_model (Q := quadPlus m (GaloisField p f)) hodd
    (nondegenerate_polarBilin_quadPlus m (GaloisField p f)) hdim
  rw [finrank_plus] at hb
  exact (centralQuot_plus hp2 (by omega) hm3 hq).chainBound1 hb

theorem chainBound1_plus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound1 (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) (2 * m) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact chainBound1_plusDatum hp2 hm (by omega) hq

end Plus

end CFSG.ClassicalInvolution.RouteD.Gaps

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv
  IsClassicalMember centralizingMembers)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}

omit [Finite G] in
theorem IsLayerMember.of_commutes_self (cx : ETCtx p f tY nY Ω N x) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hc : Commutes L N) : IsLayerMember cx L :=
  ⟨hL, fun h => not_commutes_self_of_mem cx.hΩ cx.hK (h ▸ hc)⟩

theorem chain1_config (cx : ETCtx p f tY nY Ω N x) {d : ℕ}
    (hF : Gaps.ChainBound1 (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    {r : ℕ} (hr : 4 ≤ r) {c : ℕ → Subgroup G} {w : ℕ → G}
    (hc : ∀ a < r, IsLayerMember cx (c a))
    (hw : ∀ a < r, IsClassicalMember p f (c a) (w a))
    (hadj : ∀ a, a + 1 < r → c a ≠ c (a + 1) ∧ ¬ Commutes (c a) (c (a + 1)) ∧
      Commute (w a) (w (a + 1)) ∧ conjSub (w (a + 1)) (c a) = c a)
    (hcomm : ∀ a b, a + 1 < b → b < r → Commutes (c a) (c b))
    {S : Subgroup G} (hS : IsLayerMember cx S) (hSc : ∀ a < r, Commutes S (c a)) :
    2 * (r + 1) + 4 ≤ d := by
  classical
  have hex : ∀ a : ℕ, ∃ R : Subgroup (modelUniv tY nY p f Fact.out).K, a < r →
      R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
        locImg Ω x (c a) = R.map cx.d.ψ := by
    intro a
    by_cases h : a < r
    · obtain ⟨R, hR, hlR⟩ := (hc a h).exists_fund
      exact ⟨R, fun _ => ⟨hR, hlR⟩⟩
    · exact ⟨⊥, fun h' => absurd h' h⟩
  choose R hR using hex
  obtain ⟨RS, hRS, hSR⟩ := hS.exists_fund
  refine hF r hr R ⟨fun a ha => (hR a ha).1, fun a ha => ?_, fun a b hab hb => ?_⟩ RS hRS
    (fun a ha => ?_)
  · exact modelAdj_of_adj cx (hc a (by omega)).1 (hc (a + 1) ha).1 (hR a (by omega)).1
      (hR (a + 1) ha).1 (hR a (by omega)).2 (hR (a + 1) ha).2 (hw a (by omega)) (hw (a + 1) ha)
      (hadj a ha).1 (hadj a ha).2.1 (hadj a ha).2.2.1 (hadj a ha).2.2.2
  · exact (cx.commutes_iff_fund (hc a (by omega)).1 (hc b hb).1 (hR a (by omega)).1
      (hR a (by omega)).2 (hR b hb).2).mp (hcomm a b hab hb)
  · exact (cx.commutes_iff_fund hS.1 (hc a ha).1 hRS hSR (hR a ha).2).mp (hSc a ha)

theorem chain5_member_false (cx : ETCtx p f tY nY Ω N x) {d : ℕ}
    (hF : Gaps.ChainBound1 (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d) (hd : d < 16)
    {m₀ m₁ m₂ m₃ m₄ S : Subgroup G} {v₀ v₁ v₂ v₃ v₄ : G}
    (h₀ : IsLayerMember cx m₀) (h₁ : IsLayerMember cx m₁) (h₂ : IsLayerMember cx m₂)
    (h₃ : IsLayerMember cx m₃) (h₄ : IsLayerMember cx m₄) (hS : IsLayerMember cx S)
    (hw₀ : IsClassicalMember p f m₀ v₀) (hw₁ : IsClassicalMember p f m₁ v₁)
    (hw₂ : IsClassicalMember p f m₂ v₂) (hw₃ : IsClassicalMember p f m₃ v₃)
    (hw₄ : IsClassicalMember p f m₄ v₄)
    (a₀₁ : m₀ ≠ m₁ ∧ ¬ Commutes m₀ m₁ ∧ Commute v₀ v₁ ∧ conjSub v₁ m₀ = m₀)
    (a₁₂ : m₁ ≠ m₂ ∧ ¬ Commutes m₁ m₂ ∧ Commute v₁ v₂ ∧ conjSub v₂ m₁ = m₁)
    (a₂₃ : m₂ ≠ m₃ ∧ ¬ Commutes m₂ m₃ ∧ Commute v₂ v₃ ∧ conjSub v₃ m₂ = m₂)
    (a₃₄ : m₃ ≠ m₄ ∧ ¬ Commutes m₃ m₄ ∧ Commute v₃ v₄ ∧ conjSub v₄ m₃ = m₃)
    (c₀₂ : Commutes m₀ m₂) (c₀₃ : Commutes m₀ m₃) (c₀₄ : Commutes m₀ m₄)
    (c₁₃ : Commutes m₁ m₃) (c₁₄ : Commutes m₁ m₄) (c₂₄ : Commutes m₂ m₄)
    (s₀ : Commutes S m₀) (s₁ : Commutes S m₁) (s₂ : Commutes S m₂) (s₃ : Commutes S m₃)
    (s₄ : Commutes S m₄) : False := by
  have key := chain1_config cx hF (r := 5) (by norm_num)
    (c := fun a => match a with | 0 => m₀ | 1 => m₁ | 2 => m₂ | 3 => m₃ | _ => m₄)
    (w := fun a => match a with | 0 => v₀ | 1 => v₁ | 2 => v₂ | 3 => v₃ | _ => v₄)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by
      have : a < 4 := by omega
      interval_cases a <;> assumption)
    (fun a b hab hb => by
      have : a < 4 := by omega
      interval_cases a <;> interval_cases b <;> omega)
    hS (fun a ha => by interval_cases a <;> assumption)
  omega

end CFSG.ClassicalInvolution.RouteD.ETCtx
