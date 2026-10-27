module

public import CFSG.CGT.T75H.PartA
public import CFSG.CGT.T75H.Endgame
public import CFSG.CGT.T75H.DMax4
public import CFSG.CGT.T75H.Rank2Stmt
public import CFSG.CGT.T75H.Setup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I CFSG.Open

@[expose] def Step69PartB : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Nat.card T = 4 →
    ∀ S : Sylow 2 G, SylowData T T₁ S →
      ∀ α ∈ Cbar T T₁ S, ∀ β ∈ Cbar T T₁ S, α ≠ 1 → β ≠ 1 → α ≠ β → α * α = 1 → β * β = 1 →
        α * β = β * α → ∀ (ℓ a b y : G), D8Data T T₁ ℓ a b y →
          ∀ N : Subgroup G, OddCore T T₁ N → IsPGroup 3 N →
            ∀ γ ∈ ({α, β, α * β} : Set G), ∀ h ∈ N, h * γ = γ * h → h * ℓ = ℓ * h

theorem step69Rank2_of (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h1 : Sec4NoA) (h63 : Sec63) (h57 : Step57) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) (hBen : AschbacherDisconnectedInput) (hB : Step69PartB) :
    Step69Rank2 := by
  intro G _ T T₁ hy h4 S hS α hα β hβ hα1 hβ1 hne hαα hββ hαβ
  classical
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hc := sec6Ctx_of_card_four h214 hInv hIso hy h4
  have h48 : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hc.hS hc.hI
  obtain ⟨ℓ, a, b, y, D⟩ := exists_d8Data hc
  have h57' := h57 G T T₁ hy
  obtain ⟨N, hNH, hNc, hNodd, hTN, hdec, hNnorm, -, hN3⟩ := oddCore_isPGroup_three hc h48 h57'
    h215 hI D hS hα hβ hα1 hβ1 hne hαα hββ hαβ
  have hN : OddCore T T₁ N := ⟨hNH, hNc, hNodd, hTN, hdec, hNnorm⟩
  have hαmem := mem_Cbar_iff.1 hα
  have hβmem := mem_Cbar_iff.1 hβ
  have hBN := hB G T T₁ hy h4 S hS α hα β hβ hα1 hβ1 hne hαα hββ hαβ ℓ a b y D N hN hN3
  have hNℓ : ∀ n ∈ N, n * ℓ = ℓ * n := by
    have hαP : ∀ p ∈ N, α * p * α⁻¹ ∈ N := fun p hp => hNnorm α (hS.norm α hαmem.1) p hp
    have hβP : ∀ p ∈ N, β * p * β⁻¹ ∈ N := fun p hp => hNnorm β (hS.norm β hβmem.1) p hp
    have hgen := le_sup_fixed_of_commuting_involutions hNodd hαα hββ hαβ hα1 hβ1 hne hαP hβP
    have key : ∀ γ ∈ ({α, β, α * β} : Set G),
        N ⊓ Subgroup.centralizer ({γ} : Set G) ≤ Subgroup.centralizer ({ℓ} : Set G) := by
      rintro γ hγ h ⟨hhN, hhγ⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hBN γ hγ h hhN (Subgroup.mem_centralizer_singleton_iff.1 hhγ))
    intro n hn
    have hmem := (sup_le (sup_le (key α (Set.mem_insert _ _))
      (key β (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      (key (α * β) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
      (hgen hn)
    exact Subgroup.mem_centralizer_singleton_iff.1 hmem
  obtain ⟨γ, hγC, hγ1, hγH⟩ := exists_cent_involution hc h48 h57' D hN hNℓ
    (fun s hs => hS.norm s hs) hα hβ hα1 hβ1 hne hββ
  have hγmem := mem_Cbar_iff.1 hγC
  have hsup := hSub_sup_eq_top_of_card_four h1 h63 hBen hc h48 h57' D
  have hle : (hSub T (normIn T₁ T) ⊔ T₁ : Subgroup G) ≤ Subgroup.centralizer ({γ} : Set G) := by
    refine sup_le (fun h hh => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hγH h hh).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hγmem.2.2 x hx)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({γ} : Set G) := hsup ▸ hle
  have hcard := card_centralizer_lt hy.nonab hγ1
  have h2 := Subgroup.card_le_of_le htop
  rw [Subgroup.card_top] at h2
  omega

end CFSG.CGT.T75H
