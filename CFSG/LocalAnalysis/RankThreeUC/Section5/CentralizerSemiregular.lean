module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommutatorActorTwoCoreSupActorCenterEqBot
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CyclicCentralizerEquality.CyclicCentralizerEquality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeFixedCentralCoset.CoprimeFixedCentralCoset

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem centralizer_nonidentity_actor_eq_center {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    ∀ b ∈ B, b ≠ 1 → P ⊓ Subgroup.centralizer ({b} : Set G) = centerP P := by
  intro b hb hb1
  have h9 := commutator_actorTwoCore_sup_actor_center_eq_bot h
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  have hexp : Monoid.exponent ↥P = p := h.oddPrimeClassTwoAction.setting.exponent
  have hpow : ∀ x : G, x ∈ P → x ^ p = 1 := by
    intro x hx
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥P)
    rw [hexp] at this
    exact congrArg Subtype.val this
  have hZle : centerP P ≤ P := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hZcard : Nat.card (centerP P) = p := by
    have h1 := h.extraspecial.2.2.2
    unfold centerP
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact h1
  have hX : twoCoreCommutator T B ⊔ B ≤ Subgroup.centralizer (centerP P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h9
  have hZ' : centerP P ≤ Subgroup.centralizer ((twoCoreCommutator T B ⊔ B : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 hX
  have hb' : b ∈ (twoCoreCommutator T B ⊔ B : Subgroup G) := (le_sup_right : B ≤ twoCoreCommutator T B ⊔ B) hb
  have hcomm : centerP P ≤ Subgroup.centralizer ({b} : Set G) :=
    hZ'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hb'))
  have hle : centerP P ≤ P ⊓ Subgroup.centralizer ({b} : Set G) := le_inf hZle hcomm
  exact (ProofSupport.CyclicCentralizerEquality.eq_of_cyclic_exponent_prime hp hle
    (h.oddPrimeClassTwoAction.cyclic_centralizer b hb hb1)
    (fun c hc => hpow c hc.1) hZcard)

theorem actor_isSemiregular_on_central_quotient {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    p ∉ piOf B → ∀ b ∈ B, b ≠ 1 → ∀ g ∈ P, b * g * b⁻¹ * g⁻¹ ∈ centerP P →
      g ∈ centerP P := by
  intro hpi b hb hb1 g hg hcg
  have h9 := commutator_actorTwoCore_sup_actor_center_eq_bot h
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  have hexp : Monoid.exponent ↥P = p := h.oddPrimeClassTwoAction.setting.exponent
  have hpow : ∀ x : G, x ∈ centerP P → x ^ p = 1 := by
    intro x hx
    have hxP : x ∈ P := by
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have := Monoid.pow_exponent_eq_one (⟨x, hxP⟩ : ↥P)
    rw [hexp] at this
    exact congrArg Subtype.val this
  have hX : twoCoreCommutator T B ⊔ B ≤ Subgroup.centralizer (centerP P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h9
  have hb' : b ∈ (twoCoreCommutator T B ⊔ B : Subgroup G) := (le_sup_right : B ≤ twoCoreCommutator T B ⊔ B) hb
  have hbc : ∀ x ∈ centerP P, b * x = x * b := by
    intro x hx
    have := hX hb' x hx
    exact this.symm
  have hcop : Nat.Coprime (orderOf b) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    apply hpi
    refine ⟨hp, hd.trans ?_⟩
    have : orderOf (⟨b, hb⟩ : B) ∣ Nat.card B := orderOf_dvd_natCard _
    simpa using this
  have h1 := ProofSupport.CoprimeFixedCentralCoset.commutator_eq_one hp (centerP P) hpow b g hbc
    hcg hcop
  have hcomm : g ∈ Subgroup.centralizer ({b} : Set G) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have : y * g = g * y := by
      calc y * g = (y * g * y⁻¹ * g⁻¹) * g * y := by group
        _ = g * y := by rw [h1]; group
    exact this
  rw [← centralizer_nonidentity_actor_eq_center h b hb hb1]
  exact ⟨hg, hcomm⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
