module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeNotDvdCardActorOfIrreducibleCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Local.LocalVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BstarFaithful.BstarFaithful
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
import all CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeActionFixedFree

open CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

variable {G : Type} [Group G] [Finite G]

theorem Bstar_eq_map {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e)
    {A : Subgroup G} (hAB : A ≤ B) :
    Bstar P A = (A.subgroupOf B).map (BstarFaithful.bAction h51) := by
  ext σ
  simp only [Bstar, BstarFaithful.bAction, Subgroup.mem_map, Subgroup.mem_subgroupOf,
    MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n.1, hAB hn⟩, hn, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Subgroup.inclusion h51.setting.normB b, hb, rfl⟩

theorem q_ne_two {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} {A : Subgroup G} (hAB : A ≤ B)
    (hA : Nat.card A = q) : q ≠ 2 := by
  intro hq
  have h1 : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hodd := hc.oddPrimeClassTwoAction.setting.oddOrder
  rw [hA, hq] at h1
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)

theorem q_ne_p {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) : q ≠ p := by
  intro h
  apply prime_not_dvd_card_actor_of_irreducible_counterexample hc
  refine ⟨hc.oddPrimeClassTwoAction.setting.prime, ?_⟩
  rw [← h, ← hA]
  exact Subgroup.card_dvd_of_le hAB

theorem card_image {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) : Nat.card (Bstar P A) = q := by
  rw [Bstar_eq_map hc.oddPrimeClassTwoAction hAB,
    Subgroup.card_map_of_injective (BstarFaithful.injective hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction)]
  rw [← hA]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv

theorem fixedSpace_eq_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    BinaryRepresentations.fixedSpace (sigma p P) (Bstar P A) = ⊥ := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  have hp12 : p ∉ piOf B := prime_not_dvd_card_actor_of_irreducible_counterexample hc
  have hq1 : 1 < Nat.card A := hA ▸ hq.one_lt
  obtain ⟨a, ha1⟩ := (Subgroup.one_lt_card_iff_ne_bot A).1 hq1 |> fun h => Subgroup.ne_bot_iff_exists_ne_one.1 h
  have haB : (a : G) ∈ B := hAB a.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  rw [BinaryRepresentations.mem_fixedSpace_iff] at hv
  have hN : (a : G) ∈ Subgroup.normalizer (P : Set G) := hc.oddPrimeClassTwoAction.setting.normB haB
  have hmem : Subgroup.normalizerMonoidHom P ⟨(a : G), hN⟩ ∈ Bstar P A :=
    ⟨⟨(a : G), hN⟩, a.2, rfl⟩
  have hfix := hv _ hmem
  induction v using Additive.rec with | _ x => ?_
  induction x using QuotientGroup.induction_on with | _ g => ?_
  rw [sigma_apply_mk] at hfix
  have hq' : (((Subgroup.normalizerMonoidHom P ⟨(a : G), hN⟩) g : P) : Pbar P) = (g : Pbar P) :=
    Additive.ofMul.injective hfix
  rw [QuotientGroup.eq] at hq'
  set α := Subgroup.normalizerMonoidHom P ⟨(a : G), hN⟩ with hα
  have hz : g⁻¹ * α g ∈ Subgroup.center ↥P := by
    have := Subgroup.inv_mem _ hq'
    simpa using this
  have hw : α g * g⁻¹ ∈ Subgroup.center ↥P := by
    have h2 := Subgroup.mem_center_iff.1 hz g
    have : α g * g⁻¹ = g⁻¹ * α g := by
      calc α g * g⁻¹ = g * (g⁻¹ * α g) * g⁻¹ := by group
        _ = (g⁻¹ * α g) * g * g⁻¹ := by rw [h2]
        _ = g⁻¹ * α g := by group
    rw [this]; exact hz
  have hg : (g : G) ∈ centerP P := by
    refine actor_isSemiregular_on_central_quotient hc hp12 (a : G) haB ha1' (g : G) g.2 ?_
    refine ⟨α g * g⁻¹, hw, ?_⟩
    show ((α g : P) : G) * (g : G)⁻¹ = _
    have : ((α g : P) : G) = (a : G) * g * (a : G)⁻¹ := rfl
    rw [this]
  obtain ⟨y, hy, hyg⟩ := hg
  have : y = g := Subtype.ext hyg
  subst this
  have : (y : Pbar P) = 1 := (QuotientGroup.eq_one_iff y).2 hy
  rw [this]; rfl

end CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeActionFixedFree
