module

public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule

theorem twistedChevalleyModel_of_lieModel {X : Type} [Group X] {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .twistedE6 n r f) :
    r.Prime ∧ 1 ≤ f ∧ TwistedChevalleyModel X .E6 (r ^ f) := by
  rcases hm with ⟨ht, -⟩ | ⟨-, -, ⟨⟨hrp, hf1, -⟩, hc⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact ⟨hrp, hf1, hc⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

section Setup


variable {K : Type} [Field K] [Finite K] (σ : K →+* K)

noncomputable abbrev twDerived : Subgroup (ModGL TwistTag.E6.tag K) :=
  ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆

theorem center_twDerived_eq_bot {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Subgroup.center ↥(twDerived σ) = ⊥ := by
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect .E6 hp hf K hK σ hσ
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hc := exceptional_fixed_center_trivial .E6 K (RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩)
  have hσe : (RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩).toRingHom = σ :=
    RingHom.ext fun _ => rfl
  rw [hσe] at hc
  let e : ↥(twDerived σ) ≃* ↥(graphFixedRootGroup .E6 K σ) := MulEquiv.subgroupCongr hΓ
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center ↥(graphFixedRootGroup .E6 K σ) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx y]
  rw [hc, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hex, map_one])

@[expose] noncomputable def derivedCentralQuotientEquiv
    (h : Subgroup.center ↥(twDerived σ) = ⊥) :
    DerivedCentralQuotient (twistedFixedGroup .E6 K σ) ≃* ↥(twDerived σ) :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

@[expose] noncomputable def twIsog (hθ : ∀ c, σ (σ c) = c) (hk : 4 ≤ Nat.card K) :
    ↥(fixedGroup K σ) →* ↥(twDerived σ) :=
  (e6IsogenyFixed σ).codRestrict (twDerived σ) fun g => by
    change _ ∈ ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆
    rw [← range_e6IsogenyFixed σ hθ hk]
    exact ⟨g, rfl⟩

theorem coe_twIsog (hθ : ∀ c, σ (σ c) = c) (hk : 4 ≤ Nat.card K) (g : ↥(fixedGroup K σ)) :
    ((twIsog σ hθ hk g : ↥(twDerived σ)) : ModGL TwistTag.E6.tag K) = e6IsogenyFixed σ g :=
  rfl

theorem twIsog_surjective (hθ : ∀ c, σ (σ c) = c) (hk : 4 ≤ Nat.card K) :
    Function.Surjective (twIsog σ hθ hk) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ := hy
  rw [← range_e6IsogenyFixed σ hθ hk] at hy'
  obtain ⟨g, rfl⟩ := hy'
  exact ⟨g, rfl⟩

theorem mem_center_of_twIsog_eq_one (hθ : ∀ c, σ (σ c) = c) (hk : 4 ≤ Nat.card K)
    {g : ↥(fixedGroup K σ)} (hg : twIsog σ hθ hk g = 1) :
    g ∈ Subgroup.center ↥(fixedGroup K σ) := by
  have h0 : ((twIsog σ hθ hk g : ↥(twDerived σ)) : ModGL TwistTag.E6.tag K) = 1 := by
    rw [hg]
    rfl
  have h1 : e6IsogenyT K (g : e6Data_valid.minGroup K) = 1 := Subtype.ext h0
  have hc := ker_e6IsogenyT_le_center K h1
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc y)

end Setup

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
