module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LieType.HighestRoot.CentTwistedE6Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Simplicity CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.Minuscule
  CFSG.AGLEmbedding.ParabHub CFSG.LieType.Steinberg.Minuscule.MinData.Valid

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k} {q : ℕ}

theorem hHat_pow_eq_one (i : Fin (Tag.rank .F4)) {g : fixedGroup k θ} (hg : g ∈ hHat k θ i) :
    g ^ Nat.card kˣ = 1 := by
  apply Subtype.ext
  have h1 : (g : e6Data_valid.minGroup k) ∈ hHatE k θ i := hg
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have hN : ∀ t : kˣ, t ^ Nat.card kˣ = 1 := fun t => pow_card_eq_one'
  fin_cases i
  · obtain ⟨t, ht⟩ := h1
    rw [← ht, ← map_pow]
    have : t ^ Nat.card kˣ = 1 := Subtype.ext (hN (t : kˣ))
    rw [this, map_one]
  · obtain ⟨t, ht⟩ := h1
    rw [← ht, ← map_pow]
    have : t ^ Nat.card kˣ = 1 := Subtype.ext (hN (t : kˣ))
    rw [this, map_one]
  · obtain ⟨t, ht⟩ := h1
    rw [← ht, ← map_pow, hN t, map_one]
  · obtain ⟨t, ht⟩ := h1
    rw [← ht, ← map_pow, hN t, map_one]

theorem pow_card_units_of_mem_center (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q)
    {z : fixedGroup k θ} (hz : z ∈ Subgroup.center (fixedGroup k θ)) : z ^ Nat.card kˣ = 1 := by
  have hcard := (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
    (θ := θ) hk hθq).1
  have hc : (⟨z, hz⟩ : Subgroup.center (fixedGroup k θ)) ^
      Nat.card (Subgroup.center (fixedGroup k θ)) = 1 := pow_card_eq_one'
  have hz' : z ^ Nat.card (Subgroup.center (fixedGroup k θ)) = 1 := congrArg Subtype.val hc
  have hd : Nat.card (Subgroup.center (fixedGroup k θ)) ∣ Nat.card kˣ := by
    rw [hcard, Nat.card_units, hk]
    have h := Nat.sq_sub_sq q 1
    rw [one_pow] at h
    exact (Nat.gcd_dvd_right 3 (q + 1)).trans ⟨q - 1, h⟩
  obtain ⟨m, hm⟩ := hd
  rw [hm, pow_mul, hz', one_pow]

theorem borelQuotient_e6tw (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card k)
    (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q)
    {Y : Type} [Group Y] (e : Y ≃* DerivedCentralQuotient (twistedFixedGroup .E6 k θ)) :
    BorelQuotient (twistedDatum k θ) (nHat θ) (hHat k θ)
      (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (twistedIsogeny θ hθ hK4)))
      (Nat.card kˣ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquasi := fixedGroup_isQuasisimple_of_four_le_card θ hθ hK4
  have hsurj := twistedIsogeny_surjective θ hθ hK4
  have hker := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center
    hθ hK4
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hquasi hsurj hker.le
  have hkerπ : ∀ z : fixedGroup k θ,
      (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (twistedIsogeny θ hθ hK4))) z = 1 →
        z ∈ Subgroup.center (fixedGroup k θ) := by
    intro z hz
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥⁅twistedFixedGroup .E6 k θ,
        twistedFixedGroup .E6 k θ⁆)) (twistedIsogeny θ hθ hK4 z) = 1 := by
      apply e.symm.injective
      simpa using hz
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    rw [hZ] at h2
    obtain ⟨z', hz', hzz'⟩ := h2
    have h3 : z'⁻¹ * z ∈ (twistedIsogeny θ hθ hK4).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzz', inv_mul_cancel]
    rw [hker] at h3
    have := Subgroup.mul_mem _ hz' h3
    simpa using this
  refine
    { ct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
      extras := twistedDatum_steinbergExtras θ hθ
      pGroup := fun β hβ => CFSG.LieType.HighestRoot.isPGroup_twistedE6_rootGroup θ
        (isRoot_of_mem_twistedDatum_roots θ hβ)
      surj := e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp hsurj)
      odd := by rw [Nat.card_units]; exact odd_card_sub_one k
      torus_pow := fun i g hg => hHat_pow_eq_one i hg
      ker_central := fun z hz => hkerπ z (MonoidHom.mem_ker.1 hz)
      ker_pow := fun z hz => pow_card_units_of_mem_center hk hθq (hkerπ z (MonoidHom.mem_ker.1 hz)) }

theorem hasSL2Node_e6tw (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card k) :
    HasSL2Node (twistedDatum k θ) (nf 2) k := by
  have hab : (nd 2 = nd 2 ∧ nd 4 = nd 4) ∨ (nd 2 = nd 0 ∧ nd 4 = nd 5) := Or.inl ⟨rfl, rfl⟩
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single (nd 2) 1) ≠ Pi.single (nd 2) 1 := by
    rw [rho_single, hρ]; decide
  have hne2 : rho (-Pi.single (nd 2) 1) ≠ -Pi.single (nd 2) 1 := by
    rw [rho_neg_single, hρ]
    intro h
    exact (show (Pi.single (nd 4) 1 : Fin (Tag.rank .E6) → ℤ) ≠ Pi.single (nd 2) 1 by decide)
      (neg_injective h)
  have hp1 : proj (Pi.single (nd 2) 1) = Pi.single (nf 2) 1 := proj_single _
  have hp2 : proj (-Pi.single (nd 2) 1) = -Pi.single (nf 2) 1 := proj_neg_single _
  have hup : ∀ c : k, slOrbitHom θ hθ hab (sl2Upper c) ∈
      (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) := fun c => by
    refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ (nd 2)) hp1 hne1 _).2 ⟨c, ?_⟩
    rw [show (sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) = slUpper k c from rfl,
      slOrbitHom_upper, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
  have hlo : ∀ c : k, slOrbitHom θ hθ hab (sl2Lower c) ∈
      (twistedDatum k θ).rootGroup (-Pi.single (nf 2) 1) := fun c => by
    refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ (nd 2)) hp2 hne2 _).2 ⟨c, ?_⟩
    rw [show (sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) = slLower k c from rfl,
      CFSG.LieType.HighestRoot.slOrbitHom_lower, rho_neg_single, hρ, twistSign_neg_single,
      Int.cast_one, one_mul]
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    CFSG.AGLEmbedding.ParabPrime.sl2_isSimpleGroup hK4
  refine ⟨slOrbitHom θ hθ hab, ?_, hup, hlo⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (slOrbitHom θ hθ hab).ker with
    hb | ht
  · exact hb
  · exfalso
    apply twistedRootGroup_ne_bot θ hθ (β := Pi.single (nf 2) 1) (IsRoot.basis _)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ (nd 2)) hp1 hne1 x).1 hx
    have hx1 : x = slOrbitHom θ hθ hab (sl2Upper c) := by
      apply Subtype.ext
      rw [show (sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) = slUpper k c from rfl,
        slOrbitHom_upper, hc, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
    have : slOrbitHom θ hθ hab (sl2Upper c) = 1 :=
      MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top _)
    rw [hx1, this]
    exact Subgroup.one_mem _

theorem involutive_of_card (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) :
    ∀ c, θ (θ c) = c := by
  intro c
  have := Fintype.ofFinite k
  rw [hθq, hθq, ← pow_mul, ← sq, ← hk, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
