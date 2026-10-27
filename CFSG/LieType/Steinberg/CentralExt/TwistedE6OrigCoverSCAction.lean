module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OrigCoverSC
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoToralCoords
import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore
import CFSG.LieType.Steinberg.TwistedE6.Clause0
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
import CFSG.RankThree.PartOne.S11d.PerfectCentral

set_option linter.style.haveILetI false

public section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.SeitzReduction.F4Pilot (twistedIsogenyC twistedIsogenyC_surjective
  ker_twistedIsogenyC)

section SCAut

variable {n : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)

theorem exists_twE6_sc_aut_lift (δ : MulAut ↥(twistedE6RootGroup K σ)) :
    ∃ β : MulAut ↥(fixedGroup K σ.toRingHom),
      ∀ u, twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ (β u) =
        δ (twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ u) := by
  have : Finite ↥(fixedGroup K σ.toRingHom) := by
    have : Finite (Module.End K (Fin e6Data.d →₀ K)) := Module.finite_of_finite K
    infer_instance
  have h5 : 5 ≤ 2 ^ n := by
    calc 5 ≤ 8 := by norm_num
      _ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c :=
    TwistedE6Closed.theta_theta_of_card (θ := σ.toRingHom) (q := 2 ^ n) hK hσ
  have hperf : commutator ↥(fixedGroup K σ.toRingHom) = ⊤ :=
    Group.isPerfect_def.1
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card
        σ.toRingHom hθ h4)
  let π : ↥(fixedGroup K σ.toRingHom) →* ↥(twistedE6RootGroup K σ) :=
    twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ
  have hπ : Function.Surjective π :=
    twistedIsogenyC_surjective (f := n) (by omega) hK σ.toRingHom hσ
  have hker : π.ker ≤ Subgroup.center ↥(fixedGroup K σ.toRingHom) :=
    le_of_eq (ker_twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ)
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π' : E →* ↥(fixedGroup K σ.toRingHom)),
      Function.Surjective π' → π'.ker ≤ Subgroup.center E →
      ∃ s : ↥(fixedGroup K σ.toRingHom) →* E, ∀ g, π' (s g) = g := by
    intro E _ _ π' hπ' hcen
    exact TwistedE6Closed.twistedE6_exists_section_of_central (θ := σ.toRingHom)
      (q := 2 ^ n) h5 hK hσ hπ' hcen
  obtain ⟨α, hα, hαs⟩ :=
    E6ThreeKernel.exists_surjective_of_split (q := δ.toMonoidHom.comp π)
      (δ.surjective.comp hπ) hsplit hπ hker hperf
  have hinj : Function.Injective α := (Finite.injective_iff_surjective).2 hαs
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαs⟩, hα⟩

theorem twE6_sc_aut_lift_unique {β γ : MulAut ↥(fixedGroup K σ.toRingHom)}
    (h : ∀ u, twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ (β u) =
      twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ (γ u)) : β = γ := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c :=
    TwistedE6Closed.theta_theta_of_card (θ := σ.toRingHom) (q := 2 ^ n) hK hσ
  have hperf : Group.IsPerfect ↥(fixedGroup K σ.toRingHom) :=
    CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card
      σ.toRingHom hθ h4
  have hker : (twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ).ker ≤
      Subgroup.center ↥(fixedGroup K σ.toRingHom) :=
    le_of_eq (ker_twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ)
  have heq := CFSG.RankThree.PartOne.hom_eq_of_div_central hperf β.toMonoidHom γ.toMonoidHom
    (fun u => by
      apply hker
      change twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ (β u / γ u) = 1
      rw [map_div, h u, div_self'])
  exact MulEquiv.ext (fun u => DFunLike.congr_fun heq u)

noncomputable def twE6ScAutHom :
    MulAut ↥(twistedE6RootGroup K σ) →* MulAut ↥(fixedGroup K σ.toRingHom) where
  toFun δ := Classical.choose (exists_twE6_sc_aut_lift hn3 hK σ hσ δ)
  map_one' := by
    apply twE6_sc_aut_lift_unique hn3 hK σ hσ
    intro u
    rw [Classical.choose_spec (exists_twE6_sc_aut_lift hn3 hK σ hσ 1) u]
    rfl
  map_mul' δ ε := by
    apply twE6_sc_aut_lift_unique hn3 hK σ hσ
    intro u
    rw [Classical.choose_spec (exists_twE6_sc_aut_lift hn3 hK σ hσ (δ * ε)) u]
    change δ (ε (twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ u)) =
      twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ
        (Classical.choose (exists_twE6_sc_aut_lift hn3 hK σ hσ δ)
          (Classical.choose (exists_twE6_sc_aut_lift hn3 hK σ hσ ε) u))
    rw [Classical.choose_spec (exists_twE6_sc_aut_lift hn3 hK σ hσ δ)
      (Classical.choose (exists_twE6_sc_aut_lift hn3 hK σ hσ ε) u)]
    rw [Classical.choose_spec (exists_twE6_sc_aut_lift hn3 hK σ hσ ε) u]

@[simp] theorem twE6ScAutHom_apply (δ : MulAut ↥(twistedE6RootGroup K σ))
    (u : ↥(fixedGroup K σ.toRingHom)) :
    twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ
        (twE6ScAutHom hn3 hK σ hσ δ u) =
      δ (twistedIsogenyC (f := n) (by omega) hK σ.toRingHom hσ u) :=
  Classical.choose_spec (exists_twE6_sc_aut_lift hn3 hK σ hσ δ) u

end SCAut

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
