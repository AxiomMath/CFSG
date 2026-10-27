module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

namespace L2CompQuasi

theorem center_eq_bot_of_psl3 {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 r f) : Subgroup.center K = ⊥ := by
  have hQ : LieModel (K ⧸ Subgroup.center K) .PSL 3 r f := Or.inl ⟨by simp [classicalTags], hmodel⟩
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker = Subgroup.center K := QuotientGroup.ker_mk' _
  obtain ⟨-, hdvd⟩ := CFSG.LieType.Steinberg.odd_field_higher_linear_perfect_central_two_kernel_cyclic
    (p := r) (f := f) (n := 3) hr2 hKp (η := QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) hker.le (by rw [hker]; exact hZ2) hQ
  rw [hker] at hdvd
  have h3 : Nat.card (Subgroup.center K) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ2
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    have := h2.trans h3
    omega
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.1 hk

theorem center_eq_bot_of_psu3 {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 r f) : Subgroup.center K = ⊥ := by
  classical
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have hr : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hud : UnitaryFieldData r f F := ⟨hr, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite F := hud.finite
  have : Fact r.Prime := ⟨hr⟩
  have := hud.charP
  have hK : Nat.card F = (r ^ f) ^ 2 := hud.card_eq_sq
  let ψ : K ⧸ Subgroup.center K ≃* unitaryPSU hud 3 :=
    e₀.trans (unitaryPSUEquiv hud (by omega)).symm
  let θ : unitarySU r f F 3 →* K ⧸ Subgroup.center K :=
    ψ.symm.toMonoidHom.comp (unitaryProj hud 3)
  have hθ : Function.Surjective θ := ψ.symm.surjective.comp (unitaryProj_surjective hud 3)
  have hθ1 : ∀ g : unitarySU r f F 3, θ g = 1 ↔ g ∈ unitaryScalars hud 3 := by
    intro g
    change ψ.symm (unitaryProj hud 3 g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]
  have hPp : Group.IsPerfect ↥(unitarySU r f F 3) := (isPerfect_and_center_unitarySU' hud hr2 le_rfl).1
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(unitarySU r f F 3)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : ↥(unitarySU r f F 3) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hcen h2'
    set ι := CFSG.LieType.Universal.Unitary.equivStatedSU hK 3 with hι
    let π' : E →* CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F r f) 3 :=
      ι.symm.toMonoidHom.comp π
    have hπ' : Function.Surjective π' := ι.symm.surjective.comp hπ
    have hker : π'.ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      change ι.symm (π x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.su_central_two_extension_splitting hK hr2 (n := 3) (by omega) hπ'
      (hker ▸ hcen) (hker ▸ h2')
    refine ⟨s.comp ι.symm.toMonoidHom, fun x => ?_⟩
    have := hs (ι.symm x)
    change ι.symm (π (s (ι.symm x))) = ι.symm x at this
    exact ι.symm.injective this
  let η : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hη2 : IsPGroup 2 η.ker := by rw [hηker]; exact hZ2
  obtain ⟨α, hα, hαs, hαker⟩ := exists_surjective_of_isPerfect (K := unitarySU r f F 3) (P := K)
    (Q := K ⧸ Subgroup.center K) hsplit (β := θ) hθ hη hηker.le hη2
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : z ∈ θ.ker.map α := by rw [← hαker, hηker]; exact hz
  obtain ⟨s, hs, rfl⟩ := hz'
  have hsc : s ∈ unitaryScalars hud 3 := (hθ1 s).1 hs
  obtain ⟨c, -, hc3, hcs⟩ := mem_unitaryScalars.1 hsc
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hcs, ← map_pow, hc3, map_one]
    rfl
  have hz3 : (α s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
  have hzo : orderOf (α s) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  obtain ⟨k, hk⟩ := hZ2 ⟨α s, hz⟩
  have h1 : (α s) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : orderOf (α s) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime Nat.prime_three).1 hzo with h3 | h3
  · exact orderOf_eq_one_iff.1 h3
  · rw [h3] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega

end L2CompQuasi

end CFSG.GH74.Generic.BProg.B3
