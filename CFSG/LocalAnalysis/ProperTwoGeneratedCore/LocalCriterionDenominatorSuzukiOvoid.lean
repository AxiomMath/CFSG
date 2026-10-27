module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorDerangementAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiCommutant

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI
open scoped Matrix LinearAlgebra.Projectivization Pointwise

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "P" => ℙ K (Fin 4 → K)

@[expose] def suzukiOvoidInfinity : P :=
  Projectivization.mk K ![1, 0, 0, 0] (by simp)

@[expose] def suzukiOvoidFinitePoint (x y : K) : P :=
  Projectivization.mk K
    ![x * y + suzukiCoverTits m x * x ^ 2 + suzukiCoverTits m y, y, x, 1] (by simp)

@[expose] def suzukiOvoidSet : Set P :=
  {suzukiOvoidInfinity m} ∪ Set.range fun z : K × K => suzukiOvoidFinitePoint m z.1 z.2

local notation "Omega" => {p : P // p ∈ suzukiOvoidSet m}

theorem suzuki_ovoid_preserved (g : SzG) (p : P) (hp : p ∈ suzukiOvoidSet m) :
    (suzukiNaturalRepresentation m g).toLinearEquiv • p ∈ suzukiOvoidSet m :=
  (suzukiMatrixGroup_ovoid_action_data m (suzukiCoverTits m)
    (suzukiCoverTits_apply m)).1 g p hp

@[expose, instance_reducible] def suzukiOvoidAction : MulAction SzG Omega where
  smul g p := ⟨(suzukiNaturalRepresentation m g).toLinearEquiv • p.val,
    suzuki_ovoid_preserved m g p.val p.property⟩
  one_smul p := by
    apply Subtype.ext
    change (suzukiNaturalRepresentation m 1).toLinearEquiv • p.val = p.val
    rw [map_one]
    exact one_smul _ p.val
  mul_smul g h p := by
    apply Subtype.ext
    change (suzukiNaturalRepresentation m (g * h)).toLinearEquiv • p.val =
      (suzukiNaturalRepresentation m g).toLinearEquiv •
        ((suzukiNaturalRepresentation m h).toLinearEquiv • p.val)
    rw [map_mul, LinearMap.GeneralLinearGroup.toLinearEquiv_mul, mul_smul]

theorem suzuki_ovoid_card : Nat.card Omega = (2 ^ (2 * m + 1)) ^ 2 + 1 :=
  (suzukiMatrixGroup_ovoid_action_data m (suzukiCoverTits m)
    (suzukiCoverTits_apply m)).2.2.2

instance suzuki_ovoid_finite : Finite Omega :=
  (Nat.card_pos_iff.mp (show 0 < Nat.card Omega by
    rw [suzuki_ovoid_card]; omega)).2

theorem suzuki_ovoid_two_transitive :
    letI := suzukiOvoidAction m
    MulAction.IsMultiplyPretransitive SzG Omega 2 := by
  let := suzukiOvoidAction m
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g, hga, hgb⟩ :=
    (suzukiMatrixGroup_ovoid_action_data m (suzukiCoverTits m)
      (suzukiCoverTits_apply m)).2.2.1 a.val b.val c.val d.val
      a.property b.property c.property d.property
      (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩

theorem suzuki_ovoid_three_point_free (hm : 0 < m) :
    letI := suzukiOvoidAction m
    ∀ g : SzG, g ≠ 1 → ∀ a b c : Omega,
      a ≠ b → a ≠ c → b ≠ c →
        ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
  let := suzukiOvoidAction m
  intro g hg a b c hab hac hbc hfix
  apply hg
  apply (huppert_blackburn_XI_3_3 m hm (suzukiCoverTits m)
    (suzukiCoverTits_apply m)).2.2.2.2.1 g
  exact ⟨a.val, b.val, c.val, a.property, b.property, c.property,
    (fun h => hab (Subtype.ext h)), (fun h => hac (Subtype.ext h)),
    (fun h => hbc (Subtype.ext h)), congrArg Subtype.val hfix.1,
    congrArg Subtype.val hfix.2.1, congrArg Subtype.val hfix.2.2⟩

theorem suzuki_ovoid_involution_unique_fixed (hm : 0 < m) :
    letI := suzukiOvoidAction m
    ∀ t : SzG, orderOf t = 2 → ∃! a : Omega, t • a = a := by
  let := suzukiOvoidAction m
  intro t ht
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card
    exact (show Nat.card (Subgroup.zpowers t) = 2 ^ 1 by
      simp only [Nat.card_zpowers, ht, pow_one])
  obtain ⟨T, hT⟩ := hTp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SzG T (suzukiCoverSylow m hm)
  have htT : t ∈ (T : Subgroup SzG) := hT (Subgroup.mem_zpowers t)
  have hgt : (MulAut.conj g) t ∈ suzukiCoverRoot m := by
    change (MulAut.conj g) t ∈ (suzukiCoverSylow m hm : Subgroup SzG)
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) (T : Subgroup SzG) htT
  let s : suzukiCoverRoot m := ⟨(MulAut.conj g) t, hgt⟩
  have hs : s ≠ 1 := by
    intro h
    have ht1 : t = 1 := (MulAut.conj g).injective
      ((congrArg Subtype.val h).trans (map_one _).symm)
    rw [ht1, orderOf_one] at ht
    omega
  obtain ⟨hsfix, hsuniq⟩ := suzuki_root_unique_ovoid_fixed m hm s hs
  let a : Omega := ⟨suzukiOvoidInfinity m, Or.inl rfl⟩
  have ha : (MulAut.conj g) t • a = a := Subtype.ext hsfix
  have huniq : ∀ b : Omega, (MulAut.conj g) t • b = b → b = a := by
    intro b hb
    exact Subtype.ext (hsuniq b.val b.property (congrArg Subtype.val hb))
  refine ⟨g⁻¹ • a, ?_, ?_⟩
  · have h := congrArg (fun b : Omega => g⁻¹ • b) ha
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using h
  · intro b hb
    have hgb : (MulAut.conj g) t • (g • b) = g • b := by
      simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hb]
    have h := congrArg (fun c : Omega => g⁻¹ • c) (huniq (g • b) hgb)
    simpa only [inv_smul_smul] using h

theorem suzuki_ovoid_derangement_odd (hm : 0 < m) (g : SzG) :
    letI := suzukiOvoidAction m
    (∀ a : Omega, g • a ≠ a) → Odd (orderOf g) := by
  let := suzukiOvoidAction m
  exact derangement_order_odd_of_involution_unique_fixed
    (suzuki_ovoid_involution_unique_fixed m hm) g

theorem suzuki_ovoid_derangement_full_centralizer_free (hm : 0 < m) (g : SzG) :
    letI := suzukiOvoidAction m
    (∀ a : Omega, g • a ≠ a) →
      ∀ c : Subgroup.centralizer ({g} : Set SzG), ∀ a : Omega,
        (c : SzG) • a = a → c = 1 := by
  let := suzukiOvoidAction m
  intro hg
  exact odd_derangement_full_centralizer_free (suzuki_ovoid_three_point_free m hm)
    g (suzuki_ovoid_derangement_odd m hm g hg) hg

theorem suzuki_ovoid_derangement_full_centralizer_card_dvd (hm : 0 < m) (g : SzG) :
    letI := suzukiOvoidAction m
    (∀ a : Omega, g • a ≠ a) →
      Nat.card (Subgroup.centralizer ({g} : Set SzG)) ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let := suzukiOvoidAction m
  intro hg
  rw [← suzuki_ovoid_card]
  exact free_action_card_dvd (suzuki_ovoid_derangement_full_centralizer_free m hm g hg)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
