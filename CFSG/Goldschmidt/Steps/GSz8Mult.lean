module

public import CFSG.Goldschmidt.Steps.GSz8MultBasic
public import CFSG.Goldschmidt.Steps.G3MFSz8
public import Certificates.Certificate113
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public noncomputable section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped commutatorElement

namespace GSz8Mult

local notation "𝔽" => BinaryGaloisField (2 * 1 + 1)
local notation "Sz8" => SuzukiMatrixGroup 1

theorem card_field : Nat.card 𝔽 = 8 := by
  rw [GaloisField.card 2 (2 * 1 + 1) (by norm_num)]
  norm_num

theorem two_eq_zero : (2 : 𝔽) = 0 := CharTwo.two_eq_zero

theorem pow_eight (a : 𝔽) : a ^ 8 = a := by
  have : Fintype 𝔽 := Fintype.ofFinite 𝔽
  have h := FiniteField.pow_card a
  rwa [← Nat.card_eq_fintype_card, card_field] at h

theorem pow_seven {a : 𝔽} (ha : a ≠ 0) : a ^ 7 = 1 := by
  have h := pow_eight a
  rw [show 8 = 7 + 1 from rfl, pow_succ] at h
  exact (mul_left_eq_self₀.mp h).resolve_right ha

theorem exists_ne_zero_ne_one : ∃ b : 𝔽, b ≠ 0 ∧ b ≠ 1 := by
  classical
  have : Fintype 𝔽 := Fintype.ofFinite 𝔽
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset 𝔽) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_field] at hle
  have h2 := Finset.card_le_two (a := (0 : 𝔽)) (b := 1)
  omega

theorem moore_eq_one {β : 𝔽} (h0 : β ≠ 0) (h1 : β ≠ 1) :
    β ^ 2 * (β ^ 2 * 1 ^ 4 + (β ^ 2) ^ 4 * 1) + (β * (β ^ 2) ^ 4 + β ^ 4 * β ^ 2) +
      (β ^ 2) ^ 2 * (1 * β ^ 4 + 1 ^ 4 * β) = 1 := by
  have h8 := pow_eight β
  have hS : 1 + β + β ^ 2 + β ^ 3 + β ^ 4 + β ^ 5 + β ^ 6 = 0 := by
    have h : (β - 1) * (1 + β + β ^ 2 + β ^ 3 + β ^ 4 + β ^ 5 + β ^ 6) = 0 := by
      linear_combination pow_seven h0
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)
  linear_combination (1 + β + β ^ 2) * h8 + hS - two_eq_zero

def root (a b : 𝔽) : Sz8 := (suzukiCoverRootElement 1 a b : suzukiCoverRoot 1)

theorem root_mul (a b c d : 𝔽) : root a b * root c d = root (a + c) (b + d + a * c ^ 4) := by
  have h := suzukiCoverRootElement_mul 1 one_pos a b c d
  rw [suzukiCoverTits_apply, show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
  rw [root, root, root, ← Subgroup.coe_mul, h]

theorem root_zero : root 0 0 = 1 := by
  rw [root, suzukiCoverRootElement_zero_zero]
  rfl

theorem root_inv (a b : 𝔽) : (root a b)⁻¹ = root a (b + a * a ^ 4) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [root_mul, ← root_zero]
  congr 1
  · linear_combination a * two_eq_zero
  · linear_combination (b + a * a ^ 4) * two_eq_zero

theorem root_conj (a b c d : 𝔽) :
    root a b * root c d * (root a b)⁻¹ = root c (d + a * c ^ 4 + a ^ 4 * c) := by
  rw [root_inv, root_mul, root_mul]
  congr 1
  · linear_combination a * two_eq_zero
  · linear_combination (b + a * a ^ 4) * two_eq_zero

theorem root_commutator (a b c d : 𝔽) :
    ⁅root a b, root c d⁆ = root 0 (a * c ^ 4 + a ^ 4 * c) := by
  rw [commutatorElement_def, root_conj, root_inv, root_mul]
  congr 1
  · linear_combination c * two_eq_zero
  · linear_combination (d + c * c ^ 4) * two_eq_zero

theorem root_injective {a b c d : 𝔽} (h : root a b = root c d) : a = c ∧ b = d :=
  suzukiCoverRootElement_injective 1 a b c d (Subtype.ext h)

theorem root_mem (a b : 𝔽) : root a b ∈ suzukiCoverRoot 1 := (suzukiCoverRootElement 1 a b).2

theorem exists_eq_root {x : Sz8} (hx : x ∈ suzukiCoverRoot 1) : ∃ a b, x = root a b := by
  obtain ⟨a, b, h⟩ := suzukiCoverRootElement_surjective 1 ⟨x, hx⟩
  exact ⟨a, b, by rw [root, h]⟩

def torus (x : 𝔽ˣ) : Sz8 := (suzukiCoverTorusHom 1 x : suzukiCoverTorus 1)

theorem torus_conj (x : 𝔽ˣ) (a b : 𝔽) :
    torus x * root a b * (torus x)⁻¹ = root (x * a) (x * x ^ 4 * b) := by
  have h := congrArg Subtype.val (suzukiCoverTorus_action_root 1 x a b)
  rw [coverNormalizerAction_coe, suzukiCoverTits_apply,
    show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
  exact h

section Commutators

variable {K : Type*} [Group K]

theorem commutatorElement_mul_right_of_mem_center {u w w' : K}
    (h : ⁅u, w'⁆ ∈ Subgroup.center K) : ⁅u, w * w'⁆ = ⁅u, w⁆ * ⁅u, w'⁆ := by
  obtain ⟨c, hcd⟩ : ∃ c, c = ⁅u, w'⁆ := ⟨_, rfl⟩
  rw [← hcd] at h ⊢
  have hc := Subgroup.mem_center_iff.mp h
  calc ⁅u, w * w'⁆ = u * w * u⁻¹ * c * w⁻¹ := by
        rw [hcd, commutatorElement_def, commutatorElement_def]; group
    _ = c * (u * w * u⁻¹) * w⁻¹ := by rw [hc (u * w * u⁻¹)]
    _ = c * ⁅u, w⁆ := by rw [commutatorElement_def]; group
    _ = ⁅u, w⁆ * c := (hc _).symm

theorem commutatorElement_mul_right_central {x y z : K} (hz : z ∈ Subgroup.center K) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hc := Subgroup.mem_center_iff.mp hz
  calc ⁅x, y * z⁆ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by rw [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [← hc x⁻¹]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_mul_left_of_commute {u v w : K} (h : v * w = w * v) :
    ⁅u * v, w⁆ = ⁅u, w⁆ := by
  calc ⁅u * v, w⁆ = u * (v * w) * v⁻¹ * u⁻¹ * w⁻¹ := by rw [commutatorElement_def]; group
    _ = u * (w * v) * v⁻¹ * u⁻¹ * w⁻¹ := by rw [h]
    _ = ⁅u, w⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_conj (t x y : K) :
    ⁅t * x * t⁻¹, t * y * t⁻¹⁆ = t * ⁅x, y⁆ * t⁻¹ := by
  simp only [commutatorElement_def]
  group

end Commutators

section Pairing

variable {K : Type} [Group K] {π : K →* Sz8} (hπ : Function.Surjective π)

def rootLift (a b : 𝔽) : K := Function.surjInv hπ (root a b)

theorem map_rootLift (a b : 𝔽) : π (rootLift hπ a b) = root a b :=
  Function.surjInv_eq hπ _

def pair (a c : 𝔽) : K := ⁅rootLift hπ a 0, rootLift hπ 0 c⁆

variable (hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center K)
  (hA : ∀ b c : K, (∃ s, π b = root 0 s) → (∃ s, π c = root 0 s) → b * c = c * b)
include hπ hker hA

theorem pair_spec {x y : K} {a b c : 𝔽} (hx : π x = root a b) (hy : π y = root 0 c) :
    ⁅x, y⁆ = pair hπ a c := by
  set u := rootLift hπ a 0
  set w := rootLift hπ 0 c
  have hu : π u = root a 0 := map_rootLift hπ a 0
  have hw : π w = root 0 c := map_rootLift hπ 0 c
  have hv : π (u⁻¹ * x) = root 0 b := by
    rw [map_mul, map_inv, hu, hx, root_inv, root_mul]
    congr 1
    · linear_combination a * two_eq_zero
    · linear_combination (a * a ^ 4) * two_eq_zero
  have hz : w⁻¹ * y ∈ Subgroup.center K :=
    (hker _).mp (by rw [map_mul, map_inv, hw, hy, inv_mul_cancel])
  have hvw : (u⁻¹ * x) * w = w * (u⁻¹ * x) := hA _ _ ⟨b, hv⟩ ⟨c, hw⟩
  calc ⁅x, y⁆ = ⁅u * (u⁻¹ * x), w * (w⁻¹ * y)⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
    _ = ⁅u * (u⁻¹ * x), w⁆ := commutatorElement_mul_right_central hz
    _ = ⁅u, w⁆ := commutatorElement_mul_left_of_commute hvw
    _ = pair hπ a c := rfl

omit hA in
theorem pair_mem_center (a c : 𝔽) : pair hπ a c ∈ Subgroup.center K := by
  refine (hker _).mp ?_
  rw [pair, map_commutatorElement, map_rootLift, map_rootLift, root_commutator]
  simp [root_zero]

theorem pair_zero_left (c : 𝔽) : pair hπ 0 c = 1 := by
  rw [← pair_spec hπ hker hA (x := 1) (a := 0) (b := 0) (by rw [map_one, root_zero])
    (map_rootLift hπ 0 c), commutatorElement_one_left]

theorem pair_zero_right (a : 𝔽) : pair hπ a 0 = 1 := by
  rw [← pair_spec hπ hker hA (y := 1) (c := 0) (map_rootLift hπ a 0)
    (by rw [map_one, root_zero]), commutatorElement_one_right]

theorem pair_add (a c c' : 𝔽) : pair hπ a (c + c') = pair hπ a c * pair hπ a c' := by
  have h := pair_spec hπ hker hA (x := rootLift hπ a 0) (y := rootLift hπ 0 c * rootLift hπ 0 c')
    (c := c + c') (map_rootLift hπ a 0)
    (by rw [map_mul, map_rootLift, map_rootLift, root_mul, zero_add, zero_mul, add_zero])
  rw [← h]
  exact commutatorElement_mul_right_of_mem_center (pair_mem_center hπ hker a c')

theorem pair_torus (x : 𝔽ˣ) (a c : 𝔽) :
    pair hπ (x * a) (x * x ^ 4 * c) = pair hπ a c := by
  set t := Function.surjInv hπ (torus x)
  have ht : π t = torus x := Function.surjInv_eq hπ _
  have h1 : π (t * rootLift hπ a 0 * t⁻¹) = root (x * a) 0 := by
    rw [map_mul, map_mul, map_inv, ht, map_rootLift, torus_conj, mul_zero]
  have h2 : π (t * rootLift hπ 0 c * t⁻¹) = root 0 (x * x ^ 4 * c) := by
    rw [map_mul, map_mul, map_inv, ht, map_rootLift, torus_conj, mul_zero]
  rw [← pair_spec hπ hker hA h1 h2, commutatorElement_conj]
  change t * pair hπ a c * t⁻¹ = pair hπ a c
  rw [Subgroup.mem_center_iff.mp (pair_mem_center hπ hker a c) t, mul_inv_cancel_right]

theorem pair_eq_pair_one (a c : 𝔽) : pair hπ a c = pair hπ 1 (a ^ 2 * c) := by
  by_cases ha : a = 0
  · rw [ha, pair_zero_left hπ hker hA, zero_pow two_ne_zero, zero_mul,
      pair_zero_right hπ hker hA]
  · have h := pair_torus hπ hker hA (Units.mk0 a ha) 1 (a ^ 2 * c)
    rwa [Units.val_mk0, mul_one,
      show a * a ^ 4 * (a ^ 2 * c) = c by
        rw [show a * a ^ 4 * (a ^ 2 * c) = a ^ 7 * c by ring, pow_seven ha, one_mul]] at h

theorem pair_jacobi (α β γ : 𝔽) :
    pair hπ β (γ * α ^ 4 + γ ^ 4 * α) * pair hπ α (β * γ ^ 4 + β ^ 4 * γ) *
      pair hπ γ (α * β ^ 4 + α ^ 4 * β) = 1 := by
  set x := rootLift hπ α 0
  set y := rootLift hπ β 0
  set z := rootLift hπ γ 0
  have hx : π x = root α 0 := map_rootLift hπ α 0
  have hy : π y = root β 0 := map_rootLift hπ β 0
  have hz : π z = root γ 0 := map_rootLift hπ γ 0
  have key : ∀ (p q r : K) (a b c : 𝔽), π p = root a 0 → π q = root b 0 → π r = root c 0 →
      ⁅⁅p, q⁆, q * r * q⁻¹⁆ = (pair hπ c (a * b ^ 4 + a ^ 4 * b))⁻¹ := by
    intro p q r a b c hp hq hr
    rw [← commutatorElement_inv (q * r * q⁻¹) ⁅p, q⁆]
    congr 1
    refine pair_spec hπ hker hA (a := c) (b := 0 + b * c ^ 4 + b ^ 4 * c) ?_ ?_
    · rw [map_mul, map_mul, map_inv, hq, hr, root_conj]
    · rw [map_commutatorElement, hp, hq, root_commutator]
  have hHW := commutatorElement_commutatorElement_conj_mul x y z
  rw [key x y z α β γ hx hy hz, key y z x β γ α hy hz hx, key z x y γ α β hz hx hy] at hHW
  calc _ = ((pair hπ γ (α * β ^ 4 + α ^ 4 * β))⁻¹ * (pair hπ α (β * γ ^ 4 + β ^ 4 * γ))⁻¹ *
        (pair hπ β (γ * α ^ 4 + γ ^ 4 * α))⁻¹)⁻¹ := by group
    _ = 1 := by rw [hHW, inv_one]

theorem pair_one_one : pair hπ 1 1 = (1 : K) := by
  obtain ⟨β, h0, h1⟩ := exists_ne_zero_ne_one
  have h := pair_jacobi hπ hker hA 1 β (β ^ 2)
  rw [pair_eq_pair_one hπ hker hA β, pair_eq_pair_one hπ hker hA (β ^ 2),
    ← pair_add hπ hker hA, ← pair_add hπ hker hA, moore_eq_one h0 h1] at h
  exact h

theorem card_center_le_four [Finite K]
    (hS : ∀ b : K, (∃ s, π b = root 0 s) → b ∉ Subgroup.center K →
      ∀ z ∈ Subgroup.center K, ∃ x : K, (∃ a t, π x = root a t) ∧ ⁅x, b⁆ = z) :
    Nat.card (Subgroup.center K) ≤ 4 := by
  let φ : Multiplicative 𝔽 →* K :=
    { toFun := fun s => pair hπ 1 s.toAdd
      map_one' := pair_zero_right hπ hker hA 1
      map_mul' := fun s t => pair_add hπ hker hA 1 s.toAdd t.toAdd }
  have hφ : ∀ s : 𝔽, φ (Multiplicative.ofAdd s) = pair hπ 1 s := fun _ => rfl
  have hcard : Nat.card φ.ker * Nat.card φ.range = 8 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, ← card_field]
    exact Nat.card_congr Multiplicative.toAdd
  have hker2 : 2 ≤ Nat.card φ.ker := by
    refine (Subgroup.one_lt_card_iff_ne_bot _).mpr fun hbot => ?_
    have h1 : Multiplicative.ofAdd (1 : 𝔽) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hφ]
      exact pair_one_one hπ hker hA
    rw [hbot, Subgroup.mem_bot] at h1
    exact one_ne_zero (Multiplicative.ofAdd.injective (h1.trans (ofAdd_zero (α := 𝔽)).symm))
  have hrange : Nat.card φ.range ≤ 4 := by
    have h := Nat.mul_le_mul_right (Nat.card φ.range) hker2
    rw [hcard] at h
    omega
  have hZ : Subgroup.center K ≤ φ.range := by
    intro z hz
    set b := rootLift hπ 0 1
    have hb : π b = root 0 1 := map_rootLift hπ 0 1
    have hbZ : b ∉ Subgroup.center K := fun h =>
      one_ne_zero (root_injective (hb.symm.trans (((hker b).mpr h).trans root_zero.symm))).2
    obtain ⟨x, ⟨a, t, hx⟩, rfl⟩ := hS b ⟨1, hb⟩ hbZ z hz
    exact ⟨Multiplicative.ofAdd (a ^ 2 * 1), by
      rw [hφ, ← pair_eq_pair_one hπ hker hA, pair_spec hπ hker hA hx hb]⟩
  exact (Subgroup.card_le_of_le hZ).trans hrange

end Pairing

end GSz8Mult

theorem GSz8Mult : S_GSz8Mult := by
  intro K _ _ hK ⟨e⟩
  have hZ := GSz8Mult.isElemAbelian_center hK e
  let e' := e.trans (suzukiCoverNativeEquiv 1)
  let π : K →* SuzukiMatrixGroup 1 :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center K :=
    (MonoidHom.ker_comp_of_injective _ e'.toMonoidHom e'.injective).trans
      (QuotientGroup.ker_mk' _)
  have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center K := fun x => by
    rw [← hkerπ, MonoidHom.mem_ker]
  have hT2 : IsPGroup 2 ((suzukiCoverRoot 1).comap π) :=
    (suzukiCoverRoot_structure 1 one_pos).1.comap_of_ker_isPGroup π
      (by rw [hkerπ]; exact GSz8Mult.isPGroup_center hK e)
  have hTi : ¬ 2 ∣ ((suzukiCoverRoot 1).comap π).index := by
    rw [Subgroup.index_comap_of_surjective _ hπ]
    exact (suzukiCoverRoot_index_odd 1 one_pos).not_two_dvd_nat
  let T : Sylow 2 K := hT2.toSylow hTi
  have hTmem : ∀ x, x ∈ (T : Subgroup K) ↔ π x ∈ suzukiCoverRoot 1 := fun _ => Iff.rfl
  obtain ⟨hGa, hGb⟩ := GMFSz8 K hK hZ ⟨e⟩ T
  have hAT : ∀ b : K, (∃ s, π b = GSz8Mult.root 0 s) → b ∈ (T : Subgroup K) ∧
      ∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K := by
    rintro b ⟨s, hs⟩
    refine ⟨(hTmem b).mpr (by rw [hs]; exact GSz8Mult.root_mem 0 s), fun x hx => (hker _).mp ?_⟩
    obtain ⟨a, t, hat⟩ := GSz8Mult.exists_eq_root ((hTmem x).mp hx)
    rw [← commutatorElement_def, map_commutatorElement, hs, hat, GSz8Mult.root_commutator]
    simp [GSz8Mult.root_zero]
  refine GSz8Mult.card_center_le_four hπ hker (fun b c hb hc => ?_) fun b hb hbZ z hz => ?_
  · exact (hGa b (hAT b hb).1 c (hAT c hc).1 (hAT b hb).2 (hAT c hc).2).1
  · obtain ⟨x, hx, hxz⟩ := hGb b (hAT b hb).1 (hAT b hb).2 hbZ z hz
    exact ⟨x, GSz8Mult.exists_eq_root ((hTmem x).mp hx), by rw [commutatorElement_def, hxz]⟩

end CFSG.Goldschmidt
