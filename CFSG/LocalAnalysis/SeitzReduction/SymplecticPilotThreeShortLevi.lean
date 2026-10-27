module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotTorusConj

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.LinearPilot (diagUnit coe_diagUnit)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem spCompl12_zero_eq : spCompl12 K 0 = longRootSp2 K 3 (0 : Fin 3) := by
  rw [spCompl12_eq_suppGroup, longRootSp2_eq_suppGroup]
  congr 1
  ext t
  rcases t with i | i <;> fin_cases i <;> simp [OffPQ, mem_coords]

theorem a2Levi_zero_eq :
    a2Levi K 0 = (shortBlock K one_ne_two_three).range ⊔ longRootSp2 K 3 (0 : Fin 3) := by
  rw [a2Levi, spCompl12_zero_eq]

theorem commute_range_shortBlock_longRootSp2 {s v : StatedSp 3 K}
    (hs : s ∈ (shortBlock K one_ne_two_three).range) (hv : v ∈ longRootSp2 K 3 (0 : Fin 3)) :
    Commute s v := by
  obtain ⟨A, rfl⟩ := hs
  have hY : shortBlock K one_ne_two_three A ∈ complSp K (0 : Fin 3) := by
    rw [mem_complSp]
    intro x y hxy
    refine isSupp_shortBlock one_ne_two_three A x y fun h => hxy ⟨?_, ?_⟩
    · rcases h.1 with hx | hx <;> rcases mem_coords.1 hx with rfl | rfl <;> simp [mem_coords]
    · rcases h.2 with hy | hy <;> rcases mem_coords.1 hy with rfl | rfl <;> simp [mem_coords]
  exact (commute_of_mem_longRootSp2_of_mem_complSp hv hY).symm

variable [CharP K 2]

theorem eq_one_of_mem_longRootSp2_of_commute {v : StatedSp 3 K}
    (hv : v ∈ longRootSp2 K 3 (0 : Fin 3))
    (hc : ∀ w ∈ longRootSp2 K 3 (0 : Fin 3), v * w = w * v) : v = 1 := by
  obtain ⟨A, rfl⟩ := hv
  have hA : A ∈ center SL(2, K) := by
    rw [mem_center_iff]
    intro B
    apply longBlock_injective (K := K) (n := 3) (0 : Fin 3)
    rw [map_mul, map_mul]
    exact (hc _ ⟨B, rfl⟩).symm
  have hA' : longBlockEquivOne K A ∈ center (StatedSp 1 K) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨B, rfl⟩ := (longBlockEquivOne K).surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hA) B]
  rw [center_statedSp_eq_bot, mem_bot, MulEquiv.map_eq_one_iff] at hA'
  rw [hA', map_one]

theorem mem_range_shortBlock_of_mem_a2Levi {m : StatedSp 3 K} (hm : m ∈ a2Levi K 0)
    (hc : ∀ w ∈ longRootSp2 K 3 (0 : Fin 3), m * w = w * m) :
    m ∈ (shortBlock K one_ne_two_three).range := by
  rw [a2Levi_zero_eq] at hm
  obtain ⟨s, hs, v, hv, rfl⟩ := F4Pilot.exists_mul_eq_of_mem_sup_of_commute
    (fun s hs v hv => commute_range_shortBlock_longRootSp2 hs hv) hm
  have hv1 : v = 1 := by
    refine eq_one_of_mem_longRootSp2_of_commute hv fun w hw => ?_
    have h1 := hc w hw
    have h2 : s * w = w * s := (commute_range_shortBlock_longRootSp2 hs hw).eq
    have h3 : s * (v * w) = s * (w * v) := by
      calc s * (v * w) = s * v * w := by group
        _ = w * (s * v) := h1
        _ = (w * s) * v := by group
        _ = (s * w) * v := by rw [h2]
        _ = s * (w * v) := by group
    exact mul_left_cancel h3
  rw [hv1, mul_one]
  exact hs

omit [CharP K 2] in
theorem hsl_eq_diagUnit (l : Kˣ) : CFSG.LieType.Chevalley.HSL l = diagUnit l := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_mem_a2Levi_conj_shortTorus [Finite K] (hK : 4 ≤ Nat.card K)
    (β : (wRadical K (1 : Fin 3) 2 ⊔ a2Levi K 0 : Subgroup (StatedSp 3 K)) ≃*
      (wRadical K (1 : Fin 3) 2 ⊔ a2Levi K 0 : Subgroup (StatedSp 3 K)))
    (hβ : ((wRadical K (1 : Fin 3) 2).subgroupOf (wRadical K (1 : Fin 3) 2 ⊔ a2Levi K 0)).map
      β.toMonoidHom = (wRadical K (1 : Fin 3) 2).subgroupOf (wRadical K (1 : Fin 3) 2 ⊔ a2Levi K 0))
    (ι : a2Levi K 0 ≃* a2Levi K 0)
    (hι : ∀ m : a2Levi K 0, ((ι m : a2Levi K 0) : StatedSp 3 K)⁻¹ *
      (β (inclusion le_sup_right m) : StatedSp 3 K) ∈ wRadical K (1 : Fin 3) 2) :
    ∃ c ∈ a2Levi K 0, ∀ m : a2Levi K 0, (m : StatedSp 3 K) ∈ shortTorus K →
      c⁻¹ * (ι m : StatedSp 3 K) * c ∈ shortTorus K := by
  classical
  have hQM := disjoint_spCoreRadical_spCoreLevi (K := K) (n := 0) .a2
  have hMN := spCoreLevi_le_normalizer_spCoreRadical (K := K) (n := 0) .a2
  have hιeq : ∀ m, ι m = EPilot.leviAutOfAut (spCoreRadical K 0 .a2) (spCoreLevi K 0 .a2) hQM hMN
      β hβ m := fun m => ((EPilot.leviAutOfAut_eq_iff hQM hMN hβ m (ι m)).2 (hι m)).symm
  have hS := map_leviAutOfAut_spCoreFactor (K := K) (n := 0) hK .a2 β hβ
  have hSP : ∀ w : a2Levi K 0, (w : StatedSp 3 K) ∈ longRootSp2 K 3 (0 : Fin 3) →
      ∃ w' : a2Levi K 0, (w' : StatedSp 3 K) ∈ longRootSp2 K 3 (0 : Fin 3) ∧ ι w' = w := by
    intro w hw
    have hw' : w ∈ (spCoreFactor K 0 .a2).subgroupOf (spCoreLevi K 0 .a2) := by
      change (w : StatedSp 3 K) ∈ spCompl12 K 0
      rw [spCompl12_zero_eq]
      exact hw
    rw [← hS] at hw'
    obtain ⟨w', hw'S, hw'w⟩ := hw'
    refine ⟨w', ?_, (hιeq w').trans hw'w⟩
    have h1 : (w' : StatedSp 3 K) ∈ spCompl12 K 0 := hw'S
    rwa [spCompl12_zero_eq] at h1
  have hSL : ∀ m : a2Levi K 0, (m : StatedSp 3 K) ∈ (shortBlock K one_ne_two_three).range →
      ((ι m : a2Levi K 0) : StatedSp 3 K) ∈ (shortBlock K one_ne_two_three).range := by
    intro m hm
    refine mem_range_shortBlock_of_mem_a2Levi (ι m).2 fun w hw => ?_
    have hwM : w ∈ a2Levi K 0 := by
      rw [a2Levi_zero_eq]
      exact mem_sup_right hw
    obtain ⟨w', hw'P, hw'⟩ := hSP ⟨w, hwM⟩ hw
    have hw'' : w = ((ι w' : a2Levi K 0) : StatedSp 3 K) := by rw [hw']
    have hmw : m * w' = w' * m :=
      Subtype.ext (commute_range_shortBlock_longRootSp2 hm hw'P).eq
    have h := congrArg (fun x => ((ι x : a2Levi K 0) : StatedSp 3 K)) hmw
    simp only [map_mul, Subgroup.coe_mul] at h
    rw [hw'']
    exact h
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  set y₀ : a2Levi K 0 := ⟨shortTorusHom K ζ, shortTorus_le_a2Levi ⟨ζ, rfl⟩⟩ with hy₀
  obtain ⟨A, hA⟩ := hSL y₀ (shortTorus_le_range_shortBlock ⟨ζ, rfl⟩)
  have hcardK : Nat.card K - 1 = Nat.card Kˣ := (Nat.card_units K).symm
  have hy₀q : y₀ ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    rw [hcardK, SubgroupClass.coe_pow, hy₀]
    change shortTorusHom K ζ ^ Nat.card Kˣ = 1
    rw [← map_pow, pow_card_eq_one', map_one]
  have hAq : A ^ (Nat.card K - 1) = 1 := by
    apply shortBlock_injective (K := K) one_ne_two_three
    rw [map_pow, hA, ← SubgroupClass.coe_pow, ← map_pow, hy₀q, map_one, OneMemClass.coe_one,
      map_one]
  have hζ1 : ζ ≠ 1 := by
    intro h
    have hK2 : 2 < Nat.card Kˣ := by rw [← hcardK]; omega
    have hall : ∀ x : Kˣ, x = 1 := fun x => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hζ x)
      rw [← hk, h]
      exact _root_.one_zpow k
    have : Subsingleton Kˣ := ⟨fun a b => by rw [hall a, hall b]⟩
    have : Nat.card Kˣ = 1 := Nat.card_unique
    omega
  have hA1 : A ≠ 1 := by
    intro h
    have h1 : ((ι y₀ : a2Levi K 0) : StatedSp 3 K) = 1 := by rw [← hA, h, map_one]
    have h2 : ι y₀ = 1 := Subtype.ext h1
    have h3 : y₀ = 1 := by rw [← map_one ι] at h2; exact ι.injective h2
    have h4 : shortTorusHom K ζ = 1 := congrArg Subtype.val h3
    apply hζ1
    have h5 := congrFun (diagSp_injective (h4.trans (map_one (diagSp K 3)).symm)) 1
    simpa [shortParamHom] using h5
  obtain ⟨P, l, hP, -⟩ := TwistedE6Pilot.exists_conj_eq_HSL_of_ne_one hAq hA1
  set c : StatedSp 3 K := shortBlock K one_ne_two_three P with hc
  have hcM : c ∈ a2Levi K 0 := (le_sup_left : (shortBlock K one_ne_two_three).range ≤ _) ⟨P, rfl⟩
  have hcy : c⁻¹ * ((ι y₀ : a2Levi K 0) : StatedSp 3 K) * c = shortTorusHom K l := by
    rw [← hA, hc, ← map_inv, ← map_mul, ← map_mul, hP, hsl_eq_diagUnit,
      shortTorusHom_eq_shortBlock]
  refine ⟨c, hcM, fun m hm => ?_⟩
  obtain ⟨r, hr⟩ := hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hζ r)
  have hmk : m = y₀ ^ k := by
    apply Subtype.ext
    rw [← hr, SubgroupClass.coe_zpow, hy₀, map_zpow]
  have hconj : c⁻¹ * ((ι y₀ : a2Levi K 0) : StatedSp 3 K) ^ k * c =
      (c⁻¹ * ((ι y₀ : a2Levi K 0) : StatedSp 3 K) * c) ^ k := by
    have h := conj_zpow (i := k) (a := c⁻¹) (b := ((ι y₀ : a2Levi K 0) : StatedSp 3 K))
    rw [inv_inv] at h
    exact h.symm
  rw [hmk, map_zpow, SubgroupClass.coe_zpow, hconj, hcy, ← map_zpow]
  exact ⟨l ^ k, rfl⟩

end CFSG.SeitzReduction.SymplecticPilot
