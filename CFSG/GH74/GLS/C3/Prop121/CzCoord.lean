module

public import CFSG.GH74.GLS.C3.Prop121.CentK
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.GroupTheory.Perm.Centralizer
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.CzCoordInputs
public meta import CFSG.GH74.GLS.C3.Prop121.CzCoordInputs
public import Certificates.Certificate5086
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.C3.Layer2.Final
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.C3.Prop121.Recog
public import CFSG.GH74.GLS.Defs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

theorem okOdd5 : okOdd 5 = true :=
  Certificates.certificate5086.1
theorem okOdd6 : okOdd 6 = true :=
  Certificates.certificate5086.2.1
theorem okOdd7 : okOdd 7 = true :=
  Certificates.certificate5086.2.2

theorem exists_odd_inv_comm_ord3
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) {σ : Perm (Fin n)}
    (hσ : σ * σ * σ = 1 ∧ σ ≠ 1) :
    ∃ ρ : Perm (Fin n), ρ * ρ = 1 ∧ sign ρ = -1 ∧ ρ * σ = σ * ρ := by
  have hok : okOdd n = true := by
    rcases hn with rfl | rfl | rfl
    · exact okOdd5
    · exact okOdd6
    · exact okOdd7
  have h1 := List.all_eq_true.1 hok σ (mem_allPerms n σ)
  have h2 : decide (σ * σ * σ = 1 ∧ σ ≠ 1) = true := decide_eq_true hσ
  rw [h2] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  obtain ⟨ρ, -, hρ⟩ := List.any_eq_true.1 h1
  exact ⟨ρ, of_decide_eq_true hρ⟩

theorem swap_conj_ne : ∀ d : Perm (Fin 4), d * x4 = x4 * d → sign d = 1 → d ≠ 1 → d ≠ x4 →
    swap (0 : Fin 4) 1 * d * (swap (0 : Fin 4) 1)⁻¹ ≠ d := by
  decide

theorem swap_comm_x4 : swap (0 : Fin 4) 1 * x4 = x4 * swap (0 : Fin 4) 1 := by decide

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem exists_u1
    (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4) (h : IsAConfig n x K T Q S a)
    {y₀ : G} (hy₀Q : y₀ ∈ Q) (hy₀1 : y₀ ≠ 1) (hy₀x : y₀ ≠ x)
    {t' : G} (ht'K : t' ∈ K) (ht'3 : t' * t' * t' = 1) (ht'1 : t' ≠ 1) :
    ∃ u₁ : G, u₁ * u₁ = 1 ∧ u₁ * x = x * u₁ ∧ u₁ * t' = t' * u₁ ∧ u₁ * y₀ * u₁⁻¹ ≠ y₀ := by
  classical
  obtain ⟨ι, hι1, hι2⟩ := exists_coord hn hG4 h
  have ht'C : t' ∈ centralizer ({x} : Set G) := h.K_le_C ht'K
  let T' : ↥(centralizer ({x} : Set G)) := ⟨t', ht'C⟩
  have hT'f := (K_iff hn h hι2 T').1 ht'K
  let σ : Perm (Fin n) := ((ι T' : Fgrp n) : Amb n).1
  have hT'3 : T' * T' * T' = 1 := Subtype.ext ht'3
  have hσ3 : σ * σ * σ = 1 := by
    have h1 : ι (T' * T' * T') = 1 := by rw [hT'3, map_one]
    have h2 := congrArg (fun f : ↥(Fgrp n) => ((f : Fgrp n) : Amb n).1) h1
    simpa [σ] using h2
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : ι T' = 1 := by
      apply Subtype.ext
      exact Prod.ext h1 hT'f.2
    have h3 : T' = 1 := ι.injective (by rw [h2, map_one])
    exact ht'1 (congrArg Subtype.val h3)
  obtain ⟨ρ₁, hρ₁2, hρ₁s, hρ₁c⟩ := exists_odd_inv_comm_ord3 hn ⟨hσ3, hσ1⟩
  have he : ((ρ₁, swap (0 : Fin 4) 1) : Amb n) ∈ Fgrp n :=
    ⟨swap_comm_x4, by
      show sign ρ₁ = sign (swap (0 : Fin 4) 1)
      rw [hρ₁s, sign_swap (by decide)]⟩
  let U : ↥(centralizer ({x} : Set G)) := ι.symm ⟨(ρ₁, swap (0 : Fin 4) 1), he⟩
  have hιU : ι U = ⟨(ρ₁, swap (0 : Fin 4) 1), he⟩ := ι.apply_symm_apply _
  have hUU : U * U = 1 := by
    apply ι.injective
    rw [map_mul, hιU, map_one]
    apply Subtype.ext
    exact Prod.ext hρ₁2 (swap_mul_self _ _)
  have hUT : U * T' = T' * U := by
    apply ι.injective
    rw [map_mul, map_mul, hιU]
    apply Subtype.ext
    refine Prod.ext hρ₁c ?_
    show swap (0 : Fin 4) 1 * ((ι T' : Fgrp n) : Amb n).2 = ((ι T' : Fgrp n) : Amb n).2 * swap 0 1
    rw [hT'f.2]; simp
  have hy₀C : y₀ ∈ centralizer ({x} : Set G) := (h.Q_le_T.trans h.T_le_C) hy₀Q
  let Y₀ : ↥(centralizer ({x} : Set G)) := ⟨y₀, hy₀C⟩
  refine ⟨(U : G), congrArg Subtype.val hUU, mem_centralizer_singleton_iff.1 U.2,
    congrArg Subtype.val hUT, ?_⟩
  intro hcon
  have hUY : U * Y₀ * U⁻¹ = Y₀ := Subtype.ext hcon
  have h1 := congrArg ι hUY
  rw [map_mul, map_mul, map_inv, hιU] at h1
  set fY : ↥(Fgrp n) := ι Y₀ with hfY
  have hfY1 : ((fY : Fgrp n) : Amb n).1 = 1 := (hι2 Y₀).2 hy₀Q
  have hfYc : ((fY : Fgrp n) : Amb n).2 * x4 = x4 * ((fY : Fgrp n) : Amb n).2 := fY.2.1
  have hfYs : sign ((fY : Fgrp n) : Amb n).2 = 1 := by
    have := fY.2.2
    rw [hfY1, map_one] at this
    exact this.symm
  have hfY1' : ((fY : Fgrp n) : Amb n).2 ≠ 1 := by
    intro h2
    have h3 : fY = 1 := Subtype.ext (Prod.ext hfY1 h2)
    have h4 : Y₀ = 1 := ι.injective (by rw [← hfY, h3, map_one])
    exact hy₀1 (congrArg Subtype.val h4)
  have hfYx : ((fY : Fgrp n) : Amb n).2 ≠ x4 := by
    intro h2
    have h3 : fY = ι (xC x) := by
      apply Subtype.ext
      rw [hι1]
      exact Prod.ext hfY1 h2
    have h4 : Y₀ = xC x := ι.injective h3
    exact hy₀x (congrArg Subtype.val h4)
  have h5 := congrArg (fun f : ↥(Fgrp n) => ((f : Fgrp n) : Amb n).2) h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv] at h5
  exact swap_conj_ne _ hfYc hfYs hfY1' hfYx h5

theorem card_centralizer_ord3_five {σ : Perm (Fin 5)} (h3 : σ * σ * σ = 1) (h1 : σ ≠ 1) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 5)))) = 6 := by
  have hpow : σ ^ 3 = 1 := by rw [pow_three']; exact h3
  have hord : orderOf σ = 3 := orderOf_eq_prime hpow h1
  have hmem : ∀ c ∈ σ.cycleType, c = 3 := by
    intro c hc
    have hd : c ∣ 3 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hc
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hc
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · omega
    · exact h
  have hct := Multiset.eq_replicate_of_mem hmem
  have hsum := Equiv.Perm.sum_cycleType_le σ
  have hpos : 0 < Multiset.card σ.cycleType := by
    rcases Nat.eq_zero_or_pos (Multiset.card σ.cycleType) with h0 | h0
    · exact absurd (Equiv.Perm.card_cycleType_eq_zero.1 h0) h1
    · exact h0
  rw [hct, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hm : Multiset.card σ.cycleType = 1 := by omega
  rw [Equiv.Perm.nat_card_centralizer, hct, hm, Fintype.card_fin]
  simp

theorem card_centralizer_ord3_six {σ : Perm (Fin 6)} (h3 : σ * σ * σ = 1) (h1 : σ ≠ 1) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 6)))) = 18 := by
  have hpow : σ ^ 3 = 1 := by rw [pow_three']; exact h3
  have hord : orderOf σ = 3 := orderOf_eq_prime hpow h1
  have hmem : ∀ c ∈ σ.cycleType, c = 3 := by
    intro c hc
    have hd : c ∣ 3 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hc
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hc
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · omega
    · exact h
  have hct := Multiset.eq_replicate_of_mem hmem
  have hsum := Equiv.Perm.sum_cycleType_le σ
  have hpos : 0 < Multiset.card σ.cycleType := by
    rcases Nat.eq_zero_or_pos (Multiset.card σ.cycleType) with h0 | h0
    · exact absurd (Equiv.Perm.card_cycleType_eq_zero.1 h0) h1
    · exact h0
  rw [hct, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hm : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 2 := by omega
  rw [Equiv.Perm.nat_card_centralizer, hct, Fintype.card_fin]
  rcases hm with hm | hm <;> rw [hm] <;> simp [Nat.factorial]

theorem card_centralizer_x_t' (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) {t' : G} (ht'K : t' ∈ K) (ht'3 : t' * t' * t' = 1)
    (ht'1 : t' ≠ 1) :
    ∃ σ : Perm (Fin n), σ * σ * σ = 1 ∧ σ ≠ 1 ∧
      Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({t'} : Set G)) =
        4 * Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) := by
  classical
  obtain ⟨ι, hι1, hι2⟩ := exists_coord hn hG4 h
  have ht'C : t' ∈ centralizer ({x} : Set G) := h.K_le_C ht'K
  let T' : ↥(centralizer ({x} : Set G)) := ⟨t', ht'C⟩
  have hT'f := (K_iff hn h hι2 T').1 ht'K
  let σ : Perm (Fin n) := ((ι T' : Fgrp n) : Amb n).1
  have hT'3 : T' * T' * T' = 1 := Subtype.ext ht'3
  have hσ3 : σ * σ * σ = 1 := by
    have h1 : ι (T' * T' * T') = 1 := by rw [hT'3, map_one]
    have h2 := congrArg (fun f : ↥(Fgrp n) => ((f : Fgrp n) : Amb n).1) h1
    simpa [σ] using h2
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : ι T' = 1 := by
      apply Subtype.ext
      exact Prod.ext h1 hT'f.2
    have h3 : T' = 1 := ι.injective (by rw [h2, map_one])
    exact ht'1 (congrArg Subtype.val h3)
  refine ⟨σ, hσ3, hσ1, ?_⟩
  have hHH' : Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({t'} : Set G)) =
      Nat.card ↥(centralizer ({T'} : Set ↥(centralizer ({x} : Set G)))) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩
        invFun := fun d => ⟨d.1.1, d.1.2, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun d => rfl }
    · rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.1 c.2.2
    · exact mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 d.2))
  have hH'f : Nat.card ↥(centralizer ({T'} : Set ↥(centralizer ({x} : Set G)))) =
      Nat.card ↥(centralizer ({ι T'} : Set ↥(Fgrp n))) :=
    (CFSG.GH74.GLS.Layer3.card_centralizer_mulEquiv ι T').symm
  rw [hHH', hH'f]
  let Φ : ↥(Fgrp n) →* Perm (Fin n) :=
    (MonoidHom.fst (Perm (Fin n)) (Perm (Fin 4))).comp (Fgrp n).subtype
  have hΦ : ∀ f : ↥(Fgrp n), Φ f = ((f : Fgrp n) : Amb n).1 := fun f => rfl
  have hΦsurj : Function.Surjective Φ := by
    intro ρ
    rcases Int.units_eq_one_or (sign ρ) with hs | hs
    · exact ⟨⟨(ρ, 1), ⟨by simp, by simp [hs]⟩⟩, rfl⟩
    · refine ⟨⟨(ρ, swap (0 : Fin 4) 1), ⟨swap_comm_x4, ?_⟩⟩, rfl⟩
      show sign ρ = sign (swap (0 : Fin 4) 1)
      rw [hs, sign_swap (by decide)]
  have hcomap : centralizer ({ι T'} : Set ↥(Fgrp n)) =
      (centralizer ({σ} : Set (Perm (Fin n)))).comap Φ := by
    ext f
    rw [mem_centralizer_singleton_iff, Subgroup.mem_comap, mem_centralizer_singleton_iff, hΦ]
    constructor
    · intro hf
      have := congrArg (fun z : ↥(Fgrp n) => ((z : Fgrp n) : Amb n).1) hf
      simpa [σ] using this
    · intro hf
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · simpa [σ] using hf
      · show ((f : Fgrp n) : Amb n).2 * ((ι T' : Fgrp n) : Amb n).2 =
          ((ι T' : Fgrp n) : Amb n).2 * ((f : Fgrp n) : Amb n).2
        rw [hT'f.2]; simp
  rw [hcomap]
  have hidx : ((centralizer ({σ} : Set (Perm (Fin n)))).comap Φ).index =
      (centralizer ({σ} : Set (Perm (Fin n)))).index :=
    Subgroup.index_comap_of_surjective _ hΦsurj
  have h1 := Subgroup.index_mul_card ((centralizer ({σ} : Set (Perm (Fin n)))).comap Φ)
  have h2 := Subgroup.index_mul_card (centralizer ({σ} : Set (Perm (Fin n))))
  have hn0 : 0 < (centralizer ({σ} : Set (Perm (Fin n)))).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hF : Nat.card ↥(Fgrp n) = 4 * n.factorial := card_Fgrp_eq n
  have hP : Nat.card (Perm (Fin n)) = n.factorial := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hidx, hF] at h1
  rw [hP] at h2
  apply Nat.eq_of_mul_eq_mul_left hn0
  calc (centralizer ({σ} : Set (Perm (Fin n)))).index *
        Nat.card ↥((centralizer ({σ} : Set (Perm (Fin n)))).comap Φ) = 4 * n.factorial := h1
    _ = 4 * ((centralizer ({σ} : Set (Perm (Fin n)))).index *
        Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n))))) := by rw [h2]
    _ = (centralizer ({σ} : Set (Perm (Fin n)))).index *
        (4 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n))))) := by ring

end Config

end CFSG.GH74.GLS.C3.Prop121
