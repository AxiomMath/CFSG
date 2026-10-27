module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.EnKLOrderSix
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem IsA2PlaneKernel.le_of_isQuasisimple {X : Type*} [Group X] {t : X} {a : ℕ}
    {N L S : Subgroup X} (hN : IsA2PlaneKernel t a N) (hL : L ≤ Subgroup.centralizer {t})
    (hLq : CFSG.IsQuasisimple L) (hLz : Subgroup.center L = ⊥) (hSL : S ≤ L)
    (hS : IsPGroup 2 S) (hSc : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) : L ≤ N := by
  have hone : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set X) → z = 1 := by
    intro z hz hzc
    have hc : (⟨z, hz⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      exact fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc g g.2)
    rw [hLz, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  refine hN.le_of_forall_normal hL (fun H hHL hHn => ?_) (fun z hz hzc => ?_) hSL hS hSc
  · have : (H.subgroupOf L).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hHn g g.2 x hx⟩
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hLq (H.subgroupOf L)
      with h | h
    · left
      intro x hx
      rw [hLz] at h
      have h1 := h (Subgroup.mem_subgroupOf.2 (show ((⟨x, hHL hx⟩ : L) : X) ∈ H from hx))
      rw [Subgroup.mem_bot] at h1
      rw [show x = 1 from congrArg Subtype.val h1]
      exact one_mem _
    · right
      intro x hx
      have h1 : (⟨x, hx⟩ : L) ∈ H.subgroupOf L := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 h1
  · rw [hone z hz hzc, orderOf_one]
    exact odd_one

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.GF2n.Stroth80

variable {τ : Tag} {K : Type} [Field K]


theorem exists_mem_perpLevi_orderOf_eq_three [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ u ∈ perpLevi τ K, orderOf u = 3 ∧
      ∀ c : K, (u : ModGL τ K) * pinnedX τ K (highRoot τ) c =
        pinnedX τ K (highRoot τ) c * (u : ModGL τ K) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin τ.rank, j ≠ highNode τ := by
    rcases hτ with rfl | rfl | rfl <;> exact ⟨⟨2, by decide⟩, by decide⟩
  have h₁ := single_mem_perpRoots (τ := τ) hj
  have h₂ := neg_single_mem_perpRoots (τ := τ) hj
  refine ⟨pinnedElt τ (Pi.single j 1) 1 * pinnedElt τ (-Pi.single j 1) 1,
    mul_mem (pinnedElt_mem_perpLevi h₁ 1) (pinnedElt_mem_perpLevi h₂ 1), ?_, fun c => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_pinnedX_mul_pinnedX_neg_one (isRoot_single τ j)
  · exact commute_pinnedX_highRoot_of_mem_perpLevi hτ
      (mul_mem (pinnedX_mem_rootSpan h₁ 1) (pinnedX_mem_rootSpan h₂ 1)) c

section


private theorem pinnedElt_single_mem_posUnipotent_comap (i : Fin τ.rank) (c : K) :
    pinnedElt τ (Pi.single i 1) c ∈
      (posUnipotent τ K).comap (adjointGroup τ K).subtype := by
  rw [Subgroup.mem_comap]
  change pinnedX τ K (Pi.single i 1) c ∈ posUnipotent τ K
  simpa [posUnipotent] using pinnedX_mem_rootSpan
    (S := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α})
    ⟨isRoot_single τ i, by rw [height_single]; norm_num⟩ c

private theorem closure_pinnedElt_single_isPGroup (i j : Fin τ.rank) [Finite K] [CharP K 2] :
    IsPGroup 2 (Subgroup.closure {pinnedElt τ (Pi.single i 1) (1 : K),
      pinnedElt τ (Pi.single j 1) (1 : K)}) := by
  have hP : IsPGroup 2 ((posUnipotent τ K).comap (adjointGroup τ K).subtype) :=
    (((positive_root_triangularity.{0, 0} τ).2 K 2).2.1).comap_subtype
  refine hP.to_le ((Subgroup.closure_le _).2 ?_)
  rintro g (rfl | rfl)
  · exact pinnedElt_single_mem_posUnipotent_comap i 1
  · exact pinnedElt_single_mem_posUnipotent_comap j 1

private theorem closure_pinnedElt_single_le_perpLevi (i j : Fin τ.rank)
    (hi : i ≠ highNode τ) (hj : j ≠ highNode τ) :
    Subgroup.closure {pinnedElt τ (Pi.single i 1) (1 : K),
      pinnedElt τ (Pi.single j 1) (1 : K)} ≤ perpLevi τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact pinnedElt_mem_perpLevi (single_mem_perpRoots hi) 1
  · exact pinnedElt_mem_perpLevi (single_mem_perpRoots hj) 1

end

private theorem exists_not_commute_pinnedElt_single [CharP K 2] {i j : Fin τ.rank}
    (hij : i ≠ j) (hroot : IsRoot τ (Pi.single i 1 + Pi.single j 1))
    (hlaced : oddDerivLacedCheck τ = true) :
    ∃ x ∈ Subgroup.closure {pinnedElt τ (Pi.single i 1) (1 : K),
        pinnedElt τ (Pi.single j 1) (1 : K)},
      ∃ y ∈ Subgroup.closure {pinnedElt τ (Pi.single i 1) (1 : K),
        pinnedElt τ (Pi.single j 1) (1 : K)}, x * y ≠ y * x := by
  refine ⟨pinnedElt τ (Pi.single i 1) 1, Subgroup.subset_closure (by simp),
    pinnedElt τ (Pi.single j 1) 1, Subgroup.subset_closure (by simp), fun hxy => ?_⟩
  have h1 : commutatorElement.bracket (pinnedElt τ (Pi.single i 1) (1 : K))
      (pinnedElt τ (Pi.single j 1) (1 : K)) = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 hxy
  have h2 : commutatorElement.bracket (pinnedX τ K (Pi.single i 1) 1)
      (pinnedX τ K (Pi.single j 1) 1) = 1 := by
    simpa using congrArg (Subgroup.subtype (adjointGroup τ K)) h1
  have hne : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ Pi.single j 1 :=
    fun h => hij (single_eq_single_iff.1 h)
  have h3 := commutatorElement_pinnedX_of_oddDerivLaced (CharP.cast_eq_zero K 2) hlaced
    (isRoot_single τ i) (isRoot_single τ j) hne (single_ne_neg_single' i j) hroot 1 1
  rw [h3] at h2
  have hp : pinnedX τ K (Pi.single i 1 + Pi.single j 1) (1 : K) = 1 := by
    simpa using h2
  have hp0 : pinnedX τ K (Pi.single i 1 + Pi.single j 1) (0 : K) = 1 :=
    pinnedX_zero τ K (Pi.single i 1 + Pi.single j 1)
  exact one_ne_zero (pinnedX_injective τ K (Pi.single i 1 + Pi.single j 1)
    (hp.trans hp0.symm))

private theorem perpLevi_le_of_pinnedElt_pair [Finite K] [CharP K 2]
    (hL : perpLevi τ K ≤ centralizer ({pinnedElt τ (highRoot τ) (1 : K)} :
      Set (adjointGroup τ K)))
    (hD : CFSG.IsQuasisimple (perpLevi τ K)) (hDZ : center (perpLevi τ K) = ⊥)
    {a : ℕ} {N : Subgroup (adjointGroup τ K)}
    (hN : IsA2PlaneKernel (pinnedElt τ (highRoot τ) (1 : K)) a N)
    {i j : Fin τ.rank} (hi : i ≠ highNode τ) (hj : j ≠ highNode τ) (hij : i ≠ j)
    (hroot : IsRoot τ (Pi.single i 1 + Pi.single j 1))
    (hlaced : oddDerivLacedCheck τ = true) : perpLevi τ K ≤ N := by
  let S : Subgroup (adjointGroup τ K) :=
    Subgroup.closure {pinnedElt τ (Pi.single i 1) (1 : K),
      pinnedElt τ (Pi.single j 1) (1 : K)}
  have hSL : S ≤ perpLevi τ K := closure_pinnedElt_single_le_perpLevi i j hi hj
  have hS : IsPGroup 2 S := closure_pinnedElt_single_isPGroup i j
  have hSc : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x :=
    exists_not_commute_pinnedElt_single hij hroot hlaced
  exact IsA2PlaneKernel.le_of_isQuasisimple hN hL hD hDZ hSL hS hSc

theorem perpLevi_le_of_isA2PlaneKernel [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hD : CFSG.IsQuasisimple (perpLevi τ K))
    (hDZ : center (perpLevi τ K) = ⊥) {a : ℕ} {N : Subgroup (adjointGroup τ K)}
    (hN : IsA2PlaneKernel (pinnedElt τ (highRoot τ) (1 : K)) a N) : perpLevi τ K ≤ N := by
  have hL : perpLevi τ K ≤ centralizer ({pinnedElt τ (highRoot τ) (1 : K)} :
      Set (adjointGroup τ K)) := by
    obtain ⟨-, hC, -, -⟩ := isTwoRadicalDecomp_highRoot (K := K) hτ one_ne_zero
    exact le_sup_right.trans hC.le
  have hlaced : oddDerivLacedCheck τ = true :=
    oddDerivLacedCheck_of_simplyLaced (Or.inr hτ)
  rcases hτ with rfl | rfl | rfl
  · refine perpLevi_le_of_pinnedElt_pair (τ := .E6) (K := K) hL hD hDZ hN
      (i := ((0 : Fin 6) : Fin (Tag.rank .E6)))
      (j := ((2 : Fin 6) : Fin (Tag.rank .E6)))
      (Fin.ne_of_val_ne (by decide +kernel)) (Fin.ne_of_val_ne (by decide +kernel))
      (Fin.ne_of_val_ne (by decide +kernel)) ?_ hlaced
    exact CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single
      (τ := .E6) (i := ((2 : Fin 6) : Fin (Tag.rank .E6)))
      (k := ((0 : Fin 6) : Fin (Tag.rank .E6))) (by decide +kernel)
  · refine perpLevi_le_of_pinnedElt_pair (τ := .E7) (K := K) hL hD hDZ hN
      (i := ((2 : Fin 7) : Fin (Tag.rank .E7)))
      (j := ((3 : Fin 7) : Fin (Tag.rank .E7)))
      (Fin.ne_of_val_ne (by decide +kernel)) (Fin.ne_of_val_ne (by decide +kernel))
      (Fin.ne_of_val_ne (by decide +kernel)) ?_ hlaced
    exact CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single
      (τ := .E7) (i := ((3 : Fin 7) : Fin (Tag.rank .E7)))
      (k := ((2 : Fin 7) : Fin (Tag.rank .E7))) (by decide +kernel)
  · refine perpLevi_le_of_pinnedElt_pair (τ := .E8) (K := K) hL hD hDZ hN
      (i := ((0 : Fin 8) : Fin (Tag.rank .E8)))
      (j := ((2 : Fin 8) : Fin (Tag.rank .E8)))
      (Fin.ne_of_val_ne (by decide +kernel)) (Fin.ne_of_val_ne (by decide +kernel))
      (Fin.ne_of_val_ne (by decide +kernel)) ?_ hlaced
    exact CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single
      (τ := .E8) (i := ((2 : Fin 8) : Fin (Tag.rank .E8)))
      (k := ((0 : Fin 8) : Fin (Tag.rank .E8))) (by decide +kernel)

theorem le_highRadical_of_isKLConfig [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hD : CFSG.IsQuasisimple (perpLevi τ K))
    (hDZ : center (perpLevi τ K) = ⊥) {a : ℕ} {N A : Subgroup (adjointGroup τ K)}
    (h : IsKLConfig (pinnedElt τ (highRoot τ) (1 : K)) a N A) (hDN : perpLevi τ K ≤ N) :
    A ≤ highRadical τ K := by
  obtain ⟨hQ, hC, -, hLQ⟩ := isTwoRadicalDecomp_highRoot (K := K) hτ one_ne_zero
  refine h.le_of_sup_eq_centralizer hQ hC hLQ hDN fun P hPn hP2 => ?_
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hD P with hPZ | hPT
  · rw [hDZ] at hPZ
    exact le_bot_iff.1 hPZ
  · obtain ⟨u, huD, hu3, -⟩ := exists_mem_perpLevi_orderOf_eq_three (K := K) hτ
    have huP : (⟨u, huD⟩ : perpLevi τ K) ∈ P := by
      rw [hPT]
      exact mem_top _
    obtain ⟨n, hn⟩ := hP2 ⟨⟨u, huD⟩, huP⟩
    have hu : u ^ 2 ^ n = 1 := by
      simpa using congrArg (fun x : P => ((x : perpLevi τ K) : adjointGroup τ K)) hn
    have h3 := orderOf_dvd_of_pow_eq_one hu
    rw [hu3] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

end CFSG.SeitzReduction.EPilot
