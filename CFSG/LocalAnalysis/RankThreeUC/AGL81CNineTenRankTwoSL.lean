module

public import CFSG.RankThree.SubgroupLists.DicksonGL2
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem exists_hom_GL_two {A : Subgroup X} (hAn : A.Normal)
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ ρ : X →* GL (Fin 2) (ZMod p), ρ.ker = centralizer (A : Set X) ∧
      ∀ x : X, ρ x = -1 → ∀ a ∈ A, x * a * x⁻¹ = a⁻¹ := by
  haveI := hAn
  have hcomm : ∀ a b : A, a * b = b * a := isMulCommutative_iff.mp hA.1
  have hpow : ∀ a : A, a ^ p = 1 := fun a =>
    Subtype.ext (by simpa using hA.2 (a : X) a.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hAc
  refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
    (MulAut.conjNormal (H := A)), ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx a ha
      have h1 : MulAut.conjNormal (H := A) x = 1 :=
        (MulEquiv.map_eq_one_iff (CFSG.SectionRank.Ccomm.elemAutEquivGL e)).mp hx
      have h2 : (MulAut.conjNormal (H := A) x) ⟨a, ha⟩ = ⟨a, ha⟩ := by
        rw [h1]; rfl
      have h3 : x * a * x⁻¹ = a := by
        have h4 := congrArg (fun b : A => (b : X)) h2
        rwa [MulAut.conjNormal_apply] at h4
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    · intro hx
      change (CFSG.SectionRank.Ccomm.elemAutEquivGL e)
        (MulAut.conjNormal (H := A) x) = 1
      rw [MulEquiv.map_eq_one_iff (CFSG.SectionRank.Ccomm.elemAutEquivGL e)]
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      show x * (a : X) * x⁻¹ = (a : X)
      rw [mul_inv_eq_iff_eq_mul]
      exact (hx (a : X) a.2).symm
  · intro x hx a ha
    have h1 : (MulAut.conjNormal (H := A) x) ⟨a, ha⟩ = ⟨a, ha⟩⁻¹ :=
      (CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e
        (MulAut.conjNormal (H := A) x)).mp hx ⟨a, ha⟩
    have h2 := congrArg (fun b : A => (b : X)) h1
    simpa [MulAut.conjNormal_apply] using h2

theorem mem_statedSL_of_pow_eq_one {u : GL (Fin 2) (ZMod p)} {k : ℕ}
    (hu : u ^ (p ^ k) = 1) : u ∈ CFSG.Open.StatedSL 2 (ZMod p) := by
  rw [CFSG.RankThree.SubgroupLists.mem_statedSL_iff]
  have h := congrArg (fun g : GL (Fin 2) (ZMod p) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det) hu
  simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, Units.val_one, Matrix.det_one] at h
  have h2 := ZMod.pow_card_pow (n := k) (u : Matrix (Fin 2) (Fin 2) (ZMod p)).det
  rw [h] at h2
  exact h2.symm

theorem map_closure_orderOf_eq_statedSL (ρ : X →* GL (Fin 2) (ZMod p))
    (hker : IsPGroup p ↥ρ.ker) (hV : ¬ IsPGroup p ↥(closure {x : X | orderOf x = p})) :
    (closure {x : X | orderOf x = p}).map ρ = CFSG.Open.StatedSL 2 (ZMod p) := by
  rw [MonoidHom.map_closure]
  let S : Set X := {x : X | orderOf x = p}
  let T : Set (GL (Fin 2) (ZMod p)) := ρ '' S \ {1}
  change Subgroup.closure (ρ '' S) = CFSG.Open.StatedSL 2 (ZMod p)
  have hST : Subgroup.closure (ρ '' S) = Subgroup.closure T := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g ⟨x, hxS, rfl⟩
      by_cases h1 : ρ x = 1
      · rw [h1]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure
          (show ρ x ∈ T from ⟨⟨x, hxS, rfl⟩, by simpa using h1⟩)
    · exact Subgroup.closure_mono Set.diff_subset
  have hTorder : ∀ g ∈ T, orderOf g = p := by
    rintro g ⟨⟨x, hxS, rfl⟩, hg1⟩
    have hxSp : orderOf x = p := hxS
    have hdvd : orderOf (ρ x) ∣ orderOf x := orderOf_map_dvd ρ x
    rw [hxSp] at hdvd
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (by simpa using hg1)
    · exact h
  have hle : Subgroup.closure S ≤ (Subgroup.closure T).comap ρ := by
    rw [Subgroup.closure_le]
    intro x hxS
    change ρ x ∈ Subgroup.closure T
    rw [← hST]
    exact Subgroup.subset_closure ⟨x, hxS, rfl⟩
  rcases CFSG.RankThree.SubgroupLists.dickson_gl_two_closure T hTorder with h | h | h
  · exfalso
    apply hV
    have hTgrp : IsPGroup p ↥(Subgroup.closure T) := by
      rw [h]; exact IsPGroup.of_bot
    exact IsPGroup.to_le (IsPGroup.comap_of_ker_isPGroup hTgrp ρ hker) hle
  · exfalso
    apply hV
    have hTgrp : IsPGroup p ↥(Subgroup.closure T) :=
      IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    exact IsPGroup.to_le (IsPGroup.comap_of_ker_isPGroup hTgrp ρ hker) hle
  · rw [hST, h]

theorem mem_closure_orderOf_of_pow_eq_one (ρ : X →* GL (Fin 2) (ZMod p))
    (hkerV : ρ.ker ≤ closure {x : X | orderOf x = p})
    (hρV : (closure {x : X | orderOf x = p}).map ρ = CFSG.Open.StatedSL 2 (ZMod p))
    {x : X} {k : ℕ} (hx : x ^ (p ^ k) = 1) : x ∈ closure {x : X | orderOf x = p} := by
  have hpow : ρ x ^ (p ^ k) = 1 := by rw [← map_pow, hx, map_one]
  have hmem : ρ x ∈ (closure {x : X | orderOf x = p}).map ρ := by
    rw [hρV]
    exact mem_statedSL_of_pow_eq_one hpow
  obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hmem
  have hker : v⁻¹ * x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvx, inv_mul_cancel]
  have hV := hkerV hker
  have hx' : x = v * (v⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ hv hV

theorem exists_involution_of_map_eq_statedSL (hp2 : p ≠ 2)
    (ρ : X →* GL (Fin 2) (ZMod p)) (hker : IsPGroup p ↥ρ.ker)
    (hρV : (closure {x : X | orderOf x = p}).map ρ = CFSG.Open.StatedSL 2 (ZMod p)) :
    ∃ t ∈ closure {x : X | orderOf x = p}, t ^ 2 = 1 ∧ ρ t = -1 := by
  have hp : p.Prime := Fact.out
  have hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ CFSG.Open.StatedSL 2 (ZMod p) := by
    rw [CFSG.RankThree.SubgroupLists.mem_statedSL_iff, Units.val_neg, Units.val_one,
      Matrix.det_neg, Fintype.card_fin, Matrix.det_one]
    ring
  have hmem : (-1 : GL (Fin 2) (ZMod p)) ∈
      (closure {x : X | orderOf x = p}).map ρ := by
    rw [hρV]; exact hneg
  obtain ⟨t₀, ht₀, ht₀ρ⟩ := Subgroup.mem_map.mp hmem
  have hneg2 : (-1 : GL (Fin 2) (ZMod p)) ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    exact neg_one_sq
  have ht02 : t₀ ^ 2 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, ht₀ρ, hneg2]
  obtain ⟨m, hm⟩ := isPGroup_iff_exists_orderOf_dvd_pow.mp hker
  have hm1 : (⟨t₀ ^ 2, ht02⟩ : ρ.ker) ^ (p ^ m) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hm ⟨t₀ ^ 2, ht02⟩)
  have hmX : (t₀ ^ 2) ^ (p ^ m) = 1 := by
    have h := congrArg (fun b : ρ.ker => (b : X)) hm1
    simpa using h
  refine ⟨t₀ ^ (p ^ m), Subgroup.pow_mem _ ht₀ _, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hmX]
  · rw [map_pow, ht₀ρ]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    exact Odd.neg_one_pow ((Nat.Prime.odd_of_ne_two hp hp2).pow)

theorem commutator_statedSL_eq (hp5 : 5 ≤ p) :
    ⁅CFSG.Open.StatedSL 2 (ZMod p), CFSG.Open.StatedSL 2 (ZMod p)⁆ =
      CFSG.Open.StatedSL 2 (ZMod p) := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  have hcard : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (ZMod p) hcard
  exact Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.range (f := Matrix.SpecialLinearGroup.toGL))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
