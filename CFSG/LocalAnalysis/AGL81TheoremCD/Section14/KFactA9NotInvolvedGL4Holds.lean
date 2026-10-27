module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoFrattini

import CFSG.RankThree.PartTwo.Sec4.Census.Item44Sections
import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.LinearAlgebra.ElementaryAutGLFour
import CFSG.LinearAlgebra.PrimeOrderCyclotomicCentralizer
import CFSG.GroupTheory.AlternatingNineFiveCentralizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.SectionRank

private def a9SevenCyclePerm : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 *
    Equiv.swap 4 5 * Equiv.swap 5 6

private def a9ThreeOnSevenPerm : Equiv.Perm (Fin 9) :=
  Equiv.swap 1 3 * Equiv.swap 3 2 * Equiv.swap 2 6 * Equiv.swap 6 4 *
    Equiv.swap 4 5 * Equiv.swap 7 8

private def a9SevenCycle : alternatingGroup (Fin 9) :=
  ⟨a9SevenCyclePerm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def a9ThreeOnSeven : alternatingGroup (Fin 9) :=
  ⟨a9ThreeOnSevenPerm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private theorem orderOf_a9SevenCycle : orderOf a9SevenCycle = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    show a9SevenCyclePerm ^ 7 = 1
    decide +kernel
  · intro h
    apply (show a9SevenCyclePerm ≠ 1 by decide +kernel)
    exact congrArg Subtype.val h

private theorem a9ThreeOnSeven_mul_sevenCycle :
    a9ThreeOnSeven * a9SevenCycle = a9SevenCycle ^ 3 * a9ThreeOnSeven :=
  Subtype.ext (by
    show a9ThreeOnSevenPerm * a9SevenCyclePerm = a9SevenCyclePerm ^ 3 * a9ThreeOnSevenPerm
    decide +kernel)

theorem not_ker_le_of_ne_seven {p : ℕ} [Fact p.Prime] (hp7 : p ≠ 7) {n : ℕ} (hn : 9 ≤ n)
    {Y : Type*} [Group Y] [Finite Y] (ρ : Y →* GL (Fin 4) (ZMod p))
    (φ : Y →* alternatingGroup (Fin n)) (hφ : Function.Surjective φ) : ¬ ρ.ker ≤ φ.ker := by
  intro hker
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let ι := altEmbed hn
  set y : alternatingGroup (Fin n) := ι a9SevenCycle with hydef
  set g : alternatingGroup (Fin n) := ι a9ThreeOnSeven with hgdef
  have hy : orderOf y = 7 := by
    rw [hydef, orderOf_injective ι (altEmbed_injective hn), orderOf_a9SevenCycle]
  have hgy : g * y = y ^ 3 * g := by
    rw [hydef, hgdef, ← map_mul, ← map_pow, a9ThreeOnSeven_mul_sevenCycle, map_mul]
  obtain ⟨k, hk1, hk4, hk⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.exists_pow_modEq_one
      (p := p) (r := 7) (by norm_num) (fun h => hp7 h.symm) ρ φ hφ hker hy hgy
  interval_cases k <;> exact absurd hk (by decide)

theorem exists_subgroup_surjective_alternatingNine {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 9 ≤ n)
    {Y : Type*} [Group Y] [Finite Y] (ρ : Y →* GL (Fin 4) (ZMod p))
    (φ : Y →* alternatingGroup (Fin n)) (hφ : Function.Surjective φ) (hker : ρ.ker ≤ φ.ker) :
    ∃ X : Subgroup (GL (Fin 4) (ZMod p)), ∃ ψ : X →* alternatingGroup (Fin 9),
      Function.Surjective ψ := by
  classical
  let ι := altEmbed hn
  let Y' : Subgroup Y := (ι.range).comap φ
  let φ₀ : Y' →* ι.range := (φ.comp Y'.subtype).codRestrict _ (fun y => y.2)
  let e : alternatingGroup (Fin 9) ≃* ι.range :=
    MonoidHom.ofInjective (altEmbed_injective hn)
  let φ' : Y' →* alternatingGroup (Fin 9) := e.symm.toMonoidHom.comp φ₀
  let ρ' : Y' →* GL (Fin 4) (ZMod p) := ρ.comp Y'.subtype
  have hsurj : Function.Surjective φ' := by
    intro a
    obtain ⟨y, hy⟩ := hφ (ι a)
    set y' : Y' := ⟨y, Subgroup.mem_comap.mpr (by rw [hy]; exact ⟨a, rfl⟩)⟩
    refine ⟨y', ?_⟩
    have h1 : φ₀ y' = e a := Subtype.ext (by
      show φ (y' : Y) = ι a
      simpa [y'] using hy)
    change e.symm (φ₀ y') = a
    rw [h1, e.symm_apply_apply]
  have hker' : ρ'.ker ≤ φ'.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : ρ (y : Y) = 1 := by simpa [ρ'] using hy
    have h2 : φ (y : Y) = 1 := hker h1
    have h3 : φ₀ y = 1 := Subtype.ext (by
      show φ (y : Y) = 1
      exact h2)
    show (e.symm.toMonoidHom.comp φ₀) y = 1
    rw [MonoidHom.comp_apply, h3, map_one]
  refine ⟨ρ'.range, ?_⟩
  let ψ : ρ'.range →* alternatingGroup (Fin 9) :=
    (QuotientGroup.lift ρ'.ker φ' hker').comp
      (QuotientGroup.quotientKerEquivRange ρ').symm.toMonoidHom
  refine ⟨ψ, ?_⟩
  have hlift : Function.Surjective (QuotientGroup.lift ρ'.ker φ' hker') := by
    intro a
    obtain ⟨y, hy⟩ := hsurj a
    exact ⟨QuotientGroup.mk y, by rw [QuotientGroup.lift_mk]; exact hy⟩
  simpa [ψ, MonoidHom.comp_apply] using
    hlift.comp (QuotientGroup.quotientKerEquivRange ρ').symm.surjective

theorem kFactA9NotInvolvedGL4_of_glFourSeven
    (h7 : ∀ X : Subgroup (GL (Fin 4) (ZMod 7)), ∀ ψ : X →* alternatingGroup (Fin 9),
      ¬ Function.Surjective ψ) :
    KFactA9NotInvolvedGL4 := by
  intro p hp hp5 V _ _ hcomm hpow hcard n hn Y _ _ ρ φ hφ hker
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative V := hcomm
  obtain ⟨ρ', hρ'⟩ :=
    CFSG.LinearAlgebra.ElementaryAutGLFour.exists_hom_glFour_ker_le (p := p) hpow hcard ρ
  have hρφ : ρ'.ker ≤ φ.ker := hρ'.trans hker
  by_cases hp7 : p = 7
  · subst p
    obtain ⟨X, ψ, hψ⟩ := exists_subgroup_surjective_alternatingNine (p := 7) hn ρ' φ hφ hρφ
    exact h7 X ψ hψ
  · exact not_ker_le_of_ne_seven hp7 hn ρ' φ hφ hρφ

private theorem isCyclic_centralizer_subgroup {G : Type*} [Group G] {X : Subgroup G} (s : X)
    [IsCyclic (Subgroup.centralizer ({(s : G)} : Set G))] :
    IsCyclic (Subgroup.centralizer ({s} : Set X)) := by
  let f : Subgroup.centralizer ({s} : Set X) →* Subgroup.centralizer ({(s : G)} : Set G) :=
    (X.subtype.comp (Subgroup.centralizer ({s} : Set X)).subtype).codRestrict _ fun c =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2))
  refine isCyclic_of_injective f fun a b h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem kFactA9NotInvolvedGL4_holds : KFactA9NotInvolvedGL4 := by
  refine kFactA9NotInvolvedGL4_of_glFourSeven fun _ ψ => ?_
  refine CFSG.GroupTheory.AlternatingNineFiveCentralizer.not_surjective_of_isCyclic_centralizer
    (fun s hs => ?_) ψ
  have hs' : orderOf (s : GL (Fin 4) (ZMod 7)) = 5 := by rwa [Subgroup.orderOf_coe]
  haveI :=
    CFSG.LinearAlgebra.PrimeOrderCyclotomicCentralizer.isCyclic_centralizer_of_orderOf_eq_five hs'
  exact isCyclic_centralizer_subgroup s

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
