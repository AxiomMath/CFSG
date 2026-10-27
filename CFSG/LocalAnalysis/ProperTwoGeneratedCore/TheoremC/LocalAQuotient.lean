module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseOneBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalStatement

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {u z : X}

omit [Finite X] in
theorem mk_twoCore_eq_one_iff (x : X) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 X) x = 1 ↔ x ∈ CFSG.Open.pCore 2 X := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

omit [Finite X] in
theorem conj_mem_involutionPointClass {t : X} (ht : t ∈ involutionPointClass z) (c : X) :
    c⁻¹ * t * c ∈ involutionPointClass z := by
  obtain ⟨g, rfl⟩ := ht
  exact ⟨g * c, by simp only [rightConjugateElem]; group⟩

omit [Finite X] in
theorem conj_mem_involutionPointClass' (g : X) : g * z * g⁻¹ ∈ involutionPointClass z :=
  ⟨g⁻¹, by simp only [rightConjugateElem, inv_inv]⟩

omit [Finite X] in
theorem mem_normalizer_zpowers_iff {G : Type*} [Group G] {a g : G} (ha : orderOf a = 2) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) ↔ Commute g a := by
  constructor
  · intro hg
    have h1 : g * a * g⁻¹ ∈ Subgroup.zpowers a :=
      (Subgroup.mem_normalizer_iff.mp hg a).mp (Subgroup.mem_zpowers a)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have haa : a ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← pow_two, ← ha, pow_orderOf_eq_one]
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exfalso
      rw [zpow_mul, haa, one_zpow] at hk
      have ha1 : a = 1 := by
        calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
          _ = 1 := by rw [← hk]; group
      rw [ha1, orderOf_one] at ha
      exact absurd ha (by decide)
    · rw [zpow_add_one, zpow_mul, haa, one_zpow, one_mul] at hk
      calc g * a = (g * a * g⁻¹) * g := by group
        _ = a * g := by rw [← hk]
  · intro hga
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hga.zpow_right k).eq.symm

namespace CoreConfig

theorem ne_center_of_mem_class (hc : CoreConfig Y u z) {t : X}
    (ht : t ∈ involutionPointClass z) : t ≠ u := by
  obtain ⟨g, rfl⟩ := ht
  intro h
  change rightConjugateElem z g = u at h
  apply hc.lever_ne
  calc z = g * rightConjugateElem z g * g⁻¹ := by simp only [rightConjugateElem]; group
    _ = u := by rw [h, (hc.commute_center g).eq, mul_inv_cancel_right]

theorem lever_not_mem_twoCore (hc : CoreConfig Y u z) : z ∉ CFSG.Open.pCore 2 X := by
  intro hz
  apply hc.ne_top
  refine eq_top_iff.mpr fun g _ => hc.mem_of_conj_mem hc.lever_mem hc.lever_order hc.lever_ne ?_
  have h := (twoCore_normal (X := X)).conj_mem z hz g⁻¹
  rw [inv_inv] at h
  exact hc.twoCore_le h

theorem not_mem_twoCore_of_mem_class (hc : CoreConfig Y u z) {t : X}
    (ht : t ∈ involutionPointClass z) : t ∉ CFSG.Open.pCore 2 X := by
  obtain ⟨g, rfl⟩ := ht
  intro h
  apply hc.lever_not_mem_twoCore
  have h' := (twoCore_normal (X := X)).conj_mem _ h g
  convert h' using 1
  simp only [rightConjugateElem]
  group

theorem mk_mem_map_iff (hc : CoreConfig Y u z) (x : X) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 X) x ∈ Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) ↔
      x ∈ Y := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.mpr hc.twoCore_le]

theorem orderOf_mk_lever (hc : CoreConfig Y u z) :
    orderOf (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, show z ^ 2 = 1 by simpa only [hc.lever_order] using pow_orderOf_eq_one z,
      map_one]
  · rw [Ne, mk_twoCore_eq_one_iff]
    exact hc.lever_not_mem_twoCore

theorem map_ne_top (hc : CoreConfig Y u z) :
    Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) ≠ ⊤ := by
  intro h
  apply hc.ne_top
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← hc.mk_mem_map_iff, h]
  exact Subgroup.mem_top _

theorem conj_mk_lever_mem_iff (hc : CoreConfig Y u z) (g : X ⧸ CFSG.Open.pCore 2 X) :
    g * QuotientGroup.mk' (CFSG.Open.pCore 2 X) z * g⁻¹ ∈
        Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) ↔
      g ∈ Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X) g
  rw [← map_inv, ← map_mul, ← map_mul, hc.mk_mem_map_iff, hc.mk_mem_map_iff]
  constructor
  · intro h
    have hm := hc.mem_of_conj_mem (m := m⁻¹) hc.lever_mem hc.lever_order hc.lever_ne
      (by rwa [inv_inv])
    simpa using Y.inv_mem hm
  · intro hm
    exact Y.mul_mem (Y.mul_mem hm hc.lever_mem) (Y.inv_mem hm)

theorem mk_lever_mem_rightConjugate_iff (hc : CoreConfig Y u z)
    (g : X ⧸ CFSG.Open.pCore 2 X) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 X) z ∈
        rightConjugate (Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))) g ↔
      g ∈ Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  exact hc.conj_mk_lever_mem_iff g

end CoreConfig

abbrev quasiPreimage (a : X ⧸ CFSG.Open.pCore 2 X) : Subgroup X :=
  (Subgroup.zpowers a).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 X))

omit [Finite X] in
theorem mem_normalizer_quasiPreimage_iff {a : X ⧸ CFSG.Open.pCore 2 X} (ha : orderOf a = 2)
    (x : X) :
    x ∈ Subgroup.normalizer (quasiPreimage a : Set X) ↔
      Commute (QuotientGroup.mk' (CFSG.Open.pCore 2 X) x) a := by
  rw [← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.mem_comap, mem_normalizer_zpowers_iff ha]

omit [Finite X] in
theorem map_quasiHull_eq {a : X ⧸ CFSG.Open.pCore 2 X} (ha : orderOf a = 2) (z : X) :
    (quasiHull z (quasiPreimage a)).map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
      localInvolutionPointHull (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z) a := by
  rw [quasiHull, Subgroup.map_sup,
    (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' (CFSG.Open.pCore 2 X)).ge,
    sup_bot_eq, MonoidHom.map_closure, localInvolutionPointHull]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨⟨g, rfl⟩, hxN⟩, rfl⟩
    refine ⟨⟨QuotientGroup.mk' _ g, ?_⟩, ?_⟩
    · simp only [rightConjugateElem, map_mul, map_inv]
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact ((mem_normalizer_quasiPreimage_iff ha _).mp hxN).eq
  · rintro ⟨⟨g, rfl⟩, hy⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 X) g
    refine ⟨rightConjugateElem z m, ⟨⟨m, rfl⟩, ?_⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_normalizer_quasiPreimage_iff ha]
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
      simp only [rightConjugateElem, map_mul, map_inv] at hy ⊢
      exact hy
    · simp only [rightConjugateElem, map_mul, map_inv]

end CFSG.ProperTwoGeneratedCore.TheoremC
