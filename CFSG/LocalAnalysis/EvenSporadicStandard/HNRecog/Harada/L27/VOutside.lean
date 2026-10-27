module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.RadicalLemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog

theorem card_centralizer_ge_of_base_involution {u : A5WrTwo} (hu : u ∈ commutator A5WrTwo)
    (hu1 : u ≠ 1) (hu2 : u * u = 1) (F' : Subgroup A5WrTwo)
    (eF : F' ≃* alternatingGroup (Fin 5)) (hF' : ∀ f ∈ F', f * u = u * f) :
    240 ≤ Nat.card (Subgroup.centralizer ({u} : Set A5WrTwo)) := by
  classical
  rw [← A5WrTwo.range_baseEmb] at hu
  obtain ⟨⟨a, b⟩, hu_eq⟩ := MonoidHom.mem_range.mp hu
  have hsq : A5WrTwo.baseEmb ((a, b) * (a, b)) = A5WrTwo.baseEmb (1, 1) := by
    rw [map_mul, hu_eq, hu2]
    exact (map_one A5WrTwo.baseEmb).symm
  have hpair : (a, b) * (a, b) = (1, 1) := A5WrTwo.baseEmb_injective hsq
  have ha2 : a * a = 1 := by simpa using congrArg Prod.fst hpair
  have hb2 : b * b = 1 := by simpa using congrArg Prod.snd hpair
  have hne : (a, b) ≠ (1, 1) := fun h => hu1 (by
    rw [← hu_eq, h]
    exact map_one A5WrTwo.baseEmb)
  by_cases ha1 : a = 1
  · have hb1 : b ≠ 1 := fun hb => hne (by rw [ha1, hb])
    let g : alternatingGroup (Fin 5) ×
        ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5)))) →
        ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) := fun cd =>
      ⟨A5WrTwo.baseEmb (cd.1, (cd.2 : alternatingGroup (Fin 5))), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hu_eq, ha1]
        rw [← map_mul, ← map_mul]
        apply congrArg A5WrTwo.baseEmb
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk]
        refine Prod.ext ?_ ?_
        · simp
        · simpa using (Subgroup.mem_centralizer_singleton_iff.mp cd.2.2 :
            (cd.2 : alternatingGroup (Fin 5)) * b = b * (cd.2 : alternatingGroup (Fin 5)))⟩
    have hg_inj : Function.Injective g := by
      intro x y hxy
      have hbase : A5WrTwo.baseEmb (x.1, (x.2 : alternatingGroup (Fin 5))) =
          A5WrTwo.baseEmb (y.1, (y.2 : alternatingGroup (Fin 5))) :=
        congrArg Subtype.val hxy
      have hp := A5WrTwo.baseEmb_injective hbase
      exact Prod.ext (Prod.ext_iff.mp hp).1 (Subtype.ext (Prod.ext_iff.mp hp).2)
    have hle := Nat.card_le_card_of_injective g hg_inj
    have hcard : Nat.card (alternatingGroup (Fin 5) ×
        ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5))))) = 240 := by
      rw [Nat.card_prod, card_alternatingGroup_five,
        card_centralizer_involution_a5 b hb1 hb2]
    calc 240 = Nat.card (alternatingGroup (Fin 5) ×
          ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5))))) := hcard.symm
      _ ≤ Nat.card (↥(Subgroup.centralizer ({u} : Set A5WrTwo))) := hle
  · by_cases hb1 : b = 1
    · let g : ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5)))) ×
          alternatingGroup (Fin 5) → ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) := fun cd =>
        ⟨A5WrTwo.baseEmb ((cd.1 : alternatingGroup (Fin 5)), cd.2), by
          rw [Subgroup.mem_centralizer_singleton_iff]
          rw [← hu_eq, hb1]
          rw [← map_mul, ← map_mul]
          apply congrArg A5WrTwo.baseEmb
          rw [Prod.mk_mul_mk, Prod.mk_mul_mk]
          refine Prod.ext ?_ ?_
          · simpa using (Subgroup.mem_centralizer_singleton_iff.mp cd.1.2 :
              (cd.1 : alternatingGroup (Fin 5)) * a = a * (cd.1 : alternatingGroup (Fin 5)))
          · simp⟩
      have hg_inj : Function.Injective g := by
        intro x y hxy
        have hbase : A5WrTwo.baseEmb ((x.1 : alternatingGroup (Fin 5)), x.2) =
            A5WrTwo.baseEmb ((y.1 : alternatingGroup (Fin 5)), y.2) :=
          congrArg Subtype.val hxy
        have hp := A5WrTwo.baseEmb_injective hbase
        exact Prod.ext (Subtype.ext (Prod.ext_iff.mp hp).1) (Prod.ext_iff.mp hp).2
      have hle := Nat.card_le_card_of_injective g hg_inj
      have hcard : Nat.card (↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5)))) ×
          alternatingGroup (Fin 5)) = 240 := by
        rw [Nat.card_prod, card_centralizer_involution_a5 a ha1 ha2,
          card_alternatingGroup_five]
      calc 240 = Nat.card (↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5)))) ×
            alternatingGroup (Fin 5)) := hcard.symm
        _ ≤ Nat.card (↥(Subgroup.centralizer ({u} : Set A5WrTwo))) := hle
    · exfalso
      have hperf : ⁅F', F'⁆ = F' := commutator_eq_self_of_equiv_a5 F' eF
      have hF'le : F' ≤ commutator A5WrTwo := by
        rw [← hperf]
        calc ⁅F', F'⁆ ≤ ⁅(⊤ : Subgroup A5WrTwo), ⊤⁆ :=
              Subgroup.commutator_mono le_top le_top
          _ = commutator A5WrTwo := (commutator_def A5WrTwo).symm
      have hex : ∀ f : F', ∃ p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
          A5WrTwo.baseEmb p = (f : A5WrTwo) := fun f =>
        MonoidHom.mem_range.mp (by rw [A5WrTwo.range_baseEmb]; exact hF'le f.2)
      let ψ : F' → alternatingGroup (Fin 5) × alternatingGroup (Fin 5) := fun f =>
        Classical.choose (hex f)
      have hψ : ∀ f : F', A5WrTwo.baseEmb (ψ f) = (f : A5WrTwo) := fun f =>
        Classical.choose_spec (hex f)
      have hcoord : ∀ f : F',
          (ψ f).1 * a = a * (ψ f).1 ∧ (ψ f).2 * b = b * (ψ f).2 := by
        intro f
        have hcomm := hF' (f : A5WrTwo) f.2
        rw [← hψ f, ← hu_eq] at hcomm
        have hp : ψ f * (a, b) = (a, b) * ψ f :=
          A5WrTwo.baseEmb_injective (by rw [map_mul, map_mul]; exact hcomm)
        exact ⟨(Prod.ext_iff.mp hp).1, (Prod.ext_iff.mp hp).2⟩
      let Φ : F' → ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5)))) ×
          ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5)))) := fun f =>
        (⟨(ψ f).1, Subgroup.mem_centralizer_singleton_iff.mpr (hcoord f).1⟩,
         ⟨(ψ f).2, Subgroup.mem_centralizer_singleton_iff.mpr (hcoord f).2⟩)
      have hΦ_inj : Function.Injective Φ := by
        intro f g hfg
        have h1 : (ψ f).1 = (ψ g).1 :=
          congrArg (fun z => (z.1 :
            ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5))))).1) hfg
        have h2 : (ψ f).2 = (ψ g).2 :=
          congrArg (fun z => (z.2 :
            ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5))))).1) hfg
        have hψfg : ψ f = ψ g := Prod.ext h1 h2
        have : (f : A5WrTwo) = (g : A5WrTwo) := by rw [← hψ f, ← hψ g, hψfg]
        exact Subtype.ext this
      have hle := Nat.card_le_card_of_injective Φ hΦ_inj
      have hF'card : Nat.card F' = 60 := by
        rw [Nat.card_congr eF.toEquiv, card_alternatingGroup_five]
      have hprod : Nat.card (↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5)))) ×
          ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5))))) = 16 := by
        rw [Nat.card_prod, card_centralizer_involution_a5 a ha1 ha2,
          card_centralizer_involution_a5 b hb1 hb2]
      have hle16 : (60 : ℕ) ≤ 16 := by
        calc 60 = Nat.card F' := hF'card.symm
          _ ≤ Nat.card (↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 5)))) ×
              ↥(Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 5))))) := hle
          _ = 16 := hprod
      exact absurd hle16 (by norm_num)

theorem not_mem_commutator_A5WrTwo_of_centralizer {X : Type*} [Group X] (e : X ≃* A5WrTwo)
    (F : Subgroup X) (eF : F ≃* alternatingGroup (Fin 5)) {v : X} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hFv : ∀ f ∈ F, f * v = v * f) (hC : ∀ g : X, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v) :
    e v ∉ commutator A5WrTwo := by
  classical
  intro hmem
  haveI : Finite X := Finite.of_equiv A5WrTwo e.symm.toEquiv
  let u : A5WrTwo := e v
  have hu : u ∈ commutator A5WrTwo := hmem
  have hu2 : u * u = 1 := by
    show e v * e v = 1
    rw [← map_mul, hv2, map_one]
  have hu1 : u ≠ 1 := by
    show e v ≠ 1
    intro h
    exact hv1 (e.injective (by rw [h, map_one]))
  let F' : Subgroup A5WrTwo := F.map e.toMonoidHom
  have eF' : F' ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective F e.toMonoidHom e.injective).symm.trans eF
  have hF' : ∀ f ∈ F', f * u = u * f := by
    intro f hf
    rw [Subgroup.mem_map] at hf
    obtain ⟨f0, hf0, rfl⟩ := hf
    show e f0 * e v = e v * e f0
    rw [← map_mul, ← map_mul, hFv f0 hf0]
  have h240 := card_centralizer_ge_of_base_involution hu hu1 hu2 F' eF' hF'
  have h120 := card_centralizer_le_one_twenty F eF hv2 hFv hC
  have hle : Nat.card (Subgroup.centralizer ({u} : Set A5WrTwo)) ≤
      Nat.card (Subgroup.centralizer ({v} : Set X)) := by
    let f : ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) →
        ↥(Subgroup.centralizer ({v} : Set X)) := fun y =>
      ⟨e.symm (y : A5WrTwo), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        show (y : A5WrTwo) * u = u * (y : A5WrTwo)
        exact Subgroup.mem_centralizer_singleton_iff.mp y.2⟩
    refine Nat.card_le_card_of_injective f ?_
    intro y z hyz
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val hyz))
  have hlt : (240 : ℕ) ≤ 120 := h240.trans (hle.trans h120)
  exact absurd hlt (by norm_num)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
