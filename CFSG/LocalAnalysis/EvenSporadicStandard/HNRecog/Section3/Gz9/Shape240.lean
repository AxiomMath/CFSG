module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open Subgroup
open scoped Classical

private theorem shape240_natCard_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem shape240_natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [shape240_natCard_A5, h2]
  norm_num

private theorem shape240_card_centralizer_one_wr :
    Nat.card ↥(Subgroup.centralizer ({(1 : A5WrTwo)} : Set A5WrTwo)) = 7200 := by
  have htop : Subgroup.centralizer ({(1 : A5WrTwo)} : Set A5WrTwo) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.mem_center_iff.mpr (fun g => by simp)
  rw [htop, Subgroup.card_top, shape240_natCard_A5WrTwo]

private theorem shape240_card_centralizer_one_A5 :
    Nat.card ↥(Subgroup.centralizer ({(1 : alternatingGroup (Fin 5))} : Set _)) = 60 := by
  have htop : Subgroup.centralizer ({(1 : alternatingGroup (Fin 5))} : Set _) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.mem_center_iff.mpr (fun g => by simp)
  rw [htop, Subgroup.card_top, shape240_natCard_A5]

private theorem shape240_pow_four_eq_one :
    ∀ y : alternatingGroup (Fin 5), y ^ 4 = 1 → y * y = 1 := by
  decide +kernel

private def shape240_a5CentralizerCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

private theorem shape240_a5CentralizerCard_eq_four :
    ∀ x : alternatingGroup (Fin 5), x ^ 2 = 1 → x ≠ 1 →
      shape240_a5CentralizerCard x = 4 := by
  decide +kernel

private theorem shape240_card_centralizer_A5 {x : alternatingGroup (Fin 5)} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := shape240_a5CentralizerCard_eq_four x hx2 hx1
  rw [shape240_a5CentralizerCard] at h
  rw [← h]
  congr 1
  ext y
  simp [Subgroup.mem_centralizer_singleton_iff]

private noncomputable def shape240_conjCentralizerMulEquiv (b u : A5WrTwo) :
    ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) ≃*
      ↥(Subgroup.centralizer ({b * u * b⁻¹} : Set A5WrTwo)) where
  toFun k := ⟨b * k * b⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : (k : A5WrTwo) * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b * k * b⁻¹) * (b * u * b⁻¹) = b * (k * u) * b⁻¹ := by group
      _ = b * (u * k) * b⁻¹ := by rw [hk]
      _ = (b * u * b⁻¹) * (b * k * b⁻¹) := by group⟩
  invFun k := ⟨b⁻¹ * k * b, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : (k : A5WrTwo) * (b * u * b⁻¹) = (b * u * b⁻¹) * k :=
      Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b⁻¹ * k * b) * u = b⁻¹ * (k * (b * u * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * u * b⁻¹) * k) * b := by rw [hk]
      _ = u * (b⁻¹ * k * b) := by group⟩
  left_inv k := Subtype.ext (by group)
  right_inv k := Subtype.ext (by group)
  map_mul' k l := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem shape240_baseEmb_fst (x : alternatingGroup (Fin 5)) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1)
    (hC4 : Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4) :
    IsShapeTwoTwoTimesA5
      ↥(Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo)) := by
  haveI : Finite A5WrTwo :=
    Nat.finite_of_card_ne_zero (by rw [shape240_natCard_A5WrTwo]; norm_num)
  have hnotconj : ¬ IsConj x (1 : alternatingGroup (Fin 5)) :=
    fun h => hx1 (isConj_one_left.mp h)
  have hCbase : Nat.card ↥(Subgroup.centralizer
      ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo)) = 240 := by
    rw [card_centralizer_baseEmb_of_not_isConj (x := x) (y := 1) hnotconj, hC4,
      shape240_card_centralizer_one_A5]
  have hsq : ∀ g : ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))),
      g * g = 1 := by
    intro g
    have h4 : g ^ 4 = 1 := by
      have h := pow_card_eq_one' (x := g)
      rwa [hC4] at h
    have h4' : (g : alternatingGroup (Fin 5)) ^ 4 = 1 := by
      simpa using congrArg Subtype.val h4
    exact Subtype.ext (shape240_pow_four_eq_one (g : alternatingGroup (Fin 5)) h4')
  obtain ⟨eV⟩ := TwoHSData.nonempty_mulEquiv_elem2 2 hsq (by rw [hC4]; norm_num)
  let Cx : Subgroup (alternatingGroup (Fin 5)) :=
    Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))
  let M : Subgroup A5WrTwo := (Cx.prod ⊤).map A5WrTwo.baseEmb
  have hle : M ≤ Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo) := by
    intro y hy
    dsimp only [M] at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_prod] at hp
    have hp1 : p.1 * x = x * p.1 := Subgroup.mem_centralizer_singleton_iff.mp hp.1
    calc A5WrTwo.baseEmb p * A5WrTwo.baseEmb (x, 1)
        = A5WrTwo.baseEmb (p * (x, 1)) := (map_mul A5WrTwo.baseEmb p (x, 1)).symm
      _ = A5WrTwo.baseEmb ((x, 1) * p) :=
            congrArg A5WrTwo.baseEmb (Prod.ext hp1 (by simp))
      _ = A5WrTwo.baseEmb (x, 1) * A5WrTwo.baseEmb p := map_mul A5WrTwo.baseEmb (x, 1) p
  have hMcard : Nat.card ↥M = 240 := by
    dsimp only [M]
    rw [Subgroup.card_map_of_injective A5WrTwo.baseEmb_injective,
      Nat.card_congr (Subgroup.prodEquiv Cx ⊤).toEquiv, Nat.card_prod]
    dsimp only [Cx]
    rw [hC4, Subgroup.card_top, shape240_natCard_A5]
  have hM : M = Subgroup.centralizer ({A5WrTwo.baseEmb (x, 1)} : Set A5WrTwo) :=
    Subgroup.eq_of_le_of_card_ge hle (by simp [hCbase, hMcard])
  refine ⟨(MulEquiv.subgroupCongr hM.symm).trans ?_⟩
  exact ((Subgroup.equivMapOfInjective (Cx.prod ⊤) A5WrTwo.baseEmb
      A5WrTwo.baseEmb_injective).symm).trans
    ((Subgroup.prodEquiv Cx ⊤).trans (MulEquiv.prodCongr eV Subgroup.topEquiv))

theorem gz9_isShapeTwoTwoTimesA5_wr {u : A5WrTwo} (hu : u ∈ commutator A5WrTwo)
    (hu2 : u ^ 2 = 1) (h240 : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 240) :
    IsShapeTwoTwoTimesA5 ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [shape240_card_centralizer_one_wr] at h240
    exact absurd h240 (by norm_num)
  rcases baseInvolution_cases hu hu2 hu1 with
      ⟨x, hx2, hx1, hux, _⟩ | ⟨_, _, _, _, _, _, _, h32⟩
  · have hC4 : Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 :=
      shape240_card_centralizer_A5 hx2 hx1
    rcases hux with hux | hux
    · rw [hux] at h240 ⊢
      exact shape240_baseEmb_fst x hx2 hx1 hC4
    · rw [hux] at h240 ⊢
      obtain ⟨f⟩ := shape240_baseEmb_fst x hx2 hx1 hC4
      refine ⟨((MulEquiv.subgroupCongr
        (by rw [A5WrTwo.swap_mul_baseEmb_mul_inv])).trans
        (shape240_conjCentralizerMulEquiv (⟨1, Multiplicative.ofAdd 1⟩ : A5WrTwo)
          (A5WrTwo.baseEmb (x, 1))).symm).trans f⟩
  · rw [h32] at h240
    exact absurd h240 (by norm_num)

theorem gz9_isShapeTwoTwoTimesA5_of_mulEquiv {Γ : Type} [Group Γ] (e : Γ ≃* A5WrTwo) {u : Γ}
    (hu : u ∈ commutator Γ) (hu2 : u ^ 2 = 1)
    (h240 : Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 240) :
    IsShapeTwoTwoTimesA5 ↥(Subgroup.centralizer ({u} : Set Γ)) := by
  have heu : e u ∈ commutator A5WrTwo := by
    have hmap : (commutator Γ).map e.toMonoidHom = commutator A5WrTwo := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [← hmap, Subgroup.mem_map_equiv]
    simpa using hu
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hcard : Nat.card ↥(Subgroup.centralizer ({e u} : Set A5WrTwo)) = 240 :=
    (Nat.card_congr (TwoHSData.centralizerMulEquiv e u).toEquiv).symm.trans h240
  obtain ⟨f⟩ := gz9_isShapeTwoTwoTimesA5_wr heu heu2 hcard
  exact ⟨(TwoHSData.centralizerMulEquiv e u).trans f⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
