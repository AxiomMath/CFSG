module

public import CFSG.FeitThompson.Definitions.DadeCosetPacket
public import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
public import CFSG.FeitThompson.Representations.CanonicalPiSetComponent
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses
import CFSG.FeitThompson.Representations.TISetDadeData

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem conjInv_image_conjInv_image (S : Set G) (g k : G) :
    (fun x => k⁻¹ * x * k) '' ((fun x => g⁻¹ * x * g) '' S)
      = (fun x => (g * k)⁻¹ * x * (g * k)) '' S := by
  rw [Set.image_image]
  exact Set.image_congr' (fun x => by group)

namespace IsDadeData

open CoprimeComponent

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a : G}

theorem piComponent_of_mem_conjInv_image_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) {g x : G}
    (hx : x ∈ (fun y => g⁻¹ * y * g) '' dadeCoset H a) :
    piComponent (dadePrimes L A) x = g⁻¹ * a * g := by
  obtain ⟨y, hy, rfl⟩ := hx
  change piComponent (dadePrimes L A) (g⁻¹ * y * g) = g⁻¹ * a * g
  have hc : g⁻¹ * y * (g⁻¹)⁻¹ = g⁻¹ * y * g := by group
  rw [← hc, piComponent_conj, hD.piComponent_of_mem_dadeCoset ha hy]
  group

theorem normalizer_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) :
    Subgroup.normalizer (dadeCoset H a) = Subgroup.centralizer ({a} : Set G) := by
  apply le_antisymm
  · intro g hg
    have hmem : g * a * g⁻¹ ∈ dadeCoset H a :=
      (Subgroup.mem_set_normalizer_iff.1 hg a).1 (self_mem_dadeCoset H a)
    have h1 : piComponent (dadePrimes L A) (g * a * g⁻¹) = a :=
      hD.piComponent_of_mem_dadeCoset ha hmem
    rw [piComponent_conj, hD.piComponent_of_mem_dadeCoset ha (self_mem_dadeCoset H a)] at h1
    refine Subgroup.mem_centralizer_iff.2 ?_
    simp only [Set.mem_singleton_iff, forall_eq]
    calc a * g = (g * a * g⁻¹) * g := by rw [h1]
      _ = g * a := by group
  · intro g hg
    have hcomm : Commute g⁻¹ a⁻¹ :=
      (Commute.symm (Subgroup.mem_centralizer_iff.1 hg a rfl)).inv_inv
    refine Subgroup.mem_normalizer_fintype ?_
    intro n hn
    refine mem_dadeCoset_iff.2 ?_
    have key : g * n * g⁻¹ * a⁻¹ = g * (n * a⁻¹) * g⁻¹ := by
      calc g * n * g⁻¹ * a⁻¹ = g * n * (g⁻¹ * a⁻¹) := by group
        _ = g * n * (a⁻¹ * g⁻¹) := by rw [hcomm.eq]
        _ = g * (n * a⁻¹) * g⁻¹ := by group
    rw [key]
    exact hD.conj_mem_H ha hg (mem_dadeCoset_iff.1 hn)

theorem setOf_conjInv_image_dadeCoset_eq (hD : IsDadeData L A H) (ha : a ∈ A) :
    {g : G | (fun x => g⁻¹ * x * g) '' dadeCoset H a = dadeCoset H a}
      = (Subgroup.centralizer ({a} : Set G) : Set G) := by
  ext g
  simp only [Set.mem_ofPred_eq, ← mem_normalizer_iff_conjInv_image_eq, SetLike.mem_coe,
    ← hD.normalizer_dadeCoset ha]

theorem conjInv_image_dadeCoset_eq_iff_mem_centralizer (hD : IsDadeData L A H) (ha : a ∈ A)
    {g : G} :
    (fun x => g⁻¹ * x * g) '' dadeCoset H a = dadeCoset H a
      ↔ g ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [← mem_normalizer_iff_conjInv_image_eq, hD.normalizer_dadeCoset ha]

theorem conjInv_image_dadeCoset_eq (hD : IsDadeData L A H) (ha : a ∈ A) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) :
    (fun x => g⁻¹ * x * g) '' dadeCoset H a = dadeCoset H a :=
  (hD.conjInv_image_dadeCoset_eq_iff_mem_centralizer ha).2 hg

theorem conjInv_image_dadeCoset_eq_of_not_disjoint (hD : IsDadeData L A H) (ha : a ∈ A) {g k : G}
    (h : ¬ Disjoint ((fun x => g⁻¹ * x * g) '' dadeCoset H a)
      ((fun x => k⁻¹ * x * k) '' dadeCoset H a)) :
    (fun x => g⁻¹ * x * g) '' dadeCoset H a = (fun x => k⁻¹ * x * k) '' dadeCoset H a := by
  obtain ⟨x, hxg, hxk⟩ := Set.not_disjoint_iff.1 h
  have hconj : g⁻¹ * a * g = k⁻¹ * a * k :=
    (hD.piComponent_of_mem_conjInv_image_dadeCoset ha hxg).symm.trans
      (hD.piComponent_of_mem_conjInv_image_dadeCoset ha hxk)
  have hc : g * k⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 ?_
    simp only [Set.mem_singleton_iff, forall_eq]
    have key : k * g⁻¹ * a * g * k⁻¹ = a := by
      calc k * g⁻¹ * a * g * k⁻¹ = k * (g⁻¹ * a * g) * k⁻¹ := by group
        _ = k * (k⁻¹ * a * k) * k⁻¹ := by rw [hconj]
        _ = a := by group
    calc a * (g * k⁻¹) = (g * k⁻¹) * (k * g⁻¹ * a * g * k⁻¹) := by group
      _ = (g * k⁻¹) * a := by rw [key]
  have h1 : (fun x => (g * k⁻¹ * k)⁻¹ * x * (g * k⁻¹ * k)) '' dadeCoset H a
      = (fun x => k⁻¹ * x * k) '' dadeCoset H a := by
    rw [← conjInv_image_conjInv_image, hD.conjInv_image_dadeCoset_eq ha hc]
  simpa using h1

theorem disjoint_conjInv_image_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) {g k : G}
    (h : (fun x => g⁻¹ * x * g) '' dadeCoset H a ≠ (fun x => k⁻¹ * x * k) '' dadeCoset H a) :
    Disjoint ((fun x => g⁻¹ * x * g) '' dadeCoset H a)
      ((fun x => k⁻¹ * x * k) '' dadeCoset H a) :=
  not_not.1 fun hd => h (hD.conjInv_image_dadeCoset_eq_of_not_disjoint ha hd)

theorem pairwiseDisjoint_conjInv_image_dadeCoset (hD : IsDadeData L A H) (ha : a ∈ A) :
    (Set.range fun g : G => (fun x => g⁻¹ * x * g) '' dadeCoset H a).PairwiseDisjoint id := by
  rintro S ⟨g, rfl⟩ T ⟨k, rfl⟩ hST
  exact hD.disjoint_conjInv_image_dadeCoset ha hST

theorem conjInv_image_dadeCoset_eq_or_disjoint (hD : IsDadeData L A H) (ha : a ∈ A) (g : G) :
    (fun x => g⁻¹ * x * g) '' dadeCoset H a = dadeCoset H a ∨
      Disjoint (dadeCoset H a) ((fun x => g⁻¹ * x * g) '' dadeCoset H a) := by
  by_cases hg : g ∈ Subgroup.centralizer ({a} : Set G)
  · exact Or.inl (hD.conjInv_image_dadeCoset_eq ha hg)
  · refine Or.inr ?_
    have h1 : (fun x => (1 : G)⁻¹ * x * 1) '' dadeCoset H a = dadeCoset H a := by simp
    have hne : (fun x => (1 : G)⁻¹ * x * 1) '' dadeCoset H a
        ≠ (fun x => g⁻¹ * x * g) '' dadeCoset H a := by
      rw [h1]
      exact fun heq => hg ((hD.conjInv_image_dadeCoset_eq_iff_mem_centralizer ha).1 heq.symm)
    have hd := hD.disjoint_conjInv_image_dadeCoset ha hne
    rwa [h1] at hd

end IsDadeData

end

end CFSG.FeitThompson
