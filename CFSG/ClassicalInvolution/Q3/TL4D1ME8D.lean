module

public import CFSG.ClassicalInvolution.Q3.TL4D1ME8C
public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLE
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X E : Subgroup G} {e : Fin 3 → G}

theorem e8_basis_mem (hE : E8Struct X E) (he : E8Basis E e) {N : Subgroup G}
    (hNn : ∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N) {g : ↥X} (hg : (g : G) ∈ N)
    {u : Fin 3 → ZMod 2} {k : Fin 3} (hu : (e8Hom hE he g).1 *ᵥ u + u = Pi.single k 1) :
    e k ∈ N := by
  have hc : e8Coord e u ∈ E := e8Coord_mem he u
  have h1 : e8Coord e u * (g : G)⁻¹ * (e8Coord e u)⁻¹ ∈ N :=
    hNn _ (hE.le hc) _ (N.inv_mem hg)
  have h3 : e k = (g : G) * (e8Coord e u * (g : G)⁻¹ * (e8Coord e u)⁻¹) := by
    rw [← e8Coord_single (e := e) k, ← hu, e8Coord_add he, ← conj_e8Coord_e8Hom hE he g,
      inv_eq_of_mul_eq_one_right (hE.sq _ hc)]
    group
  rw [h3]
  exact N.mul_mem hg h1

theorem e8NormalFact : E8NormalFact := by
  intro G _ _ X E hE N hNX hNn
  obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
  have hs := isSimpleGroup_sl3Two
  set L := (N.subgroupOf X).map (e8Hom hE he) with hL
  have hLn : L.Normal := by
    refine ⟨fun y hy A => ?_⟩
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := e8Hom_surjective hE he A
    refine ⟨g * n * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hNn _ g.2 _ (Subgroup.mem_subgroupOf.mp hn)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
  · left
    have hNE : N ≤ E := fun n hn => by
      have hm : e8Hom hE he ⟨n, hNX hn⟩ ∈ L :=
        ⟨⟨n, hNX hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [h, Subgroup.mem_bot] at hm
      exact (e8Hom_eq_one_iff hE he _).mp hm
    have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hE.card]; norm_num)
    exact hE2.to_le hNE
  · right
    have hmem : ∀ A, ∃ g : ↥X, (g : G) ∈ N ∧ e8Hom hE he g = A := fun A => by
      have hA : A ∈ L := by rw [h]; exact Subgroup.mem_top A
      obtain ⟨g, hg, hgA⟩ := hA
      exact ⟨g, Subgroup.mem_subgroupOf.mp hg, hgA⟩
    obtain ⟨d0, d1, d2, w0, w1, w2⟩ := transvection_facts
    obtain ⟨g0, hg0, hgA0⟩ := hmem (slOf _ d0)
    obtain ⟨g1, hg1, hgA1⟩ := hmem (slOf _ d1)
    obtain ⟨g2, hg2, hgA2⟩ := hmem (slOf _ d2)
    have hb0 : e 0 ∈ N := e8_basis_mem hE he hNn hg0 (by rw [hgA0, slOf_val]; exact w0)
    have hb1 : e 1 ∈ N := e8_basis_mem hE he hNn hg1 (by rw [hgA1, slOf_val]; exact w1)
    have hb2 : e 2 ∈ N := e8_basis_mem hE he hNn hg2 (by rw [hgA2, slOf_val]; exact w2)
    have hEN : E ≤ N := fun z hz => by
      obtain ⟨v, rfl⟩ := exists_e8Coord_eq he hz
      exact N.mul_mem (N.mul_mem (N.pow_mem hb0 _) (N.pow_mem hb1 _)) (N.pow_mem hb2 _)
    refine le_antisymm hNX fun x hx => ?_
    obtain ⟨g, hg, hgx⟩ := hmem (e8Hom hE he ⟨x, hx⟩)
    have h1 : ((g⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ E :=
      (e8Hom_eq_one_iff hE he _).mp (by rw [map_mul, map_inv, hgx, inv_mul_cancel])
    have h2 := N.mul_mem hg (hEN h1)
    simpa using h2

theorem e8PerfectFact : E8PerfectFact := by
  intro G _ _ X E hE
  have hCX : ⁅X, X⁆ ≤ X := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have hCn : ∀ x ∈ X, ∀ y ∈ ⁅X, X⁆, x * y * x⁻¹ ∈ ⁅X, X⁆ := fun x hx y hy =>
    conj_mem_commutator_self hx hy
  rcases e8NormalFact G X E hE _ hCX hCn with h2 | h
  · exfalso
    have hCE := hE.core _ hCX hCn h2
    obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
    obtain ⟨a, ha⟩ := e8Hom_surjective hE he sl3A
    obtain ⟨b, hb⟩ := e8Hom_surjective hE he sl3B
    have hab : ((⁅a, b⁆ : ↥X) : G) ∈ E := hCE (Subgroup.commutator_mem_commutator a.2 b.2)
    have h1 := (e8Hom_eq_one_iff hE he _).mpr hab
    rw [map_commutatorElement, ha, hb, commutatorElement_eq_one_iff_mul_comm] at h1
    exact sl3A_mul_ne h1
  · exact h

end CFSG.ClassicalInvolution.Q3.TL4
