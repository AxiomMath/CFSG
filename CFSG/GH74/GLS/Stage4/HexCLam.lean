module

public import CFSG.GH74.GLS.Stage4.HexCNondeg
public import CFSG.GH74.GLS.Stage4.HexCAct

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem e_ne_zero (D : HexData root F) (hnd : NondegG2 root) {A2 A4 : F → F → F}
    {g3 : F → F → G} (had : ActData D A2 A4 g3) {e : F} (hA2 : ∀ c s, A2 c s = e * c * s ^ 3) :
    e ≠ 0 := by
  intro he
  apply hnd
  intro x hx y hy
  obtain ⟨c, rfl⟩ := D.p6_surj x hx
  obtain ⟨s, rfl⟩ := D.p1_surj y hy
  rw [had.eq c s]
  have h0 : D.p2 (A2 c s) = 1 := by
    rw [hA2, he, zero_mul, zero_mul]; exact map_zero_of_add' D.p2_add
  unfold Nel
  rw [h0, one_mul]
  have h3 : g3 c s ∈ root 3 ⊔ root 4 ⊔ root 5 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (had.g3_mem c s))
  have h4 : D.p4 (A4 c s) ∈ root 3 ⊔ root 4 ⊔ root 5 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (D.p4_mem _))
  have h5 : D.p5 (c * s) ∈ root 3 ⊔ root 4 ⊔ root 5 := Subgroup.mem_sup_right (D.p5_mem _)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 h4) h5

theorem exists_Lam [Finite G] (D : HexData root F) {μ : G → F} (hμ : MuData D μ)
    {g3 : F → F → G} (hg3 : ∀ c s, g3 c s ∈ root 3) {e : F} (he : e ≠ 0) (h3 : (3 : F) ≠ 0)
    (hMg : ∀ c s, μ (g3 c s) = 3 * e * c * s ^ 2) (hcard : Nat.card (root 3) = Nat.card F) :
    ∃ Λ : F → G, (∀ v, Λ v ∈ root 3) ∧ (∀ v, μ (Λ v) = v) ∧ (∀ v w, Λ (v + w) = Λ v * Λ w) ∧
      (∀ u ∈ root 3, ∃ v, Λ v = u) := by
  have hsurj : Function.Surjective (fun u : root 3 => μ (u : G)) := by
    intro v
    have h3e : 3 * e ≠ 0 := mul_ne_zero h3 he
    refine ⟨⟨g3 (v / (3 * e)) 1, hg3 _ _⟩, ?_⟩
    show μ (g3 (v / (3 * e)) 1) = v
    rw [hMg]; field_simp
  have hb : Function.Bijective (fun u : root 3 => μ (u : G)) :=
    (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcard⟩
  let eqv := Equiv.ofBijective _ hb
  have key : ∀ v, μ ((eqv.symm v : root 3) : G) = v := fun v => eqv.apply_symm_apply v
  refine ⟨fun v => (eqv.symm v : G), fun v => (eqv.symm v).2, key, fun v w => ?_,
    fun u hu => ⟨μ u, ?_⟩⟩
  · have : eqv.symm (v + w) = eqv.symm v * eqv.symm w := by
      apply eqv.injective
      rw [Equiv.apply_symm_apply]
      show v + w = μ (((eqv.symm v : root 3) : G) * ((eqv.symm w : root 3) : G))
      rw [hμ.add _ (eqv.symm v).2 _ (eqv.symm w).2, key, key]
    exact congrArg Subtype.val this
  · have : eqv.symm (eqv ⟨u, hu⟩) = ⟨u, hu⟩ := eqv.symm_apply_apply _
    exact congrArg Subtype.val this

end CFSG.GH74.GLS.Stage4.Hex
