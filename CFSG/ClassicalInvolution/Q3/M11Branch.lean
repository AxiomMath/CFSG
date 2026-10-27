module

public import CFSG.ClassicalInvolution.Q3.M11Exact
public import CFSG.ClassicalInvolution.Q3.Quasisimple

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open scoped MatrixGroups

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem map_centralizer_singleton_mulEquiv₃ (e : X ≃* X') (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set X') := by
  ext x'
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem map_map_symm_mulEquiv₃ (e : X ≃* X') (L : Subgroup X) :
    (L.map e.toMonoidHom).map e.symm.toMonoidHom = L := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  rw [this, Subgroup.map_id]

theorem IsClassicalMember3.map_mulEquiv (e : X ≃* X') {L : Subgroup X} {z : X}
    (h : IsClassicalMember3 L z) : IsClassicalMember3 (L.map e.toMonoidHom) (e z) where
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    rw [← map_centralizer_singleton_mulEquiv₃]
    exact isSubnormal_map_mulEquiv e h.subnormal
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective e.toMonoidHom e.injective
    have hO : (classicalInvolutionOddCore L).map eL.toMonoidHom =
        classicalInvolutionOddCore (L.map e.toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant eL
    exact ⟨(QuotientGroup.congr _ _ eL hO).symm.trans e'⟩

end Transport

section Exact

variable {X : Type} [Group X] [Finite X]

theorem IsClassicalMember3.card_eq_of_mulEquiv_m11 (e : X ≃* ↥NativeSporadic.M11)
    {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) : Nat.card L = 24 := by
  have hz : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  have hC : Nat.card (Subgroup.centralizer ({z} : Set X)) ≤ 48 := by
    have h1 := Subgroup.card_map_of_injective (f := e.toMonoidHom)
      (K := Subgroup.centralizer ({z} : Set X)) e.injective
    rw [map_centralizer_singleton_mulEquiv₃] at h1
    rw [← h1]
    exact card_centralizer_le_of_orderOf_eq_two hz
  have hle : Nat.card L ≤ 48 :=
    (Subgroup.card_le_of_le (isSubnormal_le h.subnormal)).trans hC
  obtain ⟨e'⟩ := h.nonempty_equiv
  have hq : Nat.card (L ⧸ classicalInvolutionOddCore L) = 24 := by
    rw [Nat.card_congr e'.toEquiv, natCard_sl2Three]
  have hodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L)
  rw [hq] at hmul
  obtain ⟨k, hk⟩ := hodd
  omega

end Exact

section Branch

theorem m11Branch3 : M11Branch3 := by
  intro Y _ _ Λ hΛ hqs hO hex
  obtain ⟨ψ, hψ⟩ := hex
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hqs.2
  have hM : IsSimpleGroup ↥NativeSporadic.M11 := m11Facts.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      have h1 : ∀ x, ψ x = 1 := fun x => by
        rw [← MonoidHom.mem_ker, h]
        trivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Y ⧸ Subgroup.center Y)
      obtain ⟨a', rfl⟩ := hψ a
      obtain ⟨b', rfl⟩ := hψ b
      exact hab (by rw [h1, h1])
  let eψ : ↥NativeSporadic.M11 ≃* (Y ⧸ Subgroup.center Y) :=
    MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩
  let π : Y →* ↥NativeSporadic.M11 :=
    eψ.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπsurj : Function.Surjective π := fun m =>
    ⟨(eψ m).out, by
      show eψ.symm (QuotientGroup.mk (eψ m).out) = m
      rw [QuotientGroup.out_eq', MulEquiv.symm_apply_apply]⟩
  have hπker : π.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    show eψ.symm (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hper : Group.IsPerfect Y := ⟨hqs.1⟩
  have hinj : Function.Injective π :=
    injective_of_perfect_central_two π hπsurj hper hπker.le
      (by rw [hπker]; exact isPGroup_center_of_corefree hO)
  let f : Y ≃* ↥NativeSporadic.M11 := MulEquiv.ofBijective π ⟨hinj, hπsurj⟩
  obtain ⟨L₀, hL₀⟩ := hΛ.nonempty
  refine ⟨Unit, inferInstance, ⟨{
    kind := fun _ => CompData.m11
    valid := fun _ => Or.inr (Or.inr rfl)
    hom := fun _ => f.symm.toMonoidHom
    ker_le_center := fun _ => by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr f.symm.injective]
      exact bot_le
    commute := fun i j h => absurd (Subsingleton.elim i j) h
    generate := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_iSup_of_mem () ⟨f x, f.symm_apply_apply x⟩
    fundamental := fun L hL => by
      obtain ⟨z, hz⟩ := hΛ.classical L hL
      exact ⟨(), L.map f.toMonoidHom, ⟨f z, hz.map_mulEquiv f⟩, (map_map_symm_mulEquiv₃ f L).symm⟩
    meets := fun _ => by
      obtain ⟨z, hz⟩ := hΛ.classical L₀ hL₀
      exact ⟨L₀.map f.toMonoidHom, ⟨f z, hz.map_mulEquiv f⟩, by
        rw [map_map_symm_mulEquiv₃ f L₀]
        exact hL₀⟩
    card_eq := fun L hL => by
      obtain ⟨z, hz⟩ := hΛ.classical L hL
      exact hz.card_eq_of_mulEquiv_m11 f }⟩⟩

end Branch

end CFSG.ClassicalInvolution.Q3
