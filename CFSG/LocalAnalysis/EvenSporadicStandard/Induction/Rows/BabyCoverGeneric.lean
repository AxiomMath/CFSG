module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocIdx2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem commutator_le_of_index_two {H : Type*} [Group H] {N : Subgroup H} (h : N.index = 2) :
    commutator H ≤ N := by
  have hN : N.Normal := Subgroup.normal_of_index_eq_two h
  have hc : Nat.card (H ⧸ N) = 2 := h
  have : Finite (H ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have : IsMulCommutative (H ⧸ N) := isMulCommutative_of_card_le_four' (by omega)
  have := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rwa [QuotientGroup.ker_mk'] at this

theorem orderOf_eq_of_isConj_baby {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  have := MulEquiv.orderOf_eq (MulAut.conj c) a
  rw [MulAut.conj_apply] at this
  exact this.symm

theorem openQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

@[expose] def comapMulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') (E : Subgroup H') :
    ↥(E.comap e.toMonoidHom) ≃* ↥E where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by
    show e (e.symm y) ∈ E
    rw [MulEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : H) (y : H))

theorem isIdx2Cover_comap_mulEquiv {H H' : Type} [Group H] [Group H'] {E : Subgroup H'}
    (h : IsIdx2Cover H' E) (e : H ≃* H') : IsIdx2Cover H (E.comap e.toMonoidHom) := by
  have := h.normal
  refine ⟨Subgroup.Normal.comap h.normal _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ e.surjective]
    exact h.index_eq
  · exact openQuasisimple_of_mulEquiv (comapMulEquiv e E).symm h.quasisimple
  · rw [card_center_of_mulEquiv' (comapMulEquiv e E)]
    exact h.card_center
  · intro x hx
    have hx' : e x ∈ centralizer (E : Set H') := by
      rw [mem_centralizer_iff]
      intro g hg
      have hg' : e.symm g ∈ E.comap e.toMonoidHom := by
        show e (e.symm g) ∈ E
        rw [MulEquiv.apply_symm_apply]
        exact hg
      have := mem_centralizer_iff.1 hx _ hg'
      have h2 := congrArg e this
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    exact h.centralizer_le hx'

@[expose] noncomputable def infCentralizerEquiv {G H : Type*} [Group G] [Group H]
    (L : Subgroup G) (e : ↥L ≃* H) {u : G} (hu : u ∈ L) :
    ↥(L ⊓ centralizer ({u} : Set G)) ≃* ↥(centralizer ({e ⟨u, hu⟩} : Set H)) :=
  let f : ↥(L ⊓ centralizer ({u} : Set G)) →* ↥(centralizer ({e ⟨u, hu⟩} : Set H)) :=
    { toFun := fun x => ⟨e ⟨x, x.2.1⟩, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext (mem_centralizer_singleton_iff.1 x.2.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul e (⟨x, x.2.1⟩ : ↥L) ⟨y, y.2.1⟩) }
  MulEquiv.ofBijective f
    ⟨fun x y hxy => by
      have h1 := congrArg Subtype.val hxy
      have h2 := e.injective h1
      have h3 : ((⟨x, x.2.1⟩ : ↥L) : G) = ((⟨y, y.2.1⟩ : ↥L) : G) := congrArg Subtype.val h2
      exact Subtype.ext h3,
     fun y => by
      have hy := mem_centralizer_singleton_iff.1 y.2
      have hz : (e.symm y : ↥L) * ⟨u, hu⟩ = ⟨u, hu⟩ * (e.symm y : ↥L) := by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hy
      refine ⟨⟨((e.symm y : ↥L) : G), (e.symm y : ↥L).2,
        mem_centralizer_singleton_iff.2 (congrArg Subtype.val hz)⟩, ?_⟩
      exact Subtype.ext (by simp [f])⟩

@[expose] def subgroupEquivOfIff {C A : Type*} [Group C] [Group A] (Ψ : C ≃* A) {K : Subgroup C}
    {E : Subgroup A} (h : ∀ x, x ∈ K ↔ Ψ x ∈ E) : ↥K ≃* ↥E where
  toFun x := ⟨Ψ x, (h _).1 x.2⟩
  invFun y := ⟨Ψ.symm y, (h _).2 (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (Ψ.symm_apply_apply x)
  right_inv y := Subtype.ext (Ψ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul Ψ (x : C) (y : C))

theorem exists_conj_of_aut_transport {C A : Type*} [Group C] [Group A] (Ψ : C ≃* A)
    {K : Subgroup C} {E : Subgroup A} (h : ∀ x, x ∈ K ↔ Ψ x ∈ E)
    (hE : ∀ σ : MulAut ↥E, ∃ b : A, ∀ y : ↥E, ((σ y : ↥E) : A) = b * y * b⁻¹)
    (α : MulAut ↥K) : ∃ c : C, ∀ k : ↥K, ((α k : ↥K) : C) = c * k * c⁻¹ := by
  let θ := subgroupEquivOfIff Ψ h
  obtain ⟨b, hb⟩ := hE ((θ.symm.trans α).trans θ)
  refine ⟨Ψ.symm b, fun k => ?_⟩
  apply Ψ.injective
  have h1 := hb (θ k)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
  exact h1

end CFSG.EvenSporadicStandard.Induction.Hyp
