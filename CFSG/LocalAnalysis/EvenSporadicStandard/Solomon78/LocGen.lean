module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLocal

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

theorem maximal_of_isCoatom_subgroupOf {L K : Subgroup G} (hKL : K ≤ L)
    (h : IsCoatom (K.subgroupOf L)) :
    ∀ M : Subgroup G, K ≤ M → M ≤ L → M = K ∨ M = L := by
  intro M hKM hML
  have h1 : K.subgroupOf L ≤ M.subgroupOf L := fun x hx =>
    mem_subgroupOf.2 (hKM (mem_subgroupOf.1 hx))
  rcases h.le_iff.1 h1 with h2 | h2
  · right
    rw [Subgroup.subgroupOf_eq_top] at h2
    exact le_antisymm hML h2
  · left
    have h4 := Subgroup.subgroupOf_inj.1 h2
    rw [inf_eq_left.2 hML, inf_eq_left.2 hKL] at h4
    exact h4

theorem sol78Generate_of_overgroups {L K : Subgroup G} {u : G} (hu2 : orderOf u = 2)
    (hC : ∀ c ∈ L, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = u)
    (hKL : K ≤ L) (huL : u ∈ L)
    (hov : ∀ X : Subgroup G, K ≤ X → X ≤ L → X ≤ L ⊓ centralizer ({u} : Set G) ∨ X = L) :
    Sol78Generate L K u := by
  intro l hl hw
  obtain ⟨v, hv, hwv, -⟩ := hw
  have hM1 : K ≤ K ⊔ K.map (conjHom l) := le_sup_left
  have hM2 : K ⊔ K.map (conjHom l) ≤ L := by
    refine sup_le hKL ?_
    rintro _ ⟨k, hk, rfl⟩
    exact mul_mem (mul_mem hl (hKL hk)) (inv_mem hl)
  rcases hov _ hM1 hM2 with h | h
  swap
  · exact h
  exfalso
  have huu : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at this
  have hKl : K.map (conjHom l) ≤ L ⊓ centralizer ({u} : Set G) := le_sup_right.trans h
  have hc : ∀ k ∈ K, (l⁻¹ * u * l) * k = k * (l⁻¹ * u * l) := by
    intro k hk
    have hk' : l * k * l⁻¹ ∈ K.map (conjHom l) := ⟨k, hk, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (hKl hk').2
    calc (l⁻¹ * u * l) * k = l⁻¹ * (u * (l * k * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * k * l⁻¹) * u) * l := by rw [h1]
      _ = k * (l⁻¹ * u * l) := by group
  have hcL : l⁻¹ * u * l ∈ L := mul_mem (mul_mem (inv_mem hl) huL) hl
  have hv2 : orderOf v = 2 := hv.1.2.2
  rcases hC _ hcL hc with h0 | h0
  · have : u = 1 := by
      have := congrArg (fun x => l * x * l⁻¹) h0
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  · have hwu : l * u * l⁻¹ = u := by
      calc l * u * l⁻¹ = l * (l⁻¹ * u * l) * l⁻¹ := by rw [h0]
        _ = u := by group
    have hv1 : v = 1 := by
      have h1 : u * v = u := by rw [← hwv, hwu]
      have : u * v = u * 1 := by rw [h1, mul_one]
      exact mul_left_cancel this
    rw [hv1, orderOf_one] at hv2
    exact absurd hv2 (by decide)

theorem inducedByCentralizer_of_conjNormal {L K : Subgroup G} {u : G}
    (hK : K ≤ L ⊓ centralizer ({u} : Set G))
    [(K.subgroupOf (L ⊓ centralizer ({u} : Set G))).Normal]
    (hsurj : Function.Surjective
      (MulAut.conjNormal : ↥(L ⊓ centralizer ({u} : Set G)) →*
        MulAut ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G))))) :
    InducedByCentralizer L K u := by
  apply inducedByCentralizer_of_forall_aut
  intro α
  let e : ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G))) ≃* ↥K :=
    Subgroup.subgroupOfEquivOfLe hK
  obtain ⟨c, hc⟩ := hsurj (e.trans (α.trans e.symm))
  refine ⟨(c : G), c.2, fun k => ?_⟩
  have h1 := congrArg (fun β : MulAut ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G))) =>
    ((β (e.symm k) : ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G)))) :
      ↥(L ⊓ centralizer ({u} : Set G))).1) hc
  simp only [MulAut.conjNormal_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
  have h2 : (((e.symm (α k) : ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G)))) :
      ↥(L ⊓ centralizer ({u} : Set G))) : G) = ((α k : ↥K) : G) := rfl
  have h3 : (((e.symm k : ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set G)))) :
      ↥(L ⊓ centralizer ({u} : Set G))) : G) = (k : G) := rfl
  rw [← h2]
  simpa [h3] using h1.symm

@[expose] def infCentralizerMulEquiv {L : Subgroup G} {u : G} (hu : u ∈ L) :
    ↥(L ⊓ centralizer ({u} : Set G)) ≃* ↥(centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L)) where
  toFun c := ⟨⟨c, c.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
    (mem_centralizer_singleton_iff.1 c.2.2))⟩
  invFun d := ⟨d.1.1, d.1.2, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 d.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem eq_of_index_two_of_isPerfect {H : Type*} [Group H] [Finite H] {E F : Subgroup H}
    (hE : Group.IsPerfect E) (hEi : E.index = 2) (hFi : F.index = 2) : F = E := by
  have hFn : F.Normal := Subgroup.normal_of_index_eq_two hFi
  have hcard : Nat.card (H ⧸ F) = 2 := by rw [← Subgroup.index, hFi]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (H ⧸ F) := isCyclic_of_prime_card hcard
  let _ : CommGroup (H ⧸ F) := IsCyclic.commGroup
  have hker : commutator E ≤ ((QuotientGroup.mk' F).comp E.subtype).ker :=
    Abelianization.commutator_subset_ker _
  rw [show commutator E = ⊤ from hE.commutator_eq_top] at hker
  have hEF : E ≤ F := by
    intro e he
    have := hker (Subgroup.mem_top ⟨e, he⟩)
    simpa using this
  have h1 := Subgroup.card_mul_index E
  have h2 := Subgroup.card_mul_index F
  rw [hEi] at h1
  rw [hFi] at h2
  exact (Subgroup.eq_of_le_of_card_ge hEF (by omega)).symm

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := hA
  have hc : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  let e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator, hp]

end CFSG.EvenSporadicStandard.Solomon78
