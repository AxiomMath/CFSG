module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G]

structure RankFacts (X : Subgroup G) : Prop where
  bound : ∀ E : Subgroup G, E ≤ X → IsElemAbelian 2 E → Nat.card E ≤ 8
  cover : ∀ y ∈ X, y ^ 2 = 1 →
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ y ∈ E
  gen : ∀ N : Subgroup G,
    (∀ E : Subgroup G, E ≤ X → IsElemAbelian 2 E → Nat.card E = 8 → E ≤ N) → X ≤ N

private lemma isElemAbelian_map_iff {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] {f : Γ₁ →* Γ₂}
    (hf : Function.Injective f) (p : ℕ) (E : Subgroup Γ₁) :
    IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  constructor
  · intro h
    haveI : IsMulCommutative (E.map f) := h.1
    refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
    · intro a ha b hb
      apply hf
      rw [map_mul, map_mul]
      exact setLike_mul_comm (s := E.map f) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    · intro x hx
      apply hf
      simpa using h.2 (f x) (show f x ∈ E.map f from ⟨x, hx, rfl⟩)
  · intro h
    haveI : IsMulCommutative E := h.1
    refine ⟨inferInstance, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa using congrArg f (h.2 x hx)

private lemma transport_rank {X Y : Subgroup G} (e : ↥X ≃* ↥Y) {E : Subgroup G} (hE : E ≤ X) :
    ∃ E' : Subgroup G, E' ≤ Y ∧ Nat.card E' = Nat.card E ∧
      (IsElemAbelian 2 E' ↔ IsElemAbelian 2 E) ∧
      (∀ x (hx : x ∈ X), x ∈ E → ((e ⟨x, hx⟩ : ↥Y) : G) ∈ E') ∧
      (∀ y ∈ E', ∃ (x : G) (hx : x ∈ X), x ∈ E ∧ ((e ⟨x, hx⟩ : ↥Y) : G) = y) := by
  refine ⟨((E.subgroupOf X).map e.toMonoidHom).map Y.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, -, hzy⟩ := Subgroup.mem_map.1 hy
    rw [← hzy]
    exact z.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y),
      Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  · calc IsElemAbelian 2 (((E.subgroupOf X).map e.toMonoidHom).map Y.subtype)
        ↔ IsElemAbelian 2 ((E.subgroupOf X).map (Y.subtype.comp e.toMonoidHom)) := by
          rw [Subgroup.map_map]
      _ ↔ IsElemAbelian 2 (E.subgroupOf X) :=
          isElemAbelian_map_iff
            (fun a b h => e.injective (Subgroup.subtype_injective Y h)) 2 _
      _ ↔ IsElemAbelian 2 E :=
          (isElemAbelian_map_iff (Subgroup.subtype_injective X) 2 (E.subgroupOf X)).symm.trans
            (by rw [Subgroup.map_subgroupOf_eq_of_le hE])
  · intro x hx hxE
    exact Subgroup.mem_map.2
      ⟨e ⟨x, hx⟩, Subgroup.mem_map.2 ⟨⟨x, hx⟩, hxE, rfl⟩, rfl⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
    refine ⟨(w : G), w.2, hw, ?_⟩
    rw [← hzy, ← hwz]
    rfl

theorem RankFacts.of_mulEquiv {X Y : Subgroup G} (e : ↥X ≃* ↥Y) (h : RankFacts X) :
    RankFacts Y := by
  refine ⟨?_, ?_, ?_⟩
  · intro E hEY hE
    obtain ⟨E₀, hE₀X, hcard, hiff, -, -⟩ := transport_rank e.symm hEY
    rw [← hcard]
    exact h.bound E₀ hE₀X (hiff.mpr hE)
  · intro y hy hy2
    let x : ↥X := e.symm ⟨y, hy⟩
    have hx2 : (x : G) ^ 2 = 1 := by
      have hx2' : x ^ 2 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        change (e (e.symm ⟨y, hy⟩)) ^ 2 = 1
        rw [e.apply_symm_apply]
        exact Subtype.ext hy2
      have := congrArg (fun z : ↥X => (z : G)) hx2'
      simpa using this
    obtain ⟨E₀, hE₀X, hE₀, hcard, hxmem⟩ := h.cover (x : G) x.2 hx2
    obtain ⟨E', hE'Y, hcard', hiff', hfwd, -⟩ := transport_rank e hE₀X
    refine ⟨E', hE'Y, hiff'.mpr hE₀, hcard'.trans hcard, ?_⟩
    have hcoe : ((e ⟨(x : G), x.2⟩ : ↥Y) : G) = y := by
      have hx' : (⟨(x : G), x.2⟩ : ↥X) = x := rfl
      rw [hx']
      exact congrArg (fun z : ↥Y => (z : G)) (e.apply_symm_apply (⟨y, hy⟩ : ↥Y))
    have hmem := hfwd (x : G) x.2 hxmem
    rwa [hcoe] at hmem
  · intro N hN
    let N' : Subgroup G := ((N.subgroupOf Y).comap e.toMonoidHom).map X.subtype
    have hXle : X ≤ N' := h.gen N' ?_
    · intro y hy
      let x : ↥X := e.symm ⟨y, hy⟩
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hXle x.2)
      rw [Subgroup.mem_comap] at hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [show z = x from Subtype.ext hzx] at hz
      change ((e x : ↥Y) : G) ∈ N at hz
      have hxe : e x = (⟨y, hy⟩ : ↥Y) := e.apply_symm_apply _
      rw [hxe] at hz
      exact hz
    · intro E hEX hE hcardE x hxE
      obtain ⟨E', hE'Y, hcard', hiff', hfwd, -⟩ := transport_rank e hEX
      have hxX : x ∈ X := hEX hxE
      have hmem : ((e ⟨x, hxX⟩ : ↥Y) : G) ∈ N :=
        hN E' hE'Y (hiff'.mpr hE) (hcard'.trans hcardE) (hfwd x hxX hxE)
      exact Subgroup.mem_map.2
        ⟨⟨x, hxX⟩, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hmem), rfl⟩

theorem RankFacts.conj (c : G) {X : Subgroup G} (h : RankFacts X) :
    RankFacts (conjSub c X) :=
  h.of_mulEquiv
    (Subgroup.equivMapOfInjective X (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)

theorem RankFacts.of_eq {X Y : Subgroup G} (hXY : X = Y) (h : RankFacts X) : RankFacts Y := by
  subst hXY
  exact h

end CFSG.OddStandard.HigherRank.YamadaG23
