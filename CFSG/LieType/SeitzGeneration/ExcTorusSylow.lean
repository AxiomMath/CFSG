module

public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers

structure SylowTorus (G : Type*) [Group G] (p m : ℕ) : Prop where
  exists_torus : ∃ T E : Subgroup G, IsMulCommutative T ∧
    (∀ P : Subgroup G, IsPGroup p P → ∃ g : G, P ≤ T.map (MulAut.conj g).toMonoidHom) ∧
      E ≤ T ∧ (∀ x ∈ T, x ^ p = 1 → x ∈ E) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ m

@[expose] def torsionSubgroup {G : Type*} [Group G] (T : Subgroup G) (hT : IsMulCommutative T)
    (p : ℕ) : Subgroup G where
  carrier := {x | x ∈ T ∧ x ^ p = 1}
  mul_mem' {a b} ha hb := ⟨T.mul_mem ha.1 hb.1, by
    have := hT
    rw [Commute.mul_pow (show Commute a b from setLike_mul_comm ha.1 hb.1), ha.2, hb.2,
      one_mul]⟩
  one_mem' := ⟨T.one_mem, one_pow p⟩
  inv_mem' {a} ha := ⟨T.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_torsionSubgroup {G : Type*} [Group G] {T : Subgroup G} {hT : IsMulCommutative T}
    {p : ℕ} {x : G} : x ∈ torsionSubgroup T hT p ↔ x ∈ T ∧ x ^ p = 1 := Iff.rfl

namespace SylowTorus

variable {G : Type*} [Group G] {p m : ℕ}

theorem rank_le (h : SylowTorus G p m) (hp : p.Prime) {F : Subgroup G} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ m := by
  obtain ⟨T, E, -, hconj, hET, hE, -, hcard⟩ := h.exists_torus
  obtain ⟨g, hg⟩ := hconj F (isPGroup_of_isElemAbelian hF)
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp.pos m).ne')
  have hle : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hg hx
    refine hE _ ?_ ?_
    · have : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom t) = t := by
        show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t
        group
      rw [this]
      exact ht
    · have h1 := hF.2 ((MulAut.conj g).toMonoidHom t) hx
      have h2 := map_pow (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom t) p
      rw [h1, map_one] at h2
      exact h2.symm
  calc Nat.card F = Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ ≤ Nat.card E := Subgroup.card_le_of_le hle
    _ = p ^ m := hcard

theorem exists_elemAbelian (h : SylowTorus G p m) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ m := by
  obtain ⟨T, E, -, -, -, -, hE, hcard⟩ := h.exists_torus
  exact ⟨E, hE, hcard⟩

theorem rankLE2 (h : SylowTorus G p m) (hp : p.Prime) (hm : m ≤ 2) : RankLE2 p G := fun _ hF =>
  (h.rank_le hp hF).trans (Nat.pow_le_pow_right hp.pos hm)

theorem not_rankLE2 (h : SylowTorus G p m) (hp : p.Prime) (hm : 3 ≤ m) : ¬ RankLE2 p G := by
  intro hr
  obtain ⟨E, hE, hcard⟩ := h.exists_elemAbelian
  have h1 := hr E hE
  rw [hcard] at h1
  have h2 : p ^ 3 ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem of_mulEquiv {H : Type*} [Group H] (h : SylowTorus G p m) (e : G ≃* H) :
    SylowTorus H p m := by
  obtain ⟨T, E, hT, hconj, hET, hE, hEel, hcard⟩ := h.exists_torus
  refine ⟨⟨T.map e.toMonoidHom, E.map e.toMonoidHom, ?_, ?_, Subgroup.map_mono hET, ?_,
    elementary_abelian_map p hEel e.toMonoidHom, ?_⟩⟩
  · refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : H) * b = b * a
    have := hT
    rw [← hxa, ← hyb]
    change e x * e y = e y * e x
    rw [← map_mul, ← map_mul, setLike_mul_comm hx hy]
  · intro P hP
    have hP' : IsPGroup p (P.map e.symm.toMonoidHom) :=
      hP.of_surjective (e.symm.toMonoidHom.subgroupMap P)
        (e.symm.toMonoidHom.subgroupMap_surjective P)
    obtain ⟨g, hg⟩ := hconj _ hP'
    refine ⟨e g, fun y hy => ?_⟩
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1
      (hg (show e.symm y ∈ P.map e.symm.toMonoidHom from ⟨y, hy, rfl⟩))
    refine Subgroup.mem_map.2 ⟨e t, Subgroup.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩
    change e g * e t * (e g)⁻¹ = y
    rw [← map_inv, ← map_mul, ← map_mul]
    change e (g * t * g⁻¹) = y
    have : g * t * g⁻¹ = e.symm y := hty
    rw [this]
    simp
  · intro x hx hxp
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨t, hE t ht ?_, rfl⟩
    apply e.injective
    rw [map_pow, map_one]
    exact hxp
  · rw [Subgroup.card_map_of_injective e.injective, hcard]

theorem of_torsion {T : Subgroup G} (hT : IsMulCommutative T)
    (hconj : ∀ P : Subgroup G, IsPGroup p P → ∃ g : G, P ≤ T.map (MulAut.conj g).toMonoidHom)
    (hcard : Nat.card (torsionSubgroup T hT p) = p ^ m) : SylowTorus G p m :=
  ⟨⟨T, torsionSubgroup T hT p, hT, hconj, fun _ hx => hx.1, fun _ hx hxp => ⟨hx, hxp⟩,
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (setLike_mul_comm a.2.1 b.2.1),
      fun _ hx => hx.2⟩, hcard⟩⟩

open scoped Pointwise in
theorem of_sylow_le [Finite G] [Fact p.Prime] {T : Subgroup G} (hT : IsMulCommutative T)
    (S : Sylow p G) (hST : (S : Subgroup G) ≤ T)
    (hcard : Nat.card (torsionSubgroup T hT p) = p ^ m) : SylowTorus G p m := by
  refine of_torsion hT (fun P hP => ?_) hcard
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨g, hPQ.trans ?_⟩
  rw [← hg]
  intro x hx
  change x ∈ MulAut.conj g • (S : Subgroup G) at hx
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.1 hx
  exact Subgroup.mem_map.2 ⟨s, hST hs, rfl⟩

end SylowTorus

end CFSG.LieType.SeitzGeneration
