module

public import CFSG.GH74.Uniqueness.SU.SU8Setup

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8.Setup

namespace Burn

variable {G : Type} [Group G]

theorem sylowIn_of_le {X C P : Subgroup G} (hP : IsSylowIn X P) (hPC : P ≤ C) (hCX : C ≤ X) :
    IsSylowIn C P := by
  refine ⟨hPC, hP.2.1, ?_⟩
  have h := hP.2.2
  rw [← Subgroup.relIndex_mul_relIndex P C X hPC hCX] at h
  exact (Nat.odd_mul.mp h).1

@[expose] noncomputable def sylowOf {C P : Subgroup G} (hP : IsSylowIn C P) : Sylow 2 ↥C :=
  (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).toSylow (by
    have h1 : Odd (P.relIndex C) := hP.2.2
    intro h2
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2))

theorem coe_sylowOf {C P : Subgroup G} (hP : IsSylowIn C P) :
    (sylowOf hP : Subgroup ↥C) = P.subgroupOf C := rfl

theorem sylowIn_conj [Finite G] {P : Subgroup G} (hP : IsSylowIn ⊤ P) (g : G) :
    IsSylowIn ⊤ (P.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hP.2.1.map _
  · have h := hP.2.2
    rw [Subgroup.relIndex_top_right] at h ⊢
    rw [Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).bijective]
    exact h

theorem exists_normalizer_conj_of_central [Finite G] {S : Subgroup G} (hS : IsSylowIn ⊤ S)
    {a b g : G} (ha : ∀ s ∈ S, s * a = a * s) (hb : ∀ s ∈ S, s * b = b * s)
    (hab : g * a * g⁻¹ = b) : ∃ n ∈ normalizer (S : Set G), n * a * n⁻¹ = b := by
  set C : Subgroup G := centralizer ({b} : Set G) with hC
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_iff.mpr (fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]; exact (hb s hs).symm)
  have hS2 := sylowIn_conj hS g
  have hS2C : S.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    rw [Set.mem_singleton_iff.mp hy, ← hab]
    show g * a * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * s * g⁻¹) = g * (a * s) * g⁻¹ := by group
      _ = g * (s * a) * g⁻¹ := by rw [ha s hs]
      _ = g * s * g⁻¹ * (g * a * g⁻¹) := by group
  have hP1 : IsSylowIn C S := sylowIn_of_le hS hSC le_top
  have hP2 : IsSylowIn C (S.map (MulAut.conj g).toMonoidHom) := sylowIn_of_le hS2 hS2C le_top
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) (sylowOf hP1) (sylowOf hP2)
  have hmem : ∀ s ∈ S, (c : G)⁻¹ * (g * s * g⁻¹) * (c : G) ∈ S := by
    intro s hs
    have h1 : (⟨g * s * g⁻¹, hS2C ⟨s, hs, rfl⟩⟩ : ↥C) ∈ (sylowOf hP2 : Subgroup ↥C) :=
      Subgroup.mem_subgroupOf.mpr ⟨s, hs, rfl⟩
    rw [← hc, mem_sylow_smul_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨(c : G)⁻¹ * g, mem_normalizer_of_conj_le (fun s hs => ?_), ?_⟩
  · have := hmem s hs
    simpa [mul_assoc] using this
  · have hcb : (c : G) * b = b * (c : G) :=
      (Subgroup.mem_centralizer_iff.mp c.2 b (Set.mem_singleton b)).symm
    calc (c : G)⁻¹ * g * a * ((c : G)⁻¹ * g)⁻¹ = (c : G)⁻¹ * (g * a * g⁻¹) * (c : G) := by group
      _ = b := by
        rw [hab]
        calc (c : G)⁻¹ * b * (c : G) = (c : G)⁻¹ * ((c : G) * b) := by rw [hcb]; group
          _ = b := by group

theorem mem_conjSub {g : G} {E : Subgroup G} {w : G} :
    w ∈ conjSub g E ↔ ∃ e ∈ E, g * e * g⁻¹ = w := by
  unfold conjSub
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem card_subtype_ne_one {α : Type} [Group α] [Finite α] :
    Nat.card {q : α // q ≠ 1} = Nat.card α - 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h1 := Fintype.card_subtype_compl (fun q : α => q = 1)
  have h2 : Fintype.card {q : α // q = 1} = 1 := Fintype.card_subtype_eq (1 : α)
  rw [h2] at h1
  exact h1

theorem card_le_of_disjoint_conj [Finite G] {S Q : Subgroup G} {I : Type} [Finite I] (x : I → G)
    (hx : ∀ i, x i ∈ normalizer (S : Set G)) (hQS : Q ≤ S)
    (hdisj : ∀ i j, i ≠ j → ∀ w ∈ conjSub (x i) Q, w ∈ conjSub (x j) Q → w = 1) :
    Nat.card I * (Nat.card Q - 1) ≤ Nat.card S - 1 := by
  classical
  have hmem : ∀ (i : I) (q : ↥Q), x i * (q : G) * (x i)⁻¹ ∈ S := fun i q =>
    (Subgroup.mem_normalizer_iff.mp (hx i) q).mp (hQS q.2)
  let f : I × {q : ↥Q // q ≠ 1} → {s : ↥S // s ≠ 1} := fun p =>
    ⟨⟨x p.1 * (p.2.1 : G) * (x p.1)⁻¹, hmem p.1 p.2.1⟩, by
      intro h
      apply p.2.2
      have h1 : x p.1 * (p.2.1 : G) * (x p.1)⁻¹ = 1 := congrArg Subtype.val h
      have h2 : (p.2.1 : G) = 1 := by
        calc (p.2.1 : G) = (x p.1)⁻¹ * (x p.1 * (p.2.1 : G) * (x p.1)⁻¹) * x p.1 := by group
          _ = 1 := by rw [h1]; group
      exact Subtype.ext h2⟩
  have hf : Function.Injective f := by
    rintro ⟨i, q, hq⟩ ⟨j, q', hq'⟩ hij
    have hval : x i * (q : G) * (x i)⁻¹ = x j * (q' : G) * (x j)⁻¹ := by
      have := congrArg (fun s : {s : ↥S // s ≠ 1} => ((s.1 : ↥S) : G)) hij
      simpa [f] using this
    by_cases hi : i = j
    · subst hi
      have : (q : G) = q' := mul_left_cancel (mul_right_cancel hval)
      have hqq : q = q' := Subtype.ext this
      subst hqq
      rfl
    · exfalso
      have h1 := hdisj i j hi (x i * (q : G) * (x i)⁻¹)
        (mem_conjSub.mpr ⟨q, q.2, rfl⟩) (mem_conjSub.mpr ⟨q', q'.2, hval.symm⟩)
      apply hq
      apply Subtype.ext
      have h2 : (q : G) = 1 := by
        calc (q : G) = (x i)⁻¹ * (x i * (q : G) * (x i)⁻¹) * x i := by group
          _ = 1 := by rw [h1]; group
      exact h2
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_subtype_ne_one, card_subtype_ne_one] at hcard
  exact hcard

end Burn

end CFSG.GH74.Uniqueness.SU.SU8
