module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def SylowIn (p : ℕ) (P C : Subgroup G) : Prop :=
  P ≤ C ∧ IsPGroup p ↥P ∧ ¬ p ∣ P.relIndex C

namespace SylowIn

variable {p : ℕ} {P Q C : Subgroup G}

theorem le (h : SylowIn p P C) : P ≤ C := h.1

theorem isPGroup (h : SylowIn p P C) : IsPGroup p ↥P := h.2.1

theorem isPGroup_subgroupOf (h : SylowIn p P C) : IsPGroup p ↥(P.subgroupOf C) :=
  h.2.1.of_equiv (subgroupOfEquivOfLe h.1).symm

section Prime

variable [hp : Fact p.Prime]

@[expose] noncomputable def toSylow (h : SylowIn p P C) : Sylow p ↥C :=
  h.isPGroup_subgroupOf.toSylow h.2.2

theorem of_sylow [Finite G] (S : Sylow p ↥C) : SylowIn p ((S : Subgroup ↥C).map C.subtype) C := by
  refine ⟨map_subtype_le _, S.isPGroup'.map C.subtype, ?_⟩
  have : ((S : Subgroup ↥C).map C.subtype).subgroupOf C = S := by
    rw [← comap_subtype]
    exact comap_map_eq_self_of_injective C.subtype_injective _
  rw [relIndex, this]
  exact S.not_dvd_index

theorem exists_ge [Finite G] (hQC : Q ≤ C) (hQ : IsPGroup p ↥Q) :
    ∃ P, SylowIn p P C ∧ Q ≤ P := by
  have hQ' : IsPGroup p ↥(Q.subgroupOf C) := hQ.of_equiv (subgroupOfEquivOfLe hQC).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup ↥C).map C.subtype, of_sylow S, ?_⟩
  intro q hq
  refine ⟨⟨q, hQC hq⟩, hS ?_, rfl⟩
  exact hq

theorem conj [Finite G] (h : SylowIn p P C) (h' : SylowIn p Q C) :
    ∃ c ∈ C, ∀ g : G, g ∈ Q ↔ c⁻¹ * g * c ∈ P := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C h.toSylow h'.toSylow
  have hsub : Q.subgroupOf C = MulAut.conj c • P.subgroupOf C := by
    have := congrArg (fun S : Sylow p ↥C => (S : Subgroup ↥C)) hc
    exact this.symm
  have key : ∀ g : ↥C, g ∈ Q.subgroupOf C ↔ c⁻¹ * g * c ∈ P.subgroupOf C := by
    intro g
    rw [hsub, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [mul_assoc]
  refine ⟨c, c.2, fun g => ?_⟩
  constructor
  · intro hg
    exact (key ⟨g, h'.le hg⟩).1 hg
  · intro hg
    have hgC : g ∈ C := by
      have h1 : c⁻¹ * g * c ∈ C := h.le hg
      have h2 : (c : G) * (c⁻¹ * g * c) * (c : G)⁻¹ ∈ C :=
        C.mul_mem (C.mul_mem c.2 h1) (C.inv_mem c.2)
      simpa [mul_assoc] using h2
    exact (key ⟨g, hgC⟩).2 hg

end Prime

end SylowIn

@[expose] def cj (m : G) (P : Subgroup G) : Subgroup G := P.map (MulAut.conj m).toMonoidHom

theorem mem_cj {m g : G} {P : Subgroup G} : g ∈ cj m P ↔ m⁻¹ * g * m ∈ P := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro h
    exact ⟨m⁻¹ * g * m, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem card_cj (m : G) (P : Subgroup G) : Nat.card (cj m P) = Nat.card P :=
  Subgroup.card_map_of_injective (MulAut.conj m).injective

theorem cj_le {m : G} {P N : Subgroup G} (h : ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hPN : P ≤ N) :
    cj m P ≤ N := by
  rintro g hg
  obtain ⟨h1, hh, rfl⟩ := hg
  simpa [MulAut.conj_apply] using h h1 (hPN hh)

theorem sylowIn_cj {p : ℕ} [Fact p.Prime] [Finite G] {P N M : Subgroup G} (hP : SylowIn p P N)
    (hM : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) {m : G} (hm : m ∈ M) : SylowIn p (cj m P) N := by
  have hle : cj m P ≤ N := cj_le (hM m hm) hP.le
  refine ⟨hle, hP.isPGroup.map _, ?_⟩
  have h1 := relIndex_mul_card P N
  have h2 := relIndex_mul_card (cj m P) N
  rw [inf_of_le_left hP.le] at h1
  rw [inf_of_le_left hle, card_cj] at h2
  have hpos : 0 < Nat.card P := Nat.card_pos
  have : (cj m P).relIndex N = P.relIndex N := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2, h1]
  rw [this]
  exact hP.2.2

theorem sylowIn_frattini {p : ℕ} [Fact p.Prime] [Finite G] {P N M : Subgroup G}
    (hP : SylowIn p P N) (hM : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    {m : G} (hm : m ∈ M) : ∃ n ∈ N, n⁻¹ * m ∈ normalizer (P : Set G) := by
  have hP' := sylowIn_cj hP hM hm
  obtain ⟨c, hcN, hc⟩ := SylowIn.conj hP hP'
  refine ⟨c, hcN, ?_⟩
  rw [mem_normalizer_iff]
  intro x
  have := hc (m * x * m⁻¹)
  rw [mem_cj] at this
  have e1 : m⁻¹ * (m * x * m⁻¹) * m = x := by group
  have e2 : c⁻¹ * (m * x * m⁻¹) * c = (c⁻¹ * m) * x * (c⁻¹ * m)⁻¹ := by group
  rw [e1, e2] at this
  exact this

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
