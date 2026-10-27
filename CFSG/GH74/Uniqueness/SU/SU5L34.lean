module

public import CFSG.GH74.Uniqueness.SU.SU5Models
public import CFSG.GH74.Uniqueness.SU.SU5Map

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace L34Syl

@[expose] def A : Subgroup L34Syl := subOfPred (fun g => g.b = 0) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)

@[expose] def B : Subgroup L34Syl := subOfPred (fun g => g.a = 0) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)

@[expose] def U : Subgroup L34Syl := subOfPred (fun g => g.a = 0 ∧ g.b = 0) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)

theorem mem_A {g : L34Syl} : g ∈ A ↔ g.b = 0 := Iff.rfl

theorem mem_B {g : L34Syl} : g ∈ B ↔ g.a = 0 := Iff.rfl

theorem mem_U {g : L34Syl} : g ∈ U ↔ g.a = 0 ∧ g.b = 0 := Iff.rfl

theorem card_A : Nat.card A = 16 := by
  unfold A; rw [card_subOfPred]; decide +kernel

theorem card_B : Nat.card B = 16 := by
  unfold B; rw [card_subOfPred]; decide +kernel

theorem card_U : Nat.card U = 4 := by
  unfold U; rw [card_subOfPred]; decide +kernel

theorem comm_A : ∀ g h : L34Syl, g.b = 0 → h.b = 0 → g * h = h * g := by decide +kernel

theorem comm_B : ∀ g h : L34Syl, g.a = 0 → h.a = 0 → g * h = h * g := by decide +kernel

theorem sq_A : ∀ g : L34Syl, g.b = 0 → g * g = 1 := by decide +kernel

theorem sq_B : ∀ g : L34Syl, g.a = 0 → g * g = 1 := by decide +kernel

theorem isE_A : IsE 4 A := by
  refine ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => comm_A a b ha hb, fun a ha => ?_⟩, card_A⟩
  rw [pow_two]; exact sq_A a ha

theorem isE_B : IsE 4 B := by
  refine ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => comm_B a b ha hb, fun a ha => ?_⟩, card_B⟩
  rw [pow_two]; exact sq_B a ha

theorem isE_U : IsE 2 U := by
  refine ⟨isElemAbelian_iff.2 ⟨fun a ha b hb => comm_A a b ha.2 hb.2, fun a ha => ?_⟩, card_U⟩
  rw [pow_two]; exact sq_A a ha.2

theorem A_inf_B : A ⊓ B = U := by
  ext g; simp only [Subgroup.mem_inf, mem_A, mem_B, mem_U]; tauto

theorem A_ne_B : A ≠ B := by
  intro h
  have h1 : (⟨1, 0, 0⟩ : L34Syl) ∈ A := rfl
  rw [h] at h1
  have h10 : (1 : F4c) = 0 := h1
  exact absurd h10 (by decide)

theorem sq_eq_one : ∀ g : L34Syl, g * g = 1 → g.b = 0 ∨ g.a = 0 := by decide +kernel

theorem mem_A_or_B_of_sq {g : L34Syl} (h : g * g = 1) : g ∈ A ∨ g ∈ B := sq_eq_one g h

theorem central_iff : ∀ g : L34Syl, (∀ h : L34Syl, g * h = h * g) ↔ (g.a = 0 ∧ g.b = 0) := by
  decide +kernel

theorem cent_A : ∀ a g : L34Syl, a.b = 0 → a.a ≠ 0 → (g * a = a * g ↔ g.b = 0) := by
  decide +kernel

theorem cent_B : ∀ a g : L34Syl, a.a = 0 → a.b ≠ 0 → (g * a = a * g ↔ g.a = 0) := by
  decide +kernel

theorem prod_AB : ∀ g : L34Syl,
    (⟨g.a, 0, g.c + g.a * g.b⟩ : L34Syl) * ⟨0, g.b, 0⟩ = g := by decide +kernel

theorem A_sup_B : A ⊔ B = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [← prod_AB g]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (show (⟨g.a, 0, g.c + g.a * g.b⟩ : L34Syl) ∈ A from rfl))
    (Subgroup.mem_sup_right (show (⟨0, g.b, 0⟩ : L34Syl) ∈ B from rfl))

theorem Zc_top : Zc (⊤ : Subgroup L34Syl) = U := by
  ext g
  rw [mem_Zc, mem_U, ← central_iff]
  simp only [Subgroup.mem_top, true_and, true_implies]

theorem isE4_unique (E : Subgroup L34Syl) (hE : IsE 4 E) : E = A ∨ E = B := by
  have hE' := isElemAbelian_iff.1 hE.1
  have h : ∀ e ∈ E, e ∈ A ∨ e ∈ B := fun e he =>
    mem_A_or_B_of_sq (by rw [← pow_two]; exact hE'.2 e he)
  rcases le_or_le_of_subset_union h with h1 | h1
  · left; exact Subgroup.eq_of_le_of_card_ge h1 (by rw [card_A, hE.2]; norm_num)
  · right; exact Subgroup.eq_of_le_of_card_ge h1 (by rw [card_B, hE.2]; norm_num)

theorem card_le_16 (E : Subgroup L34Syl) (hE : Open.IsElemAbelian 2 E) : Nat.card E ≤ 16 := by
  have hE' := isElemAbelian_iff.1 hE
  have h : ∀ e ∈ E, e ∈ A ∨ e ∈ B := fun e he =>
    mem_A_or_B_of_sq (by rw [← pow_two]; exact hE'.2 e he)
  rcases le_or_le_of_subset_union h with h1 | h1
  · exact (Subgroup.card_le_of_le h1).trans card_A.le
  · exact (Subgroup.card_le_of_le h1).trans card_B.le

end L34Syl

section Ambient

variable {G : Type*} [Group G]

structure L34Facts (T A B : Subgroup G) : Prop where
  A_le : A ≤ T
  B_le : B ≤ T
  A_E : IsE 4 A
  B_E : IsE 4 B
  A_ne_B : A ≠ B
  unique : ∀ E : Subgroup G, E ≤ T → IsE 4 E → E = A ∨ E = B
  sup_eq : A ⊔ B = T
  inf_eq : A ⊓ B = Zc T
  Z_E : IsE 2 (Zc T)
  card_T : Nat.card T = 64
  invol : ∀ t ∈ T, t ≠ 1 → t ^ 2 = 1 → t ∈ A ∨ t ∈ B
  cent_A : ∀ a ∈ A, a ∉ B → ∀ g ∈ T, (g * a = a * g ↔ g ∈ A)
  cent_B : ∀ b ∈ B, b ∉ A → ∀ g ∈ T, (g * b = b * g ↔ g ∈ B)
  le16 : ∀ E : Subgroup G, E ≤ T → Open.IsElemAbelian 2 E → Nat.card E ≤ 16

theorem L34Facts.pRank [Finite G] {T A B : Subgroup G} (h : L34Facts T A B) :
    Open.pRank 2 T = 4 :=
  pRank_eq_of ⟨A, h.A_le, h.A_E⟩ (fun E hE hEE => by
    have := h.le16 E hE hEE
    norm_num; exact this)

@[expose] def L34Emb (T : Subgroup G) : Prop :=
  ∃ f : L34Syl →* G, Function.Injective f ∧ f.range = T

theorem isL34Type_iff_emb {T : Subgroup G} : IsL34Type T ↔ L34Emb T := by
  rw [isL34Type_iff]
  constructor
  · rintro ⟨e⟩
    refine ⟨T.subtype.comp e.symm.toMonoidHom, T.subtype_injective.comp e.symm.injective, ?_⟩
    ext g
    constructor
    · rintro ⟨m, rfl⟩; exact (e.symm m).2
    · intro hg; exact ⟨e ⟨g, hg⟩, by simp⟩
  · rintro ⟨f, hf, hrange⟩
    exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hf).symm⟩

theorem L34Syl.facts_map {f : L34Syl →* G} (hf : Function.Injective f) :
    L34Facts f.range (L34Syl.A.map f) (L34Syl.B.map f) := by
  have hrange : f.range = (⊤ : Subgroup L34Syl).map f := (Subgroup.map_top f).symm
  refine
  { A_le := Subgroup.map_le_range f _
    B_le := Subgroup.map_le_range f _
    A_E := (isE_map hf).2 L34Syl.isE_A
    B_E := (isE_map hf).2 L34Syl.isE_B
    A_ne_B := fun h => L34Syl.A_ne_B (Subgroup.map_injective hf h)
    unique := ?_
    sup_eq := ?_
    inf_eq := ?_
    Z_E := ?_
    card_T := ?_
    invol := ?_
    cent_A := ?_
    cent_B := ?_
    le16 := ?_ }
  · intro E hE hEE
    obtain ⟨X, rfl⟩ := exists_eq_map_of_le_range hE
    rcases L34Syl.isE4_unique X ((isE_map hf).1 hEE) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [← Subgroup.map_sup, L34Syl.A_sup_B, Subgroup.map_top]
  · rw [← Subgroup.map_inf_eq _ _ f hf, L34Syl.A_inf_B, hrange, Zc_map hf, L34Syl.Zc_top]
  · rw [hrange, Zc_map hf, L34Syl.Zc_top]; exact (isE_map hf).2 L34Syl.isE_U
  · rw [card_range_of_injective hf]; exact card_L34Syl
  · rintro t ⟨m, rfl⟩ h1 h2
    have hm : m * m = 1 := hf (by rw [map_mul, map_one, ← pow_two]; exact h2)
    rcases L34Syl.mem_A_or_B_of_sq hm with h | h
    · exact Or.inl (Subgroup.mem_map_of_mem f h)
    · exact Or.inr (Subgroup.mem_map_of_mem f h)
  · intro a ha hnb g hg
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨k, rfl⟩ := hg
    have hm' : m.a ≠ 0 := fun h0 => hnb (Subgroup.mem_map_of_mem f (L34Syl.mem_B.2 h0))
    rw [← map_mul, ← map_mul, hf.eq_iff, Subgroup.mem_map_iff_mem hf]
    exact L34Syl.cent_A m k hm hm'
  · intro b hb hna g hg
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨k, rfl⟩ := hg
    have hm' : m.b ≠ 0 := fun h0 => hna (Subgroup.mem_map_of_mem f (L34Syl.mem_A.2 h0))
    rw [← map_mul, ← map_mul, hf.eq_iff, Subgroup.mem_map_iff_mem hf]
    exact L34Syl.cent_B m k hm hm'
  · intro E hE hEE
    obtain ⟨X, rfl⟩ := exists_eq_map_of_le_range hE
    rw [Subgroup.card_map_of_injective hf]
    exact L34Syl.card_le_16 X ((isElemAbelian_map_iff hf).1 hEE)

theorem L34Emb.facts {T : Subgroup G} (h : L34Emb T) : ∃ A B : Subgroup G, L34Facts T A B := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨_, _, L34Syl.facts_map hf⟩

theorem IsL34Type.facts {T : Subgroup G} (h : IsL34Type T) : ∃ A B : Subgroup G, L34Facts T A B :=
  (isL34Type_iff_emb.1 h).facts

end Ambient

end CFSG.GH74.Uniqueness.SU.SU5
