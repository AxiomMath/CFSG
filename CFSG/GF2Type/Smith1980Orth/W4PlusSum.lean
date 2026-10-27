module

public import CFSG.GF2Type.Smith1980Orth.W4PlusInv
public import CFSG.LargeExtraspecial.FS77Orth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O}

@[expose] def IsSum2 (D : S2Data S M1) (y : S.Qt) : Prop :=
  ∃ p ∈ D.orbitMbar, ∃ p' ∈ D.orbitMbar, y = p + p'

theorem isSum2_apply (D : S2Data S M1) {m : S.O} (hm : m ∈ S.Mbar) (y : S.Qt) :
    D.IsSum2 ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) y) ↔ D.IsSum2 y := by
  have key : ∀ {n : S.O}, n ∈ S.Mbar → ∀ z : S.Qt, D.IsSum2 z →
      D.IsSum2 ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) z) := by
    rintro n hn z ⟨p, hp, p', hp', rfl⟩
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨x', hx', rfl⟩ := hp'
    refine ⟨_, ⟨n * x, mul_mem hn hx, rfl⟩, _, ⟨n * x', mul_mem hn hx', rfl⟩, ?_⟩
    rw [map_add, coe_mul_apply, coe_mul_apply]
  constructor
  · intro h
    have h' := key (inv_mem hm) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) y) h
    rwa [inv_apply_apply_O] at h'
  · exact key hm y

theorem isSum2_coord_iff (D : S2Data S M1) {u v : Vt S D.g D.t}
    (h2 : finrank (ZMod 2) (D.span2 (D.coord (u, v))) = 2) (hβ : polar D.QV u v = 0) :
    D.IsSum2 (D.coord (u, v)) ↔ ∀ w ∈ D.span2 (D.coord (u, v)), D.QV w = 0 := by
  have h2' : finrank (ZMod 2) (Submodule.span (ZMod 2) {u, v}) = 2 := by
    rw [D.span2_coord] at h2
    exact h2
  have hli : LinearIndependent (ZMod 2) ![u, v] := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin,
      show Set.range ![u, v] = ({u, v} : Set (Vt S D.g D.t)) by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.singleton_union, Set.pair_comm],
      Set.finrank]
    exact h2'.symm
  obtain ⟨hu0, hv0, huv⟩ := OrthoF2.linearIndependent_pair_iff.mp hli
  constructor
  · rintro ⟨p, hp, p', hp', hpp⟩
    obtain ⟨s, hs0, hsQ, hsp⟩ := D.mem_orbitMbar_iff_coord.mp hp
    obtain ⟨t, ht0, htQ, htp⟩ := D.mem_orbitMbar_iff_coord.mp hp'
    rcases hsp with hsp | hsp | hsp <;> rcases htp with htp | htp | htp
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (s + t, 0) := by simpa using D.coord.injective hpp
      exact absurd (Prod.mk.inj h).2 hv0
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (s, t) := by simpa using D.coord.injective hpp
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hβ ⊢
      rw [D.span2_coord]
      exact fun w hw => OrthoF2.map_eq_zero_of_mem_span_pair hsQ htQ hβ hw
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (s + t, t) := by simpa using D.coord.injective hpp
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hβ ⊢
      have hst : polar D.QV s t = 0 := by
        have h' := hβ
        rwa [polar_add_left, polar_self_eq_zero, add_zero] at h'
      have hu : D.QV (s + t) = 0 := by
        rw [map_add_eq, hsQ, htQ, hst]
        decide
      rw [D.span2_coord]
      exact fun w hw => OrthoF2.map_eq_zero_of_mem_span_pair hu htQ hβ hw
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (t, s) := by simpa using D.coord.injective hpp
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hβ ⊢
      rw [D.span2_coord]
      exact fun w hw => OrthoF2.map_eq_zero_of_mem_span_pair htQ hsQ hβ hw
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (0, s + t) := by simpa using D.coord.injective hpp
      exact absurd (Prod.mk.inj h).1 hu0
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (t, s + t) := by simpa using D.coord.injective hpp
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hβ ⊢
      have hst : polar D.QV s t = 0 := by
        have h' := hβ
        rw [polar_add_right, polar_self_eq_zero, add_zero] at h'
        rwa [polar_comm] at h'
      have hv : D.QV (s + t) = 0 := by
        rw [map_add_eq, hsQ, htQ, hst]
        decide
      rw [D.span2_coord]
      exact fun w hw => OrthoF2.map_eq_zero_of_mem_span_pair htQ hv hβ hw
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (s + t, s) := by simpa using D.coord.injective hpp
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hβ ⊢
      have hst : polar D.QV s t = 0 := by
        have h' := hβ
        rw [polar_add_left, polar_self_eq_zero, zero_add] at h'
        rwa [polar_comm] at h'
      have hu : D.QV (s + t) = 0 := by
        rw [map_add_eq, hsQ, htQ, hst]
        decide
      rw [D.span2_coord]
      exact fun w hw => OrthoF2.map_eq_zero_of_mem_span_pair hu hsQ hβ hw
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (s, s + t) := by simpa using D.coord.injective hpp
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hβ ⊢
      have hst : polar D.QV s t = 0 := by
        have h' := hβ
        rwa [polar_add_right, polar_self_eq_zero, zero_add] at h'
      have hv : D.QV (s + t) = 0 := by
        rw [map_add_eq, hsQ, htQ, hst]
        decide
      rw [D.span2_coord]
      exact fun w hw => OrthoF2.map_eq_zero_of_mem_span_pair hsQ hv hβ hw
    ·
      rw [hsp, htp, ← map_add] at hpp
      have h : (u, v) = (s + t, s + t) := by simpa using D.coord.injective hpp
      exact absurd ((Prod.mk.inj h).1.trans ((Prod.mk.inj h).2).symm) huv
  · intro h
    rw [D.span2_coord] at h
    have huQ : D.QV u = 0 := h u (Submodule.subset_span (by simp))
    have hvQ : D.QV v = 0 := h v (Submodule.subset_span (by simp))
    refine ⟨D.coord (u, 0), D.mem_orbitMbar_iff_coord.mpr ⟨u, hu0, huQ, Or.inl rfl⟩,
      D.coord (0, v), D.mem_orbitMbar_iff_coord.mpr ⟨v, hv0, hvQ, Or.inr (Or.inl rfl)⟩, ?_⟩
    rw [D.coord_apply, D.coord_apply_zero_right, D.coord_apply_zero_left]

theorem isSum2_of_finrank_one (D : S2Data S M1) {y : S.Qt}
    (h1 : finrank (ZMod 2) (D.span2 y) = 1) (hw : ∃ w ∈ D.span2 y, D.QV w ≠ 0) :
    D.IsSum2 y := by
  obtain ⟨w, hwmem, hwQ⟩ := hw
  have hw1 : D.QV w = 1 := OrthoF2.zmod2_eq_one_of_ne_zero hwQ
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw1
    exact zero_ne_one hw1
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S D.g D.t) := by
    rw [D.finrank_Vt]
    have := D.four_le
    omega
  obtain ⟨σ, hσQ, hσw⟩ := CFSG.LargeExtraspecial.FS77.Orth.exists_singular_polar_eq_one
    D.QV_nondegenerate h3 hw0
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hσw
    exact zero_ne_one hσw
  have hwσQ : D.QV (w + σ) = 0 := by
    rw [map_add_eq, hw1, hσQ, hσw]
    decide
  have hwσ0 : w + σ ≠ 0 := by
    intro h0
    have hwσ : w = σ := by
      rw [eq_neg_of_add_eq_zero_right h0, ZModModule.neg_eq_self]
    rw [hwσ, hσQ] at hw1
    exact zero_ne_one hw1
  have hsum : σ + (w + σ) = w := by
    rw [add_comm (w : Vt S D.g D.t) σ, ← add_assoc, OrthoF2.vec_add_self, zero_add]
  obtain ⟨⟨u, v⟩, rfl⟩ := D.coord.surjective y
  have h1' : finrank (ZMod 2) (Submodule.span (ZMod 2) {u, v}) = 1 := by
    rw [D.span2_coord] at h1
    exact h1
  have hspan : D.span2 (D.coord (u, v)) = Submodule.span (ZMod 2) {w} := by
    rw [D.span2_coord]
    have hwmem' : w ∈ Submodule.span (ZMod 2) {u, v} := by
      rwa [D.span2_coord] at hwmem
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hwmem'
    · rw [finrank_span_singleton hw0, h1']
  have hu_mem : u ∈ Submodule.span (ZMod 2) {w} := by
    rw [← hspan, D.span2_coord]
    exact Submodule.subset_span (by simp)
  have hv_mem : v ∈ Submodule.span (ZMod 2) {w} := by
    rw [← hspan, D.span2_coord]
    exact Submodule.subset_span (by simp)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu_mem
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv_mem
  rcases OrthoF2.zmod2_eq_zero_or_eq_one a with rfl | rfl
  · rcases OrthoF2.zmod2_eq_zero_or_eq_one b with rfl | rfl
    ·
      exfalso
      rw [zero_smul] at h1'
      have h0 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({(0 : Vt S D.g D.t), 0} : Set _)) = 0 := by
        rw [Set.pair_eq_singleton, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      omega
    ·
      simp only [zero_smul, one_smul]
      refine ⟨D.coord (0, σ),
        D.mem_orbitMbar_iff_coord.mpr ⟨σ, hσ0, hσQ, Or.inr (Or.inl rfl)⟩,
        D.coord (0, w + σ),
        D.mem_orbitMbar_iff_coord.mpr ⟨w + σ, hwσ0, hwσQ, Or.inr (Or.inl rfl)⟩, ?_⟩
      have hp : ((0 : Vt S D.g D.t), σ) + (0, w + σ) = ((0 : Vt S D.g D.t), w) := by
        simp only [Prod.mk_add_mk, zero_add]
        rw [hsum]
      rw [← map_add, hp]
  · rcases OrthoF2.zmod2_eq_zero_or_eq_one b with rfl | rfl
    ·
      simp only [zero_smul, one_smul]
      refine ⟨D.coord (σ, 0),
        D.mem_orbitMbar_iff_coord.mpr ⟨σ, hσ0, hσQ, Or.inl rfl⟩,
        D.coord (w + σ, 0),
        D.mem_orbitMbar_iff_coord.mpr ⟨w + σ, hwσ0, hwσQ, Or.inl rfl⟩, ?_⟩
      have hp : ((σ, 0) + (w + σ, 0) : Vt S D.g D.t × Vt S D.g D.t) = (w, 0) := by
        simp only [Prod.mk_add_mk, add_zero]
        rw [hsum]
      rw [← map_add, hp]
    ·
      simp only [one_smul]
      refine ⟨D.coord (σ, σ),
        D.mem_orbitMbar_iff_coord.mpr ⟨σ, hσ0, hσQ, Or.inr (Or.inr rfl)⟩,
        D.coord (w + σ, w + σ),
        D.mem_orbitMbar_iff_coord.mpr ⟨w + σ, hwσ0, hwσQ, Or.inr (Or.inr rfl)⟩, ?_⟩
      have hp : ((σ, σ) + (w + σ, w + σ) : Vt S D.g D.t × Vt S D.g D.t) = (w, w) := by
        simp only [Prod.mk_add_mk]
        rw [hsum]
      rw [← map_add, hp]

end S2Data

end CFSG.GF2Type.Smith1980Orth
