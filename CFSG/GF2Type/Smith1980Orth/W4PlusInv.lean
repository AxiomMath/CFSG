module

public import CFSG.GF2Type.Smith1980Orth.S2Coord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

@[expose] noncomputable def span2 (y : S.Qt) : Submodule (ZMod 2) (Vt S D.g D.t) :=
  Submodule.span (ZMod 2) {(D.coord.symm y).1, (D.coord.symm y).2}

theorem span2_coord (u v : Vt S D.g D.t) :
    D.span2 (D.coord (u, v)) = Submodule.span (ZMod 2) {u, v} := by
  simp [span2]

private theorem span2_pure {s : Vt S D.g D.t} {y : S.Qt}
    (hy : y = D.coord (s, 0) ∨ y = D.coord (0, s) ∨ y = D.coord (s, s)) :
    D.span2 y = Submodule.span (ZMod 2) {s} := by
  rcases hy with rfl | rfl | rfl
  · rw [D.span2_coord, Set.pair_comm, Submodule.span_insert_zero]
  · rw [D.span2_coord, Submodule.span_insert_zero]
  · rw [D.span2_coord, Set.pair_eq_singleton]

theorem span2_cl_of_isConj {y : G} (hyQ : y ∈ S.QG) (hyz : y ≠ S.z) (hy : IsConj S.z y) :
    finrank (ZMod 2) (D.span2 (S.cl y)) = 1 ∧ ∀ w ∈ D.span2 (S.cl y), D.QV w = 0 := by
  obtain ⟨s, hs, hsQ, h⟩ := (D.isConj_z_iff_coord hyQ hyz).mp hy
  rw [D.span2_pure h]
  refine ⟨finrank_span_singleton hs, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [QuadraticMap.map_smul, hsQ, smul_zero]

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem three_le_finrank_of_card [Module.Finite (ZMod 2) V] {U : Submodule (ZMod 2) V}
    (h8 : 8 ≤ Nat.card U) : 3 ≤ finrank (ZMod 2) U := by
  by_contra h
  have h2 : finrank (ZMod 2) U ≤ 2 := by omega
  have hc : Nat.card U = 2 ^ finrank (ZMod 2) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h4 : 2 ^ finrank (ZMod 2) U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
  omega

private theorem finrank_span_pair_le (x y : V) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {x, y}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ZMod 2) ({x, y} : Finset V)
  rw [Set.finrank, Finset.coe_pair] at h
  exact h.trans Finset.card_le_two

private theorem exists_mem_not_mem_of_finrank_lt [Module.Finite (ZMod 2) V]
    {U P : Submodule (ZMod 2) V} (h : finrank (ZMod 2) P < finrank (ZMod 2) U) :
    ∃ y ∈ U, y ∉ P := by
  by_contra hcon
  push Not at hcon
  exact absurd (Submodule.finrank_mono (fun y hy => hcon y hy)) (not_le.mpr h)

private theorem linearIndependent_pair_comb {a d : V} (h : LinearIndependent (ZMod 2) ![a, d])
    (δ₁ δ₂ e₁ e₂ : ZMod 2) (hdet : e₁ * δ₂ + e₂ * δ₁ = 1) :
    LinearIndependent (ZMod 2) ![δ₁ • d + e₁ • a, δ₂ • d + e₂ • a] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have h1 : (s * e₁ + t * e₂) • a + (s * δ₁ + t * δ₂) • d = 0 := by
    rw [← hst]
    module
  obtain ⟨h2, h3⟩ := h _ _ h1
  have key : ∀ s t e₁ e₂ δ₁ δ₂ : ZMod 2, e₁ * δ₂ + e₂ * δ₁ = 1 → s * e₁ + t * e₂ = 0 →
      s * δ₁ + t * δ₂ = 0 → s = 0 ∧ t = 0 := by decide
  exact key s t e₁ e₂ δ₁ δ₂ hdet h2 h3

end Linear

private theorem resC_eq_eichler {c : S.O} (hc : c ∈ D.Cbar) {d : Vt S D.g D.t}
    (hcd : ∀ v : Vt S D.g D.t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((eichler D.QV (aV D.good.ht) d v : Vt S D.g D.t) : S.Qt)) :
    D.resC ⟨c, hc⟩ = eichler D.QV (aV D.good.ht) d :=
  LinearEquiv.ext fun v => Subtype.ext (hcd v)

private theorem exists_coord_of_mem_commSpace_Cbar {c : S.O} (hc : c ∈ D.Cbar) {x : S.Qt}
    (hx : x ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ u v : Vt S D.g D.t, x = D.coord (D.resC ⟨c, hc⟩ u - u, D.resC ⟨c, hc⟩ v - v) := by
  obtain ⟨w, hw⟩ := mem_commSpace.mp hx
  obtain ⟨⟨u, v⟩, rfl⟩ := D.coord.surjective w
  refine ⟨u, v, ?_⟩
  rw [← hw, D.Cbar_apply_coord ⟨c, hc⟩, ← map_sub D.coord]
  rfl

theorem span2_le_of_mem_commSpace_eichler {c : S.O} (hc : c ∈ D.Cbar) {d : Vt S D.g D.t}
    (hcd : ∀ v : Vt S D.g D.t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((eichler D.QV (aV D.good.ht) d v : Vt S D.g D.t) : S.Qt)) {y : S.Qt}
    (hy : y ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    D.span2 y ≤ Submodule.span (ZMod 2) {aV D.good.ht, d} := by
  obtain ⟨u, v, rfl⟩ := D.exists_coord_of_mem_commSpace_Cbar hc hy
  rw [D.span2_coord, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩ <;>
    rw [D.resC_eq_eichler hc hcd] <;>
    exact commSpace_eichler_le (aV D.good.ht) d (sub_mem_commSpace _ _)

theorem exists_span2_of_typeC {c : S.O} (hc : c ∈ D.Cbar) {d : Vt S D.g D.t}
    (hd : polar D.QV (aV D.good.ht) d = 0) (hdQ : D.QV d = 1)
    (hcd : ∀ v : Vt S D.g D.t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((eichler D.QV (aV D.good.ht) d v : Vt S D.g D.t) : S.Qt))
    {U : Submodule (ZMod 2) S.Qt} (hU : U ≤ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (haU : D.coord (aV D.good.ht, 0) ∈ U)
    (hkU : ∀ y ∈ U, (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) y ∈ U) (h8 : 8 ≤ Nat.card U) :
    ∃ y₁ ∈ U, ∃ y₂ ∈ U, finrank (ZMod 2) (D.span2 y₁) = 1 ∧
      (∃ w ∈ D.span2 y₁, D.QV w ≠ 0) ∧ finrank (ZMod 2) (D.span2 y₂) = 2 := by
  set a := aV D.good.ht
  have ha0 : a ≠ 0 := aV_ne_zero D.good.H D.good.ht
  have haQ : D.QV a = 0 := D.QV_aV
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hdQ
    exact zero_ne_one hdQ
  have hda : a ≠ d := by
    rintro rfl
    rw [haQ] at hdQ
    exact zero_ne_one hdQ
  have hli : LinearIndependent (ZMod 2) ![a, d] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨ha0, hd0, hda⟩
  have hrep : ∀ y ∈ U, ∃ p q : Vt S D.g D.t, p ∈ Submodule.span (ZMod 2) {a, d} ∧
      q ∈ Submodule.span (ZMod 2) {a, d} ∧ y = D.coord (p, q) := by
    intro y hy
    have hle := D.span2_le_of_mem_commSpace_eichler hc hcd (hU hy)
    obtain ⟨u, v, rfl⟩ := D.exists_coord_of_mem_commSpace_Cbar hc (hU hy)
    rw [D.span2_coord] at hle
    exact ⟨_, _, hle (Submodule.subset_span (by simp)),
      hle (Submodule.subset_span (by simp)), rfl⟩
  have he₂ : D.coord (0, a) ∈ U := by
    have := hkU _ haU
    rwa [D.k_apply_coord, add_zero] at this
  have h3 : 3 ≤ finrank (ZMod 2) U := three_le_finrank_of_card h8
  obtain ⟨y, hyU, hyP⟩ := exists_mem_not_mem_of_finrank_lt
    (U := U) (P := Submodule.span (ZMod 2) {D.coord (a, 0), D.coord (0, a)})
    (lt_of_le_of_lt (finrank_span_pair_le _ _) (by omega))
  obtain ⟨p, q, hp, hq, rfl⟩ := hrep y hyU
  obtain ⟨α₁, δ₁, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨α₂, δ₂, rfl⟩ := Submodule.mem_span_pair.mp hq
  have hδ : ¬(δ₁ = 0 ∧ δ₂ = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hyP
    have e : D.coord (α₁ • a + (0 : ZMod 2) • d, α₂ • a + (0 : ZMod 2) • d) =
        α₁ • D.coord (a, 0) + α₂ • D.coord (0, a) := by
      rw [← map_smul, ← map_smul, ← map_add]
      refine congrArg D.coord (Prod.ext ?_ ?_) <;> simp
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hmem : ∀ e₁ e₂ : ZMod 2, D.coord (δ₁ • d + e₁ • a, δ₂ • d + e₂ • a) ∈ U := by
    intro e₁ e₂
    have e : D.coord (δ₁ • d + e₁ • a, δ₂ • d + e₂ • a) =
        D.coord (α₁ • a + δ₁ • d, α₂ • a + δ₂ • d) + (e₁ - α₁) • D.coord (a, 0) +
          (e₂ - α₂) • D.coord (0, a) := by
      rw [← map_smul, ← map_smul, ← map_add, ← map_add]
      refine congrArg D.coord (Prod.ext ?_ ?_)
      · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
        module
      · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]
        module
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ hyU (Submodule.smul_mem _ _ haU))
      (Submodule.smul_mem _ _ he₂)
  have hex : ∀ δ₁ δ₂ : ZMod 2, ¬(δ₁ = 0 ∧ δ₂ = 0) → ∃ e₁ e₂ : ZMod 2, e₁ * δ₂ + e₂ * δ₁ = 1 := by
    decide
  obtain ⟨e₁, e₂, hdet⟩ := hex δ₁ δ₂ hδ
  have hspan1 : D.span2 (D.coord (δ₁ • d, δ₂ • d)) = Submodule.span (ZMod 2) {d} := by
    rw [D.span2_coord]
    rcases OrthoF2.zmod2_eq_zero_or_eq_one δ₁ with rfl | rfl <;>
      rcases OrthoF2.zmod2_eq_zero_or_eq_one δ₂ with rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hδ
    · rw [zero_smul, one_smul, Submodule.span_insert_zero]
    · rw [one_smul, zero_smul, Set.pair_comm, Submodule.span_insert_zero]
    · rw [one_smul, Set.pair_eq_singleton]
  refine ⟨D.coord (δ₁ • d, δ₂ • d), ?_, D.coord (δ₁ • d + e₁ • a, δ₂ • d + e₂ • a),
    hmem e₁ e₂, ?_, ?_, ?_⟩
  · simpa only [zero_smul, add_zero] using hmem 0 0
  · rw [hspan1]
    exact finrank_span_singleton hd0
  · rw [hspan1]
    exact ⟨d, Submodule.mem_span_singleton_self d, by rw [hdQ]; exact one_ne_zero⟩
  · rw [D.span2_coord]
    exact OrthoF2.finrank_span_pair (linearIndependent_pair_comb hli δ₁ δ₂ e₁ e₂ hdet)

section Quad

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {a d : V} {L : V → V}

private theorem eL_apply_a (hd : polar Q a d = 0)
    (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a) : L a = 0 := by
  rw [hL, polar_self_eq_zero, hd, zero_smul, zero_smul, add_zero]

private theorem eL_apply_d (hd : polar Q a d = 0)
    (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a) : L d = 0 := by
  rw [hL, polar_comm Q d a, hd, polar_self_eq_zero, zero_smul, zero_smul, add_zero]

private theorem eL_add (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a) (x y : V) :
    L (x + y) = L x + L y := by
  rw [hL, hL, hL, polar_add_left, polar_add_left, add_smul, add_smul]
  abel

private theorem eL_eL (hd : polar Q a d = 0) (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a)
    (w : V) : L (L w) = 0 := by
  have h1 : polar Q (L w) a = 0 := by
    rw [hL w, polar_add_left, polar_smul_left, polar_smul_left, polar_comm Q d a, hd,
      polar_self_eq_zero]
    simp
  have h2 : polar Q (L w) d = 0 := by
    rw [hL w, polar_add_left, polar_smul_left, polar_smul_left, polar_self_eq_zero, hd]
    simp
  rw [hL (L w), h1, h2, zero_smul, zero_smul, add_zero]

private theorem finrank_span_pair_eL (hd : polar Q a d = 0)
    (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a) {w : V} (hLw : L w ≠ 0) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {w, L w}) = 2 := by
  refine OrthoF2.finrank_span_pair (OrthoF2.linearIndependent_pair_iff.mpr ⟨?_, hLw, ?_⟩)
  · rintro rfl
    apply hLw
    rw [hL, polar_zero_left, polar_zero_left, zero_smul, zero_smul, add_zero]
  · intro h
    apply hLw
    have := eL_eL hd hL w
    rwa [← h] at this

private theorem forall_mem_span_pair_eL_iff (haQ : Q a = 0) (hdQ : Q d = 0) (hd : polar Q a d = 0)
    (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a) (w : V) :
    (∀ x ∈ Submodule.span (ZMod 2) {w, L w}, Q x = 0) ↔ Q w = 0 := by
  constructor
  · intro h
    exact h w (Submodule.subset_span (by simp))
  · intro hw
    have hLQ : Q (L w) = 0 :=
      OrthoF2.map_eq_zero_of_mem_span_pair hdQ haQ (by rw [polar_comm]; exact hd)
        (Submodule.mem_span_pair.mpr ⟨polar Q w a, polar Q w d, (hL w).symm⟩)
    have hpw : polar Q w (L w) = 0 := by
      rw [hL w, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul,
        mul_comm (polar Q w d), OrthoF2.zmod2_add_self]
    intro x hx
    exact OrthoF2.map_eq_zero_of_mem_span_pair hw hLQ hpw hx

private theorem exists_pair_of_finrank_ge_three [FiniteDimensional (ZMod 2) V]
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) (haQ : Q a = 0)
    (hdQ : Q d = 0) (hd : polar Q a d = 0) (hli : LinearIndependent (ZMod 2) ![a, d])
    (hL : ∀ w, L w = polar Q w a • d + polar Q w d • a)
    {W : Submodule (ZMod 2) V} (haW : a ∈ W) (hW : 3 ≤ finrank (ZMod 2) W) :
    (∃ w ∈ W, L w ≠ 0 ∧ Q w = 0) ∧ ∃ w ∈ W, L w ≠ 0 ∧ Q w ≠ 0 := by
  have ha0 : a ≠ 0 := (OrthoF2.linearIndependent_pair_iff.mp hli).1
  have hM : ∀ w₀ ∈ W, ∀ e ∈ W, L e = 0 → Q e = 0 → polar Q w₀ e = 1 → L w₀ ≠ 0 →
      (∃ w ∈ W, L w ≠ 0 ∧ Q w = 0) ∧ ∃ w ∈ W, L w ≠ 0 ∧ Q w ≠ 0 := by
    intro w₀ hw₀ e he hLe hQe hpe hLw₀
    have hw' : w₀ + e ∈ W := W.add_mem hw₀ he
    have hLw' : L (w₀ + e) ≠ 0 := by
      rw [eL_add hL, hLe, add_zero]
      exact hLw₀
    have hQw' : Q (w₀ + e) = Q w₀ + 1 := by rw [map_add_eq, hQe, hpe, add_zero]
    by_cases h0 : Q w₀ = 0
    · refine ⟨⟨w₀, hw₀, hLw₀, h0⟩, w₀ + e, hw', hLw', ?_⟩
      rw [hQw', h0, zero_add]
      exact one_ne_zero
    · refine ⟨⟨w₀ + e, hw', hLw', ?_⟩, w₀, hw₀, hLw₀, h0⟩
      rw [hQw', OrthoF2.zmod2_eq_one_of_ne_zero h0]
      decide
  by_cases hA : ∃ w ∈ W, polar Q w a ≠ 0
  · obtain ⟨w, hwW, hwa⟩ := hA
    refine hM w hwW a haW (eL_apply_a hd hL) haQ (OrthoF2.zmod2_eq_one_of_ne_zero hwa) ?_
    intro h0
    rw [hL, OrthoF2.zmod2_eq_one_of_ne_zero hwa, one_smul] at h0
    have h1 : polar Q w d • a + (1 : ZMod 2) • d = 0 := by
      rw [one_smul, add_comm]
      exact h0
    exact one_ne_zero (LinearIndependent.pair_iff.mp hli _ _ h1).2
  · push Not at hA
    have hle : (ZMod 2) ∙ a ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [polarBilin_apply_apply]
      exact hA n hn
    have hfin : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal Q.polarBilin W) ≤
        finrank (ZMod 2) ((ZMod 2) ∙ a) := by
      rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton ha0]
      omega
    have hperp : LinearMap.BilinForm.orthogonal Q.polarBilin ((ZMod 2) ∙ a) = W := by
      rw [Submodule.eq_of_le_of_finrank_le hle hfin,
        LinearMap.BilinForm.orthogonal_orthogonal hQ (OrthoF2.isRefl_polarBilin Q)]
    obtain ⟨x, hxd, hxa⟩ :=
      OrthoF2.exists_polar_eq_one_polar_eq_zero hQ (OrthoF2.linearIndependent_pair_symm hli)
    have hxW : x ∈ W := by
      rw [← hperp, OrthoF2.mem_orthogonal_span_singleton_iff, polar_comm]
      exact hxa
    have hdW : d ∈ W := by
      rw [← hperp, OrthoF2.mem_orthogonal_span_singleton_iff]
      exact hd
    refine hM x hxW d hdW (eL_apply_d hd hL) hdQ hxd ?_
    rw [hL, hxd, hxa, zero_smul, one_smul, zero_add]
    exact ha0

end Quad

private theorem t_mul_apply_sub_coord {c : S.O} (hc : c ∈ D.Cbar) (u v : Vt S D.g D.t) :
    ((D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, v)) - D.coord (u, v) =
      D.coord (D.resC ⟨c, hc⟩ u + D.resC ⟨c, hc⟩ v - u, D.resC ⟨c, hc⟩ v - v) := by
  rw [coe_mul_apply, D.Cbar_apply_coord ⟨c, hc⟩, D.t_apply_coord, ← map_sub D.coord]
  rfl

theorem exists_span2_of_t_mul_typeA (hw : S.width = 4) {c : S.O} (hc : c ∈ D.Cbar)
    {d : Vt S D.g D.t} (hd : polar D.QV (aV D.good.ht) d = 0) (hdQ : D.QV d = 0)
    (hdn : d ∉ (ZMod 2) ∙ aV D.good.ht)
    (hcd : ∀ v : Vt S D.g D.t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((eichler D.QV (aV D.good.ht) d v : Vt S D.g D.t) : S.Qt))
    {U : Submodule (ZMod 2) S.Qt} (hU : U ≤ commSpace ((D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (haU : D.coord (aV D.good.ht, 0) ∈ U) (h8 : 8 ≤ Nat.card U) :
    ∃ y₁ ∈ U, ∃ y₂ ∈ U, finrank (ZMod 2) (D.span2 y₁) = 2 ∧
      finrank (ZMod 2) (D.span2 y₂) = 2 ∧ (∀ w ∈ D.span2 y₁, D.QV w = 0) ∧
      ∃ w ∈ D.span2 y₂, D.QV w ≠ 0 := by
  set a := aV D.good.ht
  have ha0 : a ≠ 0 := aV_ne_zero D.good.H D.good.ht
  have haQ : D.QV a = 0 := D.QV_aV
  have hd0 : d ≠ 0 := fun h => hdn (h ▸ Submodule.zero_mem _)
  have hda : a ≠ d := fun h => hdn (h ▸ Submodule.mem_span_singleton_self a)
  have hli : LinearIndependent (ZMod 2) ![a, d] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨ha0, hd0, hda⟩
  have hγ := D.resC_eq_eichler hc hcd
  have hγγ : ∀ x, D.resC ⟨c, hc⟩ (D.resC ⟨c, hc⟩ x) = x := by
    have h : D.resC ⟨c, hc⟩ * D.resC ⟨c, hc⟩ = 1 := by
      rw [hγ]
      exact eichler_mul_self hd
    exact fun x => apply_apply_of_mul_self h x
  have hL : ∀ w, D.resC ⟨c, hc⟩ w - w = polar D.QV w a • d + polar D.QV w d • a := by
    intro w
    rw [hγ, eichler_apply_zmod2 D.QV_aV hd, hdQ, zero_mul, add_zero]
    abel
  have hrep : ∀ y ∈ U, ∃ w, y = D.coord (w, D.resC ⟨c, hc⟩ w - w) := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_commSpace.mp (hU hy)
    obtain ⟨⟨u, v⟩, rfl⟩ := D.coord.surjective x
    rw [D.t_mul_apply_sub_coord hc] at hx
    refine ⟨D.resC ⟨c, hc⟩ u + D.resC ⟨c, hc⟩ v - u, ?_⟩
    rw [← hx]
    refine congrArg D.coord (Prod.ext rfl ?_)
    have h2 : ∀ z : Vt S D.g D.t, (2 : ℕ) • z = 0 := fun z => by
      rw [two_nsmul, OrthoF2.vec_add_self]
    have e : D.resC ⟨c, hc⟩ (D.resC ⟨c, hc⟩ u + D.resC ⟨c, hc⟩ v - u) -
        (D.resC ⟨c, hc⟩ u + D.resC ⟨c, hc⟩ v - u) - (D.resC ⟨c, hc⟩ v - v) =
        (2 : ℕ) • (u + v - D.resC ⟨c, hc⟩ u - D.resC ⟨c, hc⟩ v) := by
      simp only [map_sub, map_add, hγγ]
      abel
    exact (sub_eq_zero.mp (e.trans (h2 _))).symm
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Vt S D.g D.t →ₗ[ZMod 2] S.Qt,
      ∀ w, Φ w = D.coord (w, D.resC ⟨c, hc⟩ w - w) := ⟨
    (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) ∘ₗ
      LinearMap.prod LinearMap.id
        (((D.resC ⟨c, hc⟩ : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t) :
          Vt S D.g D.t →ₗ[ZMod 2] Vt S D.g D.t) - LinearMap.id), fun w => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro w₁ w₂ h
    rw [hΦ, hΦ] at h
    exact (Prod.mk.inj (D.coord.injective h)).1
  have hUle : U ≤ LinearMap.range Φ := by
    intro y hy
    obtain ⟨w, hw⟩ := hrep y hy
    exact ⟨w, by rw [hΦ, ← hw]⟩
  have hWU : finrank (ZMod 2) (U.comap Φ) = finrank (ZMod 2) U := by
    have h1 := (Submodule.equivMapOfInjective Φ hΦinj (U.comap Φ)).finrank_eq
    rwa [Submodule.map_comap_eq_of_le hUle] at h1
  have hLa : D.resC ⟨c, hc⟩ a - a = 0 := by
    rw [hL, polar_self_eq_zero, hd, zero_smul, zero_smul, add_zero]
  have haW : a ∈ U.comap Φ := by
    rw [Submodule.mem_comap, hΦ, hLa]
    exact haU
  have hW3 : 3 ≤ finrank (ZMod 2) (U.comap Φ) := by
    rw [hWU]
    exact three_le_finrank_of_card h8
  obtain ⟨⟨w₁, hw₁W, hLw₁, hQw₁⟩, ⟨w₂, hw₂W, hLw₂, hQw₂⟩⟩ :=
    exists_pair_of_finrank_ge_three (L := fun w => D.resC ⟨c, hc⟩ w - w) D.QV_nondegenerate
      (hw ▸ D.finrank_Vt) D.QV_aV hdQ hd hli hL haW hW3
  refine ⟨Φ w₁, hw₁W, Φ w₂, hw₂W, ?_, ?_, ?_, ?_⟩
  · rw [hΦ, D.span2_coord]
    exact finrank_span_pair_eL hd hL hLw₁
  · rw [hΦ, D.span2_coord]
    exact finrank_span_pair_eL hd hL hLw₂
  · rw [hΦ, D.span2_coord]
    exact (forall_mem_span_pair_eL_iff D.QV_aV hdQ hd hL w₁).mpr hQw₁
  · refine ⟨w₂, ?_, hQw₂⟩
    rw [hΦ, D.span2_coord]
    exact Submodule.subset_span (by simp)

theorem exists_q_ne_zero_of_t_mul_typeC {c : S.O} (hc : c ∈ D.Cbar) {d : Vt S D.g D.t}
    (hd : polar D.QV (aV D.good.ht) d = 0) (hdQ : D.QV d = 1)
    (hcd : ∀ v : Vt S D.g D.t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((eichler D.QV (aV D.good.ht) d v : Vt S D.g D.t) : S.Qt)) :
    ∃ y ∈ commSpace ((D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt), S.q y ≠ 0 := by
  set a := aV D.good.ht
  have ha0 : a ≠ 0 := aV_ne_zero D.good.H D.good.ht
  have haQ : D.QV a = 0 := D.QV_aV
  have hγ := D.resC_eq_eichler hc hcd
  obtain ⟨v, hv⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero D.QV_nondegenerate ha0
  have hv1 : polar D.QV a v = 1 := OrthoF2.zmod2_eq_one_of_ne_zero hv
  have hA : polar D.QV v a = 1 := by rw [polar_comm]; exact hv1
  have key : polar D.QV (eichler D.QV a d v) v = 1 := by
    rw [eichler_apply_zmod2 haQ hd v]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_self_eq_zero, hdQ, hA, hv1,
      polar_comm D.QV d v]
    generalize polar D.QV v d = δ
    revert δ
    decide
  refine ⟨((D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, v)) - D.coord (0, v),
    sub_mem_commSpace _ _, ?_⟩
  rw [D.t_mul_apply_sub_coord hc, D.q_coord, ← D.polar_QV, map_zero, zero_add, sub_zero,
    QuadraticMap.polar_sub_right, polar_self_eq_zero, zero_sub, neg_ne_zero, hγ, key]
  exact one_ne_zero

end S2Data

end CFSG.GF2Type.Smith1980Orth
