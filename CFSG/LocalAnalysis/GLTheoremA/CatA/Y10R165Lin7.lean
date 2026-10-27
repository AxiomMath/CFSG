module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp2
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)

namespace LinEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}

theorem isCompl_blockSpace_fixedByEnd (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p) :
    IsCompl (HypBlocks.blockSpace A D.1)
      (HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D)) := by
  rw [OmEngine.fixedByEnd_blockEnd_eq_ker_projBlock A hp hpF hA t ht D]
  exact HypBlocks.isCompl_blockSpace_ker A hp hpF hA D

theorem blockEnd_sub_one_apply (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p) {u r : V}
    (hu : u ∈ HypBlocks.blockSpace A D.1)
    (hr : r ∈ LinearMap.ker (HypBlocks.projBlock A hp hpF hA D)) :
    ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1) (u + r) =
      (t D : V ≃ₗ[F] V) u - u := by
  have h1 : (HypBlocks.blockEnd A hp hpF hA t ht D : V ≃ₗ[F] V) (u + r) =
      (t D : V ≃ₗ[F] V) u + r := by
    rw [map_add, HypBlocks.blockEnd_apply_mem A hp hpF hA t ht D hu,
      HypBlocks.blockEnd_apply_of_ker A hp hpF hA t ht D hr]
  show (HypBlocks.blockEnd A hp hpF hA t ht D : V ≃ₗ[F] V) (u + r) - (u + r) = _
  rw [h1]
  abel

theorem range_blockEnd_sub_one (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p) :
    LinearMap.range ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1) =
      HypBlocks.blockSpace A D.1 := by
  have hmaps : ∀ x ∈ HypBlocks.blockSpace A D.1,
      ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1) x ∈
        HypBlocks.blockSpace A D.1 := by
    intro x hx
    obtain ⟨u, r, -, rfl⟩ :=
      exists_coe_add_of_isCompl (HypBlocks.isCompl_blockSpace_ker A hp hpF hA D) x
    rw [blockEnd_sub_one_apply A hp hpF hA t ht D u.2 r.2]
    exact Submodule.sub_mem _
      (HypBlocks.blockSpace_invariant A hp hpF hA (D := D.1) (a := t D) u.2) u.2
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    obtain ⟨u, r, -, rfl⟩ :=
      exists_coe_add_of_isCompl (HypBlocks.isCompl_blockSpace_ker A hp hpF hA D) v
    rw [blockEnd_sub_one_apply A hp hpF hA t ht D u.2 r.2]
    exact Submodule.sub_mem _
      (HypBlocks.blockSpace_invariant A hp hpF hA (D := D.1) (a := t D) u.2) u.2
  · intro u hu
    let f : HypBlocks.blockSpace A D.1 →ₗ[F] HypBlocks.blockSpace A D.1 :=
      ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1).restrict hmaps
    have hf : Function.Injective f := by
      intro x y hxy
      have h0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h1 : ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1)
          ((x : V) - (y : V)) = 0 := by
        have h := congrArg (fun z : HypBlocks.blockSpace A D.1 => (z : V)) h0
        change ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1)
          ((x : V) - (y : V)) = 0 at h
        exact h
      have h2 : (HypBlocks.blockEnd A hp hpF hA t ht D : V ≃ₗ[F] V)
          ((x : V) - (y : V)) = ((x : V) - (y : V)) := by
        have h := h1
        rw [LinearMap.sub_apply] at h
        exact sub_eq_zero.mp h
      have hmem : (x : V) - (y : V) ∈ HypBlocks.blockSpace A D.1 :=
        Submodule.sub_mem _ x.2 y.2
      have h2' : (t D : V ≃ₗ[F] V) ((x : V) - (y : V)) = ((x : V) - (y : V)) := by
        rw [← HypBlocks.blockEnd_apply_mem A hp hpF hA t ht D hmem]
        exact h2
      have h3 : (x : V) - (y : V) = 0 :=
        HypBlocks.eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) hmem h2'
      exact Subtype.ext (sub_eq_zero.mp h3)
    have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
    obtain ⟨x, hx⟩ := hsurj ⟨u, hu⟩
    refine ⟨(x : V), ?_⟩
    have h : ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1) (x : V) = u := by
      have h' := congrArg (fun z : HypBlocks.blockSpace A D.1 => (z : V)) hx
      change ((HypBlocks.blockEnd A hp hpF hA t ht D : V →ₗ[F] V) - 1) (x : V) = u at h'
      exact h'
    exact h

theorem isCompl_sup_blockSpace_inf_fixedByEnd (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    IsCompl (HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1)
      (HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D) ⊓
        HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht E)) := by
  rw [OmEngine.fixedByEnd_blockEnd_eq_ker_projBlock A hp hpF hA t ht D,
    OmEngine.fixedByEnd_blockEnd_eq_ker_projBlock A hp hpF hA t ht E]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hxU, hxK⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hxK₁, hxK₂⟩ := Submodule.mem_inf.mp hxK
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxU
    have hPa : HypBlocks.projBlock A hp hpF hA D a = a :=
      HypBlocks.projBlock_apply_of_mem A hp hpF hA D ha
    have hPb : HypBlocks.projBlock A hp hpF hA D b = 0 :=
      HypBlocks.projBlock_apply_of_mem_block A hp hpF hA (D := D) (E := E) hDE.symm hb
    have hx1 := LinearMap.mem_ker.mp hxK₁
    rw [map_add, hPa, hPb, add_zero] at hx1
    have hPa' : HypBlocks.projBlock A hp hpF hA E a = 0 :=
      HypBlocks.projBlock_apply_of_mem_block A hp hpF hA (D := E) (E := D) hDE ha
    have hPb' : HypBlocks.projBlock A hp hpF hA E b = b :=
      HypBlocks.projBlock_apply_of_mem A hp hpF hA E hb
    have hx2 := LinearMap.mem_ker.mp hxK₂
    rw [map_add, hPa', hPb', zero_add] at hx2
    rw [hx1, hx2, add_zero]
    simp
  · rw [codisjoint_iff_le_sup]
    intro x _
    obtain ⟨u, r, hur⟩ :=
      exists_coe_add_of_isCompl (HypBlocks.isCompl_blockSpace_ker A hp hpF hA D) x
    obtain ⟨v, s, hvs⟩ :=
      exists_coe_add_of_isCompl (HypBlocks.isCompl_blockSpace_ker A hp hpF hA E) (r : V)
    have hr : (r : V) ∈ LinearMap.ker (HypBlocks.projBlock A hp hpF hA D) := r.2
    have hpv : HypBlocks.projBlock A hp hpF hA D (v : V) = 0 :=
      HypBlocks.projBlock_apply_of_mem_block A hp hpF hA (D := D) (E := E) hDE.symm v.2
    have hps : (s : V) ∈ LinearMap.ker (HypBlocks.projBlock A hp hpF hA D) := by
      rw [LinearMap.mem_ker]
      have h1 : HypBlocks.projBlock A hp hpF hA D (r : V) = 0 := by
        exact LinearMap.mem_ker.mp hr
      have h3 : (s : V) = (r : V) - (v : V) := by rw [← hvs]; abel
      rw [h3, map_sub, h1, hpv, sub_zero]
    refine Submodule.mem_sup.mpr ⟨(u : V) + (v : V),
      Submodule.add_mem _ (Submodule.mem_sup_left u.2) (Submodule.mem_sup_right v.2),
      (s : V), Submodule.mem_inf.mpr ⟨hps, s.2⟩, ?_⟩
    rw [← hur, ← hvs]
    abel

theorem blockEnd_mem_specialLinear [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hpd : ¬ p ∣ Fintype.card F - 1) (D : HypBlocks.Hyperplane A p) :
    LinearEquiv.det (HypBlocks.blockEnd A hp hpF hA t ht D) = 1 := by
  have hpow : HypBlocks.blockEnd A hp hpF hA t ht D ^ p = 1 :=
    HypBlocks.blockEnd_pow A hp hpF hA t ht D
  have h1 : ((LinearEquiv.det (HypBlocks.blockEnd A hp hpF hA t ht D)) ^ p : Fˣ) = 1 := by
    rw [← map_pow, hpow, map_one]
  have h2 : ((LinearEquiv.det (HypBlocks.blockEnd A hp hpF hA t ht D) : Fˣ) : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Units.ext (eq_one_of_pow_eq_one_of_not_dvd hp hpd h2)

theorem dvd_finrank_blockSpace [Fintype F] (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hn : 1 ≤ n) (D : HypBlocks.Hyperplane A p)
    (hD : HypBlocks.blockSpace A D.1 ≠ ⊥) :
    CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∣
      Module.finrank F ↥(HypBlocks.blockSpace A D.1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := by
    have h2 : ringChar F = 2 := by
      rw [FiniteField.even_card_iff_char_two]
      have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      rw [hcard]
      exact Nat.dvd_iff_mod_eq_zero.mp hdvd
    exact ringChar.of_eq h2
  have hord : orderOf (HypBlocks.blockEnd A hp hpF hA t ht D) = p :=
    HypBlocks.orderOf_blockEnd A hp hpF hA t ht hD
  have hdvd := CFSG.RankThree.GF2n.Stroth80.orderOf_card_dvd_finrank_range hp hp2 hord
  have hq : orderOf ((Nat.card F : ℕ) : ZMod p) = CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n := by
    rw [Nat.card_eq_fintype_card, hcard, CFSG.LocalAnalysis.GLTheoremA.rk2Ord]
    push_cast
    rfl
  rwa [hq, range_blockEnd_sub_one A hp hpF hA t ht D] at hdvd


theorem fixedBySet_singleton (s : V ≃ₗ[F] V) :
    fixedBySet ({s} : Set (V ≃ₗ[F] V)) = HypBlocks.fixedByEnd s := by
  ext w
  simp [fixedBySet]

theorem fixedBySet_pair (s t : V ≃ₗ[F] V) :
    fixedBySet ({s, t} : Set (V ≃ₗ[F] V)) =
      HypBlocks.fixedByEnd s ⊓ HypBlocks.fixedByEnd t := by
  ext w
  simp [fixedBySet]

abbrev Jsub (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p) : Subgroup (SpecialLinearGroup F V) :=
  pointwiseStabCentralizer {HypBlocks.blockEnd A hp hpF hA t ht D} (HypBlocks.blockSpace A D.1)

abbrev Lsub (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D E : HypBlocks.Hyperplane A p) : Subgroup (SpecialLinearGroup F V) :=
  pointwiseStabCentralizer {HypBlocks.blockEnd A hp hpF hA t ht D,
    HypBlocks.blockEnd A hp hpF hA t ht E}
    (HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1)

theorem mem_Jsub {A : Subgroup (V ≃ₗ[F] V)} [Fintype A] {hp : p.Prime} {hpF : (p : F) ≠ 0}
    {hA : IsElemAbelian p A} {t : HypBlocks.Hyperplane A p → ↥A} {ht : ∀ D, t D ∉ D.1}
    {D : HypBlocks.Hyperplane A p} {g : SpecialLinearGroup F V} :
    g ∈ Jsub A hp hpF hA t ht D ↔
      (∀ u ∈ HypBlocks.blockSpace A D.1, (g : V ≃ₗ[F] V) u = u) ∧
        ∀ s ∈ ({HypBlocks.blockEnd A hp hpF hA t ht D} : Set (V ≃ₗ[F] V)),
          (g : V ≃ₗ[F] V) * s = s * (g : V ≃ₗ[F] V) :=
  Iff.rfl

theorem mem_Lsub {A : Subgroup (V ≃ₗ[F] V)} [Fintype A] {hp : p.Prime} {hpF : (p : F) ≠ 0}
    {hA : IsElemAbelian p A} {t : HypBlocks.Hyperplane A p → ↥A} {ht : ∀ D, t D ∉ D.1}
    {D E : HypBlocks.Hyperplane A p} {g : SpecialLinearGroup F V} :
    g ∈ Lsub A hp hpF hA t ht D E ↔
      (∀ u ∈ HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1,
        (g : V ≃ₗ[F] V) u = u) ∧
      ∀ s ∈ ({HypBlocks.blockEnd A hp hpF hA t ht D,
        HypBlocks.blockEnd A hp hpF hA t ht E} : Set (V ≃ₗ[F] V)),
          (g : V ≃ₗ[F] V) * s = s * (g : V ≃ₗ[F] V) :=
  Iff.rfl

noncomputable def JsubEquiv (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p) :
    ↥(Jsub A hp hpF hA t ht D) ≃*
      SpecialLinearGroup F ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D)) := by
  show ↥(pointwiseStabCentralizer
      ({HypBlocks.blockEnd A hp hpF hA t ht D} : Set (V ≃ₗ[F] V))
      (HypBlocks.blockSpace A D.1)) ≃* _
  refine restrictStabEquiv (isCompl_blockSpace_fixedByEnd A hp hpF hA t ht D)
    {HypBlocks.blockEnd A hp hpF hA t ht D} (fixedBySet_singleton _).symm ?_
  · intro s hs u hu
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [HypBlocks.blockEnd_apply_mem A hp hpF hA t ht D hu]
    exact HypBlocks.blockSpace_invariant A hp hpF hA (a := t D) hu

noncomputable def LsubEquiv (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E) :
    ↥(Lsub A hp hpF hA t ht D E) ≃*
      SpecialLinearGroup F ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D) ⊓
        HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht E)) := by
  show ↥(pointwiseStabCentralizer
      ({HypBlocks.blockEnd A hp hpF hA t ht D,
        HypBlocks.blockEnd A hp hpF hA t ht E} : Set (V ≃ₗ[F] V))
      (HypBlocks.blockSpace A D.1 ⊔ HypBlocks.blockSpace A E.1)) ≃* _
  refine restrictStabEquiv
    (isCompl_sup_blockSpace_inf_fixedByEnd A hp hpF hA t ht hDE)
    {HypBlocks.blockEnd A hp hpF hA t ht D, HypBlocks.blockEnd A hp hpF hA t ht E}
    (fixedBySet_pair _ _).symm ?_
  · intro s hs u hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rcases hs with rfl | rfl
    · rw [map_add, HypBlocks.blockEnd_apply_mem A hp hpF hA t ht D ha,
        HypBlocks.blockEnd_apply_of_mem_block A hp hpF hA t ht (D := D) (E := E) hDE.symm hb]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (HypBlocks.blockSpace_invariant A hp hpF hA (a := t D) ha))
        (Submodule.mem_sup_right hb)
    · rw [map_add, HypBlocks.blockEnd_apply_of_mem_block A hp hpF hA t ht (D := E) (E := D) hDE ha,
        HypBlocks.blockEnd_apply_mem A hp hpF hA t ht E hb]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
        (Submodule.mem_sup_right (HypBlocks.blockSpace_invariant A hp hpF hA (a := t E) hb))

theorem isQuasisimple_Jsub (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p)
    (h : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D)))) :
    CFSG.Open.IsQuasisimple ↥(Jsub A hp hpF hA t ht D) := by
  have h' := CFSG.LocalCores.isQuasisimple_of_mulEquiv (JsubEquiv A hp hpF hA t ht D).symm h
  exact ⟨h'.1.commutator_eq_top, h'.2.1⟩

theorem isQuasisimple_Lsub (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E)
    (h : CFSG.IsQuasisimple
      (SpecialLinearGroup F ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D) ⊓
        HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht E)))) :
    CFSG.Open.IsQuasisimple ↥(Lsub A hp hpF hA t ht D E) := by
  have h' := CFSG.LocalCores.isQuasisimple_of_mulEquiv (LsubEquiv A hp hpF hA t ht hDE).symm h
  exact ⟨h'.1.commutator_eq_top, h'.2.1⟩

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
