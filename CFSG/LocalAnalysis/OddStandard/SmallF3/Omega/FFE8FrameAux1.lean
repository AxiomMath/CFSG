module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma fk3_mem_ffE8Hat {J : Finset (Fin 4)} {k : Fin 4} :
    Sum.inr k ∈ ffE8Hat J ↔ k ∈ J := by
  simp [ffE8Hat]

private lemma fk3_inl_notMem_ffE8Hat {J : Finset (Fin 4)} {m : Fin 2} :
    Sum.inl m ∉ ffE8Hat J := by
  simp [ffE8Hat]

private lemma fk3_apply_apply {e : OGroup Q} (he : e * e = 1) (v : V) :
    (e : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) v) = v := by
  have h : (e : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V) = 1 := by
    simpa using congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) he
  rw [← LinearEquiv.mul_apply, h, LinearEquiv.coe_one, id]

private lemma fk3_sq_eq_one (x : ZMod 3) (hx : x * x = 1) : x = 1 ∨ x = -1 :=
  (by decide : ∀ y : ZMod 3, y * y = 1 → y = 1 ∨ y = -1) x hx

private lemma fk3_fin2_eq (m : Fin 2) : m = 0 ∨ m = 1 := by
  revert m; decide

private lemma fk3_fin2_ne {m m' : Fin 2} (h : m ≠ m') :
    (m = 0 ∧ m' = 1) ∨ (m = 1 ∧ m' = 0) := by
  revert m m'; decide

theorem ffOutFFE8Frame_eq_signChange {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (J : Finset ι) {e : OGroup Q}
    (h : ∀ i, (e : V ≃ₗ[ZMod 3] V) (fr.b i) = if i ∈ J then -fr.b i else fr.b i) :
    e = fr.signChange J := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [h i, fr.signChange_basis J i]

theorem ffOutFFE8Frame_basis (hdim : Module.finrank (ZMod 3) V = 6) {t : OGroup Q}
    (ht : t * t = 1) {a b : V} {f : Fin 4 → V} (ha : a ∈ fixSp t) (hb : b ∈ fixSp t)
    (hab : QuadraticMap.polar Q a b = 0) (hfix : ∀ v ∈ fixSp t, ∃ x y : ZMod 3, v = x • a + y • b)
    (hf : ∀ k, f k ∈ commSp t) (hff : ∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0)
    (hspan : Submodule.span (ZMod 3) (Set.range f) = commSp t) :
    ∃ B : Module.Basis FFE8Idx (ZMod 3) V, B (Sum.inl 0) = a ∧ B (Sum.inl 1) = b ∧
      (∀ k, B (Sum.inr k) = f k) ∧
      ∀ i j, i ≠ j → QuadraticMap.polar Q (B i) (B j) = 0 := by
  let B0 : FFE8Idx → V := Sum.elim ![a, b] f
  have hB0'' : B0 (Sum.inl 0) = a := by simp [B0]
  have hB0' : B0 (Sum.inl 1) = b := by simp [B0]
  have hB0 : ∀ k, B0 (Sum.inr k) = f k := fun k => by simp [B0]
  have hba : QuadraticMap.polar Q b a = 0 := by
    rw [QuadraticMap.polar_comm Q b a]; exact hab
  have hpol_a : ∀ l, QuadraticMap.polar Q a (f l) = 0 :=
    fun l => polar_fixSp_commSp ht ha (hf l)
  have hpol_b : ∀ l, QuadraticMap.polar Q b (f l) = 0 :=
    fun l => polar_fixSp_commSp ht hb (hf l)
  have hpol_fa : ∀ k, QuadraticMap.polar Q (f k) a = 0 := fun k => by
    rw [QuadraticMap.polar_comm Q (f k) a]; exact hpol_a k
  have hpol_fb : ∀ k, QuadraticMap.polar Q (f k) b = 0 := fun k => by
    rw [QuadraticMap.polar_comm Q (f k) b]; exact hpol_b k
  have hle : ⊤ ≤ Submodule.span (ZMod 3) (Set.range B0) := by
    rw [← (isCompl_fixSp_commSp ht).sup_eq_top]
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨p, q, hpq⟩ := hfix x hx
    have ha_mem : a ∈ Submodule.span (ZMod 3) (Set.range B0) :=
      Submodule.subset_span (by rw [← hB0'']; exact Set.mem_range_self (Sum.inl 0))
    have hb_mem : b ∈ Submodule.span (ZMod 3) (Set.range B0) :=
      Submodule.subset_span (by rw [← hB0']; exact Set.mem_range_self (Sum.inl 1))
    have hxspan : x ∈ Submodule.span (ZMod 3) (Set.range B0) := by
      rw [hpq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ p ha_mem)
        (Submodule.smul_mem _ q hb_mem)
    have hyspan : y ∈ Submodule.span (ZMod 3) (Set.range B0) := by
      have hy' : y ∈ Submodule.span (ZMod 3) (Set.range f) := by rw [hspan]; exact hy
      refine Submodule.span_mono ?_ hy'
      rintro z ⟨k, hk⟩
      exact ⟨Sum.inr k, (hB0 k).trans hk⟩
    exact Submodule.add_mem _ hxspan hyspan
  have hcard : Fintype.card FFE8Idx = Module.finrank (ZMod 3) V := by
    rw [hdim]
    decide
  let B : Module.Basis FFE8Idx (ZMod 3) V := basisOfTopLeSpanOfCardEqFinrank B0 hle hcard
  have hB0v : B (Sum.inl 0) = a := by
    change (basisOfTopLeSpanOfCardEqFinrank B0 hle hcard) (Sum.inl 0) = a
    rw [coe_basisOfTopLeSpanOfCardEqFinrank, hB0'']
  have hB1v : B (Sum.inl 1) = b := by
    change (basisOfTopLeSpanOfCardEqFinrank B0 hle hcard) (Sum.inl 1) = b
    rw [coe_basisOfTopLeSpanOfCardEqFinrank, hB0']
  have hB2v : ∀ k, B (Sum.inr k) = f k := by
    intro k
    change (basisOfTopLeSpanOfCardEqFinrank B0 hle hcard) (Sum.inr k) = f k
    rw [coe_basisOfTopLeSpanOfCardEqFinrank, hB0 k]
  refine ⟨B, hB0v, hB1v, hB2v, ?_⟩
  intro i j hij
  cases i with
  | inl m =>
      cases j with
      | inl m' =>
          have hne : m ≠ m' := fun h => hij (by rw [h])
          rcases fk3_fin2_ne hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hB0v, hB1v]; exact hab
          · rw [hB1v, hB0v]; exact hba
      | inr l =>
          rw [hB2v l]
          rcases fk3_fin2_eq m with rfl | rfl
          · rw [hB0v]; exact hpol_a l
          · rw [hB1v]; exact hpol_b l
  | inr k =>
      cases j with
      | inl m =>
          rw [hB2v k]
          rcases fk3_fin2_eq m with rfl | rfl
          · rw [hB0v]; exact hpol_fa k
          · rw [hB1v]; exact hpol_fb k
      | inr l =>
          have hkl : k ≠ l := fun h => hij (by rw [h])
          rw [hB2v k, hB2v l]
          exact hff k l hkl

theorem ffOutFFE8Frame_t_eq {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {t : OGroup Q}
    (ht : t * t = 1) (ha : ∀ i : Fin 2, fr.b (Sum.inl i) ∈ fixSp t)
    (hf : ∀ k, fr.b (Sum.inr k) ∈ commSp t) :
    t = fr.signChange (ffE8Hat Finset.univ) := by
  refine ffOutFFE8Frame_eq_signChange fr (ffE8Hat Finset.univ) ?_
  intro i
  cases i with
  | inl m =>
      rw [(mem_fixSp_iff).mp (ha m), if_neg fk3_inl_notMem_ffE8Hat]
  | inr k =>
      rw [(mem_commSp_iff ht).mp (hf k), if_pos (fk3_mem_ffE8Hat.mpr (Finset.mem_univ k))]

theorem ffOutFFE8Frame_mem_group (hQ : Q.Nondegenerate) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    (hsign : ∀ K : Finset FFE8Idx, fr.signChange K ∈ omegaGroup hQ ↔
      Even K.card ∧ Even (K.filter fun i => ffE8Norm ε i = -1).card)
    {e : OGroup Q} (heΩ : e ∈ omegaGroup hQ) (hsq : e * e = 1)
    (hfix : ∀ i : Fin 2, (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inl i)) = fr.b (Sum.inl i))
    (hsc : ∀ k, ∃ c : ZMod 3,
      (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inr k)) = c • fr.b (Sum.inr k)) :
    e ∈ ffE8Group fr := by
  classical
  choose c hc using hsc
  have hc_sq : ∀ k, c k * c k = 1 := by
    intro k
    have h1 := fk3_apply_apply hsq (fr.b (Sum.inr k))
    rw [hc k, map_smul, hc k, smul_smul] at h1
    have h1' : (c k * c k) • fr.b (Sum.inr k) = (1 : ZMod 3) • fr.b (Sum.inr k) := by
      rw [one_smul]; exact h1
    exact smul_left_injective (R := ZMod 3) (fr.b.ne_zero (Sum.inr k)) h1'
  have hc_val : ∀ k, c k = 1 ∨ c k = -1 := fun k => fk3_sq_eq_one (c k) (hc_sq k)
  let J : Finset (Fin 4) := Finset.univ.filter fun k => c k = -1
  have hJ : ∀ k, k ∈ J ↔ c k = -1 := by intro k; simp [J]
  have heq : e = fr.signChange (ffE8Hat J) := by
    refine ffOutFFE8Frame_eq_signChange fr (ffE8Hat J) ?_
    intro i
    cases i with
    | inl m => rw [hfix m, if_neg fk3_inl_notMem_ffE8Hat]
    | inr k =>
        rw [hc k]
        by_cases hk : c k = -1
        · rw [if_pos (fk3_mem_ffE8Hat.mpr ((hJ k).mpr hk)), hk]
          simp
        · have hk1 : c k = 1 := (hc_val k).resolve_right hk
          rw [if_neg (fun hmem => hk ((hJ k).mp (fk3_mem_ffE8Hat.mp hmem))), hk1]
          simp
  have he' : fr.signChange (ffE8Hat J) ∈ omegaGroup hQ := heq ▸ heΩ
  have heven : Even J.card := by
    simpa [ffE8Hat, Finset.card_map] using ((hsign (ffE8Hat J)).mp he').1
  exact (mem_ffE8Group_iff fr).mpr ⟨J, heven, heq⟩

theorem ffOutFFE8Frame_pair_norm (hQ : Q.Nondegenerate) {c : FFE8Idx → ZMod 3}
    (fr : PFrame Q FFE8Idx c) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hsign : ∀ K : Finset FFE8Idx, fr.signChange K ∈ omegaGroup hQ ↔
      Even K.card ∧ Even (K.filter fun i => c i = -1).card)
    {e : OGroup Q} (he : e ∈ omegaGroup hQ) {i j : Fin 4} (hij : i ≠ j)
    (hfix : ∀ m : Fin 2, (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inl m)) = fr.b (Sum.inl m))
    (hpat : ∀ k, (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inr k)) =
      (if k = i ∨ k = j then (-1 : ZMod 3) else 1) • fr.b (Sum.inr k)) :
    c (Sum.inr i) = c (Sum.inr j) := by
  classical
  have heq : e = fr.signChange ({Sum.inr i, Sum.inr j} : Finset FFE8Idx) := by
    refine ffOutFFE8Frame_eq_signChange fr _ ?_
    intro k
    cases k with
    | inl m => rw [hfix m, if_neg (by simp)]
    | inr k =>
        rw [hpat k]
        simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq]
        by_cases hk : k = i ∨ k = j <;> simp [hk]
  have he' : fr.signChange ({Sum.inr i, Sum.inr j} : Finset FFE8Idx) ∈ omegaGroup hQ :=
    heq ▸ he
  have hEven : Even ((({Sum.inr i, Sum.inr j} : Finset FFE8Idx).filter
      fun x => c x = -1)).card := ((hsign _).mp he').2
  rcases hc (Sum.inr i) with hi | hi <;> rcases hc (Sum.inr j) with hj | hj
  · rw [hi, hj]
  · exfalso
    have hflt : (({Sum.inr i, Sum.inr j} : Finset FFE8Idx).filter fun x => c x = -1) =
        {Sum.inr j} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hcx⟩
        rcases hx with rfl | rfl
        · rw [hi] at hcx; exact absurd hcx (by decide)
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, hj⟩
    rw [hflt, Finset.card_singleton] at hEven
    exact Nat.not_even_one hEven
  · exfalso
    have hflt : (({Sum.inr i, Sum.inr j} : Finset FFE8Idx).filter fun x => c x = -1) =
        {Sum.inr i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hcx⟩
        rcases hx with rfl | rfl
        · rfl
        · rw [hj] at hcx; exact absurd hcx (by decide)
      · rintro rfl; exact ⟨Or.inl rfl, hi⟩
    rw [hflt, Finset.card_singleton] at hEven
    exact Nat.not_even_one hEven
  · rw [hi, hj]

end CFSG.OddStandard.SmallF3.Omega
