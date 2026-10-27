module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Intrinsic
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Module
open scoped MatrixGroups

section Plane

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def planeV1 (a b : K) : Fin 4 → K := ![1, 0, a, b]

@[expose] def planeV2 (a b l : K) : Fin 4 → K := ![0, 1, l * σ b, -(l * σ a)]

@[expose] def planeP (a b l : K) : Submodule K (Fin 4 → K) :=
  Submodule.span K {planeV1 a b, planeV2 σ a b l}

variable {σ}

theorem herm_V1_V1 (a b : K) (h : σ a * a + σ b * b = 0) :
    herm σ (planeV1 a b) (planeV1 a b) = 1 := by
  simp only [herm_def, Fin.sum_univ_four, planeV1]
  simp
  linear_combination h

theorem herm_V2_V2 (hσσ : ∀ c, σ (σ c) = c) (a b l : K) (h : σ a * a + σ b * b = 0) :
    herm σ (planeV2 σ a b l) (planeV2 σ a b l) = 1 := by
  simp only [herm_def, Fin.sum_univ_four, planeV2]
  simp [hσσ]
  linear_combination (σ l * l) * h

theorem herm_V1_V2 (a b l : K) :
    herm σ (planeV1 a b) (planeV2 σ a b l) = 0 := by
  simp only [herm_def, Fin.sum_univ_four, planeV1, planeV2]
  simp
  ring

theorem herm_V2_V1 (hσσ : ∀ c, σ (σ c) = c) (a b l : K) :
    herm σ (planeV2 σ a b l) (planeV1 a b) = 0 := by
  simp only [herm_def, Fin.sum_univ_four, planeV1, planeV2]
  simp [hσσ]
  ring

end Plane

section Nondeg

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem nondeg_planeP (hσσ : ∀ c, σ (σ c) = c) (a b l : K) (h : σ a * a + σ b * b = 0) :
    Nondeg σ (planeP σ a b l) := by
  intro s hs hs'
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp hs
  have h1 := hs' (planeV1 a b) (Submodule.subset_span (by simp))
  have h2 := hs' (planeV2 σ a b l) (Submodule.subset_span (by simp))
  rw [herm_add_left, herm_smul_left, herm_smul_left, herm_V1_V1 a b h,
    herm_V2_V1 hσσ a b l, mul_one, mul_zero, add_zero] at h1
  rw [herm_add_left, herm_smul_left, herm_smul_left, herm_V1_V2 a b l,
    herm_V2_V2 hσσ a b l h, mul_one, mul_zero, zero_add] at h2
  have hx : x = 0 := (map_eq_zero σ).mp h1
  have hy : y = 0 := (map_eq_zero σ).mp h2
  rw [hx, hy, zero_smul, zero_smul, add_zero]

theorem linearIndependent_plane (a b l : K) :
    LinearIndependent K ![planeV1 a b, planeV2 σ a b l] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp [planeV1, planeV2] at h0 h1
  exact ⟨h0, h1⟩

theorem finrank_planeP (a b l : K) : finrank K (planeP σ a b l) = 2 := by
  have hset : ({planeV1 a b, planeV2 σ a b l} : Set (Fin 4 → K)) =
      Set.range ![planeV1 a b, planeV2 σ a b l] := by
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [planeP, hset, finrank_span_eq_card (linearIndependent_plane (σ := σ) a b l)]
  simp

end Nondeg

section Inj

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem planeP_injective {a b l a' b' l' : K} (hb : b ≠ 0)
    (h : planeP σ a b l = planeP σ a' b' l') : a = a' ∧ b = b' ∧ l = l' := by
  have h1 : planeV1 a b ∈ planeP σ a' b' l' := h ▸ Submodule.subset_span (by simp)
  have h2 : planeV2 σ a b l ∈ planeP σ a' b' l' := h ▸ Submodule.subset_span (by simp)
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨x', y', hxy'⟩ := Submodule.mem_span_pair.mp h2
  have e0 := congrFun hxy 0
  have e1 := congrFun hxy 1
  have e2 := congrFun hxy 2
  have e3 := congrFun hxy 3
  have f0 := congrFun hxy' 0
  have f1 := congrFun hxy' 1
  have f2 := congrFun hxy' 2
  simp [planeV1, planeV2] at e0 e1 e2 e3 f0 f1 f2
  rw [e0, e1] at e2 e3
  rw [f0, f1] at f2
  simp only [one_mul, zero_mul, add_zero, neg_zero] at e2 e3
  simp only [zero_mul, one_mul, zero_add] at f2
  refine ⟨e2.symm, e3.symm, ?_⟩
  rw [e3] at f2
  have : (l - l') * σ b = 0 := by linear_combination (-1 : K) * f2
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (by simpa using hb))

end Inj

section Group

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem perp_perp_eq' {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) {m : ℕ}
    {P : Submodule K (Fin m → K)} (hP : Nondeg σ P) : perp σ (perp σ P) = P := by
  have h1 := finrank_add_finrank_herm_perp hσ hP
  have h2 := finrank_add_finrank_herm_perp hσ (nondeg_herm_perp hσ hP)
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by omega)
  intro w hw t ht
  exact herm_eq_zero_comm σ hσ.invol (ht w hw)

theorem perp_eq_fixSpaceSU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {V : Submodule K (Fin 4 → K)} (hV : Nondeg (unitaryInvolution K p f) V)
    (hV2 : finrank K V = 2) {i : Su K p f 4}
    (hi : IsLongRootSU2 K p f (show 2 ≤ 4 by norm_num)
      (fixingSubgroup (Su K p f 4) (perp (unitaryInvolution K p f) V : Set (Fin 4 → K))) i) :
    perp (unitaryInvolution K p f) V = fixSpaceSU i := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hiL := (hi.isClassicalSL2 hK hp).mem
  have hle : perp (unitaryInvolution K p f) V ≤ fixSpaceSU i := by
    intro w hw
    have := (mem_fixingSubgroup_iff (Su K p f 4)).mp hiL w hw
    rw [fixSpaceSU, mem_eigSpace, one_smul, ← suMat_smul]
    exact this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := finrank_add_finrank_herm_perp hσ hV
  have h2 := Submodule.finrank_add_eq_of_isCompl (hi.isCompl hp)
  have h3 := hi.finrank_minusSpaceSU (two_ne_zero_of_charP_ne_two hp)
  rw [Module.finrank_fin_fun] at h2
  omega

theorem plane_eq_of_fixing_eq (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {V V' : Submodule K (Fin 4 → K)} (hV : Nondeg (unitaryInvolution K p f) V)
    (hV2 : finrank K V = 2) (hV' : Nondeg (unitaryInvolution K p f) V')
    (hV2' : finrank K V' = 2)
    (h : fixingSubgroup (Su K p f 4) (perp (unitaryInvolution K p f) V : Set (Fin 4 → K)) =
      fixingSubgroup (Su K p f 4) (perp (unitaryInvolution K p f) V' : Set (Fin 4 → K))) :
    V = V' := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨i, hi⟩ := (exists_isLongRootSU2_iff_fixingSubgroup hK hp (show 2 ≤ 4 by norm_num)
    (fixingSubgroup (Su K p f 4) (perp (unitaryInvolution K p f) V : Set (Fin 4 → K)))).mpr
    ⟨V, hV, hV2, rfl⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSU2_iff_fixingSubgroup hK hp (show 2 ≤ 4 by norm_num)
    (fixingSubgroup (Su K p f 4) (perp (unitaryInvolution K p f) V' : Set (Fin 4 → K)))).mpr
    ⟨V', hV', hV2', rfl⟩
  have hP' := perp_eq_fixSpaceSU hK hp hV' hV2' hi'
  rw [← h] at hi'
  have hii' : i' = i := hi.eq_of_orderOf_eq_two hK hp (hi'.isClassicalSL2 hK hp).mem
    (hi'.isClassicalSL2 hK hp).orderOf_eq_two
  have hP := perp_eq_fixSpaceSU hK hp hV hV2 hi
  rw [hii'] at hP'
  rw [← perp_perp_eq' hσ hV, ← perp_perp_eq' hσ hV', hP, hP']

end Group

section Count

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem card_longRootSetU_ge (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) :
    2 * ((p ^ f) ^ 2 - 1) * (p ^ f) ^ 2 ≤
      Set.ncard (longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hσσ := hσ.invol
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨β, hβ⟩ := hσ.norm_surj (-1) (by simp) (by simp)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at hβ
  let bOf : Bool → K → K := fun s a => (if s then β else -β) * a
  have hnorm : ∀ s a, unitaryInvolution K p f a * a +
      unitaryInvolution K p f (bOf s a) * bOf s a = 0 := by
    intro s a
    cases s <;> simp only [bOf, ↓reduceIte, Bool.false_eq_true, map_mul, map_neg] <;>
      linear_combination (unitaryInvolution K p f a * a) * hβ
  have hbne : ∀ (s : Bool) (a : {a : K // a ≠ 0}), bOf s a.1 ≠ 0 := by
    intro s a
    cases s <;> simp [bOf, hβ0, a.2]
  let Ψ : ({a : K // a ≠ 0} × Bool × K) → Subgroup (Su K p f 4) := fun x =>
    fixingSubgroup (Su K p f 4) (perp (unitaryInvolution K p f)
      (planeP (unitaryInvolution K p f) x.1.1 (bOf x.2.1 x.1.1) x.2.2) : Set (Fin 4 → K))
  have hnd : ∀ x : {a : K // a ≠ 0} × Bool × K,
      Nondeg (unitaryInvolution K p f)
        (planeP (unitaryInvolution K p f) x.1.1 (bOf x.2.1 x.1.1) x.2.2) := fun x =>
    nondeg_planeP hσσ _ _ _ (hnorm _ _)
  have hmem : ∀ x, Ψ x ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num) :=
    fun x => (exists_isLongRootSU2_iff_fixingSubgroup hK hp (show 2 ≤ 4 by norm_num) _).mpr
      ⟨_, hnd x, finrank_planeP _ _ _, rfl⟩
  have hinj : Function.Injective Ψ := by
    rintro ⟨⟨a, ha⟩, s, l⟩ ⟨⟨a', ha'⟩, s', l'⟩ h
    have hP := plane_eq_of_fixing_eq hK hp (hnd _) (finrank_planeP _ _ _) (hnd _)
      (finrank_planeP _ _ _) h
    obtain ⟨e1, e2, e3⟩ := planeP_injective (hbne s ⟨a, ha⟩) hP
    subst e1
    have hs : s = s' := by
      by_contra hss
      have : (if s then β else -β) = (if s' then β else -β) := mul_right_cancel₀ ha e2
      cases s <;> cases s' <;> simp at hss this
      · have h3 : (2 : K) * β = 0 := by linear_combination (-1 : K) * this
        exact hβ0 ((mul_eq_zero.mp h3).resolve_left h2)
      · have h3 : (2 : K) * β = 0 := by linear_combination this
        exact hβ0 ((mul_eq_zero.mp h3).resolve_left h2)
    subst hs
    subst e3
    rfl
  have hfin : (longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num)).Finite :=
    Set.toFinite _
  have h1 : Set.ncard (Set.range Ψ) ≤
      Set.ncard (longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num)) :=
    Set.ncard_le_ncard (Set.range_subset_iff.mpr hmem) hfin
  have h2' : Set.ncard (Set.range Ψ) = Nat.card ({a : K // a ≠ 0} × Bool × K) := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  have hcard : Nat.card ({a : K // a ≠ 0} × Bool × K) =
      ((p ^ f) ^ 2 - 1) * (2 * (p ^ f) ^ 2) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_congr (unitsEquivNeZero (G₀ := K)).symm,
      Nat.card_eq_fintype_card (α := Kˣ), Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    simp
  rw [h2', hcard] at h1
  calc 2 * ((p ^ f) ^ 2 - 1) * (p ^ f) ^ 2 = ((p ^ f) ^ 2 - 1) * (2 * (p ^ f) ^ 2) := by ring
    _ ≤ _ := h1

end Count

end CFSG.ClassicalInvolution.RouteD.TWZ
