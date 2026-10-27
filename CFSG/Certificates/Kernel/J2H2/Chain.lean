module

public import CFSG.RankThree.PartTwo.J2Residue.H2Sylow
public import CFSG.Certificates.Kernel.J2H2.Stable

public section

namespace CFSG.KC.J2H2

open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue.H2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


@[expose] noncomputable def coordF (g : ↥S → ↥S → V12) (f : ℕ) : ZMod 2 :=
  g (yS (f / 1536)) (elt (f / 12 % 128)) ⟨f % 12, Nat.mod_lt _ (by norm_num)⟩

@[expose] def TreeZero (g : ↥S → ↥S → V12) : Prop :=
  ∀ x, x ≠ 0 → x < 128 → g (yS (gen x)) (elt (par x)) = 0

section Span

variable (σ : ↥S →* Module.End (ZMod 2) V12)

theorem treeZero_sum {ι : Type*} (s : Finset ι) {g : ι → ↥S → ↥S → V12} (a : ι → ZMod 2)
    (h : ∀ i ∈ s, TreeZero (g i)) : TreeZero (∑ i ∈ s, a i • g i) := by
  intro x hx0 hx
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_eq_zero fun i hi => by rw [h i hi x hx0 hx, smul_zero]

theorem span_of {H : ℕ → ↥S → ↥S → V12} {F : ℕ → ℕ}
    (hH : ∀ j < 30, IsNormCoc σ (H j)) (hT : ∀ j < 30, TreeZero (H j))
    (hF : ∀ i < 30, ∀ j < 30, coordF (H j) (F i) = if i = j then 1 else 0)
    (hE : ∀ g, IsNormCoc σ g → TreeZero g → (∀ i < 30, coordF g (F i) = 0) → g = 0)
    {g : ↥S → ↥S → V12} (hg : IsNormCoc σ g) (hgT : TreeZero g) :
    g = ∑ j ∈ Finset.range 30, coordF g (F j) • H j := by
  set G := ∑ j ∈ Finset.range 30, coordF g (F j) • H j with hGdef
  have hG : IsNormCoc σ G := IsNormCoc.sum _ fun j hj => (hH j (Finset.mem_range.1 hj)).smul _
  have hd : IsNormCoc σ (g - G) := by
    have := hg.add (hG.smul (-1))
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hGT : TreeZero G := treeZero_sum (Finset.range 30) (fun j => coordF g (F j))
    (fun j hj => hT j (Finset.mem_range.1 hj))
  have hs : ∀ i < 30, coordF G (F i) = coordF g (F i) := by
    intro i hi
    have e : coordF G (F i) = ∑ j ∈ Finset.range 30, coordF g (F j) * coordF (H j) (F i) := by
      simp only [hGdef, coordF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, Finset.sum_eq_single i]
    · rw [hF i hi i hi, if_pos rfl, mul_one]
    · intro j hj hji
      rw [hF i hi j (Finset.mem_range.1 hj), if_neg (Ne.symm hji), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 hi) h
  have h0 := hE _ hd (fun x hx0 hx => by
      change g _ _ - G _ _ = 0
      rw [hgT x hx0 hx, hGT x hx0 hx, sub_zero])
    (fun i hi => by
      change coordF g (F i) - coordF G (F i) = 0
      rw [hs i hi, sub_self])
  exact sub_eq_zero.1 h0

end Span

theorem cob_zero' (σ : ↥S →* Module.End (ZMod 2) V12) : cob σ (0 : ↥S → V12) = 0 := by
  funext s t
  simp only [CFSG.RankThree.PartTwo.J2Residue.H2.cob, Pi.zero_apply, map_zero, sub_zero, add_zero]

section Good

variable (σ : ↥S →* Module.End (ZMod 2) V12) (H : ℕ → ↥S → ↥S → V12) (IND : Finset ℕ)

@[expose] def Good (g : ↥S → ↥S → V12) : Prop :=
  ∃ ε : ℕ → ZMod 2, ∃ B : ↥S → V12, (∀ i, i ∉ IND → ε i = 0) ∧
    g = ∑ i ∈ Finset.range 30, ε i • H i + cob σ B

variable {σ H IND}

theorem Good.add {g g' : ↥S → ↥S → V12} (h : Good σ H IND g) (h' : Good σ H IND g') :
    Good σ H IND (g + g') := by
  obtain ⟨ε, B, hε, rfl⟩ := h
  obtain ⟨ε', B', hε', rfl⟩ := h'
  refine ⟨ε + ε', B + B', fun i hi => by simp [hε i hi, hε' i hi], ?_⟩
  rw [cob_add]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem Good.smul {g : ↥S → ↥S → V12} (h : Good σ H IND g) (a : ZMod 2) : Good σ H IND (a • g) := by
  obtain ⟨ε, B, hε, rfl⟩ := h
  refine ⟨a • ε, a • B, fun i hi => by simp [hε i hi], ?_⟩
  rw [cob_smul, smul_add, Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

theorem Good.cob {g : ↥S → ↥S → V12} (h : Good σ H IND g) (β : ↥S → V12) :
    Good σ H IND (g + cob σ β) := by
  obtain ⟨ε, B, hε, rfl⟩ := h
  exact ⟨ε, B + β, hε, by rw [cob_add, add_assoc]⟩

theorem good_sum (s : Finset ℕ) (a : ℕ → ZMod 2) (h : ∀ j ∈ s, Good σ H IND (H j)) :
    Good σ H IND (∑ j ∈ s, a j • H j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 0, fun _ _ => rfl, ?_⟩
    rw [Finset.sum_empty, cob_zero']
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ((h j (Finset.mem_insert_self j s)).smul (a j)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem good_H (hIND : IND ⊆ Finset.range 30)
    (hR : ∀ j < 30, j ∉ IND → ∃ A ⊆ IND, ∃ b : ↥S → V12, H j = ∑ i ∈ A, H i + cob σ b)
    {j : ℕ} (hj : j < 30) : Good σ H IND (H j) := by
  classical
  by_cases hji : j ∈ IND
  · refine ⟨fun i => if i = j then 1 else 0, 0, fun i hi => ?_, ?_⟩
    · have : i ≠ j := fun e => hi (e ▸ hji)
      simp [this]
    · rw [Finset.sum_eq_single j]
      · simp only [ite_true, one_smul, cob_zero', add_zero]
      · intro i _ hij
        simp only [if_neg hij, zero_smul]
      · intro h
        exact absurd (Finset.mem_range.2 hj) h
  · obtain ⟨A, hA, b, hb⟩ := hR j hj hji
    refine ⟨fun i => if i ∈ A then 1 else 0, b, fun i hi => ?_, ?_⟩
    · have : i ∉ A := fun h => hi (hA h)
      simp [this]
    · rw [hb]
      refine congrArg (· + cob σ b) ?_
      have hA' : A ⊆ Finset.range 30 := hA.trans hIND
      rw [← Finset.sum_subset hA' (fun i _ hi => by simp [hi])]
      exact Finset.sum_congr rfl fun i hi => by simp [hi]

end Good

section Psi

variable {ρ : ↥P →* Module.End (ZMod 2) V12}

@[expose] noncomputable def phiL (L : List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2)))
    (F : ↥S → ↥S → V12) : ZMod 2 :=
  (L.map fun e => e.2.2.2.2 (F e.1 e.2.2.1)).sum

@[expose] noncomputable def psiL (ρ : ↥P →* Module.End (ZMod 2) V12) (g : ↥P)
    (L : List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2))) (F : ↥S → ↥S → V12) : ZMod 2 :=
  (L.map fun e => e.2.2.2.2 (F e.1 e.2.2.1 - ρ g⁻¹ (F e.2.1 e.2.2.2.1))).sum

theorem psiL_add (g : ↥P) (L : List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2)))
    (F F' : ↥S → ↥S → V12) : psiL ρ g L (F + F') = psiL ρ g L F + psiL ρ g L F' := by
  unfold psiL
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, add_add_add_comm, ← map_add]
    congr 2
    simp only [Pi.add_apply, map_add]
    abel

theorem psiL_smul (g : ↥P) (L : List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2))) (a : ZMod 2)
    (F : ↥S → ↥S → V12) : psiL ρ g L (a • F) = a * psiL ρ g L F := by
  unfold psiL
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    simp only [Pi.smul_apply, map_smul, ← smul_sub, smul_eq_mul]

theorem psiL_sum (g : ↥P) (L : List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2))) (s : Finset ℕ)
    (a : ℕ → ZMod 2) (F : ℕ → ↥S → ↥S → V12) :
    psiL ρ g L (∑ i ∈ s, a i • F i) = ∑ i ∈ s, a i * psiL ρ g L (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    unfold psiL
    simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, psiL_add, psiL_smul, ih]

@[expose] noncomputable def conjB (ρ : ↥P →* Module.End (ZMod 2) V12) (g : ↥P) (B : ↥S → V12)
    (x : ↥S) : V12 :=
  open Classical in
  if h : ∃ y : ↥S, incl y = g * incl x * g⁻¹ then ρ g⁻¹ (B h.choose) else 0

theorem conjB_eq {g : ↥P} (B : ↥S → V12) {x y : ↥S} (h : incl y = g * incl x * g⁻¹) :
    conjB ρ g B x = ρ g⁻¹ (B y) := by
  have hx : ∃ y : ↥S, incl y = g * incl x * g⁻¹ := ⟨y, h⟩
  rw [conjB, dif_pos hx]
  have e := hx.choose_spec.trans h.symm
  have : hx.choose = y := Subtype.ext (by
    have e' := congrArg (fun z : ↥P => (z : Perm315)) e
    simpa only [incl_coe] using e')
  rw [this]

variable (L : List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2))) (g : ↥P)
  (hL : ∀ e ∈ L, incl e.2.1 = g * incl e.1 * g⁻¹ ∧ incl e.2.2.2.1 = g * incl e.2.2.1 * g⁻¹)
  (hΦ : ∀ β : ↥S → V12, phiL L (cob (rhoS ρ) β) = 0)
include hL hΦ

theorem psi_res {c : ↥P → ↥P → V12} (hc : IsNormCoc ρ c) :
    psiL ρ g L (fun s t => c (incl s) (incl t)) = 0 := by
  obtain ⟨γ, hγ⟩ := conjDiff_cob hc g
  rw [← hΦ (fun s => γ (incl s))]
  unfold psiL phiL
  congr 1
  refine List.map_congr_left fun e he => ?_
  congr 1
  obtain ⟨h1, h2⟩ := hL e he
  beta_reduce
  rw [h1, h2, hγ]
  simp only [CFSG.RankThree.PartTwo.J2Residue.H2.cob, rhoS, MonoidHom.comp_apply, map_mul]

omit hΦ in
theorem cob_conjB (B : ↥S → V12) {s t ps pt : ↥S} (h1 : incl ps = g * incl s * g⁻¹)
    (h2 : incl pt = g * incl t * g⁻¹) :
    cob (rhoS ρ) (conjB ρ g B) s t = ρ g⁻¹ (cob (rhoS ρ) B ps pt) := by
  have h3 : incl (ps * pt) = g * incl (s * t) * g⁻¹ := by
    rw [map_mul, map_mul, h1, h2]
    group
  simp only [CFSG.RankThree.PartTwo.J2Residue.H2.cob, rhoS, MonoidHom.comp_apply]
  rw [conjB_eq B h1, conjB_eq B h2, conjB_eq B h3, map_add, map_sub]
  have hs : ρ g⁻¹ (ρ (incl ps) (B pt)) = ρ (incl s) (ρ g⁻¹ (B pt)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h1]
    congr 2
    group
  rw [hs]

theorem psi_cob (B : ↥S → V12) : psiL ρ g L (cob (rhoS ρ) B) = 0 := by
  rw [← hΦ (B + -conjB ρ g B)]
  unfold psiL phiL
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  refine congrArg e.2.2.2.2 ?_
  obtain ⟨h1, h2⟩ := hL e he
  rw [cob_add, cob_neg, Pi.add_apply, Pi.add_apply, Pi.neg_apply, Pi.neg_apply,
    cob_conjB L g hL B h1 h2, sub_eq_add_neg]

end Psi

section Res

variable {ρ : ↥P →* Module.End (ZMod 2) V12}

theorem res_cob {H : ℕ → ↥S → ↥S → V12} {F : ℕ → ℕ} {IND : Finset ℕ}
    {g : ℕ → ↥P} {L : ℕ → List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2))} {M : ℕ → ℕ → ZMod 2}
    (hH : ∀ j < 30, IsNormCoc (rhoS ρ) (H j)) (hT : ∀ j < 30, TreeZero (H j))
    (hF : ∀ i < 30, ∀ j < 30, coordF (H j) (F i) = if i = j then 1 else 0)
    (hE : ∀ g, IsNormCoc (rhoS ρ) g → TreeZero g → (∀ i < 30, coordF g (F i) = 0) → g = 0)
    (hIND : IND ⊆ Finset.range 30)
    (hR : ∀ j < 30, j ∉ IND → ∃ A ⊆ IND, ∃ b : ↥S → V12, H j = ∑ i ∈ A, H i + cob (rhoS ρ) b)
    (hL : ∀ m < 10, ∀ e ∈ L m, incl e.2.1 = g m * incl e.1 * (g m)⁻¹ ∧
      incl e.2.2.2.1 = g m * incl e.2.2.1 * (g m)⁻¹)
    (hΦ : ∀ m < 10, ∀ β : ↥S → V12, phiL (L m) (cob (rhoS ρ) β) = 0)
    (hM : ∀ m < 10, ∀ i < 30, psiL ρ (g m) (L m) (H i) = M m i)
    (hrank : ∀ ε : ℕ → ZMod 2, (∀ i, i ∉ IND → ε i = 0) →
      (∀ m < 10, ∑ i ∈ Finset.range 30, ε i * M m i = 0) → ∀ i ∈ IND, ε i = 0)
    {c : ↥P → ↥P → V12} (hc : IsNormCoc ρ c) :
    ∃ b : ↥S → V12, ∀ s t : ↥S, c (incl s) (incl t) = cob (rhoS ρ) b s t := by
  set f : ↥S → ↥S → V12 := fun s t => c (incl s) (incl t) with hfdef
  have hf : IsNormCoc (rhoS ρ) f := hc.comp incl
  obtain ⟨β, hβ1, hβ⟩ := exists_treeNormal (rhoS ρ) hf
  have hg : IsNormCoc (rhoS ρ) (f + cob (rhoS ρ) β) := hf.add (isNormCoc_cob _ hβ1)
  have hsp := span_of (rhoS ρ) hH hT hF hE hg hβ
  have hgood : Good (rhoS ρ) H IND f := by
    have h1 := (good_sum (Finset.range 30) (fun j => coordF (f + cob (rhoS ρ) β) (F j))
      (fun j hj => good_H hIND hR (Finset.mem_range.1 hj))).cob (-β)
    rw [← hsp, add_assoc, ← cob_add, add_neg_cancel, cob_zero', add_zero] at h1
    exact h1
  obtain ⟨ε, B, hε, hfe⟩ := hgood
  have hz : ∀ m < 10, ∑ i ∈ Finset.range 30, ε i * M m i = 0 := by
    intro m hm
    have h0 := psi_res (L m) (g m) (hL m hm) (hΦ m hm) hc
    rw [← hfdef, hfe, psiL_add, psi_cob (L m) (g m) (hL m hm) (hΦ m hm), add_zero, psiL_sum] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i hi => by rw [hM m hm i (Finset.mem_range.1 hi)]
  have hε0 : ∀ i, ε i = 0 := fun i => by
    by_cases hi : i ∈ IND
    · exact hrank ε hε hz i hi
    · exact hε i hi
  refine ⟨B, fun s t => ?_⟩
  have := congrFun (congrFun hfe s) t
  simp only [hε0, zero_smul, Finset.sum_const_zero, zero_add] at this
  exact this

end Res

end CFSG.KC.J2H2

end
