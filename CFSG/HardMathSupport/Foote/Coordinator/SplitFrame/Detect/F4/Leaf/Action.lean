module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.LAData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open Heis

set_option linter.unusedSectionVars false


namespace ActionAux

theorem three_smul_not_root :
    ∀ γ ∈ rootFinset .F4, γ 0 = 0 → ∀ μ ∈ rootFinset .F4, μ 0 = 1 →
      3 • γ + μ ∉ rootFinset .F4 := by
  decide +kernel

theorem ne_of_deg {γ μ : Fin Tag.F4.rank → ℤ} (hγ0 : γ 0 = 0) (hμ1 : μ 0 = 1) :
    γ ≠ μ ∧ γ ≠ -μ := by
  constructor
  · intro h
    rw [h] at hγ0
    omega
  · intro h
    rw [h] at hγ0
    simp [hμ1] at hγ0

theorem commPairs_cases {γ μ : Fin Tag.F4.rank → ℤ} (hγ0 : γ 0 = 0) (hμ1 : μ 0 = 1)
    (h3 : 3 • γ + μ ∉ rootFinset .F4) {p : ℕ × ℕ} (hp : p ∈ commPairs .F4 γ μ) :
    p = (1, 1) ∨ p = (2, 1) ∨ p.2 = 2 := by
  obtain ⟨hc, hr⟩ := mem_commPairs.1 hp
  obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := mem_commCandidates.1 hc
  have hdeg : (p.1 • γ + p.2 • μ) 0 = p.2 := by simp [hγ0, hμ1]
  have hb := (deg_bounds _ (mem_rootFinset.2 hr)).2
  rw [hdeg] at hb
  rcases p with ⟨a, b⟩
  simp only at h1 h1' h2 h2' hb
  have hb' : b = 1 ∨ b = 2 := by omega
  rcases hb' with rfl | rfl
  · have ha : a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases ha with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd (by simpa using mem_rootFinset.2 hr) h3
  · exact Or.inr (Or.inr rfl)

theorem list_sum_two {α M : Type*} [AddCommMonoid M] [DecidableEq α] :
    ∀ (l : List α), l.Nodup → ∀ (f : α → M) (a b : α), a ≠ b →
      (∀ x ∈ l, x ≠ a → x ≠ b → f x = 0) →
      (l.map f).sum = (if a ∈ l then f a else 0) + (if b ∈ l then f b else 0)
  | [], _, f, a, b, _, _ => by simp
  | x :: l, hnd, f, a, b, hab, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
    have ih := list_sum_two l hnd' f a b hab (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.map_cons, List.sum_cons, ih]
    by_cases hxa : x = a
    · subst hxa
      have hxb : x ≠ b := hab
      have hbx : b ≠ x := fun e => hxb e.symm
      simp [hx, hxb, hbx]
    · by_cases hxb : x = b
      · subst hxb
        have hax : a ≠ x := fun e => hxa e.symm
        simp [hx, hxa, hax, add_comm]
      · have h0 := h x List.mem_cons_self hxa hxb
        have hax : a ≠ x := fun e => hxa e.symm
        have hbx : b ≠ x := fun e => hxb e.symm
        simp [h0, hax, hbx]

section Coord

variable {K : Type} [Field K]

theorem heisCoord_pinnedX_of_pos {ρ : Fin Tag.F4.rank → ℤ} (hρ : ρ ∈ rootFinset .F4)
    (hpos : 1 ≤ ρ 0) (z : K) :
    heisCoord .F4 K (pinnedX .F4 K ρ z) = if ρ 0 = 1 then Pi.single ρ z else 0 := by
  by_cases h1 : ρ 0 = 1
  · rw [if_pos h1]
    exact (heisCoord_spec .F4 K).pinnedX_deg1 ρ ⟨mem_rootFinset.1 hρ, h1⟩ z
  · rw [if_neg h1]
    have h2 : ρ = highRoot .F4 := deg_eq_two ρ hρ (by have := (deg_bounds ρ hρ).2; omega)
    subst h2
    exact (heisCoord_spec .F4 K).pinnedX_highRoot z

theorem pinnedX_mem_Qθ_of_pos {ρ : Fin Tag.F4.rank → ℤ} (hρ : ρ ∈ rootFinset .F4)
    (hpos : 1 ≤ ρ 0) (z : K) : pinnedX .F4 K ρ z ∈ Qθ .F4 K := by
  refine pinnedX_mem_rootSpan (S := parabolicRadicalRoots .F4 (Jθ .F4)) ?_ z
  rw [CoordAux.mem_radRoots_iff]
  by_cases h1 : ρ 0 = 1
  · exact Or.inl ⟨mem_rootFinset.1 hρ, h1⟩
  · exact Or.inr (deg_eq_two ρ hρ (by have := (deg_bounds ρ hρ).2; omega))

theorem heisCoord_list_prod {ι : Type*} (l : List ι) (f : ι → ModGL .F4 K)
    (hf : ∀ i ∈ l, f i ∈ Qθ .F4 K) :
    heisCoord .F4 K (l.map f).prod = (l.map fun i => heisCoord .F4 K (f i)).sum := by
  induction l with
  | nil => simp [heisCoord_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hl : (l.map f).prod ∈ Qθ .F4 K :=
      Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact hf j (List.mem_cons_of_mem _ hj)
    rw [(heisCoord_spec .F4 K).mul _ (hf i List.mem_cons_self) _ hl,
      ih fun j hj => hf j (List.mem_cons_of_mem _ hj)]

end Coord

open Classical in
def f4CommConst (γ μ : Fin Tag.F4.rank → ℤ) : ℕ × ℕ → ℤ :=
  if h : IsRoot .F4 γ ∧ IsRoot .F4 μ ∧ γ ≠ μ ∧ γ ≠ -μ then
    Classical.choose (exists_pinnedX_commFormula_F4_exact h.1 h.2.1 h.2.2.1 h.2.2.2)
  else fun _ => 0

open Classical in
theorem f4CommConst_spec {γ μ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (hμ : IsRoot .F4 μ)
    (hne : γ ≠ μ) (hne' : γ ≠ -μ) :
    (∀ p ∈ commPairs .F4 γ μ,
      |f4CommConst γ μ p| = if p = (1, 1) ∧ IsRoot .F4 (μ - γ) then 2 else 1) ∧
    ∀ (R : Type) [CommRing R] (c d : R),
      pinnedX .F4 R γ c * pinnedX .F4 R μ d * pinnedX .F4 R γ (-c) * pinnedX .F4 R μ (-d) =
        ((commPairs .F4 γ μ).map fun p =>
          pinnedX .F4 R (p.1 • γ + p.2 • μ)
            ((f4CommConst γ μ p : R) * c ^ p.1 * d ^ p.2)).prod := by
  have h : IsRoot .F4 γ ∧ IsRoot .F4 μ ∧ γ ≠ μ ∧ γ ≠ -μ := ⟨hγ, hμ, hne, hne'⟩
  have hC : f4CommConst γ μ =
      Classical.choose (exists_pinnedX_commFormula_F4_exact h.1 h.2.1 h.2.2.1 h.2.2.2) := by
    unfold f4CommConst
    exact dif_pos h
  rw [hC]
  exact Classical.choose_spec (exists_pinnedX_commFormula_F4_exact h.1 h.2.1 h.2.2.1 h.2.2.2)

def a1fun (γ μ : Fin Tag.F4.rank → ℤ) : ℤ :=
  if (1, 1) ∈ commPairs .F4 γ μ then f4CommConst γ μ (1, 1) else 0

def a2fun (γ μ : Fin Tag.F4.rank → ℤ) : ℤ :=
  if (2, 1) ∈ commPairs .F4 γ μ then f4CommConst γ μ (2, 1) else 0

section Act

variable {K : Type} [Field K]

theorem actFun_add (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) (t : K) (c c' : (Fin Tag.F4.rank → ℤ) → K) :
    actFun a1 a2 γ t (c + c') = actFun a1 a2 γ t c + actFun a1 a2 γ t c' := by
  funext ν
  simp only [actFun, Pi.add_apply]
  ring

theorem actFun_zero (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) (t : K) :
    actFun a1 a2 γ t (0 : (Fin Tag.F4.rank → ℤ) → K) = 0 := by
  funext ν
  simp [actFun]

theorem actFun_neg (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) (t : K) (c : (Fin Tag.F4.rank → ℤ) → K) :
    actFun a1 a2 γ t (-c) = -actFun a1 a2 γ t c := by
  funext ν
  simp only [actFun, Pi.neg_apply]
  ring

theorem shift_single (s : K) (g : (Fin Tag.F4.rank → ℤ) → K) (δ μ : Fin Tag.F4.rank → ℤ) (c : K)
    (ν : Fin Tag.F4.rank → ℤ) :
    s * g (ν - δ) * (Pi.single μ c : (Fin Tag.F4.rank → ℤ) → K) (ν - δ) =
      (Pi.single (μ + δ) (s * g μ * c) : (Fin Tag.F4.rank → ℤ) → K) ν := by
  by_cases h : ν - δ = μ
  · have h' : ν = μ + δ := sub_eq_iff_eq_add.1 h
    subst h'
    rw [h]
    simp
  · have h' : ν ≠ μ + δ := fun e => h (sub_eq_iff_eq_add.2 e)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    simp

theorem actFun_single (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ μ : Fin Tag.F4.rank → ℤ) (t c : K) :
    actFun a1 a2 γ t (Pi.single μ c : (Fin Tag.F4.rank → ℤ) → K) =
      (Pi.single μ c : (Fin Tag.F4.rank → ℤ) → K) +
        (Pi.single (μ + γ) (t * (a1 γ μ : K) * c) : (Fin Tag.F4.rank → ℤ) → K) +
        (Pi.single (μ + 2 • γ) (t ^ 2 * (a2 γ μ : K) * c) : (Fin Tag.F4.rank → ℤ) → K) := by
  funext ν
  have h2 : t * (a1 γ (ν - γ) : K) * (Pi.single μ c : (Fin Tag.F4.rank → ℤ) → K) (ν - γ) =
      (Pi.single (μ + γ) (t * (a1 γ μ : K) * c) : (Fin Tag.F4.rank → ℤ) → K) ν :=
    shift_single t (fun x => (a1 γ x : K)) γ μ c ν
  have h3 : t ^ 2 * (a2 γ (ν - 2 • γ) : K) *
      (Pi.single μ c : (Fin Tag.F4.rank → ℤ) → K) (ν - 2 • γ) =
      (Pi.single (μ + 2 • γ) (t ^ 2 * (a2 γ μ : K) * c) : (Fin Tag.F4.rank → ℤ) → K) ν :=
    shift_single (t ^ 2) (fun x => (a2 γ x : K)) (2 • γ) μ c ν
  simp only [actFun, Pi.add_apply]
  rw [h2, h3]

end Act

section Gen

variable {K : Type} [Field K]

theorem conj_gen_deg1 {γ μ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ rootFinset .F4) (hγ0 : γ 0 = 0)
    (hμ : μ ∈ rootFinset .F4) (hμ1 : μ 0 = 1) (t c : K) :
    pinnedX .F4 K γ t * pinnedX .F4 K μ c * (pinnedX .F4 K γ t)⁻¹ ∈ Qθ .F4 K ∧
    heisCoord .F4 K (pinnedX .F4 K γ t * pinnedX .F4 K μ c * (pinnedX .F4 K γ t)⁻¹) =
      actFun a1fun a2fun γ t (heisCoord .F4 K (pinnedX .F4 K μ c)) := by
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  obtain ⟨hC, hF⟩ := f4CommConst_spec (mem_rootFinset.1 hγ) (mem_rootFinset.1 hμ) hne hne'
  have h3 := three_smul_not_root γ hγ hγ0 μ hμ hμ1
  have hform := hF K t c
  rw [← pinnedX_neg .F4 K γ t, ← pinnedX_neg .F4 K μ c] at hform
  have hconj : pinnedX .F4 K γ t * pinnedX .F4 K μ c * (pinnedX .F4 K γ t)⁻¹ =
      ((commPairs .F4 γ μ).map fun p => pinnedX .F4 K (p.1 • γ + p.2 • μ)
        ((f4CommConst γ μ p : K) * t ^ p.1 * c ^ p.2)).prod * pinnedX .F4 K μ c := by
    rw [← hform]
    group
  have hdeg : ∀ p : ℕ × ℕ, (p.1 • γ + p.2 • μ) 0 = p.2 := fun p => by simp [hγ0, hμ1]
  have hpos : ∀ p ∈ commPairs .F4 γ μ, 1 ≤ (p.1 • γ + p.2 • μ) 0 := fun p hp => by
    rw [hdeg]
    have := (mem_commCandidates.1 (mem_commPairs.1 hp).1).2.1
    omega
  have hfac : ∀ p ∈ commPairs .F4 γ μ, pinnedX .F4 K (p.1 • γ + p.2 • μ)
      ((f4CommConst γ μ p : K) * t ^ p.1 * c ^ p.2) ∈ Qθ .F4 K := fun p hp =>
    pinnedX_mem_Qθ_of_pos (mem_rootFinset.2 (mem_commPairs.1 hp).2) (hpos p hp) _
  have hμQ : pinnedX .F4 K μ c ∈ Qθ .F4 K := pinnedX_mem_Qθ_of_pos hμ (by omega) c
  have hPQ : ((commPairs .F4 γ μ).map fun p => pinnedX .F4 K (p.1 • γ + p.2 • μ)
        ((f4CommConst γ μ p : K) * t ^ p.1 * c ^ p.2)).prod ∈ Qθ .F4 K :=
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hfac p hp
  refine ⟨hconj ▸ mul_mem hPQ hμQ, ?_⟩
  let f : ℕ × ℕ → (Fin Tag.F4.rank → ℤ) → K := fun p =>
    if (p.1 • γ + p.2 • μ) 0 = 1 then
      Pi.single (p.1 • γ + p.2 • μ) ((f4CommConst γ μ p : K) * t ^ p.1 * c ^ p.2) else 0
  have hmap : ((commPairs .F4 γ μ).map fun p => heisCoord .F4 K (pinnedX .F4 K (p.1 • γ + p.2 • μ)
      ((f4CommConst γ μ p : K) * t ^ p.1 * c ^ p.2))) = (commPairs .F4 γ μ).map f :=
    List.map_congr_left fun p hp =>
      heisCoord_pinnedX_of_pos (mem_rootFinset.2 (mem_commPairs.1 hp).2) (hpos p hp) _
  have hzero : ∀ x ∈ commPairs .F4 γ μ, x ≠ (1, 1) → x ≠ (2, 1) → f x = 0 := by
    intro x hx h1 h2
    have hx2 : x.2 = 2 := by
      rcases commPairs_cases hγ0 hμ1 h3 hx with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    have : (x.1 • γ + x.2 • μ) 0 ≠ 1 := by
      rw [hdeg, hx2]
      norm_num
    exact if_neg this
  have hsum := list_sum_two (commPairs .F4 γ μ) (commPairs_nodup γ μ) f (1, 1) (2, 1)
    (by decide) hzero
  have e11 : f (1, 1) = Pi.single (γ + μ) ((f4CommConst γ μ (1, 1) : K) * t * c) := by
    simp [f, hγ0, hμ1]
  have e21 : f (2, 1) = Pi.single (2 • γ + μ) ((f4CommConst γ μ (2, 1) : K) * t ^ 2 * c) := by
    simp [f, hγ0, hμ1]
  have hA : (if (1, 1) ∈ commPairs .F4 γ μ then f (1, 1) else 0) =
      (Pi.single (μ + γ) (t * (a1fun γ μ : K) * c) : (Fin Tag.F4.rank → ℤ) → K) := by
    by_cases hm : (1, 1) ∈ commPairs .F4 γ μ
    · rw [if_pos hm, e11, a1fun, if_pos hm, add_comm γ μ]
      congr 1
      ring
    · rw [if_neg hm, a1fun, if_neg hm]
      simp
  have hB : (if (2, 1) ∈ commPairs .F4 γ μ then f (2, 1) else 0) =
      (Pi.single (μ + 2 • γ) (t ^ 2 * (a2fun γ μ : K) * c) : (Fin Tag.F4.rank → ℤ) → K) := by
    by_cases hm : (2, 1) ∈ commPairs .F4 γ μ
    · rw [if_pos hm, e21, a2fun, if_pos hm, add_comm (2 • γ) μ]
      congr 1
      ring
    · rw [if_neg hm, a2fun, if_neg hm]
      simp
  rw [hconj, (heisCoord_spec .F4 K).mul _ hPQ _ hμQ, heisCoord_list_prod _ _ hfac, hmap, hsum,
    hA, hB, heisCoord_pinnedX_of_pos hμ (by omega) c, if_pos hμ1, actFun_single]
  abel

end Gen

theorem deg1Roots_data : ∀ μ ∈ deg1Roots, μ ∈ rootFinset .F4 ∧ μ 0 = 1 := by
  decide +kernel

theorem mem_commPairs_one_one {γ μ : Fin Tag.F4.rank → ℤ} :
    (1, 1) ∈ commPairs .F4 γ μ ↔ γ + μ ∈ rootFinset .F4 := by
  rw [mem_commPairs, mem_rootFinset]
  simp [commCandidates]

theorem mem_commPairs_two_one {γ μ : Fin Tag.F4.rank → ℤ} :
    (2, 1) ∈ commPairs .F4 γ μ ↔ 2 • γ + μ ∈ rootFinset .F4 := by
  rw [mem_commPairs, mem_rootFinset]
  simp [commCandidates]

theorem adm1 : Adm1 a1fun := by
  intro γ hγ hγ0 μ hμ
  obtain ⟨hμr, hμ1⟩ := deg1Roots_data μ hμ
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  obtain ⟨hC, -⟩ := f4CommConst_spec (mem_rootFinset.1 hγ) (mem_rootFinset.1 hμr) hne hne'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hm := mem_commPairs_one_one.2 h
    rw [a1fun, if_pos hm, hC _ hm]
    by_cases hr : μ - γ ∈ rootFinset .F4
    · rw [if_pos hr, if_pos ⟨rfl, mem_rootFinset.1 hr⟩]
    · rw [if_neg hr, if_neg fun h' => hr (mem_rootFinset.2 h'.2)]
  · have hm : (1, 1) ∉ commPairs .F4 γ μ := fun h' => h (mem_commPairs_one_one.1 h')
    rw [a1fun, if_neg hm]

theorem adm2 : Adm2 a2fun := by
  intro γ hγ hγ0 μ hμ
  obtain ⟨hμr, hμ1⟩ := deg1Roots_data μ hμ
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  obtain ⟨hC, -⟩ := f4CommConst_spec (mem_rootFinset.1 hγ) (mem_rootFinset.1 hμr) hne hne'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hm := mem_commPairs_two_one.2 h
    rw [a2fun, if_pos hm, hC _ hm, if_neg fun h' => absurd h'.1 (by decide)]
  · have hm : (2, 1) ∉ commPairs .F4 γ μ := fun h' => h (mem_commPairs_two_one.1 h')
    rw [a2fun, if_neg hm]

section Main

variable {K : Type} [Field K]

def actGood (γ : Fin Tag.F4.rank → ℤ) (t : K) : Subgroup (ModGL .F4 K) where
  carrier := {q | q ∈ Qθ .F4 K ∧ pinnedX .F4 K γ t * q * (pinnedX .F4 K γ t)⁻¹ ∈ Qθ .F4 K ∧
    heisCoord .F4 K (pinnedX .F4 K γ t * q * (pinnedX .F4 K γ t)⁻¹) =
      actFun a1fun a2fun γ t (heisCoord .F4 K q)}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    have e : pinnedX .F4 K γ t * (q * q') * (pinnedX .F4 K γ t)⁻¹ =
        (pinnedX .F4 K γ t * q * (pinnedX .F4 K γ t)⁻¹) *
          (pinnedX .F4 K γ t * q' * (pinnedX .F4 K γ t)⁻¹) := by group
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [e]
      exact mul_mem hcq hcq'
    · rw [e, (heisCoord_spec .F4 K).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec .F4 K).mul _ hq _ hq', actFun_add]
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [mul_one, mul_inv_cancel, heisCoord_one, actFun_zero]
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    have e : pinnedX .F4 K γ t * q⁻¹ * (pinnedX .F4 K γ t)⁻¹ =
        (pinnedX .F4 K γ t * q * (pinnedX .F4 K γ t)⁻¹)⁻¹ := by group
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [e]
      exact inv_mem hcq
    · rw [e, heisCoord_inv hcq, hqe, heisCoord_inv hq, actFun_neg]

theorem commute_theta {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ rootFinset .F4) (hγ0 : γ 0 = 0)
    (t c : K) : Commute (pinnedX .F4 K γ t) (pinnedX .F4 K (highRoot .F4) c) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg γ hγ (Or.inl hγ0)
  have hnil : commPairs .F4 theta γ = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun p hp =>
      commCandidates_theta_data γ hγ (Or.inl hγ0) p (mem_commPairs.1 hp).1
        (mem_rootFinset.2 (mem_commPairs.1 hp).2)
  exact (commute_pinnedX_of_commPairs_nil .F4 K (mem_rootFinset.1 theta_mem)
    (mem_rootFinset.1 hγ) hne hne' hnil c t).symm

end Main

end ActionAux

theorem exists_action_data (K : Type) [Field K] :
    ∃ a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ, Adm1 a1 ∧ Adm2 a2 ∧
      ∀ γ ∈ rootFinset .F4, γ 0 = 0 → ∀ t : K, ∀ q ∈ Qθ Tag.F4 K,
        heisCoord Tag.F4 K (pinnedX Tag.F4 K γ t * q * (pinnedX Tag.F4 K γ t)⁻¹) =
          actFun a1 a2 γ t (heisCoord Tag.F4 K q) := by
  refine ⟨ActionAux.a1fun, ActionAux.a2fun, ActionAux.adm1, ActionAux.adm2, ?_⟩
  intro γ hγ hγ0 t q hq
  have hle : Qθ Tag.F4 K ≤ ActionAux.actGood γ t := by
    show rootSpan Tag.F4 K (parabolicRadicalRoots Tag.F4 (Jθ Tag.F4)) ≤ _
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
    · have hαf : α ∈ rootFinset .F4 := mem_rootFinset.2 (CoordAux.mem_Deg1.1 h).1
      have hα1 : α 0 = 1 := (CoordAux.mem_Deg1.1 h).2
      obtain ⟨hmem, heq⟩ := ActionAux.conj_gen_deg1 hγ hγ0 hαf hα1 t c
      exact ⟨ActionAux.pinnedX_mem_Qθ_of_pos hαf (by omega) c, hmem, heq⟩
    · subst h
      have hc := ActionAux.commute_theta hγ hγ0 t c
      have hconj : pinnedX Tag.F4 K γ t * pinnedX Tag.F4 K (highRoot .F4) c *
          (pinnedX Tag.F4 K γ t)⁻¹ = pinnedX Tag.F4 K (highRoot .F4) c := by
        rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
      have hQ : pinnedX Tag.F4 K (highRoot .F4) c ∈ Qθ Tag.F4 K := pinnedX_mem_rootSpan hα c
      refine ⟨hQ, ?_, ?_⟩
      · rw [hconj]
        exact hQ
      · rw [hconj, (heisCoord_spec _ K).pinnedX_highRoot, ActionAux.actFun_zero]
  exact (hle hq).2.2

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
