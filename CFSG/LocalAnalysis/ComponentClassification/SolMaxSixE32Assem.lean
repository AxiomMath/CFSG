module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Gamma
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32GAct
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Symm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Omega

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_iff_of_map_eq {A : Subgroup X} {y : X}
    (h : A.map (MulAut.conj y).toMonoidHom = A) (a : X) : y * a * y⁻¹ ∈ A ↔ a ∈ A := by
  constructor
  · intro ha
    rw [← h] at ha
    obtain ⟨a', ha', he⟩ := ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    have : a' = a := by simpa using he
    rwa [← this]
  · intro ha
    rw [← h]
    exact ⟨a, ha, rfl⟩

theorem map_eq_of_forall_mem [Finite X] {A : Subgroup X} {y : X}
    (h : ∀ a ∈ A, y * a * y⁻¹ ∈ A) : A.map (MulAut.conj y).toMonoidHom = A := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]

@[expose] def avec : Fin 4 → Fin 5 → ZMod 2 :=
  ![![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 1, 1, 0], ![1, 0, 0, 0, 1]]

theorem aF_eq_mono {s t w₀ w₁ x : X} (i : Fin 4) :
    aF s w₀ w₁ x i = mono ![s, t, w₀, w₁, x] (avec i) := by
  have h0 : (0 : ZMod 2).val = 0 := rfl
  have h1 : (1 : ZMod 2).val = 1 := rfl
  fin_cases i <;> simp [aF, avec, mono, h0, h1, mul_assoc]

theorem aF_prod {s t w₀ w₁ x : X} (hg : IsE5 ![s, t, w₀, w₁, x]) :
    aF s w₀ w₁ x 0 * aF s w₀ w₁ x 1 * aF s w₀ w₁ x 2 = s ∧
    aF s w₀ w₁ x 1 * aF s w₀ w₁ x 2 = w₀ ∧
    aF s w₀ w₁ x 0 * aF s w₀ w₁ x 2 = w₁ ∧
    aF s w₀ w₁ x 0 * aF s w₀ w₁ x 1 = w₀ * w₁ ∧
    s * aF s w₀ w₁ x 3 = x := by
  have e : ∀ v : Fin 5 → ZMod 2, ∀ i : Fin 5, v = Pi.single i 1 →
      mono ![s, t, w₀, w₁, x] v = ![s, t, w₀, w₁, x] i := fun v i h => by
    rw [h, hg.mono_single]
  simp only [aF_eq_mono (t := t)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg.mono_add, ← hg.mono_add]
    exact e _ 0 (by decide)
  · rw [← hg.mono_add]
    exact e _ 2 (by decide)
  · rw [← hg.mono_add]
    exact e _ 3 (by decide)
  · rw [← hg.mono_add]
    have : avec 0 + avec 1 = Pi.single 2 1 + Pi.single 3 1 := by decide
    rw [this, hg.mono_add, hg.mono_single, hg.mono_single]
    rfl
  · have : s * mono ![s, t, w₀, w₁, x] (avec 3) =
        mono ![s, t, w₀, w₁, x] (Pi.single 0 1) * mono ![s, t, w₀, w₁, x] (avec 3) := by
      rw [hg.mono_single]
      rfl
    rw [this, ← hg.mono_add]
    exact e _ 4 (by decide)

@[expose] def Wf (w₀ w₁ : X) : Fin 3 → X := ![w₀, w₁, w₀ * w₁]

@[expose] def wvec : Fin 3 → Fin 5 → ZMod 2 :=
  ![Pi.single 2 1, Pi.single 3 1, Pi.single 2 1 + Pi.single 3 1]

@[expose] def pa : Fin 3 → Fin 4 := ![1, 0, 0]

@[expose] def pb : Fin 3 → Fin 4 := ![2, 2, 1]

theorem Wf_eq_mono {s t w₀ w₁ x : X} (hg : IsE5 ![s, t, w₀, w₁, x]) (i : Fin 3) :
    Wf w₀ w₁ i = mono ![s, t, w₀, w₁, x] (wvec i) := by
  fin_cases i
  · exact (hg.mono_single 2).symm
  · exact (hg.mono_single 3).symm
  · show w₀ * w₁ = mono ![s, t, w₀, w₁, x] (Pi.single 2 1 + Pi.single 3 1)
    rw [hg.mono_add, hg.mono_single, hg.mono_single]
    rfl

theorem Wf_eq_prod {s t w₀ w₁ x : X} (hg : IsE5 ![s, t, w₀, w₁, x]) (i : Fin 3) :
    Wf w₀ w₁ i = aF s w₀ w₁ x (pa i) * aF s w₀ w₁ x (pb i) := by
  obtain ⟨-, hp1, hp2, hp3, -⟩ := aF_prod hg
  fin_cases i
  · exact hp1.symm
  · exact hp2.symm
  · exact hp3.symm

theorem wvec_injective : Function.Injective wvec := by decide

theorem wvec_ne_zero : ∀ i : Fin 3, wvec i ≠ 0 := by decide

theorem cases_wvec : ∀ a b : ZMod 2, (![0, 0, a, b, 0] : Fin 5 → ZMod 2) ≠ 0 →
    (![0, 0, a, b, 0] : Fin 5 → ZMod 2) = wvec 0 ∨ (![0, 0, a, b, 0] : Fin 5 → ZMod 2) = wvec 1 ∨
      (![0, 0, a, b, 0] : Fin 5 → ZMod 2) = wvec 2 := by decide

theorem exists_extend (σ : Perm (Fin 3)) :
    ∃ α : Perm (Fin 4), α 3 = 3 ∧ ∀ j : Fin 3, α j.castSucc = (σ j).castSucc := by
  revert σ
  decide

theorem extend_vec : ∀ (σ : Perm (Fin 3)) (α : Perm (Fin 4)), α 3 = 3 →
    (∀ j : Fin 3, α j.castSucc = (σ j).castSucc) → ∀ i : Fin 3,
      avec (α (pa i)) + avec (α (pb i)) = wvec (σ i) := by
  decide

theorem swap_vec (i : Fin 3) : (Equiv.swap (pa i) (pb i)) 3 = 3 ∧
    Equiv.swap (pa i) (pb i) (pa i) = pb i := by
  revert i
  decide

theorem conj_mem_gamma {s t ν c : X} (hs2 : s * s = 1)
    (hνt : ν * t * ν⁻¹ = s) (hνs : ν * s * ν⁻¹ = s * t)
    (hc : c ∈ centralizer ({s, t} : Set X)) : ν * c * ν⁻¹ ∈ centralizer ({s, t} : Set X) := by
  have hcs : s * c = c * s := Subgroup.mem_centralizer_iff.mp hc s (by simp)
  have hct : t * c = c * t := Subgroup.mem_centralizer_iff.mp hc t (by simp)
  have h1 : Commute (ν * c * ν⁻¹) s := by
    show (ν * c * ν⁻¹) * s = s * (ν * c * ν⁻¹)
    calc ν * c * ν⁻¹ * s = ν * c * ν⁻¹ * (ν * t * ν⁻¹) := by rw [hνt]
      _ = ν * (c * t) * ν⁻¹ := by group
      _ = ν * (t * c) * ν⁻¹ := by rw [hct]
      _ = (ν * t * ν⁻¹) * (ν * c * ν⁻¹) := by group
      _ = s * (ν * c * ν⁻¹) := by rw [hνt]
  have h2 : Commute (ν * c * ν⁻¹) (s * t) := by
    show (ν * c * ν⁻¹) * (s * t) = (s * t) * (ν * c * ν⁻¹)
    calc ν * c * ν⁻¹ * (s * t) = ν * c * ν⁻¹ * (ν * s * ν⁻¹) := by rw [hνs]
      _ = ν * (c * s) * ν⁻¹ := by group
      _ = ν * (s * c) * ν⁻¹ := by rw [hcs]
      _ = (ν * s * ν⁻¹) * (ν * c * ν⁻¹) := by group
      _ = (s * t) * (ν * c * ν⁻¹) := by rw [hνs]
  have h3 : Commute (ν * c * ν⁻¹) t := by
    have : t = s * (s * t) := by rw [← mul_assoc, hs2, one_mul]
    rw [this]
    exact h1.mul_right h2
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with h' | h'
  · rw [h']; exact h1.symm.eq
  · rw [h']; exact h3.symm.eq

theorem odd_power [Finite X] {s t w₀ w₁ : X} {A : Subgroup X} {ν : X}
    (hts : s * t = t * s) (hs2 : s * s = 1)
    (hνt : ν * t * ν⁻¹ = s) (hνs : ν * s * ν⁻¹ = s * t)
    (hν0 : ν * w₀ * ν⁻¹ = w₀) (hν1 : ν * w₁ * ν⁻¹ = w₁) (hA : ∀ a ∈ A, ν * a * ν⁻¹ ∈ A) :
    ∃ ω : X, Odd (orderOf ω) ∧ ω * t * ω⁻¹ = s ∧ ω * s * ω⁻¹ = s * t ∧ ω * w₀ * ω⁻¹ = w₀ ∧
      ω * w₁ * ω⁻¹ = w₁ ∧ ∀ a ∈ A, ω * a * ω⁻¹ ∈ A := by
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos ν).ne'
  have h4 : ∃ j, 4 ^ k = 3 * j + 1 := by
    refine ⟨(4 ^ k) / 3, ?_⟩
    have h := Nat.pow_mod 4 k 3
    have h1 : 4 % 3 = 1 := by norm_num
    rw [h1, one_pow] at h
    omega
  obtain ⟨j, hj⟩ := h4
  have hν3 : ν ^ 3 = ν * ν * ν := pow_three' ν
  have hsts : s * t * s = t := by
    calc s * t * s = t * s * s := by rw [hts]
      _ = t * (s * s) := mul_assoc _ _ _
      _ = t := by rw [hs2, mul_one]
  have hν3t : ν ^ 3 * t = t * ν ^ 3 := by
    have : ν * ν * ν * t * (ν * ν * ν)⁻¹ = t := by
      calc ν * ν * ν * t * (ν * ν * ν)⁻¹ = ν * (ν * (ν * t * ν⁻¹) * ν⁻¹) * ν⁻¹ := by group
        _ = ν * (ν * s * ν⁻¹) * ν⁻¹ := by rw [hνt]
        _ = ν * (s * t) * ν⁻¹ := by rw [hνs]
        _ = (ν * s * ν⁻¹) * (ν * t * ν⁻¹) := by group
        _ = (s * t) * s := by rw [hνs, hνt]
        _ = t := hsts
    rw [hν3]
    calc ν * ν * ν * t = ν * ν * ν * t * (ν * ν * ν)⁻¹ * (ν * ν * ν) := by group
      _ = t * (ν * ν * ν) := by rw [this]
  have hν3s : ν ^ 3 * s = s * ν ^ 3 := by
    have hst : ν * (s * t) * ν⁻¹ = t := by
      calc ν * (s * t) * ν⁻¹ = (ν * s * ν⁻¹) * (ν * t * ν⁻¹) := by group
        _ = (s * t) * s := by rw [hνs, hνt]
        _ = t := hsts
    have : ν * ν * ν * s * (ν * ν * ν)⁻¹ = s := by
      calc ν * ν * ν * s * (ν * ν * ν)⁻¹ = ν * (ν * (ν * s * ν⁻¹) * ν⁻¹) * ν⁻¹ := by group
        _ = ν * (ν * (s * t) * ν⁻¹) * ν⁻¹ := by rw [hνs]
        _ = ν * t * ν⁻¹ := by rw [hst]
        _ = s := hνt
    rw [hν3]
    calc ν * ν * ν * s = ν * ν * ν * s * (ν * ν * ν)⁻¹ * (ν * ν * ν) := by group
      _ = s * (ν * ν * ν) := by rw [this]
  have hc3t : Commute (ν ^ 3) t := hν3t
  have hc3s : Commute (ν ^ 3) s := hν3s
  have hpow : ν ^ (4 ^ k) = (ν ^ 3) ^ j * ν := by
    rw [hj, pow_succ, pow_mul]
  refine ⟨ν ^ (4 ^ k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : (ν ^ (4 ^ k)) ^ m = 1 := by
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hord]
      refine ⟨2 ^ k, ?_⟩
      have h44 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      rw [h44]
      ring
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  · rw [hpow]
    calc (ν ^ 3) ^ j * ν * t * ((ν ^ 3) ^ j * ν)⁻¹
        = (ν ^ 3) ^ j * (ν * t * ν⁻¹) * ((ν ^ 3) ^ j)⁻¹ := by group
      _ = (ν ^ 3) ^ j * s * ((ν ^ 3) ^ j)⁻¹ := by rw [hνt]
      _ = s := by
          rw [(hc3s.pow_left j).eq, mul_assoc, mul_inv_cancel, mul_one]
  · rw [hpow]
    calc (ν ^ 3) ^ j * ν * s * ((ν ^ 3) ^ j * ν)⁻¹
        = (ν ^ 3) ^ j * (ν * s * ν⁻¹) * ((ν ^ 3) ^ j)⁻¹ := by group
      _ = (ν ^ 3) ^ j * (s * t) * ((ν ^ 3) ^ j)⁻¹ := by rw [hνs]
      _ = s * t := by
          rw [((hc3s.pow_left j).mul_right (hc3t.pow_left j)).eq, mul_assoc, mul_inv_cancel,
            mul_one]
  · have hc : Commute ν w₀ := by
      show ν * w₀ = w₀ * ν
      calc ν * w₀ = ν * w₀ * ν⁻¹ * ν := by group
        _ = w₀ * ν := by rw [hν0]
    rw [(hc.pow_left _).eq]
    group
  · have hc : Commute ν w₁ := by
      show ν * w₁ = w₁ * ν
      calc ν * w₁ = ν * w₁ * ν⁻¹ * ν := by group
        _ = w₁ * ν := by rw [hν1]
    rw [(hc.pow_left _).eq]
    group
  · have hall : ∀ n : ℕ, ∀ a ∈ A, ν ^ n * a * (ν ^ n)⁻¹ ∈ A := by
      intro n
      induction n with
      | zero => intro a ha; simpa using ha
      | succ n ih =>
        intro a ha
        have h1 := hA _ (ih a ha)
        rw [show ν * (ν ^ n * a * (ν ^ n)⁻¹) * ν⁻¹ = ν ^ (n + 1) * a * (ν ^ (n + 1))⁻¹ by
          rw [pow_succ']; group] at h1
        exact h1
    exact hall _

namespace IsFrame

variable [Finite X] {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}
  {Z : Ctx M θ ρ t s H Q} {w₀ w₁ x : X} (F : IsFrame Z w₀ w₁ x)
include F

theorem aF_mem (k : Fin 4) :
    aF s w₀ w₁ x k ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
  (F.E5.mem_closure_iff _).mpr ⟨avec k, aF_eq_mono k⟩

theorem s_mem : s ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
  Subgroup.subset_closure ⟨0, rfl⟩

theorem t_mem : t ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
  Subgroup.subset_closure ⟨1, rfl⟩

theorem x_mem : x ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
  Subgroup.subset_closure ⟨4, rfl⟩

theorem symm_gamma (α : Perm (Fin 4)) (hα : α 3 = 3) :
    ∃ c ∈ centralizer ({s, t} : Set X),
      (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
        Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) ∧
      ∀ i, c * aF s w₀ w₁ x i * c⁻¹ = aF s w₀ w₁ x (α i) := by
  obtain ⟨c, hcC, hct, hca⟩ := F.exists_symm α
  obtain ⟨hp0, hp1, hp2, hp3, hp4⟩ := aF_prod F.E5
  have key : ∀ β : Perm (Fin 4), β 3 = 3 →
      avec (β 0) + avec (β 1) + avec (β 2) = Pi.single 0 1 := by decide
  have hcs : c * s * c⁻¹ = s := by
    calc c * s * c⁻¹ = c * (aF s w₀ w₁ x 0 * aF s w₀ w₁ x 1 * aF s w₀ w₁ x 2) * c⁻¹ := by
          rw [hp0]
      _ = (c * aF s w₀ w₁ x 0 * c⁻¹) * (c * aF s w₀ w₁ x 1 * c⁻¹) *
            (c * aF s w₀ w₁ x 2 * c⁻¹) := by group
      _ = aF s w₀ w₁ x (α 0) * aF s w₀ w₁ x (α 1) * aF s w₀ w₁ x (α 2) := by
          rw [hca 0, hca 1, hca 2]
      _ = s := by
          simp only [aF_eq_mono (t := t)]
          rw [← F.E5.mono_add, ← F.E5.mono_add, key α hα, F.E5.mono_single]
          rfl
  have hcx : c * x * c⁻¹ = x := by
    calc c * x * c⁻¹ = (c * s * c⁻¹) * (c * aF s w₀ w₁ x 3 * c⁻¹) := by
          conv_lhs => rw [← hp4]
          group
      _ = x := by rw [hcs, hca 3, hα, hp4]
  have hcw₀ : c * w₀ * c⁻¹ = aF s w₀ w₁ x (α 1) * aF s w₀ w₁ x (α 2) := by
    calc c * w₀ * c⁻¹ = (c * aF s w₀ w₁ x 1 * c⁻¹) * (c * aF s w₀ w₁ x 2 * c⁻¹) := by
          conv_lhs => rw [← hp1]
          group
      _ = _ := by rw [hca 1, hca 2]
  have hcw₁ : c * w₁ * c⁻¹ = aF s w₀ w₁ x (α 0) * aF s w₀ w₁ x (α 2) := by
    calc c * w₁ * c⁻¹ = (c * aF s w₀ w₁ x 0 * c⁻¹) * (c * aF s w₀ w₁ x 2 * c⁻¹) := by
          conv_lhs => rw [← hp2]
          group
      _ = _ := by rw [hca 0, hca 2]
  refine ⟨c, ?_, ?_, hca⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with h1 | h1
    · rw [h1]
      calc s * c = (c * s * c⁻¹) * c := by rw [hcs]
        _ = c * s := by group
    · rw [h1]
      exact (mem_centralizer_singleton_iff.mp hcC).symm
  · apply map_eq_of_forall_mem
    intro a ha
    have hle : Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) ≤
        (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).comap (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      show c * ![s, t, w₀, w₁, x] i * c⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x])
      fin_cases i
      · show c * s * c⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x])
        rw [hcs]; exact F.s_mem
      · show c * t * c⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x])
        rw [hct]; exact F.t_mem
      · show c * w₀ * c⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x])
        rw [hcw₀]; exact mul_mem (F.aF_mem _) (F.aF_mem _)
      · show c * w₁ * c⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x])
        rw [hcw₁]; exact mul_mem (F.aF_mem _) (F.aF_mem _)
      · show c * x * c⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x])
        rw [hcx]; exact F.x_mem
    exact hle ha

theorem symm_W (σ : Perm (Fin 3)) :
    ∃ c ∈ centralizer ({s, t} : Set X),
      (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
        Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) ∧
      ∀ i, c * Wf w₀ w₁ i * c⁻¹ = Wf w₀ w₁ (σ i) := by
  obtain ⟨α, hα3, hα⟩ := exists_extend σ
  obtain ⟨c, hcΓ, hcA, hca⟩ := F.symm_gamma α hα3
  refine ⟨c, hcΓ, hcA, fun i => ?_⟩
  have key : aF s w₀ w₁ x (α (pa i)) * aF s w₀ w₁ x (α (pb i)) = Wf w₀ w₁ (σ i) := by
    rw [aF_eq_mono (t := t) (α (pa i)), aF_eq_mono (t := t) (α (pb i)), ← F.E5.mono_add,
      extend_vec σ α hα3 hα i, Wf_eq_mono F.E5 (σ i)]
  calc c * Wf w₀ w₁ i * c⁻¹
      = c * (aF s w₀ w₁ x (pa i) * aF s w₀ w₁ x (pb i)) * c⁻¹ := by rw [Wf_eq_prod F.E5 i]
    _ = (c * aF s w₀ w₁ x (pa i) * c⁻¹) * (c * aF s w₀ w₁ x (pb i) * c⁻¹) := by group
    _ = aF s w₀ w₁ x (α (pa i)) * aF s w₀ w₁ x (α (pb i)) := by rw [hca, hca]
    _ = Wf w₀ w₁ (σ i) := key

theorem nu_W {ν : X}
    (hνA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj ν).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x]))
    (hνt : ν * t * ν⁻¹ = s) (hνs : ν * s * ν⁻¹ = s * t) (i : Fin 3) :
    ∃ j : Fin 3, ν * Wf w₀ w₁ i * ν⁻¹ = Wf w₀ w₁ j := by
  obtain ⟨hα3, hαp⟩ := swap_vec i
  obtain ⟨c, hcΓ, hcA, hca⟩ := F.symm_gamma (Equiv.swap (pa i) (pb i)) hα3
  have hW : Wf w₀ w₁ i = aF s w₀ w₁ x (pa i) * (c * aF s w₀ w₁ x (pa i) * c⁻¹) := by
    rw [hca, hαp, Wf_eq_prod F.E5 i]
  obtain ⟨v, hv⟩ := (F.E5.mem_closure_iff (ν * aF s w₀ w₁ x (pa i) * ν⁻¹)).mp
    ((mem_iff_of_map_eq hνA _).mpr (F.aF_mem _))
  have hc'Γ : ν * c * ν⁻¹ ∈ centralizer ({s, t} : Set X) := conj_mem_gamma Z.hs2 hνt hνs hcΓ
  have hc'A : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map
      (MulAut.conj (ν * c * ν⁻¹)).toMonoidHom =
        Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) := by
    apply map_eq_of_forall_mem
    intro a ha
    have h1 : ν⁻¹ * a * ν⁻¹⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) := by
      have := (mem_iff_of_map_eq hνA (ν⁻¹ * a * ν⁻¹⁻¹)).mp
      rw [show ν * (ν⁻¹ * a * ν⁻¹⁻¹) * ν⁻¹ = a by group] at this
      exact (mem_iff_of_map_eq hνA (ν⁻¹ * a * ν⁻¹⁻¹)).mp (by
        rw [show ν * (ν⁻¹ * a * ν⁻¹⁻¹) * ν⁻¹ = a by group]; exact ha)
    have h2 : c * (ν⁻¹ * a * ν⁻¹⁻¹) * c⁻¹ ∈
        Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) := by
      have := (mem_iff_of_map_eq hcA (ν⁻¹ * a * ν⁻¹⁻¹)).mpr h1
      exact this
    have h3 := (mem_iff_of_map_eq hνA _).mpr h2
    rw [show ν * (c * (ν⁻¹ * a * ν⁻¹⁻¹) * c⁻¹) * ν⁻¹ = ν * c * ν⁻¹ * a * (ν * c * ν⁻¹)⁻¹ by
      group] at h3
    exact h3
  obtain ⟨u, hu0, hu1, hu4, hu⟩ := F.gamma_action hc'Γ hc'A v
  have hconj : ν * Wf w₀ w₁ i * ν⁻¹ = mono ![s, t, w₀, w₁, x] u := by
    calc ν * Wf w₀ w₁ i * ν⁻¹
        = ν * (aF s w₀ w₁ x (pa i) * (c * aF s w₀ w₁ x (pa i) * c⁻¹)) * ν⁻¹ := by rw [← hW]
      _ = (ν * aF s w₀ w₁ x (pa i) * ν⁻¹) *
            ((ν * c * ν⁻¹) * (ν * aF s w₀ w₁ x (pa i) * ν⁻¹) * (ν * c * ν⁻¹)⁻¹) := by group
      _ = mono ![s, t, w₀, w₁, x] v *
            ((ν * c * ν⁻¹) * mono ![s, t, w₀, w₁, x] v * (ν * c * ν⁻¹)⁻¹) := by rw [← hv]
      _ = mono ![s, t, w₀, w₁, x] v *
            (mono ![s, t, w₀, w₁, x] v * mono ![s, t, w₀, w₁, x] u) := by rw [hu]
      _ = mono ![s, t, w₀, w₁, x] u := by rw [← mul_assoc, F.E5.mono_self, one_mul]
  have hW1 : Wf w₀ w₁ i ≠ 1 := by
    rw [Wf_eq_mono F.E5 i]
    intro h
    exact wvec_ne_zero i (F.mono_injective (h.trans F.E5.mono_zero.symm))
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, F.E5.mono_zero] at hconj
    apply hW1
    have : Wf w₀ w₁ i = ν⁻¹ * 1 * ν := by
      rw [← hconj]; group
    rw [this]; group
  have hucases : u = wvec 0 ∨ u = wvec 1 ∨ u = wvec 2 := by
    have hu' : u = ![0, 0, u 2, u 3, 0] := by
      funext k
      fin_cases k <;> simp [hu0, hu1, hu4]
    rw [hu'] at hune ⊢
    exact cases_wvec _ _ hune
  rcases hucases with h | h | h
  · exact ⟨0, by rw [hconj, h, ← Wf_eq_mono F.E5 0]⟩
  · exact ⟨1, by rw [hconj, h, ← Wf_eq_mono F.E5 1]⟩
  · exact ⟨2, by rw [hconj, h, ← Wf_eq_mono F.E5 2]⟩

theorem exists_U_fix {ν : X}
    (hνA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj ν).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x]))
    (hνt : ν * t * ν⁻¹ = s) (hνs : ν * s * ν⁻¹ = s * t) :
    ∃ c ∈ centralizer ({s, t} : Set X),
      (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
        Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) ∧
      c * ν * w₀ * (c * ν)⁻¹ = w₀ ∧ c * ν * w₁ * (c * ν)⁻¹ = w₁ := by
  choose ψ hψ using F.nu_W hνA hνt hνs
  have hinj : Function.Injective ψ := by
    intro i i' h
    have h1 : ν * Wf w₀ w₁ i * ν⁻¹ = ν * Wf w₀ w₁ i' * ν⁻¹ := by rw [hψ, hψ, h]
    have h2 : Wf w₀ w₁ i = Wf w₀ w₁ i' := by simpa using h1
    rw [Wf_eq_mono F.E5, Wf_eq_mono F.E5] at h2
    exact wvec_injective (F.mono_injective h2)
  have hbij : Function.Bijective ψ := Finite.injective_iff_bijective.mp hinj
  obtain ⟨c, hcΓ, hcA, hcW⟩ := F.symm_W (Equiv.ofBijective ψ hbij).symm
  have key : ∀ i, c * ν * Wf w₀ w₁ i * (c * ν)⁻¹ = Wf w₀ w₁ i := by
    intro i
    calc c * ν * Wf w₀ w₁ i * (c * ν)⁻¹ = c * (ν * Wf w₀ w₁ i * ν⁻¹) * c⁻¹ := by group
      _ = c * Wf w₀ w₁ (ψ i) * c⁻¹ := by rw [hψ]
      _ = Wf w₀ w₁ ((Equiv.ofBijective ψ hbij).symm (ψ i)) := hcW _
      _ = Wf w₀ w₁ i := by
          congr 1
          exact (Equiv.ofBijective ψ hbij).symm_apply_apply i
  exact ⟨c, hcΓ, hcA, key 0, key 1⟩

theorem exists_nu {m r : X} (hmt : m * t * m⁻¹ = s) (hms : m * s * m⁻¹ = t)
    (hrt : r * t * r⁻¹ = t) (hrs : r * s * r⁻¹ = s * t) :
    ∃ ν : X, (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map
        (MulAut.conj ν).toMonoidHom = Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) ∧
      ν * t * ν⁻¹ = s ∧ ν * s * ν⁻¹ = s * t := by
  have hts : s * t = t * s := Z.hst
  have hω₀t : m * r * t * (m * r)⁻¹ = s := by
    calc m * r * t * (m * r)⁻¹ = m * (r * t * r⁻¹) * m⁻¹ := by group
      _ = s := by rw [hrt, hmt]
  have hω₀s : m * r * s * (m * r)⁻¹ = s * t := by
    calc m * r * s * (m * r)⁻¹ = m * (r * s * r⁻¹) * m⁻¹ := by group
      _ = m * (s * t) * m⁻¹ := by rw [hrs]
      _ = (m * s * m⁻¹) * (m * t * m⁻¹) := by group
      _ = t * s := by rw [hms, hmt]
      _ = s * t := hts.symm
  obtain ⟨f, hfΓ, hf⟩ := F.exists_conj_gamma hω₀t hω₀s
  have hfs : s * f = f * s := Subgroup.mem_centralizer_iff.mp hfΓ s (by simp)
  have hft : t * f = f * t := Subgroup.mem_centralizer_iff.mp hfΓ t (by simp)
  have hfs' : f⁻¹ * s * f = s := by
    calc f⁻¹ * s * f = f⁻¹ * (s * f) := by group
      _ = s := by rw [hfs]; group
  have hft' : f⁻¹ * t * f = t := by
    calc f⁻¹ * t * f = f⁻¹ * (t * f) := by group
      _ = t := by rw [hft]; group
  refine ⟨f⁻¹ * (m * r), ?_, ?_, ?_⟩
  · apply map_eq_of_forall_mem
    intro a ha
    have h1 : m * r * a * (m * r)⁻¹ ∈ (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map
        (MulAut.conj (m * r)).toMonoidHom := ⟨a, ha, rfl⟩
    rw [hf] at h1
    obtain ⟨a', ha', he⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    have h2 : f⁻¹ * (m * r) * a * (f⁻¹ * (m * r))⁻¹ = a' := by
      calc f⁻¹ * (m * r) * a * (f⁻¹ * (m * r))⁻¹ = f⁻¹ * (m * r * a * (m * r)⁻¹) * f := by group
        _ = f⁻¹ * (f * a' * f⁻¹) * f := by rw [he]
        _ = a' := by group
    rw [h2]
    exact ha'
  · calc f⁻¹ * (m * r) * t * (f⁻¹ * (m * r))⁻¹ = f⁻¹ * (m * r * t * (m * r)⁻¹) * f := by group
      _ = f⁻¹ * s * f := by rw [hω₀t]
      _ = s := hfs'
  · calc f⁻¹ * (m * r) * s * (f⁻¹ * (m * r))⁻¹ = f⁻¹ * (m * r * s * (m * r)⁻¹) * f := by group
      _ = f⁻¹ * (s * t) * f := by rw [hω₀s]
      _ = (f⁻¹ * s * f) * (f⁻¹ * t * f) := by group
      _ = s * t := by rw [hfs', hft']

theorem exists_omega {m r : X} (hmt : m * t * m⁻¹ = s) (hms : m * s * m⁻¹ = t)
    (hrt : r * t * r⁻¹ = t) (hrs : r * s * r⁻¹ = s * t) :
    ∃ ω : X, ω * t * ω⁻¹ = s ∧ ω * s * ω⁻¹ = s * t ∧ ω * w₀ * ω⁻¹ = w₀ ∧
      ω * w₁ * ω⁻¹ = w₁ ∧ ∃ v : Fin 5 → ZMod 2, v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧
        ω * x * ω⁻¹ = x * mono ![s, t, w₀, w₁, x] v := by
  obtain ⟨ν, hνA, hνt, hνs⟩ := F.exists_nu hmt hms hrt hrs
  obtain ⟨c, hcΓ, hcA, hc0, hc1⟩ := F.exists_U_fix hνA hνt hνs
  have hcs : s * c = c * s := Subgroup.mem_centralizer_iff.mp hcΓ s (by simp)
  have hct : t * c = c * t := Subgroup.mem_centralizer_iff.mp hcΓ t (by simp)
  have hcs' : c * s * c⁻¹ = s := by
    calc c * s * c⁻¹ = (c * s) * c⁻¹ := by group
      _ = s := by rw [← hcs]; group
  have hct' : c * t * c⁻¹ = t := by
    calc c * t * c⁻¹ = (c * t) * c⁻¹ := by group
      _ = t := by rw [← hct]; group
  have hν't : c * ν * t * (c * ν)⁻¹ = s := by
    calc c * ν * t * (c * ν)⁻¹ = c * (ν * t * ν⁻¹) * c⁻¹ := by group
      _ = s := by rw [hνt, hcs']
  have hν's : c * ν * s * (c * ν)⁻¹ = s * t := by
    calc c * ν * s * (c * ν)⁻¹ = c * (ν * s * ν⁻¹) * c⁻¹ := by group
      _ = (c * s * c⁻¹) * (c * t * c⁻¹) := by rw [hνs]; group
      _ = s * t := by rw [hcs', hct']
  have hν'A : ∀ a ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]),
      c * ν * a * (c * ν)⁻¹ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) := by
    intro a ha
    have h1 := (mem_iff_of_map_eq hνA a).mpr ha
    have h2 := (mem_iff_of_map_eq hcA _).mpr h1
    rw [show c * (ν * a * ν⁻¹) * c⁻¹ = c * ν * a * (c * ν)⁻¹ by group] at h2
    exact h2
  obtain ⟨ω, hodd, hωt, hωs, hω0, hω1, hωA⟩ :=
    odd_power Z.hst Z.hs2 hν't hν's hc0 hc1 hν'A
  obtain ⟨v, hv2, hv3, hv4, hvx⟩ := omega_fix F.E5 F.mono_injective hodd
    ⟨hωt, hωs, hω0, hω1⟩ (hωA x F.x_mem)
  exact ⟨ω, hωt, hωs, hω0, hω1, v, hv2, hv3, hv4, hvx⟩

end IsFrame

end CFSG.ComponentClassification.SolMax.Sig36.E32
