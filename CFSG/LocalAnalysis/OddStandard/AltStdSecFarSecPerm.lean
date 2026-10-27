module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarChain

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm Subgroup

section Gen

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem comm_fixSub_compl {F : Finset α} {x s : Perm α} (hx : x ∈ fixSub Fᶜ) (hs : s ∈ fixSub F) :
    x * s = s * x := by
  refine Perm.Disjoint.commute (fun i => ?_)
  by_cases hi : i ∈ F
  · exact Or.inr (hs i hi)
  · exact Or.inl (hx i (by simpa using hi))

theorem mem_of_comm_of_transitive {F : Finset α} {R : Subgroup (Perm α)} (hRF : R ≤ fixSub Fᶜ)
    (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (htr : ∀ i ∈ F, ∀ j ∈ F, ∃ r ∈ R, r i = j) {i₀ : α} (hi₀ : i₀ ∈ F) {x : Perm α}
    (hxF : x ∈ fixSub Fᶜ) (hxR : ∀ r ∈ R, x * r = r * x) : x ∈ R := by
  have hxi₀ : x i₀ ∈ F := by
    by_contra h
    have := hxF (x i₀) (by simpa using h)
    exact h (by rw [x.injective this]; exact hi₀)
  obtain ⟨r, hr, hri⟩ := htr i₀ hi₀ (x i₀) hxi₀
  have hfix : ∀ i, (r⁻¹ * x) i = i := by
    intro i
    by_cases hi : i ∈ F
    · obtain ⟨s, hs, hsi⟩ := htr i₀ hi₀ i hi
      have h1 : (r⁻¹ * x) * s = s * (r⁻¹ * x) := by
        rw [mul_assoc, hxR s hs, ← mul_assoc, ← mul_assoc]
        congr 1
        have := hRab r hr s hs
        calc r⁻¹ * s = r⁻¹ * (s * r) * r⁻¹ := by group
          _ = r⁻¹ * (r * s) * r⁻¹ := by rw [this]
          _ = s * r⁻¹ := by group
      have h2 := DFunLike.congr_fun h1 i₀
      simp only [Perm.mul_apply] at h2
      rw [← hsi]
      rw [show (r⁻¹ * x) (s i₀) = s ((r⁻¹ * x) i₀) by
        simpa [Perm.mul_apply] using h2]
      congr 1
      simp [Perm.mul_apply, ← hri]
    · have h1 : x i = i := hxF i (by simpa using hi)
      have h2 : r⁻¹ i = i := by
        rw [Perm.inv_eq_iff_eq]
        exact (hRF hr i (by simpa using hi)).symm
      simp [Perm.mul_apply, h1, h2]
  have : r⁻¹ * x = 1 := Equiv.ext hfix
  have hx : x = r := by
    calc x = r * (r⁻¹ * x) := by group
      _ = r := by rw [this, mul_one]
  rw [hx]; exact hr

theorem exists_mul_of_mem_centralizer {F : Finset α} {R : Subgroup (Perm α)}
    (hRF : R ≤ fixSub Fᶜ) (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (htr : ∀ i ∈ F, ∀ j ∈ F, ∃ r ∈ R, r i = j) (hF2 : 2 ≤ F.card) {x : Perm α}
    (hx : ∀ r ∈ R, x * r = r * x) : ∃ r ∈ R, ∃ s ∈ fixSub F, x = r * s := by
  classical
  have hmove : ∀ i ∈ F, ∃ r ∈ R, r i ≠ i := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < F.card) i
    obtain ⟨r, hr, hri⟩ := htr i hi j hj
    exact ⟨r, hr, by rw [hri]; exact hji⟩
  have hout : ∀ y : Perm α, (∀ r ∈ R, y * r = r * y) → ∀ i, i ∉ F → y i ∉ F := by
    intro y hy i hi hyi
    obtain ⟨r, hr, hri⟩ := hmove (y i) hyi
    apply hri
    have h1 := DFunLike.congr_fun (hy r hr) i
    simp only [Perm.mul_apply] at h1
    rw [← h1, hRF hr i (by simpa using hi)]
  have hxinv : ∀ r ∈ R, x⁻¹ * r = r * x⁻¹ := by
    intro r hr
    have := hx r hr
    calc x⁻¹ * r = x⁻¹ * (r * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * r) * x⁻¹ := by rw [this]
      _ = r * x⁻¹ := by group
  have hpres : ∀ i, x i ∈ F ↔ i ∈ F := by
    intro i
    constructor
    · intro hxi
      by_contra hi
      exact hout x hx i hi hxi
    · intro hi
      by_contra hxi
      have := hout x⁻¹ hxinv (x i) hxi
      have h2 : x⁻¹ (x i) = i := by simp
      rw [h2] at this
      exact this hi
  set r₀ : Perm α := Perm.ofSubtype (x.subtypePerm (p := (· ∈ F)) hpres) with hr₀
  have hr₀F : ∀ i, i ∈ F → r₀ i = x i := fun i hi => by
    rw [hr₀]; exact Perm.ofSubtype_apply_of_mem _ hi
  have hr₀fix : r₀ ∈ fixSub Fᶜ := fun i hi => by
    rw [hr₀]; exact Perm.ofSubtype_apply_of_not_mem _ (by simpa using hi)
  have hs : r₀⁻¹ * x ∈ fixSub F := by
    intro i hi
    simp only [Perm.mul_apply]
    rw [← hr₀F i hi]
    simp
  have hscomm : ∀ r ∈ R, (r₀⁻¹ * x) * r = r * (r₀⁻¹ * x) := fun r hr =>
    (comm_fixSub_compl (hRF hr) hs).symm
  have hr₀R : ∀ r ∈ R, r₀ * r = r * r₀ := by
    intro r hr
    have h1 : r₀ = x * (r₀⁻¹ * x)⁻¹ := by group
    rw [h1]
    calc x * (r₀⁻¹ * x)⁻¹ * r = x * ((r₀⁻¹ * x)⁻¹ * r) := by group
      _ = x * (r * (r₀⁻¹ * x)⁻¹) := by
        congr 1
        have := hscomm r hr
        calc (r₀⁻¹ * x)⁻¹ * r = (r₀⁻¹ * x)⁻¹ * (r * (r₀⁻¹ * x)) * (r₀⁻¹ * x)⁻¹ := by group
          _ = (r₀⁻¹ * x)⁻¹ * ((r₀⁻¹ * x) * r) * (r₀⁻¹ * x)⁻¹ := by rw [this]
          _ = r * (r₀⁻¹ * x)⁻¹ := by group
      _ = (x * r) * (r₀⁻¹ * x)⁻¹ := by group
      _ = (r * x) * (r₀⁻¹ * x)⁻¹ := by rw [hx r hr]
      _ = r * (x * (r₀⁻¹ * x)⁻¹) := by group
  obtain ⟨i₀, hi₀⟩ : F.Nonempty := Finset.card_pos.1 (by omega)
  refine ⟨r₀, mem_of_comm_of_transitive hRF hRab htr hi₀ hr₀fix hr₀R, r₀⁻¹ * x, hs, by group⟩

theorem eq_one_of_fixes_of_transitive {F : Finset α} {R : Subgroup (Perm α)}
    (hRF : R ≤ fixSub Fᶜ) (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (htr : ∀ i ∈ F, ∀ j ∈ F, ∃ r ∈ R, r i = j) {r : Perm α} (hr : r ∈ R) {p : α} (hp : p ∈ F)
    (hrp : r p = p) : r = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ F
  · obtain ⟨s, hs, hsi⟩ := htr p hp i hi
    have h1 := DFunLike.congr_fun (hRab r hr s hs) p
    simp only [Perm.mul_apply, hrp] at h1
    rw [← hsi, Perm.one_apply]
    exact h1
  · exact hRF hr i (by simpa using hi)

theorem support_eq_of_transitive {F : Finset α} {R : Subgroup (Perm α)}
    (hRF : R ≤ fixSub Fᶜ) (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (htr : ∀ i ∈ F, ∀ j ∈ F, ∃ r ∈ R, r i = j) {r : Perm α} (hr : r ∈ R) (h1 : r ≠ 1) :
    r.support = F := by
  ext i
  rw [mem_support]
  constructor
  · intro hi
    by_contra hiF
    exact hi (hRF hr i (by simpa using hiF))
  · intro hiF hri
    exact h1 (eq_one_of_fixes_of_transitive hRF hRab htr hr hiF hri)

end Gen

section Incl

variable {m : ℕ}

theorem exists_inclPerm_eq {σ : Perm (Fin (m + 3))} (h1 : σ ⟨m + 1, by omega⟩ = ⟨m + 1, by omega⟩)
    (h2 : σ ⟨m + 2, by omega⟩ = ⟨m + 2, by omega⟩) : ∃ σ' : Perm (Fin (m + 1)), inclPerm m σ' = σ := by
  have hfix : ∀ x : Fin (m + 3), ¬ (x : ℕ) < m + 1 → σ x = x := by
    intro x hx
    rcases (by omega : (x : ℕ) = m + 1 ∨ (x : ℕ) = m + 2) with h | h
    · have : x = ⟨m + 1, by omega⟩ := Fin.ext h
      rw [this, h1]
    · have : x = ⟨m + 2, by omega⟩ := Fin.ext h
      rw [this, h2]
  have hp : ∀ x : Fin (m + 3), (σ x : ℕ) < m + 1 ↔ (x : ℕ) < m + 1 := by
    intro x
    constructor
    · intro h
      by_contra hx
      rw [hfix x hx] at h
      exact hx h
    · intro hx
      by_contra h
      have := hfix (σ x) h
      rw [σ.injective this] at h
      exact h hx
  set τ : Perm {i : Fin (m + 3) // (i : ℕ) < m + 1} := σ.subtypePerm hp with hτ
  refine ⟨(finIncl m).permCongr.symm τ, ?_⟩
  apply Equiv.ext
  intro x
  show (((finIncl m).permCongr.symm τ).extendDomain (finIncl m)) x = σ x
  by_cases hx : (x : ℕ) < m + 1
  · rw [Perm.extendDomain_apply_subtype _ (finIncl m) (b := x) hx]
    simp [Equiv.permCongr_apply, hτ]
  · rw [Perm.extendDomain_apply_not_subtype _ (finIncl m) (b := x) hx, hfix x hx]

end Incl

section Four

variable {N : ℕ}

@[expose] def fourSet (N : ℕ) : Finset (Fin N) := Finset.univ.filter fun i => (i : ℕ) < 4

theorem mem_fourSet {i : Fin N} : i ∈ fourSet N ↔ (i : ℕ) < 4 := by simp [fourSet]

@[expose] def fin4Equiv (hN : 4 ≤ N) : Fin 4 ≃ {i : Fin N // (i : ℕ) < 4} where
  toFun i := ⟨⟨i, by omega⟩, i.2⟩
  invFun j := ⟨j.1, j.2⟩
  left_inv i := rfl
  right_inv j := rfl

@[expose] noncomputable def emb4 (hN : 4 ≤ N) : Perm (Fin 4) →* Perm (Fin N) :=
  Perm.extendDomainHom (fin4Equiv hN)

theorem emb4_apply_image (hN : 4 ≤ N) (x : Perm (Fin 4)) (i : Fin 4) :
    emb4 hN x ⟨i, by omega⟩ = ⟨x i, by omega⟩ := by
  exact Perm.extendDomain_apply_image x (fin4Equiv hN) i

theorem emb4_mem_fixSub (hN : 4 ≤ N) (x : Perm (Fin 4)) : emb4 hN x ∈ fixSub (fourSet N)ᶜ := by
  intro i hi
  simp only [Finset.mem_compl, mem_fourSet] at hi
  exact Perm.extendDomain_apply_not_subtype x (fin4Equiv hN) (b := i) hi

@[expose] noncomputable def kleinA (hN : 4 ≤ N) : Perm (Fin N) := emb4 hN (swap 0 1 * swap 2 3)

@[expose] noncomputable def kleinB (hN : 4 ≤ N) : Perm (Fin N) := emb4 hN (swap 0 2 * swap 1 3)

@[expose] noncomputable def cycC (hN : 4 ≤ N) : Perm (Fin N) :=
  emb4 hN (swap 0 3 * swap 0 1 * swap 0 2)

@[expose] noncomputable def kleinR (hN : 4 ≤ N) : Subgroup (Perm (Fin N)) :=
  closure {kleinA hN, kleinB hN}

@[expose] noncomputable def cycR (hN : 4 ≤ N) : Subgroup (Perm (Fin N)) := zpowers (cycC hN)

theorem kleinA_mul_kleinB (hN : 4 ≤ N) : kleinA hN * kleinB hN = kleinB hN * kleinA hN := by
  rw [kleinA, kleinB, ← map_mul, ← map_mul]
  congr 1
  decide

theorem cycC_sq (hN : 4 ≤ N) : cycC hN * cycC hN = kleinA hN := by
  rw [cycC, kleinA, ← map_mul]
  congr 1
  decide

theorem kleinR_le (hN : 4 ≤ N) : kleinR hN ≤ fixSub (fourSet N)ᶜ := by
  rw [kleinR, closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact emb4_mem_fixSub hN _
  · exact emb4_mem_fixSub hN _

theorem cycR_le (hN : 4 ≤ N) : cycR hN ≤ fixSub (fourSet N)ᶜ :=
  zpowers_le.2 (emb4_mem_fixSub hN _)

theorem kleinR_comm (hN : 4 ≤ N) : ∀ r ∈ kleinR hN, ∀ s ∈ kleinR hN, r * s = s * r := by
  have h1 : kleinR hN ≤ centralizer ({kleinA hN, kleinB hN} : Set (Perm (Fin N))) := by
    rw [kleinR, closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact (kleinA_mul_kleinB hN).symm
    · exact kleinA_mul_kleinB hN
    · rfl
  intro r hr s hs
  have h2 : kleinR hN ≤ centralizer ({r} : Set (Perm (Fin N))) := by
    rw [kleinR, closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 (h1 hr) x hx)
  exact (mem_centralizer_singleton_iff.1 (h2 hs)).symm

theorem cycR_comm (hN : 4 ≤ N) : ∀ r ∈ cycR hN, ∀ s ∈ cycR hN, r * s = s * r := by
  intro r hr s hs
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
  obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hs
  rw [← zpow_add, ← zpow_add, add_comm]

theorem transitive_of_base {F : Finset (Fin N)} {R : Subgroup (Perm (Fin N))} {p : Fin N}
    (hp : ∀ i ∈ F, ∃ r ∈ R, r p = i) : ∀ i ∈ F, ∀ j ∈ F, ∃ r ∈ R, r i = j := by
  intro i hi j hj
  obtain ⟨r, hr, hri⟩ := hp i hi
  obtain ⟨s, hs, hsj⟩ := hp j hj
  refine ⟨s * r⁻¹, mul_mem hs (inv_mem hr), ?_⟩
  rw [Perm.mul_apply, ← hri]
  simp [hsj]

theorem transitive_emb4 (hN : 4 ≤ N) {R : Subgroup (Perm (Fin N))}
    (h4 : ∀ i : Fin 4, ∃ x : Perm (Fin 4), emb4 hN x ∈ R ∧ x 0 = i) :
    ∀ i ∈ fourSet N, ∀ j ∈ fourSet N, ∃ r ∈ R, r i = j := by
  refine transitive_of_base (p := ⟨0, by omega⟩) (fun i hi => ?_)
  rw [mem_fourSet] at hi
  obtain ⟨x, hx, hx0⟩ := h4 ⟨i, hi⟩
  refine ⟨emb4 hN x, hx, ?_⟩
  apply Fin.ext
  have h1 : emb4 hN x ⟨0, by omega⟩ = ⟨x 0, by omega⟩ := emb4_apply_image hN x 0
  rw [h1]
  show ((x 0 : Fin 4) : ℕ) = i
  rw [hx0]

theorem kleinR_transitive (hN : 4 ≤ N) :
    ∀ i ∈ fourSet N, ∀ j ∈ fourSet N, ∃ r ∈ kleinR hN, r i = j := by
  have hA : kleinA hN ∈ kleinR hN := subset_closure (by simp)
  have hB : kleinB hN ∈ kleinR hN := subset_closure (by simp)
  refine transitive_emb4 hN (fun i => ?_)
  fin_cases i
  · exact ⟨1, by rw [map_one]; exact one_mem _, rfl⟩
  · exact ⟨swap 0 1 * swap 2 3, hA, by decide⟩
  · exact ⟨swap 0 2 * swap 1 3, hB, by decide⟩
  · exact ⟨(swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3),
      by rw [map_mul]; exact mul_mem hA hB, by decide⟩

theorem cycR_transitive (hN : 4 ≤ N) :
    ∀ i ∈ fourSet N, ∀ j ∈ fourSet N, ∃ r ∈ cycR hN, r i = j := by
  have hC : cycC hN ∈ cycR hN := mem_zpowers _
  refine transitive_emb4 hN (fun i => ?_)
  fin_cases i
  · exact ⟨1, by rw [map_one]; exact one_mem _, rfl⟩
  · exact ⟨(swap 0 3 * swap 0 1 * swap 0 2) * (swap 0 3 * swap 0 1 * swap 0 2),
      by rw [map_mul]; exact mul_mem hC hC, by decide⟩
  · exact ⟨swap 0 3 * swap 0 1 * swap 0 2, hC, by decide⟩
  · exact ⟨(swap 0 3 * swap 0 1 * swap 0 2) * (swap 0 3 * swap 0 1 * swap 0 2) *
      (swap 0 3 * swap 0 1 * swap 0 2), by rw [map_mul, map_mul]; exact mul_mem (mul_mem hC hC) hC,
      by decide⟩

theorem card_fourSet (hN : 4 ≤ N) : (fourSet N).card = 4 := by
  have h := Fintype.card_congr (fin4Equiv hN)
  rw [Fintype.card_fin, Fintype.card_subtype] at h
  simpa [fourSet] using h.symm

theorem kleinA_mem_kleinR (hN : 4 ≤ N) : kleinA hN ∈ kleinR hN := subset_closure (by simp)

theorem kleinA_mem_cycR (hN : 4 ≤ N) : kleinA hN ∈ cycR hN := by
  rw [← cycC_sq]
  exact mul_mem (mem_zpowers _) (mem_zpowers _)

end Four

end CFSG.OddStandard.AltStdSec
