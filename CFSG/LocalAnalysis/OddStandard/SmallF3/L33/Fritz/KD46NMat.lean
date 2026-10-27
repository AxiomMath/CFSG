module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NSyl

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C}

namespace Inst

variable (I : Inst S)

@[expose] def Mat (n : X) (c : Fin 4 → V4) : Prop :=
  ∃ h : n ∈ normalizer (I.E : Set X), ∀ i, I.μ ⟨n, h⟩ (bas i) = c i

theorem mem_E0_iff {e : X} : e ∈ S.E0 I.yi I.ki ↔ ∃ a b d : Fin 2, e = I.wV (a, b, 0, d) := by
  constructor
  · intro he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp [wV]⟩
      · exact ⟨0, 1, 0, by simp [wV]⟩
      · exact ⟨0, 0, 1, by simp [wV]⟩
    | one => exact ⟨0, 0, 0, by simp [wV]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, d, rfl⟩ := hx
      obtain ⟨a', b', d', rfl⟩ := hy
      exact ⟨a + a', b + b', d + d', by rw [← I.wV_add]; simp [addV]⟩
    | inv x _ hx =>
      obtain ⟨a, b, d, rfl⟩ := hx
      exact ⟨a, b, d, inv_eq_of_mul_eq_one_right
        (by rw [← pow_two]; exact I.sq_eq_one (I.wV_mem _))⟩
  · rintro ⟨a, b, d, rfl⟩
    have hz : S.z ∈ S.E0 I.yi I.ki := subset_closure (by simp)
    have hy : I.yi ∈ S.E0 I.yi I.ki := subset_closure (by simp)
    have hk : I.ki ∈ S.E0 I.yi I.ki := subset_closure (by simp)
    simp only [wV, Fin.val_zero, pow_zero, mul_one]
    exact mul_mem (mul_mem (pow_mem hz _) (pow_mem hy _)) (pow_mem hk _)

theorem E0_le_E : S.E0 I.yi I.ki ≤ I.E := fun e he => by
  obtain ⟨a, b, d, rfl⟩ := (I.mem_E0_iff).mp he
  exact I.wV_mem _

variable {I}

namespace Mat

theorem mem {n : X} {c : Fin 4 → V4} (h : I.Mat n c) : n ∈ normalizer (I.E : Set X) := h.1

theorem conj {n : X} {c : Fin 4 → V4} (h : I.Mat n c) (w : V4) :
    n * I.wV w * n⁻¹ = I.wV (lin c w) := by
  obtain ⟨hn, hc⟩ := h
  have h1 := I.conj_wV ⟨n, hn⟩ w
  rw [I.μ_eq_lin, show (fun i => I.μ ⟨n, hn⟩ (bas i)) = c from funext hc] at h1
  exact h1

theorem conj_bas {n : X} {c : Fin 4 → V4} (h : I.Mat n c) (i : Fin 4) :
    n * I.wV (bas i) * n⁻¹ = I.wV (c i) := by
  rw [h.conj, lin_bas]

theorem conj_z {n : X} {c : Fin 4 → V4} (h : I.Mat n c) : n * S.z * n⁻¹ = I.wV (c 0) := by
  rw [← h.conj_bas 0, I.wV_bas_zero]

theorem conj_yi {n : X} {c : Fin 4 → V4} (h : I.Mat n c) : n * I.yi * n⁻¹ = I.wV (c 1) := by
  rw [← h.conj_bas 1, I.wV_bas_one]

theorem conj_t {n : X} {c : Fin 4 → V4} (h : I.Mat n c) : n * t * n⁻¹ = I.wV (c 2) := by
  rw [← h.conj_bas 2, I.wV_bas_two]

theorem conj_ki {n : X} {c : Fin 4 → V4} (h : I.Mat n c) : n * I.ki * n⁻¹ = I.wV (c 3) := by
  rw [← h.conj_bas 3, I.wV_bas_three]

theorem mk {n : X} (hn : n ∈ normalizer (I.E : Set X)) {c : Fin 4 → V4}
    (h0 : n * S.z * n⁻¹ = I.wV (c 0)) (h1 : n * I.yi * n⁻¹ = I.wV (c 1))
    (h2 : n * t * n⁻¹ = I.wV (c 2)) (h3 : n * I.ki * n⁻¹ = I.wV (c 3)) : I.Mat n c :=
  ⟨hn, I.μ_bas_of (n := ⟨n, hn⟩) h0 h1 h2 h3⟩

theorem mul {n m : X} {c₁ c₂ : Fin 4 → V4} (h₁ : I.Mat n c₁) (h₂ : I.Mat m c₂) :
    I.Mat (n * m) (comp c₁ c₂) :=
  ⟨mul_mem h₁.1 h₂.1, fun i => I.μ_comp (n := ⟨n, h₁.1⟩) (m := ⟨m, h₂.1⟩) h₁.2 h₂.2 i⟩

theorem unique {n : X} {c c' : Fin 4 → V4} (h : I.Mat n c) (h' : I.Mat n c') : c = c' := by
  funext i
  exact I.wV_injective ((h.conj_bas i).symm.trans (h'.conj_bas i))

theorem of_mem_centralizer {e : X} (he : e ∈ centralizer (I.E : Set X)) : I.Mat e bas :=
  ⟨I.centralizer_le_normalizer he, (I.μ_eq_id_iff _).mpr he⟩

theorem mem_centralizer {n : X} (h : I.Mat n bas) : n ∈ centralizer (I.E : Set X) :=
  (I.μ_eq_id_iff ⟨n, h.1⟩).mp h.2

theorem inv {n : X} {c c' : Fin 4 → V4} (h : I.Mat n c) (hc : ∀ i, comp c c' i = bas i) :
    I.Mat n⁻¹ c' := by
  refine ⟨inv_mem h.1, fun i => I.μ_eq_of ?_⟩
  have e := h.conj (c' i)
  rw [show lin c (c' i) = bas i from hc i] at e
  show n⁻¹ * I.wV (bas i) * n⁻¹⁻¹ = I.wV (c' i)
  rw [← e]
  group

theorem inv_mul_mem_centralizer {n m : X} {c : Fin 4 → V4} (hn : I.Mat n c) (hm : I.Mat m c) :
    n⁻¹ * m ∈ centralizer (I.E : Set X) := by
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨w, rfl⟩ := I.eq_wV hg
  have e : n * I.wV w * n⁻¹ = m * I.wV w * m⁻¹ := (hn.conj w).trans (hm.conj w).symm
  calc I.wV w * (n⁻¹ * m) = n⁻¹ * (n * I.wV w * n⁻¹) * m := by group
    _ = n⁻¹ * (m * I.wV w * m⁻¹) * m := by rw [e]
    _ = n⁻¹ * m * I.wV w := by group

theorem mul_central {n e : X} {c : Fin 4 → V4} (h : I.Mat n c)
    (he : e ∈ centralizer (I.E : Set X)) : I.Mat (n * e) c := by
  have := h.mul (of_mem_centralizer he)
  rwa [show comp c bas = c from funext fun i => lin_bas c i] at this

theorem central_mul {n e : X} {c : Fin 4 → V4} (h : I.Mat n c)
    (he : e ∈ centralizer (I.E : Set X)) : I.Mat (e * n) c := by
  have := (of_mem_centralizer he).mul h
  rwa [show comp bas c = c from funext fun i => lin_bas_self (c i)] at this

theorem pw {n : X} {c : Fin 4 → V4} (h : I.Mat n c) (e : Fin 2) :
    I.Mat (n ^ (e : ℕ)) (CFSG.ComponentClassification.HSFLit.pw c e) :=
  ⟨pow_mem h.1 _, fun i => I.μ_pw (n := ⟨n, h.1⟩) h.2 e i⟩

theorem pw3 {n : X} {c : Fin 4 → V4} (h : I.Mat n c) (e : Fin 3) :
    I.Mat (n ^ (e : ℕ)) (CFSG.ComponentClassification.HSFLit.pw3 c e) :=
  ⟨pow_mem h.1 _, fun i => I.μ_pw3 (n := ⟨n, h.1⟩) h.2 e i⟩

theorem mem_centralizer_t {n : X} {c : Fin 4 → V4} (h : I.Mat n c) (hc : c 2 = (0, 0, 1, 0)) :
    n ∈ centralizer ({t} : Set X) := by
  rw [mem_centralizer_singleton_iff]
  have e := h.conj_t
  rw [hc, show I.wV (0, 0, 1, 0) = t by simp [wV]] at e
  calc n * t = n * t * n⁻¹ * n := by group
    _ = t * n := by rw [e]

end Mat

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
