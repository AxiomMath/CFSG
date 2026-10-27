module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7End1

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

section Sylow

variable {P : Subgroup X} (hP2 : IsPGroup 2 P) (hSP : C.S₂ ≤ P)
include hP2 hSP

theorem swap_of_not_mem {h : X} (hhP : h ∈ P) (hh : h ∈ normalizer (C.S₂ : Set X))
    (hS : h ∉ C.S₂) : h * C.F.kF * h⁻¹ = S.z ∧ h * S.z * h⁻¹ = C.F.kF := by
  have key : ∀ {h : X}, h ∈ P → h ∈ normalizer (C.S₂ : Set X) → h ∉ C.S₂ →
      h * C.F.kF * h⁻¹ = S.z := fun {h} hhP hh hS =>
    (C.conj_k_cases hh).resolve_left fun hk => hS (C.mem_S₂_of_fix_k hP2 hSP hhP hh hk)
  refine ⟨key hhP hh hS, ?_⟩
  have h1 := key (inv_mem hhP) (inv_mem hh) (fun h' => hS (by simpa using inv_mem h'))
  calc h * S.z * h⁻¹ = h * (h⁻¹ * C.F.kF * h⁻¹⁻¹) * h⁻¹ := by rw [h1]
    _ = C.F.kF := by group

theorem mem_S₂_of_two {h₁ h₂ : X} (h₁P : h₁ ∈ P) (h₁N : h₁ ∈ normalizer (C.S₂ : Set X))
    (h₁S : h₁ ∉ C.S₂) (h₂P : h₂ ∈ P) (h₂N : h₂ ∈ normalizer (C.S₂ : Set X))
    (h₂S : h₂ ∉ C.S₂) : h₁⁻¹ * h₂ ∈ C.S₂ := by
  obtain ⟨hk₁, -⟩ := C.swap_of_not_mem hP2 hSP h₁P h₁N h₁S
  obtain ⟨hk₂, -⟩ := C.swap_of_not_mem hP2 hSP h₂P h₂N h₂S
  refine C.mem_S₂_of_fix_k hP2 hSP (mul_mem (inv_mem h₁P) h₂P) (mul_mem (inv_mem h₁N) h₂N) ?_
  rw [show h₁⁻¹ * h₂ * C.F.kF * (h₁⁻¹ * h₂)⁻¹ = h₁⁻¹ * (h₂ * C.F.kF * h₂⁻¹) * h₁ by group, hk₂,
    ← hk₁]
  group

end Sylow

theorem comm_Fv_inv {s c : X} (h : ∀ f ∈ C.Fv, s * f * s⁻¹ * f⁻¹ ∈ zpowers c) {a : X}
    (ha : a ∈ C.Fv) : a * s * a⁻¹ * s⁻¹ ∈ zpowers c := by
  rw [show a * s * a⁻¹ * s⁻¹ = (s * a * s⁻¹ * a⁻¹)⁻¹ by group]
  exact inv_mem (h a ha)

theorem zk_not_mem_zpowers_z : S.z * C.F.kF ∉ zpowers S.z := fun h => by
  rcases eq_one_or_eq_of_mem_zpowers z_sq h with h' | h'
  · exact C.ne_one_zk h'
  · exact C.zk_ne_z h'

theorem zk_not_mem_zpowers_k : S.z * C.F.kF ∉ zpowers C.F.kF := fun h => by
  rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq h with h' | h'
  · exact C.ne_one_zk h'
  · exact C.zk_ne_k h'

section R

variable (P : Sylow 2 X) (hSP : C.S₂ ≤ P)
include hSP

omit hSP in
theorem S₂_ne_P : C.S₂ ≠ P := fun h => C.z_ne_k (by
  refine C.eq_of_mem_center P (h ▸ C.Zz_le_S₂ (mem_sup_left (mem_zpowers _)))
    (h ▸ C.Zz_le_S₂ (mem_sup_right (mem_zpowers _))) (fun x hx => ?_) (fun x hx => ?_)
    S.z_ne_one C.ne_one_k
  · rw [← h] at hx
    calc S.z * x = (x * S.z * x⁻¹) * x := by rw [C.S₂_z hx]
      _ = x * S.z := by group
  · rw [← h] at hx
    calc C.F.kF * x = (x * C.F.kF * x⁻¹) * x := by rw [C.S₂_k hx]
      _ = x * C.F.kF := by group)

theorem exists_g : ∃ g ∈ (P : Subgroup X), g ∉ C.S₂ ∧ g ∈ normalizer (C.S₂ : Set X) :=
  exists_mem_normalizer_of_lt P.isPGroup' hSP (C.S₂_ne_P P)

abbrev R : Subgroup X := (P : Subgroup X) ⊓ normalizer (C.S₂ : Set X)

theorem S₂_le_R : C.S₂ ≤ C.R P := le_inf hSP le_normalizer

theorem swapR {r : X} (hr : r ∈ C.R P) (hS : r ∉ C.S₂) :
    r * C.F.kF * r⁻¹ = S.z ∧ r * S.z * r⁻¹ = C.F.kF :=
  C.swap_of_not_mem P.isPGroup' hSP hr.1 hr.2 hS

theorem zk_central {r : X} (hr : r ∈ C.R P) : r * (S.z * C.F.kF) * r⁻¹ = S.z * C.F.kF := by
  by_cases hS : r ∈ C.S₂
  · exact C.S₂_Zz hS (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))
  · obtain ⟨hk, hz⟩ := C.swapR P hSP hr hS
    rw [conj_mul_eq, hz, hk, C.kz]

theorem center_R {c : X} (hc : c ∈ C.R P) (hcc : ∀ r ∈ C.R P, c * r = r * c) :
    c = 1 ∨ c = S.z * C.F.kF := by
  obtain ⟨g, hgP, hgS, hgN⟩ := C.exists_g P hSP
  have hgR : g ∈ C.R P := ⟨hgP, hgN⟩
  obtain ⟨hgk, hgz⟩ := C.swapR P hSP hgR hgS
  have hcS : c ∈ C.S₂ := by
    by_contra hS
    obtain ⟨-, hz⟩ := C.swapR P hSP hc hS
    have h1 := hcc S.z (C.S₂_le_R P hSP (C.Zz_le_S₂ (mem_sup_left (mem_zpowers _))))
    rw [show c * S.z * c⁻¹ = S.z by rw [h1, mul_inv_cancel_right]] at hz
    exact C.z_ne_k hz
  have hcZ := C.mem_Zz_of_center hcS fun s hs => hcc s (C.S₂_le_R P hSP hs)
  have hgc : g * c * g⁻¹ = c := by rw [← hcc g hgR, mul_inv_cancel_right]
  rcases C.Zz_cases hcZ with h | h | h | h
  · exact Or.inl h
  · rw [h] at hgc; exact absurd (hgc.symm.trans hgz) C.z_ne_k
  · rw [h] at hgc; exact absurd (hgc.symm.trans hgk) (Ne.symm C.z_ne_k)
  · exact Or.inr h

theorem comm_z_R {r : X} (hr : r ∈ C.R P) :
    S.z * r * S.z⁻¹ * r⁻¹ = 1 ∨ S.z * r * S.z⁻¹ * r⁻¹ = S.z * C.F.kF := by
  by_cases hS : r ∈ C.S₂
  · left
    rw [show S.z * r * S.z⁻¹ * r⁻¹ = S.z * (r * S.z * r⁻¹)⁻¹ by group, C.S₂_z hS, mul_inv_cancel]
  · right
    obtain ⟨-, hz⟩ := C.swapR P hSP hr hS
    rw [show S.z * r * S.z⁻¹ * r⁻¹ = S.z * (r * S.z * r⁻¹)⁻¹ by group, hz,
      inv_eq_of_mul_eq_one_right C.kk]

theorem mem_Zz_of_Z₂R {a : X} (ha : a ∈ C.R P)
    (h : ∀ r ∈ C.R P, a * r * a⁻¹ * r⁻¹ = 1 ∨ a * r * a⁻¹ * r⁻¹ = S.z * C.F.kF) : a ∈ C.Zz := by
  have hZ : ∀ r ∈ C.R P, a * r * a⁻¹ * r⁻¹ ∈ C.Zz := fun r hr => by
    rcases h r hr with h' | h' <;> rw [h']
    · exact one_mem _
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  have htR : S.t ∈ C.R P := C.S₂_le_R P hSP C.t_mem_S₂
  by_cases hS : a ∈ C.S₂
  · have haF := C.mem_Fv_of_Z₂ hS fun s hs => hZ s (C.S₂_le_R P hSP hs)
    have hu := C.comm_Fv_inv ((C.fixV_iff C.u_mem_S₂).mp C.u_v') haF
    have ht := C.comm_Fv_inv ((C.fixY_iff C.t_mem_S₂).mp C.t_y) haF
    have hu1 : a * C.D₁.u * a⁻¹ * C.D₁.u⁻¹ = 1 := by
      rcases h _ (C.S₂_le_R P hSP C.u_mem_S₂) with h' | h'
      · exact h'
      · exact absurd (h' ▸ hu) C.zk_not_mem_zpowers_z
    have ht1 : a * S.t * a⁻¹ * S.t⁻¹ = 1 := by
      rcases h _ htR with h' | h'
      · exact h'
      · exact absurd (h' ▸ ht) C.zk_not_mem_zpowers_k
    have haE : a ∈ C.E₀ := by
      rcases C.Fv_cases haF with he | ⟨e, he, rfl⟩
      · exact he
      · exfalso
        have h1 : S.t * (e * C.v') * S.t⁻¹ = e * C.v' := by
          calc S.t * (e * C.v') * S.t⁻¹ =
                (e * C.v' * S.t * (e * C.v')⁻¹ * S.t⁻¹)⁻¹ * (e * C.v') := by group
            _ = e * C.v' := by rw [ht1, inv_one, one_mul]
        rw [conj_mul_eq, conj_eq_of_comm (C.t_comm_E0 he), C.t_v'] at h1
        exact C.ne_one_k (by simpa using h1)
    refine C.mem_zk_of_mem_E0 haE ?_
    calc C.D₁.u * a * C.D₁.u⁻¹ = (a * C.D₁.u * a⁻¹ * C.D₁.u⁻¹)⁻¹ * a := by group
      _ = a := by rw [hu1, inv_one, one_mul]
  · exfalso
    obtain ⟨hk, hz⟩ := C.swapR P hSP ha hS
    have haN : a ∈ normalizer (C.S₂ : Set X) := ha.2
    have hatS : a * S.t * a⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp haN _).mp C.t_mem_S₂
    obtain ⟨c, hcZ, hc⟩ : ∃ c ∈ C.Zz, a * S.t * a⁻¹ = c * S.t :=
      ⟨_, hZ _ htR, by group⟩
    have hy : (a * S.t * a⁻¹) * C.F.yF * (a * S.t * a⁻¹)⁻¹ = C.F.yF := by
      rw [hc, show c * S.t * C.F.yF * (c * S.t)⁻¹ = c * (S.t * C.F.yF * S.t⁻¹) * c⁻¹ by group,
        C.t_y, conj_eq_of_comm (C.comm_E0 (C.Zz_le_E0 hcZ) C.y_mem_E0)]
    have h1 := C.comm_conj_zpowers (inv_mem haN) ((C.fixY_iff hatS).mp hy)
    rw [show a⁻¹ * (a * S.t * a⁻¹) * a⁻¹⁻¹ = S.t by group,
      show a⁻¹ * C.F.kF * a⁻¹⁻¹ = S.z by
        rw [← hz]; group] at h1
    have hv := (C.fixV_iff C.t_mem_S₂).mpr h1
    rw [C.t_v'] at hv
    exact C.ne_one_k (by simpa using hv)

theorem P_le_normalizer : (P : Subgroup X) ≤ normalizer (C.S₂ : Set X) := by
  by_contra hne
  have hRP : C.R P ≠ P := fun h => hne (h ▸ inf_le_right)
  obtain ⟨n, hnP, hnR, hnN⟩ := exists_mem_normalizer_of_lt P.isPGroup' inf_le_left hRP
  apply hnR
  refine ⟨hnP, mem_normalizer_of_map_le ?_⟩
  have hconjR : ∀ {m : X}, m ∈ normalizer ((C.R P : Subgroup X) : Set X) → ∀ {r : X},
      r ∈ C.R P → m * r * m⁻¹ ∈ C.R P := fun {m} hm {r} hr => (mem_normalizer_iff.mp hm r).mp hr
  have hzk : n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹ = S.z * C.F.kF := by
    have hc : n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹ ∈ C.R P := hconjR (inv_mem hnN)
      (C.S₂_le_R P hSP (mul_mem (C.Zz_le_S₂ (mem_sup_left (mem_zpowers _)))
        (C.Zz_le_S₂ (mem_sup_right (mem_zpowers _)))))
    have hcc : ∀ r ∈ C.R P, n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹ * r =
        r * (n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹) := fun r hr => by
      have hr' := C.zk_central P hSP (hconjR hnN hr)
      calc n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹ * r =
            n⁻¹ * ((S.z * C.F.kF) * (n * r * n⁻¹)) * n⁻¹⁻¹ := by group
        _ = n⁻¹ * ((n * r * n⁻¹) * (S.z * C.F.kF) * (n * r * n⁻¹)⁻¹ * (n * r * n⁻¹)) * n⁻¹⁻¹ :=
            by rw [hr']
        _ = r * (n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹) := by group
    rcases C.center_R P hSP hc hcc with h | h
    · exfalso
      exact C.ne_one_zk (by
        calc S.z * C.F.kF = n * (n⁻¹ * (S.z * C.F.kF) * n⁻¹⁻¹) * n⁻¹ := by group
          _ = 1 := by rw [h]; group)
    · exact h
  have hzZ : n⁻¹ * S.z * n⁻¹⁻¹ ∈ C.Zz := by
    refine C.mem_Zz_of_Z₂R P hSP (hconjR (inv_mem hnN)
      (C.S₂_le_R P hSP (C.Zz_le_S₂ (mem_sup_left (mem_zpowers _))))) fun r hr => ?_
    have hr' := hconjR hnN hr
    rw [show n⁻¹ * S.z * n⁻¹⁻¹ * r * (n⁻¹ * S.z * n⁻¹⁻¹)⁻¹ * r⁻¹ =
      n⁻¹ * (S.z * (n * r * n⁻¹) * S.z⁻¹ * (n * r * n⁻¹)⁻¹) * n⁻¹⁻¹ by group]
    rcases C.comm_z_R P hSP hr' with h | h <;> rw [h]
    · left; group
    · right; exact hzk
  rintro _ ⟨s, hs, rfl⟩
  show n * s * n⁻¹ ∈ C.S₂
  have hsR : n * s * n⁻¹ ∈ C.R P := hconjR hnN (C.S₂_le_R P hSP hs)
  by_contra hS
  obtain ⟨-, hz⟩ := C.swapR P hSP hsR hS
  have h1 : n * s * n⁻¹ * S.z * (n * s * n⁻¹)⁻¹ = S.z := by
    have h2 := C.S₂_Zz hs hzZ
    calc n * s * n⁻¹ * S.z * (n * s * n⁻¹)⁻¹ =
          n * (s * (n⁻¹ * S.z * n⁻¹⁻¹) * s⁻¹) * n⁻¹ := by group
      _ = S.z := by rw [h2]; group
  exact C.z_ne_k (h1.symm.trans hz)

end R

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
