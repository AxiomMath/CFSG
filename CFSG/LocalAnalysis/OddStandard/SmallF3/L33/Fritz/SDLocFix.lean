module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDComm

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

private theorem actX_gen_z : ctx.actX ctx.S.z = MulAut.conj (ctx.M.F.x ^ 4) := by
  rw [ctx.z_eq, ctx.actX_of_mem_L]

private theorem actX_gen_y0 : ctx.actX ctx.S.y₀ = MulAut.conj ctx.M.F.y := by
  rw [ctx.y0_eq, ctx.actX_of_mem_L]

private theorem actX_gen_xy :
    ctx.actX (ctx.S.x₀ * ctx.S.y₀) = MulAut.conj (ctx.M.F.x ^ 6 * ctx.M.F.y) := by
  have h : ctx.S.x₀ * ctx.S.y₀ = ((ctx.M.F.x ^ 6 * ctx.M.F.y : ↥L) : X) := by
    rw [ctx.x0_eq, ctx.y0_eq]
    rfl
  rw [h, ctx.actX_of_mem_L]

private theorem actX_gen_t : ctx.actX t = 1 :=
  (ctx.actX_eq_one_iff SD.t_mem_C).mpr (Or.inr rfl)

private theorem actX_mem_closure_iff {gens : Set X} {T : Set (MulAut ↥L)}
    (hgens : ∀ g ∈ gens, g ∈ centralizer ({t} : Set X))
    (hmap : ∀ g ∈ gens, ctx.actX g ∈ closure T)
    (hinv : ∀ φ ∈ T, ∃ e ∈ closure gens, ctx.actX e = φ) :
    ∀ φ : MulAut ↥L, φ ∈ closure T ↔ ∃ e ∈ closure gens, ctx.actX e = φ := by
  have hE : closure gens ≤ centralizer ({t} : Set X) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hgens y hy
    | one => exact one_mem _
    | mul y z hy hz ihy ihz => exact mul_mem ihy ihz
    | inv y hy ihy => exact inv_mem ihy
  intro φ
  constructor
  · intro hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx => exact hinv x hx
    | one => exact ⟨1, one_mem _, ctx.actX_one⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨ex, hex, hexeq⟩ := ihx
        obtain ⟨ey, hey, heyeq⟩ := ihy
        exact ⟨ex * ey, mul_mem hex hey,
          by rw [ctx.actX_mul (hE hex) (hE hey), hexeq, heyeq]⟩
    | inv x hx ihx =>
        obtain ⟨ex, hex, hexeq⟩ := ihx
        exact ⟨ex⁻¹, inv_mem hex, by rw [ctx.actX_inv (hE hex), hexeq]⟩
  · intro ⟨e, he, heq⟩
    have key : ∀ x ∈ closure gens, ctx.actX x ∈ closure T := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy => exact hmap y hy
      | one => rw [ctx.actX_one]; exact one_mem _
      | mul y z hy hz ihy ihz =>
          rw [ctx.actX_mul (hE hy) (hE hz)]
          exact mul_mem ihy ihz
      | inv y hy ihy =>
          rw [ctx.actX_inv (hE hy)]
          exact inv_mem ihy
    rw [← heq]
    exact key e he

private theorem actX_mem_normalizer_of {gens : Set X} {T : Set (MulAut ↥L)}
    (hgens : ∀ g ∈ gens, g ∈ centralizer ({t} : Set X))
    (hmap : ∀ g ∈ gens, ctx.actX g ∈ closure T)
    (hinv : ∀ φ ∈ T, ∃ e ∈ closure gens, ctx.actX e = φ) {n : X}
    (hn : n ∈ normalizer (closure gens : Set X) ⊓ centralizer ({t} : Set X)) :
    ctx.actX n ∈ normalizer (closure T : Set (MulAut ↥L)) := by
  have himg := actX_mem_closure_iff ctx hgens hmap hinv
  obtain ⟨hnN, hnC⟩ := Subgroup.mem_inf.mp hn
  have hE : closure gens ≤ centralizer ({t} : Set X) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hgens y hy
    | one => exact one_mem _
    | mul y z hy hz ihy ihz => exact mul_mem ihy ihz
    | inv y hy ihy => exact inv_mem ihy
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  constructor
  · intro hφ
    obtain ⟨e, he, rfl⟩ := (himg φ).mp hφ
    have hne : n * e * n⁻¹ ∈ closure gens := (mem_normalizer_iff.mp hnN e).mp he
    have heq : ctx.actX n * ctx.actX e * (ctx.actX n)⁻¹ = ctx.actX (n * e * n⁻¹) := by
      rw [← ctx.actX_mul hnC (hE he), ← ctx.actX_inv hnC,
        ← ctx.actX_mul (mul_mem hnC (hE he)) (inv_mem hnC)]
    rw [heq]
    exact (himg _).mpr ⟨n * e * n⁻¹, hne, rfl⟩
  · intro hφ
    obtain ⟨e', he', he'eq⟩ := (himg _).mp hφ
    have hne' : n⁻¹ * e' * n ∈ closure gens := by
      simpa using (mem_normalizer_iff.mp (inv_mem hnN) e').mp he'
    have heq : ctx.actX (n⁻¹ * e' * n) = φ := by
      calc ctx.actX (n⁻¹ * e' * n)
          = ctx.actX (n⁻¹ * e') * ctx.actX n := by
            rw [ctx.actX_mul (mul_mem (inv_mem hnC) (hE he')) hnC]
        _ = ctx.actX n⁻¹ * ctx.actX e' * ctx.actX n := by
            rw [ctx.actX_mul (inv_mem hnC) (hE he')]
        _ = (ctx.actX n)⁻¹ * ctx.actX e' * ctx.actX n := by rw [ctx.actX_inv hnC]
        _ = φ := by rw [he'eq]; group
    exact (himg φ).mpr ⟨n⁻¹ * e' * n, hne', heq⟩

theorem actX_mem_normalizer_E1 {n : X}
    (hn : n ∈ normalizer (closure {ctx.S.x₀ ^ 2, ctx.S.y₀, t, ctx.C.k} : Set X) ⊓
      centralizer ({t} : Set X)) :
    ctx.actX n ∈ normalizer (closure {MulAut.conj (ctx.M.F.x ^ 4), MulAut.conj ctx.M.F.y,
      ctx.M.F.k} : Set (MulAut ↥L)) := by
  refine actX_mem_normalizer_of ctx (gens := {ctx.S.x₀ ^ 2, ctx.S.y₀, t, ctx.C.k})
    (T := {MulAut.conj (ctx.M.F.x ^ 4), MulAut.conj ctx.M.F.y, ctx.M.F.k}) ?_ ?_ ?_ hn
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ctx.L_le_centralizer (ctx.A.R_le_L ctx.S.z_mem)
    · exact ctx.L_le_centralizer (ctx.A.R_le_L ctx.S.y₀_mem)
    · exact SD.t_mem_C
    · exact ctx.k_mem_centralizer
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [actX_gen_z ctx]
      exact Subgroup.subset_closure (by simp)
    · rw [actX_gen_y0 ctx]
      exact Subgroup.subset_closure (by simp)
    · rw [actX_gen_t ctx]
      exact one_mem _
    · rw [ctx.actX_k]
      exact Subgroup.subset_closure (by simp)
  · intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact ⟨ctx.S.x₀ ^ 2, Subgroup.subset_closure (by simp), actX_gen_z ctx⟩
    · exact ⟨ctx.S.y₀, Subgroup.subset_closure (by simp), actX_gen_y0 ctx⟩
    · exact ⟨ctx.C.k, Subgroup.subset_closure (by simp), ctx.actX_k⟩

theorem actX_mem_normalizer_E2 {n : X}
    (hn : n ∈ normalizer (closure {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k} : Set X) ⊓
      centralizer ({t} : Set X)) :
    ctx.actX n ∈ normalizer (closure {MulAut.conj (ctx.M.F.x ^ 4),
      MulAut.conj (ctx.M.F.x ^ 2 * ctx.M.F.y), ctx.M.F.k} : Set (MulAut ↥L)) := by
  refine actX_mem_normalizer_of ctx (gens := {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k})
    (T := {MulAut.conj (ctx.M.F.x ^ 4), MulAut.conj (ctx.M.F.x ^ 2 * ctx.M.F.y),
      ctx.M.F.k}) ?_ ?_ ?_ hn
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ctx.L_le_centralizer (ctx.A.R_le_L ctx.S.z_mem)
    · exact ctx.L_le_centralizer (ctx.A.R_le_L (mul_mem ctx.S.x₀_mem ctx.S.y₀_mem))
    · exact SD.t_mem_C
    · exact ctx.k_mem_centralizer
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [actX_gen_z ctx]
      exact Subgroup.subset_closure (by simp)
    · rw [actX_gen_xy ctx]
      have hfac : ctx.M.F.x ^ 6 * ctx.M.F.y =
          ctx.M.F.x ^ 4 * (ctx.M.F.x ^ 2 * ctx.M.F.y) := by group
      have hconj : MulAut.conj (ctx.M.F.x ^ 6 * ctx.M.F.y) =
          MulAut.conj (ctx.M.F.x ^ 4) * MulAut.conj (ctx.M.F.x ^ 2 * ctx.M.F.y) := by
        rw [hfac]
        exact map_mul (MulAut.conj : ↥L →* MulAut ↥L) _ _
      rw [hconj]
      apply mul_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · rw [actX_gen_t ctx]
      exact one_mem _
    · rw [ctx.actX_k]
      exact Subgroup.subset_closure (by simp)
  · intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact ⟨ctx.S.x₀ ^ 2, Subgroup.subset_closure (by simp), actX_gen_z ctx⟩
    · refine ⟨(ctx.S.x₀ ^ 2)⁻¹ * (ctx.S.x₀ * ctx.S.y₀),
        mul_mem (inv_mem (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp)), ?_⟩
      have hzC : ctx.S.x₀ ^ 2 ∈ centralizer ({t} : Set X) :=
        ctx.L_le_centralizer (ctx.A.R_le_L ctx.S.z_mem)
      have hxyC : ctx.S.x₀ * ctx.S.y₀ ∈ centralizer ({t} : Set X) :=
        ctx.L_le_centralizer (ctx.A.R_le_L (mul_mem ctx.S.x₀_mem ctx.S.y₀_mem))
      rw [ctx.actX_mul (inv_mem hzC) hxyC, ctx.actX_inv hzC, actX_gen_z ctx, actX_gen_xy ctx]
      have h1 : (MulAut.conj (ctx.M.F.x ^ 4))⁻¹ =
          MulAut.conj ((ctx.M.F.x ^ 4)⁻¹) :=
        (map_inv (MulAut.conj : ↥L →* MulAut ↥L) (ctx.M.F.x ^ 4)).symm
      have h2 : MulAut.conj ((ctx.M.F.x ^ 4)⁻¹) *
            MulAut.conj (ctx.M.F.x ^ 6 * ctx.M.F.y) =
          MulAut.conj ((ctx.M.F.x ^ 4)⁻¹ * (ctx.M.F.x ^ 6 * ctx.M.F.y)) :=
        (map_mul (MulAut.conj : ↥L →* MulAut ↥L) _ _).symm
      rw [h1, h2]
      congr 1
      group
    · exact ⟨ctx.C.k, Subgroup.subset_closure (by simp), ctx.actX_k⟩

theorem k_fixed : ∀ n ∈ normalizer (closure {ctx.S.x₀ ^ 2, ctx.S.y₀, t, ctx.C.k} : Set X) ⊓
      centralizer ({t} : Set X), n * ctx.C.k * n⁻¹ = ctx.C.k := by
  intro n hn
  have hnorm := actX_mem_normalizer_E1 ctx hn
  have hfix := ctx.M.F.k_fixed (ctx.actX n) hnorm
  have hcomm : ctx.actX n * ctx.actX ctx.C.k = ctx.actX ctx.C.k * ctx.actX n := by
    rw [ctx.actX_k]
    have h2 : (ctx.actX n * ctx.M.F.k * (ctx.actX n)⁻¹) * ctx.actX n =
        ctx.actX n * ctx.M.F.k := by group
    rw [hfix] at h2
    exact h2.symm
  have hcomm' := comm_outer ctx (Or.inl rfl) (Subgroup.mem_inf.mp hn).2 hcomm
  calc n * ctx.C.k * n⁻¹ = ctx.C.k * n * n⁻¹ := by rw [hcomm']
    _ = ctx.C.k := by group

theorem zk_fixed : ∀ n ∈ normalizer (closure {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k} :
      Set X) ⊓ centralizer ({t} : Set X),
    n * (ctx.S.x₀ ^ 2 * ctx.C.k) * n⁻¹ = ctx.S.x₀ ^ 2 * ctx.C.k := by
  intro n hn
  have hnorm := actX_mem_normalizer_E2 ctx hn
  have hfix := ctx.M.F.zk_fixed (ctx.actX n) hnorm
  have hcomm : ctx.actX n * ctx.actX (ctx.S.x₀ ^ 2 * ctx.C.k) =
      ctx.actX (ctx.S.x₀ ^ 2 * ctx.C.k) * ctx.actX n := by
    have hzk : ctx.actX (ctx.S.x₀ ^ 2 * ctx.C.k) =
        MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k := by
      rw [ctx.actX_mul (ctx.L_le_centralizer (ctx.A.R_le_L ctx.S.z_mem))
        ctx.k_mem_centralizer, actX_gen_z ctx, ctx.actX_k]
    rw [hzk]
    have h2 : (ctx.actX n * (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) *
        (ctx.actX n)⁻¹) * ctx.actX n =
        ctx.actX n * (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) := by group
    rw [hfix] at h2
    exact h2.symm
  have hcomm' := comm_outer ctx (Or.inr rfl) (Subgroup.mem_inf.mp hn).2 hcomm
  calc n * (ctx.S.x₀ ^ 2 * ctx.C.k) * n⁻¹
      = (ctx.S.x₀ ^ 2 * ctx.C.k) * n * n⁻¹ := by rw [hcomm']
    _ = ctx.S.x₀ ^ 2 * ctx.C.k := by group

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
