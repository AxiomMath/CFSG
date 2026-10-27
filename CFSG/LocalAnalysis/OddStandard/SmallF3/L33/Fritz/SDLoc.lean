module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDict

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

theorem mem_normalizer_closure {s : Set X} {g : X}
    (h : ∀ a ∈ s, g * a * g⁻¹ ∈ closure s) : g ∈ normalizer (closure s : Set X) := by
  have hmap : (closure s).map (MulAut.conj g : X →* X) ≤ closure s := by
    rw [MonoidHom.map_closure]
    exact (Subgroup.closure_le (K := closure s)).mpr (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)
  have hcard : Nat.card (closure s) ≤ Nat.card ((closure s).map (MulAut.conj g : X →* X)) :=
    (Subgroup.card_map_of_injective (f := (MulAut.conj g : X →* X))
      (MulAut.conj g).injective).ge
  have heq : (closure s).map (MulAut.conj g : X →* X) = closure s :=
    Subgroup.eq_of_le_of_card_ge hmap hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hy' : g * y * g⁻¹ ∈ (closure s).map (MulAut.conj g : X →* X) :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rwa [heq] at hy'
  · intro hy
    rw [← heq] at hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have : x = y := (MulAut.conj g).injective hxy
    rwa [this] at hx

include ctx

private theorem commute_of_actX_conj {b : X} (hb : b ∈ centralizer ({t} : Set X)) {a : ↥L}
    (h : ctx.actX b * MulAut.conj a = MulAut.conj a * ctx.actX b) :
    b * (a : X) = (a : X) * b := by
  have hfix : ctx.actX b a = a := by
    apply ctx.conj_injective
    have hconj : MulAut.conj (ctx.actX b a)
        = ctx.actX b * MulAut.conj a * (ctx.actX b)⁻¹ := by
      ext u
      simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
        MulAut.apply_inv_self]
    rw [hconj, h, mul_assoc, mul_inv_cancel, mul_one]
  have happ := ctx.actX_apply hb a
  rw [hfix] at happ
  have hb' : b * (a : X) * b⁻¹ = (a : X) := happ.symm
  calc b * (a : X) = b * (a : X) * b⁻¹ * b := by group
    _ = (a : X) * b := by rw [hb']

theorem commute_k_of_inner {a : ↥L} (ha : ∀ u : ↥L, ctx.M.F.g₁ u = a * u * a⁻¹) :
    (a : X) * ctx.C.k = ctx.C.k * a := by
  have hg1 : ctx.M.F.g₁ = MulAut.conj a :=
    MulEquiv.ext (fun u => by rw [MulAut.conj_apply]; exact ha u)
  have hkg1 : ctx.M.F.k * MulAut.conj a = MulAut.conj a * ctx.M.F.k := by
    have h := ctx.M.F.g₁_k
    rw [hg1] at h
    have h' := congrArg (fun x => x * MulAut.conj a) h
    simpa [mul_assoc] using h'.symm
  have hk_act : ctx.actX ctx.C.k * MulAut.conj a = MulAut.conj a * ctx.actX ctx.C.k := by
    rw [ctx.actX_k]
    exact hkg1
  exact (ctx.commute_of_actX_conj ctx.k_mem_centralizer hk_act).symm

theorem commute_zk_of_inner {a : ↥L} (ha : ∀ u : ↥L, ctx.M.F.g₂ u = a * u * a⁻¹) :
    (a : X) * (ctx.S.z * ctx.C.k) = (ctx.S.z * ctx.C.k) * a := by
  have hg2 : ctx.M.F.g₂ = MulAut.conj a :=
    MulEquiv.ext (fun u => by rw [MulAut.conj_apply]; exact ha u)
  have hzC : ctx.S.z ∈ centralizer ({t} : Set X) := ctx.A.T_le_centralizer ctx.S.z_mem.1
  have hzk_act : ctx.actX (ctx.S.z * ctx.C.k)
      = MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k := by
    rw [ctx.actX_mul hzC ctx.k_mem_centralizer, ctx.actX_k, ctx.z_eq, ctx.actX_of_mem_L]
  have hcomm : (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) * MulAut.conj a
      = MulAut.conj a * (MulAut.conj (ctx.M.F.x ^ 4) * ctx.M.F.k) := by
    have h := ctx.M.F.g₂_zk
    rw [hg2] at h
    have h' := congrArg (fun x => x * MulAut.conj a) h
    simpa [mul_assoc] using h'.symm
  have hzk_act' : ctx.actX (ctx.S.z * ctx.C.k) * MulAut.conj a
      = MulAut.conj a * ctx.actX (ctx.S.z * ctx.C.k) := by
    rw [hzk_act]
    exact hcomm
  have hzkC : ctx.S.z * ctx.C.k ∈ centralizer ({t} : Set X) :=
    mul_mem hzC ctx.k_mem_centralizer
  exact (ctx.commute_of_actX_conj hzkC hzk_act').symm

theorem d_y : ∃ g ∈ centralizer ({t} : Set X),
    g ∈ normalizer (closure {ctx.S.x₀ ^ 2, ctx.S.y₀, t, ctx.C.k} : Set X) ∧
      g * ctx.S.x₀ ^ 2 * g⁻¹ = ctx.S.y₀ ∧ g * ctx.S.y₀ * g⁻¹ = ctx.S.x₀ ^ 2 * ctx.S.y₀ ∧
        g * ctx.C.k * g⁻¹ = ctx.C.k := by
  obtain ⟨a, ha⟩ := ctx.M.F.g₁_inner
  have hcomm := ctx.commute_k_of_inner ha
  have hz_eq : ctx.S.x₀ ^ 2 = ((ctx.M.F.x ^ 4 : ↥L) : X) := ctx.z_eq
  have hza : (a : X) * ctx.S.x₀ ^ 2 * (a : X)⁻¹ = ctx.S.y₀ := by
    have h' : (a * ctx.M.F.x ^ 4 * a⁻¹ : ↥L) = ctx.M.F.y := by
      rw [← ha (ctx.M.F.x ^ 4)]
      exact ctx.M.F.g₁_z
    rw [hz_eq, ctx.y0_eq]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun z : ↥L => (z : X)) h'
  have hya : (a : X) * ctx.S.y₀ * (a : X)⁻¹ = ctx.S.x₀ ^ 2 * ctx.S.y₀ := by
    have h' : (a * ctx.M.F.y * a⁻¹ : ↥L) = ctx.M.F.x ^ 4 * ctx.M.F.y := by
      rw [← ha ctx.M.F.y]
      exact ctx.M.F.g₁_y
    rw [ctx.y0_eq, hz_eq]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun z : ↥L => (z : X)) h'
  have hka : (a : X) * ctx.C.k * (a : X)⁻¹ = ctx.C.k := by
    rw [hcomm]
    group
  have hta : (a : X) * t * (a : X)⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp (ctx.L_le_centralizer a.2)]
    group
  refine ⟨(a : X), ctx.L_le_centralizer a.2, ?_, hza, hya, hka⟩
  apply mem_normalizer_closure
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rw [hza]; exact subset_closure (by simp)
  · rw [hya]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [hta]; exact subset_closure (by simp)
  · rw [hka]; exact subset_closure (by simp)

theorem d_xy : ∃ g ∈ centralizer ({t} : Set X),
    g ∈ normalizer (closure {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k} : Set X) ∧
      g * ctx.S.x₀ ^ 2 * g⁻¹ = ctx.S.x₀ * ctx.S.y₀ ∧
        g * (ctx.S.x₀ * ctx.S.y₀) * g⁻¹ = ctx.S.x₀ ^ 2 * (ctx.S.x₀ * ctx.S.y₀) ∧
          g * (ctx.S.x₀ ^ 2 * ctx.C.k) * g⁻¹ = ctx.S.x₀ ^ 2 * ctx.C.k := by
  obtain ⟨a, ha⟩ := ctx.M.F.g₂_inner
  have hg2inv : ctx.M.F.g₂⁻¹ = ctx.M.F.g₂ ^ 2 := by
    have h : ctx.M.F.g₂ * ctx.M.F.g₂ ^ 2 = 1 := by
      rw [← pow_succ']
      simpa using ctx.M.F.g₂_pow
    exact inv_eq_of_mul_eq_one_right h
  have hg2inv_apply : ∀ u : ↥L, ctx.M.F.g₂⁻¹ u = a⁻¹ * u * a := by
    intro u
    rw [show ctx.M.F.g₂ = MulAut.conj a from
      MulEquiv.ext (fun v => by rw [MulAut.conj_apply]; exact ha v)]
    exact MulAut.conj_inv_apply a u
  have h1 : ctx.M.F.g₂⁻¹ (ctx.M.F.x ^ 4) = ctx.M.F.x ^ 6 * ctx.M.F.y := by
    rw [hg2inv, pow_two, MulAut.mul_apply, ctx.M.F.g₂_z, ctx.M.F.g₂_w]
    group
  have h6 : ctx.M.F.x ^ 6 * ctx.M.F.y = ctx.M.F.x ^ 4 * (ctx.M.F.x ^ 2 * ctx.M.F.y) := by
    rw [← mul_assoc, ← pow_add]
  have h2 : ctx.M.F.g₂⁻¹ (ctx.M.F.x ^ 6 * ctx.M.F.y) = ctx.M.F.x ^ 2 * ctx.M.F.y := by
    rw [hg2inv, h6, ← ctx.M.F.g₂_w]
    rw [← MulAut.mul_apply, ← pow_succ]
    show (ctx.M.F.g₂ ^ 3) (ctx.M.F.x ^ 2 * ctx.M.F.y) = ctx.M.F.x ^ 2 * ctx.M.F.y
    rw [ctx.M.F.g₂_pow]
    rfl
  have hx10 : ctx.M.F.x ^ 10 = ctx.M.F.x ^ 2 := by
    have h : ctx.M.F.x ^ 10 = ctx.M.F.x ^ 8 * ctx.M.F.x ^ 2 := by
      rw [← pow_add]
    rw [h, ctx.M.F.x_pow_eight, one_mul]
  have hw : ctx.M.F.x ^ 4 * (ctx.M.F.x ^ 6 * ctx.M.F.y) = ctx.M.F.x ^ 2 * ctx.M.F.y := by
    rw [← mul_assoc, ← pow_add]
    change ctx.M.F.x ^ 10 * ctx.M.F.y = ctx.M.F.x ^ 2 * ctx.M.F.y
    rw [hx10]
  have hza' : (a⁻¹ * ctx.M.F.x ^ 4 * a : ↥L) = ctx.M.F.x ^ 6 * ctx.M.F.y := by
    rw [← hg2inv_apply (ctx.M.F.x ^ 4)]
    exact h1
  have hxy' : (a⁻¹ * (ctx.M.F.x ^ 6 * ctx.M.F.y) * a : ↥L)
      = ctx.M.F.x ^ 4 * (ctx.M.F.x ^ 6 * ctx.M.F.y) := by
    rw [← hg2inv_apply (ctx.M.F.x ^ 6 * ctx.M.F.y)]
    rw [h2]
    exact hw.symm
  have hz_eq : ctx.S.x₀ ^ 2 = ((ctx.M.F.x ^ 4 : ↥L) : X) := ctx.z_eq
  have hza : ((a⁻¹ : ↥L) : X) * ctx.S.x₀ ^ 2 * ((a⁻¹ : ↥L) : X)⁻¹
      = ctx.S.x₀ * ctx.S.y₀ := by
    rw [hz_eq, ctx.x0_eq, ctx.y0_eq]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun z : ↥L => (z : X)) hza'
  have hxy : ((a⁻¹ : ↥L) : X) * (ctx.S.x₀ * ctx.S.y₀) * ((a⁻¹ : ↥L) : X)⁻¹
      = ctx.S.x₀ ^ 2 * (ctx.S.x₀ * ctx.S.y₀) := by
    rw [hz_eq, ctx.x0_eq, ctx.y0_eq]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun z : ↥L => (z : X)) hxy'
  have hcomm_zk : (ctx.S.x₀ ^ 2 * ctx.C.k) * (a : X)
      = (a : X) * (ctx.S.x₀ ^ 2 * ctx.C.k) := (ctx.commute_zk_of_inner ha).symm
  have hzk : ((a⁻¹ : ↥L) : X) * (ctx.S.x₀ ^ 2 * ctx.C.k) * ((a⁻¹ : ↥L) : X)⁻¹
      = ctx.S.x₀ ^ 2 * ctx.C.k := by
    rw [Subgroup.coe_inv, inv_inv]
    calc (a : X)⁻¹ * (ctx.S.x₀ ^ 2 * ctx.C.k) * (a : X)
        = (a : X)⁻¹ * ((ctx.S.x₀ ^ 2 * ctx.C.k) * (a : X)) := by group
      _ = (a : X)⁻¹ * ((a : X) * (ctx.S.x₀ ^ 2 * ctx.C.k)) := by rw [hcomm_zk]
      _ = ctx.S.x₀ ^ 2 * ctx.C.k := by group
  have ht : ((a⁻¹ : ↥L) : X) * t * ((a⁻¹ : ↥L) : X)⁻¹ = t := by
    rw [Subgroup.coe_inv]
    rw [mem_centralizer_singleton_iff.mp (ctx.L_le_centralizer (inv_mem a.2))]
    group
  have hk : ((a⁻¹ : ↥L) : X) * ctx.C.k * ((a⁻¹ : ↥L) : X)⁻¹ ∈
      closure {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k} := by
    have hzk_in : ctx.S.x₀ ^ 2 * ctx.C.k ∈
        closure {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k} :=
      mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have hxy_in : ctx.S.x₀ * ctx.S.y₀ ∈
        closure {ctx.S.x₀ ^ 2, ctx.S.x₀ * ctx.S.y₀, t, ctx.C.k} :=
      subset_closure (by simp)
    have h1' : ((a⁻¹ : ↥L) : X) * (ctx.S.x₀ ^ 2)⁻¹ * ((a⁻¹ : ↥L) : X)⁻¹
        = (ctx.S.x₀ * ctx.S.y₀)⁻¹ := by
      rw [show ((a⁻¹ : ↥L) : X) * (ctx.S.x₀ ^ 2)⁻¹ * ((a⁻¹ : ↥L) : X)⁻¹
          = (((a⁻¹ : ↥L) : X) * ctx.S.x₀ ^ 2 * ((a⁻¹ : ↥L) : X)⁻¹)⁻¹ by group, hza]
    have hmid : ((a⁻¹ : ↥L) : X) * ctx.C.k * ((a⁻¹ : ↥L) : X)⁻¹
        = (ctx.S.x₀ * ctx.S.y₀)⁻¹ * (ctx.S.x₀ ^ 2 * ctx.C.k) := by
      calc ((a⁻¹ : ↥L) : X) * ctx.C.k * ((a⁻¹ : ↥L) : X)⁻¹
          = ((a⁻¹ : ↥L) : X) * ((ctx.S.x₀ ^ 2)⁻¹ * (ctx.S.x₀ ^ 2 * ctx.C.k))
              * ((a⁻¹ : ↥L) : X)⁻¹ := by group
        _ = (((a⁻¹ : ↥L) : X) * (ctx.S.x₀ ^ 2)⁻¹ * ((a⁻¹ : ↥L) : X)⁻¹)
              * (((a⁻¹ : ↥L) : X) * (ctx.S.x₀ ^ 2 * ctx.C.k)
                * ((a⁻¹ : ↥L) : X)⁻¹) := by group
        _ = (ctx.S.x₀ * ctx.S.y₀)⁻¹ * (ctx.S.x₀ ^ 2 * ctx.C.k) := by rw [h1', hzk]
    rw [hmid]
    exact mul_mem (inv_mem hxy_in) hzk_in
  refine ⟨((a⁻¹ : ↥L) : X), ctx.L_le_centralizer (inv_mem a.2), ?_, hza, hxy, hzk⟩
  apply mem_normalizer_closure
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rw [hza]; exact subset_closure (by simp)
  · rw [hxy]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [ht]; exact subset_closure (by simp)
  · exact hk

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
