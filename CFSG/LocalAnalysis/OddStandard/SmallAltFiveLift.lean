module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveFull

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}
  {S : Sylow 2 (centralizer (L : Set G))} {t : G} {e : L ≃* alternatingGroup (Fin 5)}

theorem Full.x_normalizes_L (hf : Full L S t e) {x : G} (hx : x ∈ centralizer ({t} : Set G)) :
    zpowers x ≤ normalizer (L : Set G) :=
  (zpowers_le.mpr (hf.H_le_M hx))

theorem Full.mem_U_iff (hf : Full L S t e) {x : G} (hx : x ∈ centralizer ({t} : Set G))
    (hx2 : x * x = 1) (u : G) :
    u ∈ L ⊔ zpowers x ↔ ∃ l ∈ L, u = l ∨ u = l * x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L (zpowers x)
    (hf.x_normalizes_L hx), Set.mem_mul]
  constructor
  · rintro ⟨l, hl, y, hy, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 hy with rfl | rfl
    · exact ⟨l, hl, Or.inl (mul_one l)⟩
    · exact ⟨l, hl, Or.inr rfl⟩
  · rintro ⟨l, hl, rfl | rfl⟩
    · exact ⟨u, hl, 1, one_mem _, mul_one u⟩
    · exact ⟨l, hl, x, mem_zpowers x, rfl⟩

theorem Full.rhoAt_swap_of_outer (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S)
    (hx2 : x * x = 1) : ∃ i j : Fin 5, i ≠ j ∧ hf.rhoAt x = swap i j :=
  hf.exists_swap_of_involution Q hSQ hx hxA hx2

theorem Full.eq_one_of_rhoAt_eq_one_of_mem_U (hf : Full L S t e)
    (Q : Sylow 2 (centralizer ({t} : Set G))) (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q)
    (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S) (hx2 : x * x = 1) {u : G} (hu : u ∈ L ⊔ zpowers x)
    (h1 : hf.rhoAt u = 1) : u = 1 := by
  have hxH : x ∈ centralizer ({t} : Set G) := qg_le_H t Q hx
  obtain ⟨i, j, hij, hρx⟩ := hf.rhoAt_swap_of_outer Q hSQ hx hxA hx2
  obtain ⟨l, hl, hu' | hu'⟩ := (hf.mem_U_iff hxH hx2 u).1 hu
  · rw [hu', hf.rhoAt_of_mem_L hl] at h1
    have : e ⟨l, hl⟩ = 1 := Subtype.ext h1
    have h2 : (⟨l, hl⟩ : L) = 1 := e.injective (this.trans (map_one e).symm)
    rw [hu']
    exact congrArg Subtype.val h2
  · exfalso
    rw [hu', hf.rhoAt_mul (hf.L_le_H hl) hxH, hρx] at h1
    have h2 := congrArg Perm.sign h1
    rw [map_mul, hf.sign_rhoAt_of_mem_L hl, Perm.sign_swap hij, map_one] at h2
    exact absurd h2 (by decide)

theorem Full.exists_U_rhoAt_eq (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S)
    (hx2 : x * x = 1) (σ : Perm (Fin 5)) : ∃ u ∈ L ⊔ zpowers x, hf.rhoAt u = σ := by
  have hxH : x ∈ centralizer ({t} : Set G) := qg_le_H t Q hx
  obtain ⟨i, j, hij, hρx⟩ := hf.rhoAt_swap_of_outer Q hSQ hx hxA hx2
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · obtain ⟨l, hl⟩ := e.surjective ⟨σ, Perm.mem_alternatingGroup.mpr h1⟩
    refine ⟨l, mem_sup_left l.2, ?_⟩
    rw [hf.rhoAt_of_mem_L l.2]
    exact congrArg Subtype.val hl
  · have hs : Perm.sign (σ * swap i j) = 1 := by
      rw [map_mul, h1, Perm.sign_swap hij]
      decide
    obtain ⟨l, hl⟩ := e.surjective ⟨σ * swap i j, Perm.mem_alternatingGroup.mpr hs⟩
    refine ⟨l * x, Subgroup.mul_mem _ (mem_sup_left l.2) (mem_sup_right (mem_zpowers x)), ?_⟩
    rw [hf.rhoAt_mul (hf.L_le_H l.2) hxH, hf.rhoAt_of_mem_L l.2, hρx]
    have := congrArg Subtype.val hl
    simp only at this
    rw [this]
    simp

theorem Full.U_normalizes_sg (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) (hx2 : x * x = 1) {u v : G}
    (hu : u ∈ L ⊔ zpowers x) (hv : v ∈ sg L S) : u * v * u⁻¹ ∈ sg L S := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hLn : L ≤ normalizer ((sg L S : Subgroup G) : Set G) := fun l hl =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw =>
      (hf.L_comm_sg hl hw).symm)
  have hxn : zpowers x ≤ normalizer ((sg L S : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hf.conj_mem_sg Q hSQ hx hy, fun hy => ?_⟩
    have := hf.conj_mem_sg Q hSQ hx hy
    have e1 : x * (x * y * x⁻¹) * x⁻¹ = y := by
      calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
        _ = y := by rw [hx2]; group
    rwa [e1] at this
  exact (mem_normalizer_iff.mp (sup_le hLn hxn hu) v).mp hv

theorem Full.Kt_normalized (hf : Full L S t e) {h k : G} (hh : h ∈ centralizer ({t} : Set G))
    (hk : k ∈ oddKer L ⊓ centralizer ({t} : Set G)) :
    h * k * h⁻¹ ∈ oddKer L ⊓ centralizer ({t} : Set G) :=
  ⟨oddKer_normalized hf.sector (hf.H_le_M hh) hk.1,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hk.2) (Subgroup.inv_mem _ hh)⟩

theorem Full.Kt_inf_sg (hf : Full L S t e) :
    (oddKer L ⊓ centralizer ({t} : Set G)) ⊓ sg L S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have := (oddKer_complement hf.sector).2.1
  exact (eq_bot_iff.mp this) ⟨hx.1.1, hx.2⟩

theorem Full.R_decomp (hf : Full L S t e) {r : G}
    (hr : r ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :
    ∃ k ∈ oddKer L ⊓ centralizer ({t} : Set G), ∃ b ∈ sg L S, r = k * b := by
  have hr' : r ∈ (oddKer L : Set G) * (sg L S : Set G) := by
    rw [(oddKer_complement hf.sector).2.2]
    exact hr.1
  obtain ⟨k, hk, b, hb, hkb⟩ := hr'
  refine ⟨k, ⟨hk, ?_⟩, b, hb, hkb.symm⟩
  have : k = r * b⁻¹ := by rw [← hkb]; group
  rw [this]
  exact Subgroup.mul_mem _ hr.2 (Subgroup.inv_mem _ (sg_le_centralizer_t hf.sector hb))

end CFSG.OddStandard
