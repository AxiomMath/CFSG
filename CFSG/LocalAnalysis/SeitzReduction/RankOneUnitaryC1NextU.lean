module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem normalizer_U_le_normalizer_szA₁ :
    normalizer (U : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := fun n hn =>
  mem_normalizer_iff.mpr fun b => ⟨fun hb => H.conj_mem_szA₁ hn hb, fun hb => by
    have := H.conj_mem_szA₁ (inv_mem hn) hb
    rwa [show n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b by group] at this⟩

theorem u3C1U_V₁_le :
    u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t ≤ normalizer (U : Set G) := by
  rw [← H.stage.szR_V₁_eq H.lam]
  exact u3C1U_le_normalizer

theorem normalizer_le_normalizer_u3C1U_V₁ :
    normalizer (U : Set G) ≤
      normalizer (u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t : Set G) := by
  have hR := H.stage.szR_V₁_eq H.lam
  have h := le_normalizer_u3C1U (L := L) (T := T) (R₂ := U₁ ⊓ centralizer (szT₁ L T : Set G))
    (t := t) (by rw [hR]; exact H.stage.normalizer_U_le_normalizer_T₁ H.mu H.lam H.nu)
    (by rw [hR]; exact H.normalizer_U_le_normalizer_szA₁)
  rwa [hR] at h

theorem U_le_u3C1U_V₁ : U ≤ u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t := by
  intro x hx
  refine ⟨by rw [H.stage.szR_V₁_eq H.lam]; exact le_normalizer hx,
    mem_centralizer_iff.mpr fun b hb => ?_,
    H.stage.normalizer_U_le_normalizer_T₁ H.mu H.lam H.nu (le_normalizer hx),
    fun y hy => H.stage.conj_T₁ x hx y hy⟩
  calc b * x = (x * b * x⁻¹) * x := by rw [H.stage.conj_szA₁ x hx b hb]
    _ = x * b := by group

theorem perm_u3C1U_V₁ {x : G} (hx : x ∈ u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t)
    (s : K) : H.perm ⟨x, H.u3C1U_V₁_le hx⟩ s = H.perm ⟨x, H.u3C1U_V₁_le hx⟩ 0 + s :=
  H.perm_eq_add_of_conj_szA₁ _ (fun _ hb => U3Start.conj_szA₁_of_mem_u3C1U hx hb) s

theorem mem_U_of_mem_u3C1U_V₁ {x : G}
    (hx : x ∈ u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t)
    (h0 : H.perm ⟨x, H.u3C1U_V₁_le hx⟩ 0 = 0) : x ∈ U := by
  obtain ⟨x₁, hx₁, hm⟩ := H.mem_U₁_mul_centralizer ⟨x, H.u3C1U_V₁_le hx⟩ h0
  have hx₁U' := H.U_le_u3C1U_V₁ (H.stage.U₁_le hx₁)
  have hmU' : x₁⁻¹ * x ∈ u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t :=
    mul_mem (inv_mem hx₁U') hx
  obtain ⟨-, hmC, hmT, hmtriv⟩ := hmU'
  have hmA : x₁⁻¹ * x ∈ normalizer (szA L T t : Set G) :=
    U3Start.mem_normalizer_szA_of_conj_t_mem (b := 1) (centralizer_le_normalizer _ hmC) (one_mem _)
      (by rw [mem_centralizer_singleton_iff.mp hm, mul_inv_cancel_right, one_mul])
  have hmR : x₁⁻¹ * x ∈ u3R₁ L T t ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨⟨hmA, hmC, hmT, hmtriv⟩, hm⟩
  rw [H.stage.start.u3R₁_inf_centralizer_of_card_sylow H.stage.card_sylow] at hmR
  have hmU : x₁⁻¹ * x ∈ U :=
    sup_le (H.stage.T₁_le_U₁.trans H.stage.U₁_le) (zpowers_le.mpr H.stage.t_mem_U) hmR
  have e : x = x₁ * (x₁⁻¹ * x) := by group
  rw [e]
  exact mul_mem (H.stage.U₁_le hx₁) hmU

@[expose] noncomputable def regPre (E : Subgroup (Equiv.Perm K)) : Subgroup G :=
  (E.comap H.perm).map (normalizer (U : Set G)).subtype

theorem mem_regPre {E : Subgroup (Equiv.Perm K)} {x : G} :
    x ∈ H.regPre E ↔ ∃ hx : x ∈ normalizer (U : Set G), H.perm ⟨x, hx⟩ ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxE⟩
    exact ⟨⟨x, hx⟩, hxE, rfl⟩

theorem perm_conj_d_zero {x : G} (hxN : x ∈ normalizer (U : Set G))
    (hdx : d⁻¹ * x * d ∈ normalizer (U : Set G)) :
    H.perm ⟨d⁻¹ * x * d, hdx⟩ 0 = μ * H.perm ⟨x, hxN⟩ 0 := by
  set δ : normalizer (U : Set G) := ⟨d⁻¹, inv_mem H.d_mem_normalizer_U⟩ with hδ
  have e : (⟨d⁻¹ * x * d, hdx⟩ : normalizer (U : Set G)) = δ * ⟨x, hxN⟩ * δ⁻¹ :=
    Subtype.ext (by simp [hδ])
  have hδ0 : H.perm δ⁻¹ 0 = 0 := by
    have h3 := H.perm_d_inv 0
    rw [mul_zero] at h3
    rw [← h3, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply,
      h3]
  rw [e, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hδ0, H.perm_d_inv]

theorem mu_ne_zero : μ ≠ 0 := by
  intro h0
  obtain ⟨b, hb, hb1⟩ := H.coords.surj 1
  have h1 := H.coords.conj b hb
  rw [h0, zero_mul] at h1
  have h2 := H.coords.eq_one_of_v_eq_zero (H.coords.conj_mem b hb) h1
  have h3 : b = 1 := by
    calc b = d * (d⁻¹ * b * d) * d⁻¹ := by group
      _ = 1 := by rw [h2]; group
  rw [h3, H.coords.v_one] at hb1
  exact zero_ne_one hb1

end U3C1Next

end CFSG.SeitzReduction.RankOne
