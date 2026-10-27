module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD17A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD10
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem rho_conj_sq' {G : Type*} [Group G] {r g : G} (h : r ^ 3 = 1) :
    r * (r * g * r⁻¹) * r⁻¹ = r⁻¹ * g * r := by
  have h2 : r * r = r⁻¹ := by
    have h3 : r * (r * r) = 1 := by
      rw [show r * (r * r) = r ^ 3 by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]
        group]
      exact h
    exact eq_inv_of_mul_eq_one_right h3
  rw [show r * (r * g * r⁻¹) * r⁻¹ = (r * r) * g * (r * r)⁻¹ by group, h2, inv_inv]

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem no_T_invol_Mc {T : H → Prop} (hT : ZJClass T Q t τ l)
    (he16 : ∀ F : Subgroup H, F ≤ zjVh Mc t τ l → (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) →
      (∀ a ∈ F, a * a = 1) → Nat.card F = 16 → {u : H | u ∈ F ∧ T u}.ncard ≤ 4)
    {α : H} (hα : α ∈ Mc) (hαQ : α ∉ Q) (hα2 : α * α = 1) (hTα : T α) : False := by
  set α' : H := ρ * α * ρ⁻¹ with hα'def
  set α'' : H := ρ⁻¹ * α * ρ with hα''def
  have hα'Mc : α' ∈ Mc := by
    rw [hα'def]
    exact h.Mc_conj_rho hMh hMc hα
  have hα''Mc : α'' ∈ Mc := by
    have hρ : ρ * α' * ρ⁻¹ = α'' := by
      rw [hα'def, hα''def]
      exact rho_conj_sq' h.rho_pow_three
    rw [← hρ]
    exact h.Mc_conj_rho hMh hMc hα'Mc
  have hα'2 : α' * α' = 1 := by
    rw [hα'def]
    calc (ρ * α * ρ⁻¹) * (ρ * α * ρ⁻¹) = ρ * (α * α) * ρ⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  have hα''2 : α'' * α'' = 1 := by
    rw [hα''def]
    calc (ρ⁻¹ * α * ρ) * (ρ⁻¹ * α * ρ) = ρ⁻¹ * (α * α) * ρ := by group
      _ = 1 := by rw [hα2]; group
  have hα'Q : α' ∉ Q := by
    intro hQ
    apply hαQ
    have hconj : ρ⁻¹ * α' * ρ = α := by rw [hα'def]; group
    rw [← hconj]
    simpa using h.normal_Q ρ⁻¹ α' hQ
  have hα''Q : α'' ∉ Q := by
    intro hQ
    apply hαQ
    have hconj : ρ * α'' * ρ⁻¹ = α := by rw [hα''def]; group
    rw [← hconj]
    exact h.normal_Q ρ α'' hQ
  have hc : α * α' = α' * α := by
    rw [hα'def]
    exact h.Mc_comm_rho_eq_one hMh hMc hα
  have hVQ : V ≤ Q := fun x hx =>
    h.Y_le_Q (by rw [h.Y_eq]; exact Subgroup.mem_sup_left hx)
  set n : H := α * α' * α'' with hn_def
  have hnV : n ∈ V := by
    rw [hn_def, hα'def, hα''def]
    exact h.zjNorm_mem_V hMh hMc hα
  have hkey : α * α' = n * α'' := by
    have h1 : n * α'' = α * α' * α'' * α'' := by rw [hn_def]
    rw [h1]
    rw [show α * α' * α'' * α'' = α * α' * (α'' * α'') by group, hα''2, mul_one]
  have hα''key : α'' = n⁻¹ * (α * α') := by
    rw [hkey]
    group
  have hαα'Q : α * α' ∉ Q := by
    intro hQ
    have hninvQ : n⁻¹ ∈ Q := Q.inv_mem (hVQ hnV)
    have hmem : α'' ∈ Q := by
      rw [hα''key]
      exact Q.mul_mem hninvQ hQ
    exact hα''Q hmem
  obtain ⟨F, hFMc, hVF, hFcomm, hFsq, hFcard, hFdecomp⟩ :=
    exists_E16 h hMh hMc hα hα'Mc hα2 hα'2 hc hαQ hα'Q hαα'Q
  have hα''Mh : α'' ∈ Mh := h.Mc_le_Mh hMh hMc hα''Mc
  have hTα' : T α' := by
    have hh := hT.conj α ρ hTα
    simpa [hα'def] using hh
  have hTα'' : T α'' := by
    have hh := hT.conj α ρ⁻¹ hTα
    simpa [hα''def] using hh
  have huT : ∀ u ∈ F, u ∉ V → T u := by
    intro u huF huV
    obtain ⟨v, hv, hcase⟩ := hFdecomp u huF huV
    rcases hcase with hu | hu | hu
    · obtain ⟨w, _hwY, hw⟩ := exists_conj_Y h hMh hMc hα hαQ hv
      rw [hu, ← hw]
      exact hT.conj α w hTα
    · obtain ⟨w, _hwY, hw⟩ := exists_conj_Y h hMh hMc hα'Mc hα'Q hv
      rw [hu, ← hw]
      exact hT.conj α' w hTα'
    · have hnVv : n * v ∈ V := V.mul_mem hnV hv
      have hvu : (α * α') * v = α'' * (n * v) := by
        rw [hkey]
        have hcn : n * α'' = α'' * n := by
          have hcent := h.Mh_cent_V hMh hα''Mh hnV
          calc n * α'' = (α'' * n * α''⁻¹) * α'' := by rw [hcent]
            _ = α'' * n := by group
        calc n * α'' * v = (α'' * n) * v := by rw [hcn]
          _ = α'' * (n * v) := by group
      obtain ⟨w, _hwY, hw⟩ := exists_conj_Y h hMh hMc hα''Mc hα''Q hnVv
      rw [hu, hvu, ← hw]
      exact hT.conj α'' w hTα''
  have hsubset : ((F : Set H) \ (V : Set H)) ⊆ {u : H | u ∈ F ∧ T u} := by
    rintro u ⟨huF, huV⟩
    exact ⟨huF, huT u huF huV⟩
  have hcarddiff : ((F : Set H) \ (V : Set H)).ncard = 12 := by
    have hFn : (F : Set H).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact hFcard
    have hVn : (V : Set H).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact h.card_V
    rw [Set.ncard_sdiff (show (V : Set H) ⊆ (F : Set H) from hVF), hFn, hVn]
  have hle12 : 12 ≤ {u : H | u ∈ F ∧ T u}.ncard := by
    rw [← hcarddiff]
    exact Set.ncard_le_ncard hsubset
  have hbound : {u : H | u ∈ F ∧ T u}.ncard ≤ 4 :=
    he16 F (hFMc.trans (Mc_le_zjVh Mc t τ l)) hFcomm hFsq hFcard
  omega

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
