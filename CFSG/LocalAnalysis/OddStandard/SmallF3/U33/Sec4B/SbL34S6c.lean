module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Conj

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau) {W : Subgroup G} {v : G}
  (hv : Ctx4V t x₁ x₂ lam tau W v)
include hc hv

theorem exists_conj_Sp_S : ∃ g : G, g * (t * lam) * g⁻¹ = t ∧
    ∀ x : G, x ∈ S ↔ g⁻¹ * x * g ∈ ctxSp t tau x₁ x₂ lam v := by
  obtain ⟨g₀, hg₀⟩ := hc.inv_tl 1 (Subgroup.one_mem _)
    (by simpa using q_mul_self hc.toCtx4Q)
  have hg₀' : g₀ * t * g₀⁻¹ = t * lam := by simpa using hg₀
  have hg₁ : g₀⁻¹ * (t * lam) * g₀ = t := by
    have h := congrArg (fun z => g₀⁻¹ * z * g₀) hg₀'
    rw [show g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ = t from by group] at h
    exact h.symm
  have hg₁' : t * lam = g₀ * t * g₀⁻¹ := hg₀'.symm
  have hle : S4B.cj g₀⁻¹ (ctxSp t tau x₁ x₂ lam v) ≤ invCent t := by
    intro x hx
    rw [invCent, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hxS' : g₀ * x * g₀⁻¹ ∈ ctxSp t tau x₁ x₂ lam v := by
      have := (S4B.mem_cj (H := ctxSp t tau x₁ x₂ lam v)).mp hx
      simpa [inv_inv] using this
    have hxc := Sp_le_cent hc hv hxS'
    rw [Subgroup.mem_centralizer_iff] at hxc
    have hq := hxc (t * lam) (Set.mem_singleton (t * lam))
    have hconj := congrArg (fun z => g₀⁻¹ * z * g₀) hq
    have e1 : g₀⁻¹ * ((t * lam) * (g₀ * x * g₀⁻¹)) * g₀ = t * x := by
      rw [hg₁']; group
    have e2 : g₀⁻¹ * ((g₀ * x * g₀⁻¹) * (t * lam)) * g₀ = x * t := by
      rw [hg₁']; group
    exact e1.symm.trans (hconj.trans e2)
  have hD2 : IsPGroup 2 (S4B.cj g₀⁻¹ (ctxSp t tau x₁ x₂ lam v)) :=
    S4B.isPGroup_cj (Sp_isPGroup hc hv)
  have hcard : Nat.card S ≤ Nat.card (S4B.cj g₀⁻¹ (ctxSp t tau x₁ x₂ lam v)) := by
    rw [Ctx4.card_S_seven hc.toCtx4, S4B.card_cj]
    exact le_card_Sp hc hv
  have hSyl : IsSylowIn 2 S (invCent t) := ⟨hc.le_invCent, hc.isPGroup, hc.relIndex_odd⟩
  obtain ⟨c, hcH, hcj⟩ := S4B.exists_cj_of_card_le (S := S)
    (D := S4B.cj g₀⁻¹ (ctxSp t tau x₁ x₂ lam v)) (H := invCent t) hSyl hle hD2 hcard
  have hgq : (c⁻¹ * g₀⁻¹) * (t * lam) * (c⁻¹ * g₀⁻¹)⁻¹ = t := by
    have hmemc : c ∈ Subgroup.centralizer ({t} : Set G) := hcH
    have hct : t * c = c * t :=
      (Subgroup.mem_centralizer_iff.mp hmemc) t (Set.mem_singleton t)
    calc (c⁻¹ * g₀⁻¹) * (t * lam) * (c⁻¹ * g₀⁻¹)⁻¹
        = c⁻¹ * (g₀⁻¹ * (t * lam) * g₀) * c := by group
      _ = c⁻¹ * t * c := by rw [hg₁]
      _ = t := by rw [mul_assoc, hct, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨c⁻¹ * g₀⁻¹, hgq, ?_⟩
  intro x
  have h1 : x ∈ S ↔ c * x * c⁻¹ ∈ S4B.cj c S := by
    constructor
    · intro hx; exact S4B.conj_mem_cj hx
    · intro hx
      have := (S4B.mem_cj (H := S)).mp hx
      convert this using 1 <;> group
  rw [h1, hcj]
  rw [S4B.mem_cj (H := ctxSp t tau x₁ x₂ lam v)]
  constructor
  · intro hx; convert hx using 1 <;> group
  · intro hx; convert hx using 1 <;> group

end Conj

section Final

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau) {W : Subgroup G} {v : G}
  (hv : Ctx4V t x₁ x₂ lam tau W v) {ω : G} (hω : ω = tau ∨ ω = t * tau)
  (hn : NormalIn (ctxN ω x₁ x₂) (ctxLO t tau x₁ x₂))
include hc hv hω hn

theorem conj_omega_mem_V {g : G} (hg1 : g * (t * lam) * g⁻¹ = t)
    (hg2 : ∀ x : G, x ∈ S ↔ g⁻¹ * x * g ∈ ctxSp t tau x₁ x₂ lam v) :
    g * ω * g⁻¹ ∈ fourGrp x₁ x₂ := by
  have hDle : S4B.cj g (ctxD ω x₁ x₂) ≤ S := by
    intro x hx
    exact (hg2 x).mpr (D_le_Sp hc hv hω ((S4B.mem_cj (H := ctxD ω x₁ x₂)).mp hx))
  have hDnorm : NormalIn (S4B.cj g (ctxD ω x₁ x₂)) S := by
    refine ⟨hDle, ?_⟩
    intro s hs k hk
    rw [S4B.mem_cj]
    have hsk : g⁻¹ * s * g ∈ ctxSp t tau x₁ x₂ lam v := (hg2 s).mp hs
    have hkD : g⁻¹ * k * g ∈ ctxD ω x₁ x₂ := (S4B.mem_cj (H := ctxD ω x₁ x₂)).mp hk
    have hkey := (D_normal_Sp hc hv hω hn).2 (g⁻¹ * s * g) hsk (g⁻¹ * k * g) hkD
    convert hkey using 1 <;> group
  have hD2 : CFSG.Open.IsElemAbelian 2 (S4B.cj g (ctxD ω x₁ x₂)) :=
    S4B.isElemAbelian_cj (D_elemAbelian hc.toCtx4Q hω)
  have hcard : Nat.card (S4B.cj g (ctxD ω x₁ x₂)) = 4 := by
    rw [S4B.card_cj, card_D hc.toCtx4Q hω]
  have hfree : ∀ g' : G, ∀ a ∈ S4B.cj g (ctxD ω x₁ x₂), g' * t * g'⁻¹ ≠ a := by
    intro g' a ha h
    have hd : g⁻¹ * a * g ∈ ctxD ω x₁ x₂ := (S4B.mem_cj (H := ctxD ω x₁ x₂)).mp ha
    exact D_tG hc hω (g⁻¹ * g') (g⁻¹ * a * g) hd (by
      have := congrArg (fun z => g⁻¹ * z * g) h
      convert this using 1 <;> group)
  have hEq : S4B.cj g (ctxD ω x₁ x₂) = fourGrp x₁ x₂ :=
    (hc.l45 (S4B.cj g (ctxD ω x₁ x₂)) hDnorm hD2 hcard hfree).1
  have hωD : ω ∈ ctxD ω x₁ x₂ := Subgroup.subset_closure (by simp)
  have hmem : g * ω * g⁻¹ ∈ S4B.cj g (ctxD ω x₁ x₂) := S4B.conj_mem_cj hωD
  rw [hEq] at hmem
  exact hmem

theorem q_omega_mem_tG : ∃ h : G, h * t * h⁻¹ = (t * lam) * ω := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_Sp_S hc hv
  have ha : g * ω * g⁻¹ ∈ fourGrp x₁ x₂ := conj_omega_mem_V hc hv hω hn hg1 hg2
  have hmem : t * (g * ω * g⁻¹) ∈ t • (fourGrp x₁ x₂ : Set G) := by
    rw [Set.mem_smul_set]
    exact ⟨g * ω * g⁻¹, ha, by rw [smul_eq_mul]⟩
  rw [← hc.tM] at hmem
  obtain ⟨m, _, hm⟩ := hmem
  refine ⟨g⁻¹ * m, ?_⟩
  have ht_eq : g⁻¹ * t * g = t * lam := by
    have h := congrArg (fun z => g⁻¹ * z * g) hg1
    rw [show g⁻¹ * (g * (t * lam) * g⁻¹) * g = t * lam from by group] at h
    exact h.symm
  have hω_eq : g⁻¹ * (g * ω * g⁻¹) * g = ω := by group
  calc (g⁻¹ * m) * t * (g⁻¹ * m)⁻¹
      = g⁻¹ * (m * t * m⁻¹) * g := by group
    _ = g⁻¹ * (t * (g * ω * g⁻¹)) * g := by rw [hm]
    _ = (g⁻¹ * t * g) * (g⁻¹ * (g * ω * g⁻¹) * g) := by group
    _ = (t * lam) * ω := by rw [ht_eq, hω_eq]

theorem q_omega_not_mem_tG : ¬ ∃ h : G, h * t * h⁻¹ = (t * lam) * ω := by
  rintro ⟨h, hh⟩
  have htau : tau * tau = 1 := by rw [← pow_two]; exact hc.l44.1
  have htt : t * t = 1 := Ctx4Q.t_mul_self hc.toCtx4Q
  have hll : lam * lam = 1 := lam_mul_self hc.toCtx4Q
  rcases hω with htau_eq | httau_eq
  · rw [htau_eq] at hh
    have hltau : (t * lam * tau * 1) * (t * lam * tau * 1) = 1 := by
      simp only [mul_one]
      have hqt : tau * (t * lam) = (t * lam) * tau := (q_comm_tau hc.toCtx4Q).symm
      calc (t * lam * tau) * (t * lam * tau)
          = (t * lam) * (tau * (t * lam)) * tau := by group
        _ = (t * lam) * ((t * lam) * tau) * tau := by rw [hqt]
        _ = ((t * lam) * (t * lam)) * (tau * tau) := by group
        _ = 1 := by rw [q_mul_self hc.toCtx4Q, htau, mul_one]
    obtain ⟨k, hk⟩ := hc.inv_tltau 1 (Subgroup.one_mem _) hltau
    have hk' : k * (t * tau) * k⁻¹ = t * lam * tau := by simpa using hk
    have hh' : h * t * h⁻¹ = t * lam * tau := by simpa using hh
    have hmem : t * tau ∈ ctxN (t * tau) x₁ x₂ := Subgroup.subset_closure (by simp)
    refine hc.tG_tN (k⁻¹ * h) (t * tau) hmem ?_
    calc (k⁻¹ * h) * t * (k⁻¹ * h)⁻¹
        = k⁻¹ * (h * t * h⁻¹) * k := by group
      _ = k⁻¹ * (t * lam * tau) * k := by rw [hh']
      _ = t * tau := by rw [← hk']; group
  · rw [httau_eq] at hh
    have hltau : (lam * tau * 1) * (lam * tau * 1) = 1 := by
      simp only [mul_one]
      have hlt : tau * lam = lam * tau := (lam_comm_tau hc.toCtx4Q).symm
      calc (lam * tau) * (lam * tau)
          = lam * (tau * lam) * tau := by group
        _ = lam * (lam * tau) * tau := by rw [hlt]
        _ = (lam * lam) * (tau * tau) := by group
        _ = 1 := by rw [hll, htau, mul_one]
    obtain ⟨k, hk⟩ := hc.inv_ltau 1 (Subgroup.one_mem _) hltau
    have hk' : k * tau * k⁻¹ = lam * tau := by simpa using hk
    have hh2 : (t * lam) * (t * tau) = lam * tau := by
      have htl : lam * t = t * lam := (t_comm_lam hc.toCtx4Q).symm
      calc (t * lam) * (t * tau) = t * (lam * t) * tau := by group
        _ = t * (t * lam) * tau := by rw [htl]
        _ = (t * t) * (lam * tau) := by group
        _ = lam * tau := by rw [htt, one_mul]
    have hh' : h * t * h⁻¹ = lam * tau := by rw [hh, hh2]
    have hmem : tau ∈ ctxN tau x₁ x₂ := Subgroup.subset_closure (by simp)
    refine hc.tG_N (k⁻¹ * h) tau hmem ?_
    calc (k⁻¹ * h) * t * (k⁻¹ * h)⁻¹
        = k⁻¹ * (h * t * h⁻¹) * k := by group
      _ = k⁻¹ * (lam * tau) * k := by rw [hh']
      _ = tau := by rw [← hk']; group

end Final

end CFSG.OddStandard.SmallF3.HarrisU33.L34

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l34_s6 : L34S6Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau W v hG hB hc hv ω hω hn
  exact L34.q_omega_not_mem_tG hc hv hω hn (L34.q_omega_mem_tG hc hv hω hn)

end CFSG.OddStandard.SmallF3.HarrisU33
