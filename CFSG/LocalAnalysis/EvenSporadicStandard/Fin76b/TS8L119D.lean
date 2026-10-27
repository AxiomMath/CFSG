module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119C
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G} {α σ : G}

theorem centr_E0 {c : OI13Ctx L z t T E B β S α σ} {y : G} (hy : OYFacts c y) {c' : G}
    (hc' : c' ∈ centralizer ((c.E0 hy : Subgroup G) : Set G)) {e0 : G} (he0 : e0 ∈ c.E0 hy) :
    c' * e0 * c'⁻¹ = e0 := by
  have h1 := (Subgroup.mem_centralizer_iff.1 hc') e0 he0
  rw [mul_inv_eq_iff_eq_mul]
  exact h1.symm

theorem conj_S_centralizer (h : OuterS8Hyp G L z t T E Q x B β S)
    (c : OI13Ctx L z t T E B β S α σ) {y : G} (hy : OYFacts c y) {g₁ : G}
    (hE₁ : ∀ e : G, e ∈ E ↔ g₁ * e * g₁⁻¹ ∈ c.E0 hy) {v : G} (hv : v ∈ S) :
    g₁ * v * g₁⁻¹ ∈ centralizer ((c.E0 hy : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e0 he0
  have he : g₁⁻¹ * e0 * g₁ ∈ E := by
    rw [hE₁]
    have e : g₁ * (g₁⁻¹ * e0 * g₁) * g₁⁻¹ = e0 := by group
    rw [e]
    exact he0
  have hcomm := (Subgroup.mem_centralizer_iff.1 (h.SC hv)) _ he
  calc e0 * (g₁ * v * g₁⁻¹) = g₁ * ((g₁⁻¹ * e0 * g₁) * v) * g₁⁻¹ := by group
    _ = g₁ * (v * (g₁⁻¹ * e0 * g₁)) * g₁⁻¹ := by rw [hcomm]
    _ = (g₁ * v * g₁⁻¹) * e0 := by group

theorem exists_c1 (h : OuterS8Hyp G L z t T E Q x B β S) (c : OI13Ctx L z t T E B β S α σ)
    (hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹)
    {y : G} (hy : OYFacts c y) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = y)
    (hE₁ : ∀ e : G, e ∈ E ↔ g₁ * e * g₁⁻¹ ∈ c.E0 hy) :
    ∃ c₁ : G, c₁ ∈ centralizer ((c.E0 hy : Subgroup G) : Set G) ∧
      (∀ v : G, v ∈ conjSubMap g₁ S ↔ c₁ * v * c₁⁻¹ ∈ Y0 y α) ∧ c₁ * y * c₁⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Θ : Subgroup G := centralizer ((c.E0 hy : Subgroup G) : Set G) with hΘ
  set S₁ : Subgroup G := conjSubMap g₁ S with hS₁
  have hS₁Θ : ∀ v ∈ S₁, v ∈ Θ := by
    intro v hv
    have hs : g₁⁻¹ * v * g₁ ∈ S := (mem_conjSubMap).1 hv
    have key := conj_S_centralizer h c hy hE₁ hs
    have e : g₁ * (g₁⁻¹ * v * g₁) * g₁⁻¹ = v := by group
    rw [e] at key
    exact key
  have hS₁p : IsPGroup 2 S₁ := h.S2.map _
  have hS₁max : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → S₁ ≤ R → R ≤ S₁ := by
    intro R hR hRΘ hSR
    have hR'C : conjSubMap g₁⁻¹ R ≤ centralizer (E : Set G) := by
      intro x hx
      have hx' : g₁ * x * g₁⁻¹ ∈ R := by
        have := (mem_conjSubMap (a := g₁⁻¹) (x := x) (H := R)).1 hx
        rwa [inv_inv] at this
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he0 : g₁ * e * g₁⁻¹ ∈ c.E0 hy := (hE₁ e).1 he
      have hc := (Subgroup.mem_centralizer_iff.1 (hRΘ hx')) _ he0
      calc e * x = g₁⁻¹ * ((g₁ * e * g₁⁻¹) * (g₁ * x * g₁⁻¹)) * g₁ := by group
        _ = g₁⁻¹ * ((g₁ * x * g₁⁻¹) * (g₁ * e * g₁⁻¹)) * g₁ := by rw [hc]
        _ = x * e := by group
    have hR'p : IsPGroup 2 (conjSubMap g₁⁻¹ R) := hR.map _
    have hSR' : S ≤ conjSubMap g₁⁻¹ R := by
      intro s hs
      rw [mem_conjSubMap, inv_inv]
      apply hSR
      refine (mem_conjSubMap).2 ?_
      have e : g₁⁻¹ * (g₁ * s * g₁⁻¹) * g₁ = s := by group
      rw [e]
      exact hs
    have hR'eq : conjSubMap g₁⁻¹ R = S := h.Smax _ hR'p hR'C hSR'
    intro v hv
    have hvS : g₁⁻¹ * v * g₁ ∈ S := by
      rw [← hR'eq, mem_conjSubMap, inv_inv]
      have e : g₁ * (g₁⁻¹ * v * g₁) * g₁⁻¹ = v := by group
      rw [e]
      exact hv
    exact (mem_conjSubMap).2 hvS
  have hY0Θ : Y0 y α ≤ Θ := by
    unfold Y0
    refine (Subgroup.closure_le Θ).2 ?_
    intro v hv
    rcases Set.mem_insert_iff.1 hv with hv | hv
    · rw [hv]
      exact Subgroup.mem_centralizer_iff.2 (fun e0 he0 => (y_comm_E0 hy he0).symm)
    · rw [Set.mem_singleton_iff.1 hv]
      exact Subgroup.mem_centralizer_iff.2 (fun e0 he0 => (alpha_comm_E0 hy he0).symm)
  have hΘS₁ : S₁ ≤ Θ := fun v hv => hS₁Θ v hv
  let sylS₁ : Sylow 2 ↥Θ := sylowOfMax hΘS₁ hS₁p hS₁max
  have hY0p : IsPGroup 2 ((Y0 y α).subgroupOf Θ) :=
    (Y0_pgroup c hy).comap_of_injective Θ.subtype Subtype.val_injective
  obtain ⟨P₀, hP₀⟩ := IsPGroup.exists_le_sylow hY0p
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥Θ P₀ sylS₁
  have hkey : ∀ v ∈ Y0 y α, (k : G) * v * (k : G)⁻¹ ∈ S₁ := by
    intro v hv
    have hvΘ : v ∈ Θ := hY0Θ hv
    have hmem : (MulAut.conj k) ⟨v, hvΘ⟩ ∈ (sylS₁ : Subgroup ↥Θ) := by
      rw [← hk, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP₀ (mem_subgroupOf.2 hv))
    exact (mem_sylowOfMax hΘS₁ hS₁p hS₁max).1 hmem
  have hconjle : conjSubMap (k : G) (Y0 y α) ≤ S₁ := by
    intro x hx
    have h1 := hkey _ ((mem_conjSubMap).1 hx)
    have e : (k : G) * ((k : G)⁻¹ * x * (k : G)) * (k : G)⁻¹ = x := by group
    rwa [e] at h1
  have hcardS : Nat.card ↥S = 8 := by
    obtain ⟨eD⟩ := h.D8
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hcardS₁ : Nat.card ↥S₁ = 8 := by
    rw [← hcardS]
    exact Nat.card_congr (conjIso g₁ S).toEquiv.symm
  have hcardconj : Nat.card ↥(conjSubMap (k : G) (Y0 y α)) = 8 := by
    rw [← Y0_card c hy]
    exact Nat.card_congr (conjIso (k : G) (Y0 y α)).toEquiv.symm
  have hconjeq : conjSubMap (k : G) (Y0 y α) = S₁ :=
    Subgroup.eq_of_le_of_card_ge hconjle (le_of_eq (by rw [hcardS₁, hcardconj]))
  obtain ⟨c₀, hc₀Θ, hc₀iff⟩ : ∃ c₀ ∈ Θ, ∀ v : G, v ∈ S₁ ↔ c₀ * v * c₀⁻¹ ∈ Y0 y α := by
    refine ⟨(k : G)⁻¹, inv_mem k.2, fun v => ?_⟩
    rw [← hconjeq, mem_conjSubMap, inv_inv]
  have hyS₁ : y ∈ S₁ := by
    rw [hS₁, mem_conjSubMap]
    have e : g₁⁻¹ * y * g₁ = z := by
      rw [← hg₁]
      group
    rw [e]
    exact h.zS
  have hx_S0 : c₀ * y * c₀⁻¹ ∈ Y0 y α := (hc₀iff y).1 hyS₁
  have hx_sq : (c₀ * y * c₀⁻¹) * (c₀ * y * c₀⁻¹) = 1 := by
    calc (c₀ * y * c₀⁻¹) * (c₀ * y * c₀⁻¹) = c₀ * (y * y) * c₀⁻¹ := by group
      _ = 1 := by rw [hy.sq]; group
  have hconjz : ∀ c' : G, c' * y * c'⁻¹ = (c' * g₁) * z * (c' * g₁)⁻¹ := by
    intro c'
    rw [← hg₁]
    group
  have hZQ' : ∀ q : G, q ∈ c.Qs → q * q = 1 → ∀ c' : G, q ≠ c' * y * c'⁻¹ := by
    intro q hq hqq c' hqc
    exact hZQ q hq hqq ⟨c' * g₁, by rw [hqc, hconjz]⟩
  have hαyt : α * (y * t) * α⁻¹ = y := by
    rw [inv_eq_of_mul_eq_one_right (rel_αα c)]
    calc α * (y * t) * α = (α * y) * (t * α) := by group
      _ = (y * α * t) * (t * α) := by rw [rel_αy c hy]
      _ = y * α * (t * t) * α := by group
      _ = y * α * α := by rw [rel_tt c, mul_one]
      _ = y := by rw [mul_assoc, rel_αα c, mul_one]
  obtain ⟨c₁, hc₁Θ, hc₁iff, hc₁y⟩ :
      ∃ c₁ ∈ Θ, (∀ v : G, v ∈ S₁ ↔ c₁ * v * c₁⁻¹ ∈ Y0 y α) ∧ c₁ * y * c₁⁻¹ = y := by
    rcases Y0_invol c hy hx_S0 hx_sq with h1 | h1 | h1 | h1 | h1 | h1
    · exact (hZQ' 1 (one_mem _) (one_mul 1) c₀ h1.symm).elim
    · exact (hZQ' t (c.Zs_le_Qs c.t_mem_Zs) c.h.t_sq c₀ h1.symm).elim
    · exact (hZQ' α (c.Zs_le_Qs c.alpha_mem_Zs) c.hα.sq c₀ h1.symm).elim
    · exact (hZQ' (α * t) (c.Zs_le_Qs c.alpha_t_mem_Zs) (c.Zs_sq c.alpha_t_mem_Zs) c₀
        h1.symm).elim
    · exact ⟨c₀, hc₀Θ, hc₀iff, h1⟩
    · refine ⟨α * c₀, mul_mem (Subgroup.mem_centralizer_iff.2 (fun e0 he0 =>
          (alpha_comm_E0 hy he0).symm)) hc₀Θ, fun v => ?_, ?_⟩
      · have e : α * c₀ * v * (α * c₀)⁻¹ = α * (c₀ * v * c₀⁻¹) * α⁻¹ := by group
        rw [e, alpha_conj_Y0_iff c hy]
        exact hc₀iff v
      · have e : α * c₀ * y * (α * c₀)⁻¹ = α * (c₀ * y * c₀⁻¹) * α⁻¹ := by group
        rw [e, h1, hαyt]
  exact ⟨c₁, hc₁Θ, hc₁iff, hc₁y⟩

theorem exists_g2 (h : OuterS8Hyp G L z t T E Q x B β S) (c : OI13Ctx L z t T E B β S α σ)
    (hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹)
    {y : G} (hy : OYFacts c y) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = y)
    (hE₁ : ∀ e : G, e ∈ E ↔ g₁ * e * g₁⁻¹ ∈ c.E0 hy) :
    ∃ g₂ : G, g₂ * z * g₂⁻¹ = y ∧ conjSubMap g₂ E = c.E0 hy ∧ conjSubMap g₂ S = Y0 y α ∧
      conjSubMap g₂ c.Zs = c.Zs := by
  obtain ⟨c₁, hc₁Θ, hc₁iff, hc₁y⟩ := exists_c1 h c hZQ hy hg₁ hE₁
  have hg₂z : c₁ * g₁ * z * (c₁ * g₁)⁻¹ = y := by
    calc c₁ * g₁ * z * (c₁ * g₁)⁻¹ = c₁ * (g₁ * z * g₁⁻¹) * c₁⁻¹ := by group
      _ = c₁ * y * c₁⁻¹ := by rw [hg₁]
      _ = y := hc₁y
  set g₂ : G := c₁ * g₁ with hg₂
  have hS : ∀ s : G, s ∈ S ↔ g₂ * s * g₂⁻¹ ∈ Y0 y α := by
    intro s
    have e1 : g₂ * s * g₂⁻¹ = c₁ * (g₁ * s * g₁⁻¹) * c₁⁻¹ := by rw [hg₂]; group
    rw [e1, ← hc₁iff, mem_conjSubMap]
    have e2 : g₁⁻¹ * (g₁ * s * g₁⁻¹) * g₁ = s := by group
    rw [e2]
  have hEiff : ∀ w : G, w ∈ c.E0 hy ↔ c₁ * w * c₁⁻¹ ∈ c.E0 hy := by
    intro w
    constructor
    · intro hw
      rw [centr_E0 hy hc₁Θ hw]
      exact hw
    · intro hw
      have h1 := centr_E0 hy (inv_mem hc₁Θ) hw
      rw [inv_inv] at h1
      have h2 : w = c₁ * w * c₁⁻¹ := by
        calc w = c₁⁻¹ * (c₁ * w * c₁⁻¹) * c₁ := by group
          _ = c₁ * w * c₁⁻¹ := h1
      rw [h2]
      exact hw
  have hES : ∀ s : G, s ∈ E ↔ g₂ * s * g₂⁻¹ ∈ c.E0 hy := by
    intro s
    have e1 : g₂ * s * g₂⁻¹ = c₁ * (g₁ * s * g₁⁻¹) * c₁⁻¹ := by rw [hg₂]; group
    rw [e1, ← hEiff, hE₁]
  have hEeq : conjSubMap g₂ E = c.E0 hy := by
    ext e
    rw [mem_conjSubMap, hES]
    have e2 : g₂ * (g₂⁻¹ * e * g₂) * g₂⁻¹ = e := by group
    rw [e2]
  have hαyα : α * y * α⁻¹ = y * t := by
    rw [inv_eq_of_mul_eq_one_right (rel_αα c)]
    calc α * y * α = (y * α * t) * α := by rw [rel_αy c hy]
      _ = y * (α * t * α) := by group
      _ = y * t := by rw [αtα_eq_t c]
  have hZt : g₂ * t * g₂⁻¹ ∈ c.Zs := by
    have ht : g₂ * t * g₂⁻¹ ∈ Y0 y α := (hS t).1 c.h.t_mem_S
    have htt : (g₂ * t * g₂⁻¹) * (g₂ * t * g₂⁻¹) = 1 := by
      calc (g₂ * t * g₂⁻¹) * (g₂ * t * g₂⁻¹) = g₂ * (t * t) * g₂⁻¹ := by group
        _ = 1 := by rw [c.h.t_sq]; group
    rcases Y0_invol c hy ht htt with h1 | h1 | h1 | h1 | h1 | h1
    · exfalso
      have h3 : t = 1 := by
        calc t = g₂⁻¹ * (g₂ * t * g₂⁻¹) * g₂ := by group
          _ = 1 := by rw [h1]; group
      exact c.h.t_ne h3
    · rw [h1]; exact c.t_mem_Zs
    · rw [h1]; exact c.alpha_mem_Zs
    · rw [h1]; exact c.alpha_t_mem_Zs
    · exfalso
      have htz : g₂ * t * g₂⁻¹ = g₂ * z * g₂⁻¹ := h1.trans hg₂z.symm
      exact c.h.z_ne_t (mul_left_cancel (mul_right_cancel htz)).symm
    · exfalso
      have hzc : t = (g₂⁻¹ * α * g₂) * z * (g₂⁻¹ * α * g₂)⁻¹ := by
        calc t = g₂⁻¹ * (g₂ * t * g₂⁻¹) * g₂ := by group
          _ = g₂⁻¹ * (y * t) * g₂ := by rw [h1]
          _ = g₂⁻¹ * (α * y * α⁻¹) * g₂ := by rw [hαyα]
          _ = g₂⁻¹ * (α * (g₂ * z * g₂⁻¹) * α⁻¹) * g₂ := by rw [hg₂z]
          _ = (g₂⁻¹ * α * g₂) * z * (g₂⁻¹ * α * g₂)⁻¹ := by group
      exact hZQ t (c.Zs_le_Qs c.t_mem_Zs) c.h.t_sq ⟨g₂⁻¹ * α * g₂, hzc⟩
  have hZα : g₂ * α * g₂⁻¹ ∈ c.Zs := by
    have hα' : g₂ * α * g₂⁻¹ ∈ Y0 y α := (hS α).1 c.hα.mem
    have hαα' : (g₂ * α * g₂⁻¹) * (g₂ * α * g₂⁻¹) = 1 := by
      calc (g₂ * α * g₂⁻¹) * (g₂ * α * g₂⁻¹) = g₂ * (α * α) * g₂⁻¹ := by group
        _ = 1 := by rw [c.hα.sq]; group
    rcases Y0_invol c hy hα' hαα' with h1 | h1 | h1 | h1 | h1 | h1
    · exfalso
      have h3 : α = 1 := by
        calc α = g₂⁻¹ * (g₂ * α * g₂⁻¹) * g₂ := by group
          _ = 1 := by rw [h1]; group
      exact c.hα.ne_one h3
    · rw [h1]; exact c.t_mem_Zs
    · rw [h1]; exact c.alpha_mem_Zs
    · rw [h1]; exact c.alpha_t_mem_Zs
    · exfalso
      have hαz : g₂ * α * g₂⁻¹ = g₂ * z * g₂⁻¹ := h1.trans hg₂z.symm
      exact c.hα.ne_z (mul_left_cancel (mul_right_cancel hαz))
    · exfalso
      have hzc : α = (g₂⁻¹ * α * g₂) * z * (g₂⁻¹ * α * g₂)⁻¹ := by
        calc α = g₂⁻¹ * (g₂ * α * g₂⁻¹) * g₂ := by group
          _ = g₂⁻¹ * (y * t) * g₂ := by rw [h1]
          _ = g₂⁻¹ * (α * y * α⁻¹) * g₂ := by rw [hαyα]
          _ = g₂⁻¹ * (α * (g₂ * z * g₂⁻¹) * α⁻¹) * g₂ := by rw [hg₂z]
          _ = (g₂⁻¹ * α * g₂) * z * (g₂⁻¹ * α * g₂)⁻¹ := by group
      exact hZQ α (c.Zs_le_Qs c.alpha_mem_Zs) c.hα.sq ⟨g₂⁻¹ * α * g₂, hzc⟩
  have hZle : conjSubMap g₂ c.Zs ≤ c.Zs := by
    intro x hx
    have hx' := (mem_conjSubMap).1 hx
    have hxe : g₂ * (g₂⁻¹ * x * g₂) * g₂⁻¹ = x := by group
    rcases (c.mem_Zs).1 hx' with h1 | h1 | h1 | h1
    · have h3 : x = 1 := by rw [← hxe, h1, mul_one, mul_inv_cancel]
      rw [h3]
      exact one_mem _
    · rw [← hxe, h1]
      exact hZt
    · rw [← hxe, h1]
      exact hZα
    · rw [← hxe, h1]
      have e : g₂ * (α * t) * g₂⁻¹ = (g₂ * α * g₂⁻¹) * (g₂ * t * g₂⁻¹) := by group
      rw [e]
      exact mul_mem hZα hZt
  have hZeq : conjSubMap g₂ c.Zs = c.Zs :=
    Subgroup.eq_of_le_of_card_ge hZle
      (le_of_eq (Nat.card_congr (conjIso g₂ c.Zs).toEquiv))
  have hSeq : conjSubMap g₂ S = Y0 y α := by
    ext x
    rw [mem_conjSubMap]
    have h3 := hS (g₂⁻¹ * x * g₂)
    have e : g₂ * (g₂⁻¹ * x * g₂) * g₂⁻¹ = x := by group
    rw [e] at h3
    exact h3
  exact ⟨g₂, hg₂z, hEeq, hSeq, hZeq⟩

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
