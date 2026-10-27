module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610C

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem cent_E_M {c : G} (hcM : c ∈ normalizer ((S ⊔ E : Subgroup G) : Set G))
    (hcE : ∀ e ∈ E, c * e = e * c) : c ∈ S := by
  obtain ⟨N, hNn, hNodd, hNS, hNprod⟩ := h.odd
  have hcCE : c ∈ centralizer (E : Set G) := mem_centralizer_iff.2 fun e he => (hcE e he).symm
  have hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    intro s hs
    have hU : c * s * c⁻¹ ∈ S ⊔ E := (mem_normalizer_iff.1 hcM s).1 (mem_sup_left hs)
    obtain ⟨s₁, hs₁, e₁, he₁, hse⟩ := exists_mul_of_mem_sup_of_le_centralizer h.E_le_cent_S hU
    have he₁c : ∀ f ∈ E, f * e₁ = e₁ * f := by
      intro f hf
      have h1 : (c * s * c⁻¹) * f = f * (c * s * c⁻¹) := by
        have hsf := h.S_comm_E s hs f hf
        have hcf : c⁻¹ * f = f * c⁻¹ := by
          have := hcE f hf
          calc c⁻¹ * f = c⁻¹ * (f * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * f) * c⁻¹ := by rw [this]
            _ = f * c⁻¹ := by group
        calc (c * s * c⁻¹) * f = c * s * (c⁻¹ * f) := by group
          _ = c * s * (f * c⁻¹) := by rw [hcf]
          _ = c * (s * f) * c⁻¹ := by group
          _ = c * (f * s) * c⁻¹ := by rw [hsf]
          _ = (c * f) * s * c⁻¹ := by group
          _ = (f * c) * s * c⁻¹ := by rw [hcE f hf]
          _ = f * (c * s * c⁻¹) := by group
      rw [hse] at h1
      have hs₁f := h.S_comm_E s₁ hs₁ f hf
      calc f * e₁ = (s₁⁻¹ * s₁) * f * e₁ := by group
        _ = s₁⁻¹ * (s₁ * f) * e₁ := by group
        _ = s₁⁻¹ * (f * s₁) * e₁ := by rw [hs₁f]
        _ = s₁⁻¹ * (f * (s₁ * e₁)) := by group
        _ = s₁⁻¹ * ((s₁ * e₁) * f) := by rw [← h1]
        _ = (s₁⁻¹ * s₁) * e₁ * f := by group
        _ = e₁ * f := by group
    have he₁t : e₁ = 1 ∨ e₁ = t := h.conf.econfig.center e₁ he₁ he₁c
    rw [hse]
    refine mul_mem hs₁ ?_
    rcases he₁t with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact h.t_mem_S
  have hmem : (⟨c, hcCE⟩ : ↥(centralizer (E : Set G))) ∈
      (N : Set ↥(centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set ↥(centralizer (E : Set G))) := by
    rw [hNprod]; exact Set.mem_univ _
  obtain ⟨n', hn', s', hs', hns⟩ := Set.mem_mul.1 hmem
  have hcns : (n' : G) * (s' : G) = c := congrArg Subtype.val hns
  have hs : (s' : G) ∈ S := mem_subgroupOf.1 hs'
  have hn_odd : Odd (orderOf (n' : G)) := by
    rw [Subgroup.orderOf_coe]; exact (hNodd n').1 hn'
  set n : G := (n' : G) with hn_def
  set s : G := (s' : G) with hs_def
  have hnS : ∀ x ∈ S, n * x * n⁻¹ ∈ S := by
    intro x hx
    have h1 : n * x * n⁻¹ = c * (s⁻¹ * x * s) * c⁻¹ := by
      rw [← hcns]; group
    rw [h1]
    exact hcS _ (mul_mem (mul_mem (inv_mem hs) hx) hs)
  have hnz : n * z = z * n := by
    let zc : ↥(centralizer (E : Set G)) := ⟨z, h.SC h.zS⟩
    have hm1 : n' * zc * n'⁻¹ * zc⁻¹ ∈ N := by
      have := hNn.conj_mem _ (inv_mem hn') zc
      have h2 := mul_mem hn' this
      have e1 : n' * zc * n'⁻¹ * zc⁻¹ = n' * (zc * n'⁻¹ * zc⁻¹) := by group
      rw [e1]; exact h2
    have hmS : n' * zc * n'⁻¹ * zc⁻¹ ∈ S.subgroupOf (centralizer (E : Set G)) := by
      rw [mem_subgroupOf]
      have : ((n' * zc * n'⁻¹ * zc⁻¹ : ↥(centralizer (E : Set G))) : G) = n * z * n⁻¹ * z⁻¹ := by
        simp [zc, hn_def]
      rw [this]
      exact mul_mem (hnS z h.zS) (inv_mem h.zS)
    have h0 : n' * zc * n'⁻¹ * zc⁻¹ ∈ N ⊓ S.subgroupOf (centralizer (E : Set G)) := ⟨hm1, hmS⟩
    rw [hNS, mem_bot] at h0
    have h1 : n * z * n⁻¹ * z⁻¹ = 1 := by
      have := congrArg (fun y : ↥(centralizer (E : Set G)) => (y : G)) h0
      simpa [zc, hn_def] using this
    calc n * z = (n * z * n⁻¹ * z⁻¹) * (z * n) := by group
      _ = z * n := by rw [h1, one_mul]
  have hnL : n ∈ L := h.odd_mem_L (mem_centralizer_singleton_iff.2 hnz) hn_odd
  have hn1 : n = 1 := by
    rcases h.wf.cent n hnL (fun e he => (mem_centralizer_iff.1 n'.2 e he).symm) with h1 | h1
    · exact h1
    · exfalso
      rw [h1, h.conf.cfg.t_order] at hn_odd
      exact absurd hn_odd (by decide)
  have hcs : c = s := by rw [← hcns, hn1, one_mul]
  exact hcs ▸ hs

theorem QF_normal {α : G} (hα : AlphaSpec S z t α) {g q : G}
    (hg : g ∈ normalizer ((S ⊔ E : Subgroup G) : Set G))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := by
  refine ⟨h.Fsub_normal hα hg hq.1, mem_centralizer_singleton_iff.2 ?_⟩
  have hqα : q * α = α * q := mem_centralizer_singleton_iff.1 hq.2
  have hqt : q * t = t * q := by
    have := h.conj_t_of_M hq.1.1
    calc q * t = (q * t * q⁻¹) * q := by group
      _ = t * q := by rw [this]
  have hα' : g⁻¹ * α * g⁻¹⁻¹ = α ∨ g⁻¹ * α * g⁻¹⁻¹ = α * t := h.alpha_orbit hα (inv_mem hg)
  have hq' : q * (g⁻¹ * α * g) = (g⁻¹ * α * g) * q := by
    rw [inv_inv] at hα'
    rcases hα' with h1 | h1
    · rw [h1]; exact hqα
    · rw [h1]
      calc q * (α * t) = (q * α) * t := by group
        _ = (α * q) * t := by rw [hqα]
        _ = α * (q * t) := by group
        _ = α * (t * q) := by rw [hqt]
        _ = (α * t) * q := by group
  calc g * q * g⁻¹ * α = g * (q * (g⁻¹ * α * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * α * g) * q) * g⁻¹ := by rw [hq']
    _ = α * (g * q * g⁻¹) := by group

theorem CMalpha_eq {α : G} (hα : AlphaSpec S z t α) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) (hmα : m * α = α * m) :
    ∃ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), ∃ b ∈ B, m = q * b := by
  obtain ⟨f, hf, b, hb, rfl⟩ := h.M_eq_FB hα hm
  refine ⟨f, ⟨hf, mem_centralizer_singleton_iff.2 ?_⟩, b, hb, rfl⟩
  have hbα : b * α = α * b := h.BS b hb α hα.mem
  calc f * α = (f * b) * α * b⁻¹ := by
        calc f * α = f * (b * α) * b⁻¹ := by rw [hbα]; group
          _ = (f * b) * α * b⁻¹ := by group
    _ = (α * (f * b)) * b⁻¹ := by rw [hmα]
    _ = α * f := by group

theorem center_QF {α : G} (hα : AlphaSpec S z t α) {y : G} :
    (y ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
      ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), y * q = q * y) ↔
      (y = 1 ∨ y = t ∨ y = α ∨ y = α * t) := by
  have hα_F : α ∈ Fsub h hα := h.U_le_Fsub hα (mem_sup_left hα.mem)
  have ht_F : t ∈ Fsub h hα := h.U_le_Fsub hα (mem_sup_right h.t_mem_E)
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  have ht_cent : ∀ q ∈ Fsub h hα, q * t = t * q := fun q hq => by
    have := h.conj_t_of_M hq.1
    calc q * t = (q * t * q⁻¹) * q := by group
      _ = t * q := by rw [this]
  have hαq : ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), α * q = q * α := fun q hq =>
    (mem_centralizer_singleton_iff.1 hq.2).symm
  constructor
  · rintro ⟨hy, hyc⟩
    have hyE : ∀ e ∈ E, y * e = e * y := fun e he =>
      hyc e ⟨h.U_le_Fsub hα (mem_sup_right he),
        mem_centralizer_singleton_iff.2 (h.S_comm_E α hα.mem e he).symm⟩
    have hyS : y ∈ S := h.cent_E_M hy.1.1 hyE
    have hyα : y * α = α * y := mem_centralizer_singleton_iff.1 hy.2
    rcases hα.list y hyS with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exfalso
      rw [h1] at hyα
      exact h.sigma_z_a hα hyα
    · exfalso
      rw [h1] at hyα
      apply h.sigma_z_a hα
      have h2 : z * α * t = α * z * t := by
        calc z * α * t = z * (α * t) := by group
          _ = z * (t * α) := by rw [hαt]
          _ = (z * t) * α := by group
          _ = α * (z * t) := hyα
          _ = α * z * t := by group
      exact mul_right_cancel h2
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
    · exfalso
      rw [h1] at hyα
      exact h.sigma_r_a hα hyα
    · exfalso
      rw [h1] at hyα
      apply h.sigma_r_a hα
      have h2 : (α * z) * α * t = α * (α * z) * t := by
        calc (α * z) * α * t = (α * z) * (α * t) := by group
          _ = (α * z) * (t * α) := by rw [hαt]
          _ = (α * z * t) * α := by group
          _ = α * (α * z * t) := hyα
          _ = α * (α * z) * t := by group
      exact mul_right_cancel h2
  · intro hy
    rcases hy with h1 | h1 | h1 | h1
    · rw [h1]; exact ⟨one_mem _, fun q _ => by simp⟩
    · rw [h1]
      exact ⟨⟨ht_F, mem_centralizer_singleton_iff.2 hαt.symm⟩,
        fun q hq => (ht_cent q hq.1).symm⟩
    · rw [h1]
      exact ⟨⟨hα_F, mem_centralizer_singleton_iff.2 rfl⟩, fun q hq => hαq q hq⟩
    · rw [h1]
      refine ⟨⟨mul_mem hα_F ht_F, mem_centralizer_singleton_iff.2 ?_⟩, fun q hq => ?_⟩
      · calc α * t * α = α * (t * α) := by group
          _ = α * (α * t) := by rw [hαt]
      · calc α * t * q = α * (t * q) := by group
          _ = α * (q * t) := by rw [ht_cent q hq.1]
          _ = (α * q) * t := by group
          _ = (q * α) * t := by rw [hαq q hq]
          _ = q * (α * t) := by group

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
