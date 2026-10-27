module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46a

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

@[expose] def HTransfer (G : Type) [Group G] [Finite G] (S : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ S → (∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N) → N ≠ S →
    (∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ N) →
    ∀ w ∈ S, w * w = 1 → w ∉ N → ∃ g : G, g⁻¹ * w * g ∈ N

namespace Cfg1

theorem S_syl_C (h : Cfg1 G z S P Q F FA) : Syl2In S (centralizer ({z} : Set G)) := by
  have hle : S ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.z_cent s hs).symm
  refine ⟨hle, h.S_pgroup, fun hdvd => h.S_syl.2.2 ?_⟩
  have h1 : S.relIndex (centralizer ({z} : Set G)) ∣ S.relIndex ⊤ := by
    rw [← Subgroup.relIndex_mul_relIndex S (centralizer ({z} : Set G)) ⊤ hle le_top]
    exact dvd_mul_right _ _
  exact hdvd.trans h1

theorem mem_Q_four (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) (hQ4 : Nat.card ↥Q = 4) {u₂ : G}
    (hu₂ : u₂ ∈ Q) (h2 : u₂ * u₂ = z) {q : G} (hq : q ∈ Q) :
    q = 1 ∨ q = z ∨ q = u₂ ∨ q = u₂ * z := by
  have hq4 : q ^ 4 = 1 := by
    have := pow_card_eq_one' (G := ↥Q) (x := ⟨q, hq⟩)
    rw [hQ4] at this
    simpa using congrArg Subtype.val this
  have hqF : q ∈ F := h.Q_le_F hq
  have hqq : (q * q) * (q * q) = 1 := by
    have e : q ^ 4 = (q * q) * (q * q) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← e]; exact hq4
  rcases h.invol_F hF (mul_mem hqF hqF) hqq with e | e
  · rcases h.invol_F hF hqF e with e1 | e1
    · exact Or.inl e1
    · exact Or.inr (Or.inl e1)
  · right; right
    have hu₂F : u₂ ∈ F := h.Q_le_F hu₂
    have hc : q * u₂⁻¹ = u₂⁻¹ * q := comm_of_cyclic hF hqF (inv_mem hu₂F)
    have hsq : (q * u₂⁻¹) * (q * u₂⁻¹) = 1 := by
      calc (q * u₂⁻¹) * (q * u₂⁻¹) = q * (u₂⁻¹ * q) * u₂⁻¹ := by group
        _ = q * (q * u₂⁻¹) * u₂⁻¹ := by rw [← hc]
        _ = (q * q) * (u₂⁻¹ * u₂⁻¹) := by group
        _ = (q * q) * (u₂ * u₂)⁻¹ := by group
        _ = z * z⁻¹ := by rw [e, h2]
        _ = 1 := mul_inv_cancel z
    rcases h.invol_F hF (mul_mem hqF (inv_mem hu₂F)) hsq with e1 | e1
    · left
      calc q = q * u₂⁻¹ * u₂ := by group
        _ = u₂ := by rw [e1, one_mul]
    · right
      calc q = q * u₂⁻¹ * u₂ := by group
        _ = z * u₂ := by rw [e1]
        _ = u₂ * z := (h.z_cent u₂ (h.Q_le hu₂))

end Cfg1

namespace Cfg1K

theorem exists_not_norm (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F) (hTr : HTransfer G S)
    {y : G} (hy : Is47b S P F y) (hzy : IsConj z y) {u : G} (huS : u ∈ S) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hu : ¬ IsConj z u) : ∃ s ∈ S, s * y * s⁻¹ ∉ P ⊔ zpowers y := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  have hy' : Is47b S P F y := h.toCfg1.is47b_of hyS hy2 hyPF
  by_contra hcon
  push Not at hcon
  set N : Subgroup G := P ⊔ zpowers y with hN
  have hNS : N ≤ S := sup_le h.P_le (zpowers_le.2 hyS)
  have hynorm : zpowers y ≤ normalizer (P : Set G) := by
    refine zpowers_le.2 (mem_normalizer_of_both (fun x hx => h.P_norm y hyS x hx) (fun x hx => ?_))
    have := h.P_norm y⁻¹ (S.inv_mem hyS) x hx
    simpa using this
  have hNel : ∀ n ∈ N, ∃ b ∈ zpowers y, ∃ a ∈ P, n = b * a := by
    intro n hn
    rw [hN, sup_comm] at hn
    exact mem_sup_of_le_normalizer hynorm hn
  have hNnorm : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N := by
    intro t ht q hq
    obtain ⟨b, hb, a, ha, rfl⟩ := hNel q hq
    have e : t * (b * a) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹) := by group
    rw [e]
    refine mul_mem ?_ (mem_sup_left (h.P_norm t ht a ha))
    rcases (mem_zpowers_of_sq hy2).1 hb with hb1 | hb1
    · rw [hb1]; simp
    · rw [hb1]; exact hcon t ht
  have hNne : N ≠ S := by
    intro hNS'
    obtain ⟨q, hqQ, hq1, hqz⟩ := h.exists_q hF
    have hqN : q ∈ N := by rw [hNS']; exact h.Q_le hqQ
    obtain ⟨b, hb, a, ha, hqe⟩ := hNel q hqN
    rcases (mem_zpowers_of_sq hy2).1 hb with hb1 | hb1
    · rw [hb1, one_mul] at hqe
      rcases h.PQ_inf q (hqe ▸ ha) hqQ with e | e
      · exact hq1 e
      · exact hqz e
    · rw [hb1] at hqe
      apply hyPF
      have e1 : y = q * a⁻¹ := by rw [hqe]; group
      rw [e1]
      exact mul_mem (mem_sup_right (h.Q_le_F hqQ)) (mem_sup_left (inv_mem ha))
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ N := by
    obtain ⟨c, hcF, hgen⟩ := exists_gen_of_cyclic hF
    have hcS : c ∈ S := h.F_le hcF
    refine ⟨c, hcS, fun t ht => ?_⟩
    have hconj : ∀ (k : ℤ) (a : G), a ∈ P → (c ^ k)⁻¹ * a * ((c ^ k)⁻¹)⁻¹ ∈ P := by
      intro k a ha
      exact h.P_norm _ (S.inv_mem (S.zpow_mem hcS k)) a ha
    rcases B.mem_or_mul_inv_mem h.idx hyS hyPF ht with htPF | htPF
    · obtain ⟨p, hp, f, hf, rfl⟩ := h.mem_PF htPF
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hgen f hf)
      refine ⟨k, ?_⟩
      have e : (c ^ k)⁻¹ * (p * f) = (c ^ k)⁻¹ * p * ((c ^ k)⁻¹)⁻¹ := by rw [← hk]; group
      rw [e]
      exact mem_sup_left (hconj k p hp)
    · obtain ⟨p, hp, f, hf, hpf⟩ := h.mem_PF htPF
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hgen f hf)
      refine ⟨k, ?_⟩
      have e1 : t = p * f * y := by rw [← hpf]; group
      have e : (c ^ k)⁻¹ * t = ((c ^ k)⁻¹ * p * ((c ^ k)⁻¹)⁻¹) * y := by rw [e1, ← hk]; group
      rw [e]
      exact mul_mem (mem_sup_left (hconj k p hp)) (mem_sup_right (mem_zpowers y))
  have hallN : ∀ s ∈ N, s * s = 1 → s ≠ 1 → IsConj z s := by
    intro s hs hs2 hs1
    obtain ⟨b, hb, a, ha, rfl⟩ := hNel s hs
    rcases (mem_zpowers_of_sq hy2).1 hb with hb1 | hb1
    · rw [hb1, one_mul] at hs2 hs1 ⊢
      rcases h.P_inv a ha hs2 with e | e
      · exact absurd e hs1
      · rw [e]
    · rw [hb1] at hs2 hs1 ⊢
      have hwy : y * a * y⁻¹ ∈ P := h.P_norm y hyS a ha
      obtain ⟨p, hp, hpy⟩ := h.conj_in_Py hy' hs2 hwy
      refine hzy.trans (isConj_iff.2 ⟨p⁻¹, ?_⟩)
      rw [inv_inv]; exact hpy
  have huS' : ∀ w : G, w ∈ S → w * w = 1 → w ≠ 1 → IsConj z w := by
    intro w hw hw2 hw1
    by_cases hwN : w ∈ N
    · exact hallN w hwN hw2 hw1
    · obtain ⟨g, hg⟩ := hTr N hNS hNnorm hNne hcyc w hw hw2 hwN
      have hg2 : (g⁻¹ * w * g) * (g⁻¹ * w * g) = 1 := by
        calc (g⁻¹ * w * g) * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
          _ = 1 := by rw [hw2]; group
      have hg1 : g⁻¹ * w * g ≠ 1 := by
        intro e
        apply hw1
        calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
          _ = 1 := by rw [e]; group
      have h1 := hallN _ hg hg2 hg1
      exact h1.trans (isConj_iff.2 ⟨g, by group⟩)
  exact hu (huS' u huS hu2 hu1)

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
