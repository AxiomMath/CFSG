module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzb_le_invCent (h : Ctx t L S x₁ x₂ lam rho tau) : L ≤ invCent t := by
  intro ℓ hℓ
  rw [invCent, Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer ℓ hℓ

private lemma fzb_twoCore_le_invCent (h : Ctx t L S x₁ x₂ lam rho tau) :
    twoCore t ≤ invCent t := by
  rw [← h.hyp.centralizer_eq]
  exact inf_le_right

private lemma fzb_mem_sup_of_commute {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have hba : b * a' = a' * b := (hc a' ha' b hb).eq.symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hba]
      _ = a * a' * (b * b') := by group
  | inv y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have hba : b * a = a * b := (hc a ha b hb).eq.symm
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hba]

theorem fzb_H_norm_L (h : Ctx t L S x₁ x₂ lam rho tau) {a ℓ : G} (ha : a ∈ invCent t)
    (hℓ : ℓ ∈ L) : a * ℓ * a⁻¹ ∈ L := by
  have hmem := h.hyp.normal.conj_mem (⟨ℓ, fzb_le_invCent h hℓ⟩ : ↥(invCent t))
    (by rw [Subgroup.mem_subgroupOf]; exact hℓ) (⟨a, ha⟩ : ↥(invCent t))
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem fzb_K_comm_L (h : Ctx t L S x₁ x₂ lam rho tau) {k ℓ : G} (hk : k ∈ twoCore t)
    (hℓ : ℓ ∈ L) : k * ℓ = ℓ * k := by
  rw [← h.hyp.centralizer_eq] at hk
  exact (Subgroup.mem_centralizer_iff.mp hk.1 ℓ hℓ).symm

theorem fzb_H_norm_K (h : Ctx t L S x₁ x₂ lam rho tau) {a k : G} (ha : a ∈ invCent t)
    (hk : k ∈ twoCore t) : a * k * a⁻¹ ∈ twoCore t := by
  have hcent : a * k * a⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun ℓ hℓ => by
      have hℓ' : a⁻¹ * ℓ * a ∈ L := by
        have h1 := fzb_H_norm_L h (inv_mem ha) hℓ
        simpa using h1
      have hcomm : k * (a⁻¹ * ℓ * a) = (a⁻¹ * ℓ * a) * k := fzb_K_comm_L h hk hℓ'
      have hconj : (a * k * a⁻¹) * ℓ = ℓ * (a * k * a⁻¹) := by
        calc (a * k * a⁻¹) * ℓ = a * (k * (a⁻¹ * ℓ * a)) * a⁻¹ := by group
          _ = a * ((a⁻¹ * ℓ * a) * k) * a⁻¹ := by rw [hcomm]
          _ = ℓ * (a * k * a⁻¹) := by group
      exact hconj.symm)
  have hinv : a * k * a⁻¹ ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).mul_mem ha (fzb_twoCore_le_invCent h hk)) (inv_mem ha)
  rw [← h.hyp.centralizer_eq]
  exact ⟨hcent, hinv⟩

theorem fzb_H_norm_N (h : Ctx t L S x₁ x₂ lam rho tau) {a n : G} (ha : a ∈ invCent t)
    (hn : n ∈ zpowers t ⊔ L) : a * n * a⁻¹ ∈ zpowers t ⊔ L := by
  rw [Subgroup.sup_eq_closure] at hn
  induction hn using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute a t := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hci : a * t ^ i * a⁻¹ = t ^ i := by
        rw [show a * t ^ i = t ^ i * a from hcomm.zpow_right i, mul_assoc, mul_inv_cancel,
          mul_one]
      rw [hci]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩)
    · exact Subgroup.mem_sup_right (fzb_H_norm_L h ha hy)
  | one => simp
  | mul y z _ _ hy hz =>
    rw [show a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) from by group]
    exact (zpowers t ⊔ L).mul_mem hy hz
  | inv y _ hy =>
    rw [show a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ from by group]
    exact (zpowers t ⊔ L).inv_mem hy

theorem fzb_H_cases (h : Ctx t L S x₁ x₂ lam rho tau) {a : G} (ha : a ∈ invCent t) :
    a ∈ twoCore t ⊔ L ∨ a * tau⁻¹ ∈ twoCore t ⊔ L := by
  by_cases haF : a ∈ twoCore t ⊔ L
  · exact Or.inl haF
  · right
    have htau : tau ∈ invCent t := h.le_invCent h.tau_mem
    have hFidx : ((twoCore t ⊔ L).subgroupOf (invCent t)).index = 2 := h.relIndex_two
    have hb : (⟨tau, htau⟩ : ↥(invCent t))⁻¹ ∉ (twoCore t ⊔ L).subgroupOf (invCent t) := by
      rw [Subgroup.mem_subgroupOf]
      simpa using h.tau_not_mem
    have ha' : (⟨a, ha⟩ : ↥(invCent t)) ∉ (twoCore t ⊔ L).subgroupOf (invCent t) := by
      rw [Subgroup.mem_subgroupOf]
      exact haF
    have hprod : (⟨a, ha⟩ : ↥(invCent t)) * (⟨tau, htau⟩ : ↥(invCent t))⁻¹ ∈
        (twoCore t ⊔ L).subgroupOf (invCent t) := by
      rw [Subgroup.mul_mem_iff_of_index_two hFidx]
      exact ⟨fun hh => absurd hh ha', fun hh => absurd hh hb⟩
    rw [Subgroup.mem_subgroupOf] at hprod
    simpa using hprod

theorem fzb_KL_decomp (h : Ctx t L S x₁ x₂ lam rho tau) {x : G} (hx : x ∈ twoCore t ⊔ L) :
    ∃ k ∈ twoCore t, ∃ ℓ ∈ L, x = k * ℓ :=
  fzb_mem_sup_of_commute (fun k hk ℓ hℓ => fzb_K_comm_L h hk hℓ) hx

theorem fzb_K_inf_N (h : Ctx t L S x₁ x₂ lam rho tau) {k : G} (hk : k ∈ twoCore t)
    (hkN : k ∈ zpowers t ⊔ L) : k ∈ zpowers t := by
  obtain ⟨a, ha, ℓ, hℓ, hkeq⟩ := fzb_mem_sup_of_commute (A := zpowers t) (B := L)
    (fun a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hcomm : Commute t b :=
        (Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer b hb).symm
      exact hcomm.zpow_left m)
    hkN
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have htK : t ^ i ∈ twoCore t := (twoCore t).zpow_mem h.hyp.mem_twoCore i
  have hℓK : ℓ ∈ twoCore t := by
    have h1 : (t ^ i)⁻¹ * k ∈ twoCore t := (twoCore t).mul_mem ((twoCore t).inv_mem htK) hk
    have h2 : ℓ = (t ^ i)⁻¹ * k := by rw [hkeq]; group
    rw [h2]; exact h1
  have hℓbot : ℓ ∈ (⊥ : Subgroup G) := by
    rw [← h.hyp.twoCore_inf]
    exact ⟨hℓK, hℓ⟩
  have hℓ1 : ℓ = 1 := Subgroup.mem_bot.mp hℓbot
  rw [hkeq, hℓ1, mul_one]
  exact (Subgroup.zpowers t).zpow_mem (Subgroup.mem_zpowers t) i

end CFSG.OddStandard.SmallF3.FritzII
