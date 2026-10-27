module

public import CFSG.CGT.T75R.Tri1

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_eq_of_prod_eq_one {N : Subgroup G} (hN : IsElemAbelian 2 N) {t a b c : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (ha : a ∈ N) (hb : b ∈ N) (hc : c ∈ N)
    (hprod : a * b * c = 1) (hta : t * a = a * t) : ⁅t, b⁆ = ⁅t, c⁆ := by
  have hab : a * b ∈ N := N.mul_mem ha hb
  have h1 : ⁅t, a * b * c⁆ = ⁅t, a * b⁆ * ⁅t, c⁆ := comm_mul_comm hN ht hab hc
  have h2 : ⁅t, a * b⁆ = ⁅t, a⁆ * ⁅t, b⁆ := comm_mul_comm hN ht ha hb
  have h3 : ⁅t, a⁆ = 1 := by
    simp only [commutatorElement_def]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hta
  rw [hprod, h2, h3, one_mul] at h1
  have h4 : ⁅t, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
  rw [h4] at h1
  have hcN : ⁅t, c⁆ ∈ N := comm_mem_of_mem_normalizer ht hc
  have hbN : ⁅t, b⁆ ∈ N := comm_mem_of_mem_normalizer ht hb
  have h5 : ⁅t, c⁆ = (⁅t, b⁆)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
  rw [h5, elemAbelian_inv hN hbN]

theorem exists_fixed_vector {N L₀ L₁ L₂ : Subgroup G} (hN : IsElemAbelian 2 N) (hL₀N : L₀ ≤ N)
    (hL₁N : L₁ ≤ N) (hL₂N : L₂ ≤ N) {t₀ t₁ t₂ c₀ c₁ c₂ : G}
    (ht₀ : t₀ ∈ Subgroup.normalizer (N : Set G)) (ht₁ : t₁ ∈ Subgroup.normalizer (N : Set G))
    (ht₂ : t₂ ∈ Subgroup.normalizer (N : Set G))
    (m01 : ∀ e ∈ L₁, ⁅t₀, e⁆ ∈ L₀) (m10 : ∀ e ∈ L₀, ⁅t₁, e⁆ ∈ L₁)
    (m21 : ∀ e ∈ L₁, ⁅t₂, e⁆ ∈ L₂)
    (htc₀ : t₀ * c₀ = c₀ * t₀) (htc₁ : t₁ * c₁ = c₁ * t₁) (htc₂ : t₂ * c₂ = c₂ * t₂)
    (r01 : ∀ e ∈ L₀, ⁅t₀, ⁅t₁, e⁆⁆ = e) (r10 : ∀ e ∈ L₁, ⁅t₁, ⁅t₀, e⁆⁆ = e)
    (r20 : ∀ e ∈ L₂, ⁅t₂, ⁅t₀, e⁆⁆ = e) (r12 : ∀ e ∈ L₁, ⁅t₁, ⁅t₂, e⁆⁆ = e)
    (inj01 : ∀ e ∈ L₁, t₀ * e = e * t₀ → e = 1)
    (hc₀ : c₀ ∈ L₀) (hc₁ : c₁ ∈ L₁) (hc₂ : c₂ ∈ L₂) (hc₁1 : c₁ ≠ 1) (hprod : c₀ * c₁ * c₂ = 1) :
    ∃ d ∈ L₀, d ≠ 1 ∧ ⁅t₁, d⁆ = ⁅t₁, ⁅t₂, d⁆⁆ := by
  have hc₀N := hL₀N hc₀
  have hc₁N := hL₁N hc₁
  have hc₂N := hL₂N hc₂
  have hprod' : c₁ * c₀ * c₂ = 1 := by
    rw [elemAbelian_mul_comm hN hc₁N hc₀N]; exact hprod
  have hprod'' : c₂ * c₀ * c₁ = 1 := by
    calc c₂ * c₀ * c₁ = c₂ * (c₀ * c₁) := by group
      _ = (c₀ * c₁) * c₂ := elemAbelian_mul_comm hN hc₂N (N.mul_mem hc₀N hc₁N)
      _ = 1 := hprod
  have hcyc0 : ⁅t₀, c₁⁆ = ⁅t₀, c₂⁆ := comm_eq_of_prod_eq_one hN ht₀ hc₀N hc₁N hc₂N hprod htc₀
  have hcyc1 : ⁅t₁, c₀⁆ = ⁅t₁, c₂⁆ := comm_eq_of_prod_eq_one hN ht₁ hc₁N hc₀N hc₂N hprod' htc₁
  have hcyc2 : ⁅t₂, c₀⁆ = ⁅t₂, c₁⁆ := comm_eq_of_prod_eq_one hN ht₂ hc₂N hc₀N hc₁N hprod'' htc₂
  have hu₀ : ⁅t₀, c₁⁆ ∈ L₀ := m01 c₁ hc₁
  have hu₁ : ⁅t₁, c₀⁆ ∈ L₁ := m10 c₀ hc₀
  have hu₂ : ⁅t₂, c₁⁆ ∈ L₂ := m21 c₁ hc₁
  have hu₀N := hL₀N hu₀
  have hu₁N := hL₁N hu₁
  have hu₂N := hL₂N hu₂
  have e1 : ⁅t₁, ⁅t₀, c₁⁆⁆ = c₁ := r10 c₁ hc₁
  have e2 : ⁅t₂, ⁅t₀, c₁⁆⁆ = c₂ := by rw [hcyc0]; exact r20 c₂ hc₂
  have e3 : ⁅t₁, ⁅t₂, c₁⁆⁆ = c₁ := r12 c₁ hc₁
  have e4 : ⁅t₀, ⁅t₁, c₀⁆⁆ = c₀ := r01 c₀ hc₀
  by_cases h : c₀ * ⁅t₀, c₁⁆ = 1
  ·
    have hc₀u : c₀ = ⁅t₀, c₁⁆ := by
      have := eq_inv_of_mul_eq_one_left h
      rw [this, elemAbelian_inv hN hu₀N]
    have hu₀1 : ⁅t₀, c₁⁆ ≠ 1 := by
      intro h1
      apply hc₁1
      refine inj01 c₁ hc₁ ?_
      simp only [commutatorElement_def] at h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hhom : ⁅t₀, ⁅t₁, c₀⁆ * c₁⁆ = ⁅t₀, ⁅t₁, c₀⁆⁆ * ⁅t₀, c₁⁆ := comm_mul_comm hN ht₀ hu₁N hc₁N
    rw [e4, ← hc₀u, elemAbelian_mul_self hN hc₀N] at hhom
    have hu₁c₁ : ⁅t₁, c₀⁆ * c₁ = 1 := by
      refine inj01 _ (L₁.mul_mem hu₁ hc₁) ?_
      simp only [commutatorElement_def] at hhom
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hhom
      exact hhom
    have hc₁u₁ : c₁ = ⁅t₁, c₀⁆ := by
      have := eq_inv_of_mul_eq_one_right hu₁c₁
      rw [this, elemAbelian_inv hN hu₁N]
    refine ⟨⁅t₀, c₁⁆, hu₀, hu₀1, ?_⟩
    rw [e1, e2, ← hcyc1, hc₁u₁]
  · refine ⟨c₀ * ⁅t₀, c₁⁆, L₀.mul_mem hc₀ hu₀, h, ?_⟩
    have h1 : ⁅t₁, c₀ * ⁅t₀, c₁⁆⁆ = ⁅t₁, c₀⁆ * ⁅t₁, ⁅t₀, c₁⁆⁆ := comm_mul_comm hN ht₁ hc₀N hu₀N
    have h2 : ⁅t₂, c₀ * ⁅t₀, c₁⁆⁆ = ⁅t₂, c₀⁆ * ⁅t₂, ⁅t₀, c₁⁆⁆ := comm_mul_comm hN ht₂ hc₀N hu₀N
    rw [h2, hcyc2, e2]
    have h3 : ⁅t₁, ⁅t₂, c₁⁆ * c₂⁆ = ⁅t₁, ⁅t₂, c₁⁆⁆ * ⁅t₁, c₂⁆ := comm_mul_comm hN ht₁ hu₂N hc₂N
    rw [h3, e3, ← hcyc1, h1, e1]
    exact elemAbelian_mul_comm hN hu₁N hc₁N

variable [Finite G]

theorem tri_conj_eq {T₀ T₁ T₂ L₀ L₁ L₂ N : Subgroup G} {t₀ t₁ t₂ c₀ c₁ c₂ : G}
    (hT₁ : ∃ w : G, T₁ = conjSubgroup w T₀)
    (hC01 : Cfg T₀ T₁) (hC02 : Cfg T₀ T₂) (hC12 : Cfg T₁ T₂)
    (hL01 : normIn T₀ T₁ = L₀) (hL10 : normIn T₁ T₀ = L₁) (hL02 : normIn T₀ T₂ = L₀)
    (hL20 : normIn T₂ T₀ = L₂) (hL12 : normIn T₁ T₂ = L₁) (hL21 : normIn T₂ T₁ = L₂)
    (hcard₁ : Nat.card T₁ = Nat.card L₁ * 2) (ht₀ : t₀ ∈ T₀) (ht₀L : t₀ ∉ L₀) (ht₁ : t₁ ∈ T₁)
    (ht₁L : t₁ ∉ L₁) (ht₂ : t₂ ∈ T₂) (hN : IsElemAbelian 2 N) (hL₀N : L₀ ≤ N) (hL₁N : L₁ ≤ N)
    (hL₂N : L₂ ≤ N) (htN₀ : t₀ ∈ Subgroup.normalizer (N : Set G))
    (htN₁ : t₁ ∈ Subgroup.normalizer (N : Set G)) (htN₂ : t₂ ∈ Subgroup.normalizer (N : Set G))
    (r01 : ∀ e ∈ L₀, ⁅t₀, ⁅t₁, e⁆⁆ = e) (r10 : ∀ e ∈ L₁, ⁅t₁, ⁅t₀, e⁆⁆ = e)
    (r20 : ∀ e ∈ L₂, ⁅t₂, ⁅t₀, e⁆⁆ = e) (r12 : ∀ e ∈ L₁, ⁅t₁, ⁅t₂, e⁆⁆ = e)
    (hc₀ : c₀ ∈ L₀) (hc₁ : c₁ ∈ L₁) (hc₂ : c₂ ∈ L₂) (hc₁1 : c₁ ≠ 1)
    (hprod : c₀ * c₁ * c₂ = 1) : conjSubgroup t₂ T₁ = T₀ := by
  have hw₀ : IsWC T₀ := hC01.wc
  have hL₀T : L₀ ≤ T₀ := hL01 ▸ normIn_le T₀ T₁
  have hL₁T : L₁ ≤ T₁ := hL10 ▸ normIn_le T₁ T₀
  have hL₂T : L₂ ≤ T₂ := hL20 ▸ normIn_le T₂ T₀
  have m01 : ∀ e ∈ L₁, ⁅t₀, e⁆ ∈ L₀ := fun e he =>
    hL01 ▸ hC01.comm_mem_normIn ht₀ (hL10 ▸ he)
  have m10 : ∀ e ∈ L₀, ⁅t₁, e⁆ ∈ L₁ := fun e he =>
    hL10 ▸ hC01.symm.comm_mem_normIn ht₁ (hL01 ▸ he)
  have m21 : ∀ e ∈ L₁, ⁅t₂, e⁆ ∈ L₂ := fun e he =>
    hL21 ▸ hC12.symm.comm_mem_normIn ht₂ (hL12 ▸ he)
  have m20 : ∀ e ∈ L₀, ⁅t₂, e⁆ ∈ L₂ := fun e he =>
    hL20 ▸ hC02.symm.comm_mem_normIn ht₂ (hL02 ▸ he)
  have htc₀ : t₀ * c₀ = c₀ * t₀ := elemAbelian_mul_comm hw₀.1 ht₀ (hL₀T hc₀)
  have htc₁ : t₁ * c₁ = c₁ * t₁ := elemAbelian_mul_comm hC01.wc₁.1 ht₁ (hL₁T hc₁)
  have htc₂ : t₂ * c₂ = c₂ * t₂ := elemAbelian_mul_comm hC02.wc₁.1 ht₂ (hL₂T hc₂)
  have inj01 : ∀ e ∈ L₁, t₀ * e = e * t₀ → e = 1 := fun e he h =>
    eq_one_of_comm hC01 ht₀ (by rw [hL01]; exact ht₀L) (by rw [hL10]; exact he) h
  obtain ⟨d, hd, hd1, hdd⟩ := exists_fixed_vector hN hL₀N hL₁N hL₂N htN₀ htN₁ htN₂ m01 m10 m21
    htc₀ htc₁ htc₂ r01 r10 r20 r12 inj01 hc₀ hc₁ hc₂ hc₁1 hprod
  have hdN : d ∈ N := hL₀N hd
  have ht₂i : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right (elemAbelian_mul_self hC02.wc₁.1 ht₂)
  have hd''N : t₂ * d * t₂⁻¹ ∈ N := conj_mem_of_mem_normalizer htN₂ hdN
  have he₂ : ⁅t₂, d⁆ ∈ L₂ := m20 d hd
  have hd''eq : t₂ * d * t₂⁻¹ = ⁅t₂, d⁆ * d := by simp only [commutatorElement_def]; group
  have ht₁d'' : t₁ * (t₂ * d * t₂⁻¹) = (t₂ * d * t₂⁻¹) * t₁ := by
    have hg : ⁅t₁, ⁅t₂, d⁆⁆ ∈ N := hL₁N (hL12 ▸ hC12.comm_mem_normIn ht₁ (hL21 ▸ he₂))
    have hgd : ⁅t₁, d⁆ ∈ N := hL₁N (m10 d hd)
    have he₂N : ⁅t₂, d⁆ ∈ N := hL₂N he₂
    have hconj : t₁ * (⁅t₂, d⁆ * d) * t₁⁻¹ = (⁅t₁, ⁅t₂, d⁆⁆ * ⁅t₂, d⁆) * (⁅t₁, d⁆ * d) := by
      simp only [commutatorElement_def]; group
    have h1 : t₁ * (t₂ * d * t₂⁻¹) * t₁⁻¹ = t₂ * d * t₂⁻¹ := by
      rw [hd''eq, hconj, ← hdd]
      set g := ⁅t₁, d⁆ with hgdef
      have hgg : g * g = 1 := elemAbelian_mul_self hN hgd
      calc (g * ⁅t₂, d⁆) * (g * d) = g * (⁅t₂, d⁆ * g) * d := by group
        _ = g * (g * ⁅t₂, d⁆) * d := by rw [elemAbelian_mul_comm hN he₂N hgd]
        _ = (g * g) * ⁅t₂, d⁆ * d := by group
        _ = ⁅t₂, d⁆ * d := by rw [hgg, one_mul]
    calc t₁ * (t₂ * d * t₂⁻¹) = (t₁ * (t₂ * d * t₂⁻¹) * t₁⁻¹) * t₁ := by group
      _ = (t₂ * d * t₂⁻¹) * t₁ := by rw [h1]
  have hy : ∀ y ∈ T₁, y * (t₂ * d * t₂⁻¹) = (t₂ * d * t₂⁻¹) * y := by
    intro y hyT
    by_cases hyL : y ∈ L₁
    · exact elemAbelian_mul_comm hN (hL₁N hyL) hd''N
    · have ht₁iL : t₁⁻¹ ∉ L₁ := fun h0 => ht₁L (by simpa using L₁.inv_mem h0)
      have hℓ : t₁⁻¹ * y ∈ L₁ :=
        mul_mem_of_not_mem_of_card hL₁T hcard₁ (T₁.inv_mem ht₁) hyT ht₁iL hyL
      have hℓd : (t₁⁻¹ * y) * (t₂ * d * t₂⁻¹) = (t₂ * d * t₂⁻¹) * (t₁⁻¹ * y) :=
        elemAbelian_mul_comm hN (hL₁N hℓ) hd''N
      obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = t₁⁻¹ * y := ⟨_, rfl⟩
      obtain ⟨D, hD⟩ : ∃ D, D = t₂ * d * t₂⁻¹ := ⟨_, rfl⟩
      rw [← hℓdef, ← hD] at hℓd
      rw [← hD] at ht₁d''
      rw [← hD]
      have hy' : y = t₁ * ℓ := by rw [hℓdef]; group
      calc y * D = t₁ * (ℓ * D) := by rw [hy', mul_assoc]
        _ = t₁ * (D * ℓ) := by rw [hℓd]
        _ = (t₁ * D) * ℓ := by rw [mul_assoc]
        _ = (D * t₁) * ℓ := by rw [ht₁d'']
        _ = D * (t₁ * ℓ) := by rw [mul_assoc]
        _ = D * y := by rw [← hy']
  have hcent : conjSubgroup t₂ T₁ ≤ Subgroup.centralizer ({d} : Set G) := by
    intro w hw
    obtain ⟨y, hyT, rfl⟩ := mem_conjSubgroup_iff_exists.1 hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hD : t₂⁻¹ * d * t₂ = t₂ * d * t₂⁻¹ := by rw [ht₂i]
    have hy2 : y * (t₂⁻¹ * d * t₂) = (t₂⁻¹ * d * t₂) * y := by
      rw [hD]; exact hy y hyT
    calc d * (t₂ * y * t₂⁻¹) = t₂ * ((t₂⁻¹ * d * t₂) * y) * t₂⁻¹ := by group
      _ = t₂ * (y * (t₂⁻¹ * d * t₂)) * t₂⁻¹ := by rw [hy2]
      _ = (t₂ * y * t₂⁻¹) * d := by group
  obtain ⟨w, hw⟩ := hT₁
  have hdT : d ∈ T₀ := hL₀T hd
  have hwc := (hw₀.2 d hdT hd1).2 (t₂ * w) (by
    rw [← conjSubgroup_conjSubgroup, ← hw]
    exact hcent)
  rw [hw, conjSubgroup_conjSubgroup]
  exact hwc

end CFSG.CGT.T75R
