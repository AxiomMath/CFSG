module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BThData
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.ThSchreier

section Generic

variable {G : Type*} [Group G] (D : CFSG.Sporadic.ThSchreier.AutCore.Data G)

private theorem mem_Q_of_κPerm {g : G} (h : D.κPerm g = 1) : g ∈ D.Q := by
  have h1 : D.κ (QuotientGroup.mk g) = 1 := Subtype.ext ((D.κPerm_apply g).symm.trans h)
  rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1

private theorem eq_one_of_κPerm {F : Subgroup G} (hF : IsElemAbelian 3 F) {f : G} (hf : f ∈ F)
    (h : D.κPerm f = 1) : f = 1 := by
  have hQ : IsPGroup 2 D.Q := D.core ▸ CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hQ ⟨f, mem_Q_of_κPerm D h⟩
  have hk' : f ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := (by norm_num : Nat.Coprime 3 2).pow_right k
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one (hF.2 f hf)) (orderOf_dvd_of_pow_eq_one hk'))

private theorem κPerm_conj_inj {F : Subgroup G} (hF : IsElemAbelian 3 F) (n : G) {a b : G}
    (ha : a ∈ F) (hb : b ∈ F) (h : D.κPerm (n⁻¹ * a * n) = D.κPerm (n⁻¹ * b * n)) : a = b := by
  simp only [map_mul, map_inv, mul_left_inj, mul_right_inj] at h
  have h2 : D.κPerm (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.1 (eq_one_of_κPerm D hF (F.mul_mem ha (F.inv_mem hb)) h2)

private theorem card_map_κPerm {F : Subgroup G} (hF : IsElemAbelian 3 F) (hc : Nat.card F = 27) :
    Nat.card (F.map D.κPerm) = 27 := by
  have hinj : Function.Injective (D.κPerm.comp F.subtype) := by
    rw [injective_iff_map_eq_one]
    exact fun f hf => Subtype.ext (eq_one_of_κPerm D hF f.2 hf)
  have e : F.map D.κPerm = (D.κPerm.comp F.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e, ← hc]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

private theorem exists_conj_baseNine {F : Subgroup G} (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 27) :
    ∃ n : G, (∀ f ∈ F, ∃ u, D.κPerm (n⁻¹ * f * n) = nineExp u) ∧
      ∃ f₀ ∈ F, D.κPerm (n⁻¹ * f₀ * n) = nineExp (1, 0, 0) := by
  obtain ⟨σ, hσ, hEσ⟩ := exists_conj_eq_baseNine (hF.map D.κPerm) (card_map_κPerm D hF hc)
  obtain ⟨n, hn⟩ := D.exists_κ_eq ⟨σ, hσ⟩
  have hnσ : D.κPerm n = σ := congrArg Subtype.val hn
  have key : ∀ g : G, D.κPerm (n⁻¹ * g * n) = σ⁻¹ * D.κPerm g * σ := fun g => by
    rw [map_mul, map_mul, map_inv, hnσ]
  refine ⟨n, fun f hf => ?_, ?_⟩
  · have hmem : D.κPerm f ∈ baseNine.map (MulAut.conj σ).toMonoidHom := by
      rw [← hEσ]
      exact ⟨f, hf, rfl⟩
    obtain ⟨τ, hτ, hτf⟩ := hmem
    obtain ⟨u, rfl⟩ := mem_baseNine_iff.1 hτ
    refine ⟨u, ?_⟩
    rw [key, ← hτf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · have hmem : σ * nineExp (1, 0, 0) * σ⁻¹ ∈ F.map D.κPerm := by
      rw [hEσ]
      exact ⟨nineExp (1, 0, 0), mem_baseNine_iff.2 ⟨_, rfl⟩, rfl⟩
    obtain ⟨f₀, hf₀, hf₀e⟩ := hmem
    refine ⟨f₀, hf₀, ?_⟩
    rw [key, hf₀e]
    group

theorem le_Q_of_elemAbelian_le_normalizer {F T : Subgroup G} (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 27) (hT : IsPGroup 2 T) (hFT : F ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ D.Q := by
  have hX := eq_bot_of_elemAbelian27_le_normalizer (hF.map D.κPerm) (card_map_κPerm D hF hc)
    (hT.map D.κPerm) ((Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map D.κPerm))
  intro t ht
  have h1 : D.κPerm t ∈ T.map D.κPerm := ⟨t, ht, rfl⟩
  rw [hX, Subgroup.mem_bot] at h1
  exact mem_Q_of_κPerm D h1

private def conjQ (n : G) (X : Subgroup G) : ↥(D.Q ⊓ X) →* ↥D.Q where
  toFun c := ⟨n⁻¹ * c * n, by simpa using D.normal.conj_mem c (Subgroup.mem_inf.1 c.2).1 n⁻¹⟩
  map_one' := Subtype.ext (by change n⁻¹ * (1 : G) * n = 1; group)
  map_mul' a b := Subtype.ext (by
    change n⁻¹ * ((a : G) * b) * n = n⁻¹ * a * n * (n⁻¹ * b * n)
    group)

private theorem conj_comm {n a b : G} (h : a * b = b * a) :
    (n⁻¹ * a * n) * (n⁻¹ * b * n) = (n⁻¹ * b * n) * (n⁻¹ * a * n) := by
  calc (n⁻¹ * a * n) * (n⁻¹ * b * n) = n⁻¹ * (a * b) * n := by group
    _ = n⁻¹ * (b * a) * n := by rw [h]
    _ = (n⁻¹ * b * n) * (n⁻¹ * a * n) := by group

private theorem mem_zpowers_of_conj {n c : G} (h : n⁻¹ * c * n ∈ Subgroup.zpowers D.z) :
    c ∈ Subgroup.zpowers D.z := by
  have e : c = n * (n⁻¹ * c * n) * n⁻¹ := by group
  rcases D.zpowers_z _ h with h1 | h1 <;> rw [e, h1]
  · simp
  · rw [← D.z_central n, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _

end Generic

section Fixed

variable {G : Type*} [Group G]
  (D : CFSG.Sporadic.ThSchreier.AutCore.Data G)

theorem Q_inf_centralizer_le_zpowers_of_elemAbelian {F : Subgroup G} (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 27) : D.Q ⊓ Subgroup.centralizer (F : Set G) ≤ Subgroup.zpowers D.z := by
  obtain ⟨n, -, f₀, hf₀, hf₀e⟩ := exists_conj_baseNine D hF hc
  intro c hc'
  have hπ := π_eq_one_of_comm_cycZero D hf₀e (conjQ D n _ ⟨c, hc'⟩)
    (conj_comm (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').2 f₀ hf₀))
  exact mem_zpowers_of_conj D (n := n) (c := c) ((D.center _).1 ((D.π_ker _).1 hπ))

theorem card_Q_inf_centralizer_le_of_index_three [Finite G] {F H : Subgroup G}
    (hF : IsElemAbelian 3 F) (hc : Nat.card F = 27) (hHF : H ≤ F)
    (hH : Nat.card H * 3 = Nat.card F) :
    Nat.card ↥(D.Q ⊓ Subgroup.centralizer (H : Set G)) ≤ 2 ^ 3 := by
  obtain ⟨n, hn, -⟩ := exists_conj_baseNine D hF hc
  have hH9 : Nat.card H = 9 := by omega
  obtain ⟨h₁, hh₁, hh₁1⟩ : ∃ h ∈ H, h ≠ 1 := by
    by_contra! hall
    have hbot : H = ⊥ := eq_bot_iff.2 fun h hh => Subgroup.mem_bot.2 (hall h hh)
    rw [hbot, Subgroup.card_bot] at hH9
    omega
  obtain ⟨h₂, hh₂, hh₂z⟩ : ∃ h ∈ H, h ∉ Subgroup.zpowers h₁ := by
    by_contra! hall
    have h := Subgroup.card_le_of_le (fun h hh => hall h hh : H ≤ Subgroup.zpowers h₁)
    rw [Nat.card_zpowers, orderOf_eq_prime (hF.2 h₁ (hHF hh₁)) hh₁1, hH9] at h
    omega
  obtain ⟨u₁, hu₁⟩ := hn h₁ (hHF hh₁)
  obtain ⟨u₂, hu₂⟩ := hn h₂ (hHF hh₂)
  have h1F : D.κPerm (n⁻¹ * 1 * n) = nineExp 0 := by rw [nineExp_zero]; simp
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    exact hh₁1 (κPerm_conj_inj D hF n (hHF hh₁) F.one_mem (hu₁.trans h1F.symm))
  have hne : ∀ g ∈ F, D.κPerm (n⁻¹ * h₂ * n) = D.κPerm (n⁻¹ * g * n) →
      g ∈ Subgroup.zpowers h₁ → False := fun g hg he hgz => by
    rw [← κPerm_conj_inj D hF n (hHF hh₂) hg he] at hgz
    exact hh₂z hgz
  have hu₂0 : u₂ ≠ 0 := by
    rintro rfl
    exact hne 1 F.one_mem (hu₂.trans h1F.symm) (Subgroup.one_mem _)
  have hu₂1 : u₂ ≠ u₁ := by
    rintro rfl
    exact hne h₁ (hHF hh₁) (hu₂.trans hu₁.symm) (Subgroup.mem_zpowers _)
  have hu₂2 : u₂ ≠ u₁ + u₁ := by
    intro h
    have hsq : D.κPerm (n⁻¹ * (h₁ * h₁) * n) = nineExp (u₁ + u₁) := by
      rw [nineExp_add_self, ← hu₁, ← map_mul]
      congr 1
      group
    rw [h] at hu₂
    exact hne _ (F.mul_mem (hHF hh₁) (hHF hh₁)) (hu₂.trans hsq.symm)
      (Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
  obtain ⟨S, hS, hmemS⟩ := exists_finset_card_le_four_comm_pair D hu₁0 hu₂0 hu₂1 hu₂2
  set φ := D.π.comp (conjQ D n (Subgroup.centralizer (H : Set G)))
  have hker : Nat.card φ.ker ≤ 2 := by
    have hz2 : orderOf D.z = 2 := orderOf_eq_prime (by rw [pow_two, D.z_sq]) D.z_ne_one
    have hmem : ∀ k : φ.ker, ((k : ↥(D.Q ⊓ Subgroup.centralizer (H : Set G))) : G) ∈
        Subgroup.zpowers D.z := fun k => by
      have hk : D.π (conjQ D n (Subgroup.centralizer (H : Set G)) k) = 1 := k.2
      exact mem_zpowers_of_conj D (n := n) ((D.center _).1 ((D.π_ker _).1 hk))
    have h := Nat.card_le_card_of_injective (fun k : φ.ker => (⟨_, hmem k⟩ : Subgroup.zpowers D.z))
      fun a b hab => by
        have e := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext e)
    rwa [Nat.card_zpowers, hz2] at h
  have hrange : Nat.card φ.range ≤ 4 := by
    have hL : ∀ r : φ.range, Multiplicative.toAdd (r : Multiplicative (Fin 8 → ZMod 2)) ∈ S := by
      rintro ⟨_, c, rfl⟩
      have hcH := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2
      exact hmemS _ _ hu₁ hu₂ (conjQ D n (Subgroup.centralizer (H : Set G)) c)
        (conj_comm (hcH h₁ hh₁)) (conj_comm (hcH h₂ hh₂))
    have hinj : Function.Injective fun r : φ.range => (⟨_, hL r⟩ : S) := fun a b hab => by
      have e := congrArg Subtype.val hab
      exact Subtype.ext (Multiplicative.toAdd.injective e)
    have h := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_finsetCard] at h
    exact h.trans hS
  rw [← Subgroup.card_ker_mul_card_range φ]
  exact (Nat.mul_le_mul hker hrange).trans (by norm_num)

end Fixed

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
