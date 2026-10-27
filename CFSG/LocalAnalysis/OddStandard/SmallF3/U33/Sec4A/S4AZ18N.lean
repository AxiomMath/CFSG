module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18J
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18M

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem z18_exists_M_abs {Y K V₁ V₂ : Subgroup G} {t lam : G} (hV₂ : IsPGroup 2 V₂)
    (hN : V₂ ≤ normalizer (Y : Set G)) (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hY2 : ∀ y ∈ Y, y * y = 1) (hY16 : Nat.card Y = 16)
    (hker : V₂ ⊓ centralizer (Y : Set G) = K) (hKV₁ : K ≤ V₁) (hV₁ : V₁ ≤ V₂)
    (ht : t ∈ V₁) (hl : lam ∈ V₁) (ht2 : t * t = 1) (hl2 : lam * lam = 1)
    (htl : t * lam = lam * t) (htK : t ∉ K)
    (hlY : ¬ ∀ y ∈ Y, y * lam = lam * y)
    (htlY : ¬ ∀ y ∈ Y, y * (t * lam) = (t * lam) * y)
    (hV₁dec : ∀ v ∈ V₁, ∃ q ∈ K, ∃ k : G,
      (k = 1 ∨ k = t ∨ k = lam ∨ k = t * lam) ∧ v = q * k)
    (hcl : ∀ x ∈ V₂, x * t * x⁻¹ * t⁻¹ ∈ K → x ∈ V₁) (hbig : ¬ V₂ ≤ V₁)
    (hlam : ∀ g : G, ∀ k ∈ K, g⁻¹ * t * g ≠ lam * k) :
    ∃ M : Subgroup G, M ≤ V₂ ∧ M.relIndex V₂ = 2 ∧ t ∉ M ∧
      ∀ u ∈ M, u * u = 1 → u ∈ K ∨ ∃ k ∈ K, u = lam * k := by
  classical
  have hker' : ∀ v : ↥V₂, z18Psi Y V₂ hN v = 1 ↔ (v : G) ∈ K := by
    intro v
    rw [z18Psi_eq_one_iff, ← hker, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨fun hc => ⟨v.2, hc⟩, fun hc => hc.2⟩
  set ψ : ↥V₂ →* MulAut ↥Y := z18Psi Y V₂ hN with hψdef
  set ψ' : ↥V₂ →* ↥ψ.range := ψ.rangeRestrict with hψ'def
  have hψ' : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  haveI : Finite ↥ψ.range := Finite.of_surjective ψ' hψ'
  have hpg : IsPGroup 2 ↥ψ.range := hV₂.of_surjective ψ' hψ'
  have hone : ∀ v : ↥V₂, ψ' v = 1 ↔ (v : G) ∈ K := fun v =>
    ⟨fun hh => (hker' v).mp (congrArg Subtype.val hh), fun hh => Subtype.ext ((hker' v).mpr hh)⟩
  have hexp : ∀ g : ↥ψ.range, g ^ 4 = 1 := by
    intro g
    obtain ⟨v, rfl⟩ := hψ' g
    exact Subtype.ext (z18_psi_pow4 Y V₂ hN hV₂ hYc hY2 hY16 v)
  obtain ⟨tV, htV⟩ : ∃ tV : ↥V₂, (tV : G) = t := ⟨⟨t, hV₁ ht⟩, rfl⟩
  obtain ⟨lV, hlV⟩ : ∃ lV : ↥V₂, (lV : G) = lam := ⟨⟨lam, hV₁ hl⟩, rfl⟩
  have htV2 : tV * tV = 1 := Subtype.ext (show (tV : G) * tV = 1 by rw [htV]; exact ht2)
  have hlV2 : lV * lV = 1 := Subtype.ext (show (lV : G) * lV = 1 by rw [hlV]; exact hl2)
  have htlV : tV * lV = lV * tV :=
    Subtype.ext (show (tV : G) * lV = lV * tV by rw [htV, hlV]; exact htl)
  have ha : ψ' tV * ψ' tV = 1 := by rw [← map_mul, htV2, map_one]
  have hb : ψ' lV * ψ' lV = 1 := by rw [← map_mul, hlV2, map_one]
  have hab : ψ' tV * ψ' lV = ψ' lV * ψ' tV := by rw [← map_mul, ← map_mul, htlV]
  have ha1 : ψ' tV ≠ 1 := fun h1 => htK (by have := (hone tV).mp h1; rwa [htV] at this)
  have hb1 : ψ' lV ≠ 1 := by
    intro h1
    apply hlY
    have := (z18Psi_eq_one_iff Y V₂ hN lV).mp (congrArg Subtype.val h1)
    rwa [hlV] at this
  have hne : ψ' tV ≠ ψ' lV := by
    intro h1
    apply htlY
    have h2 : ψ' (tV * lV) = 1 := by rw [map_mul, h1, ← map_mul, hlV2, map_one]
    have h3 := (z18Psi_eq_one_iff Y V₂ hN (tV * lV)).mp (congrArg Subtype.val h2)
    intro y hy
    have h4 : y * ((tV : G) * (lV : G)) = ((tV : G) * (lV : G)) * y := h3 y hy
    rwa [htV, hlV] at h4
  have hmem_of_psi : ∀ v w : ↥V₂, ψ' v = ψ' w → (w : G)⁻¹ * v ∈ K := by
    intro v w hvw
    have h1 : ψ' (w⁻¹ * v) = 1 := by rw [map_mul, map_inv, hvw, inv_mul_cancel]
    exact (hone _).mp h1
  have hmemV₁ : ∀ k v : G, k ∈ V₁ → k⁻¹ * v ∈ K → v ∈ V₁ := by
    intro k v hk hkv
    simpa using Subgroup.mul_mem V₁ hk (hKV₁ hkv)
  have hC : ∀ x : ↥ψ.range, x * ψ' tV = ψ' tV * x →
      x = 1 ∨ x = ψ' tV ∨ x = ψ' lV ∨ x = ψ' tV * ψ' lV := by
    intro x hx
    obtain ⟨v, rfl⟩ := hψ' x
    have h1 : ψ' (v * tV * v⁻¹ * tV⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hx]
      group
    have h2 : (v : G) * (tV : G) * (v : G)⁻¹ * (tV : G)⁻¹ ∈ K := (hone _).mp h1
    rw [htV] at h2
    obtain ⟨q, hq, k, hk, hvk⟩ := hV₁dec _ (hcl _ v.2 h2)
    obtain ⟨qV, hqV⟩ : ∃ qV : ↥V₂, (qV : G) = q := ⟨⟨q, hV₁ (hKV₁ hq)⟩, rfl⟩
    have hψq : ψ' qV = 1 := (hone qV).mpr (by rw [hqV]; exact hq)
    rcases hk with hk | hk | hk | hk
    · left
      exact (hone v).mpr (by rw [hvk, hk, mul_one]; exact hq)
    · right; left
      have hvq : v = qV * tV := Subtype.ext (show (v : G) = qV * tV by rw [hvk, hk, hqV, htV])
      rw [hvq, map_mul, hψq, one_mul]
    · right; right; left
      have hvq : v = qV * lV := Subtype.ext (show (v : G) = qV * lV by rw [hvk, hk, hqV, hlV])
      rw [hvq, map_mul, hψq, one_mul]
    · right; right; right
      have hvq : v = qV * (tV * lV) :=
        Subtype.ext (show (v : G) = qV * (tV * lV) by rw [hvk, hk, hqV, htV, hlV])
      rw [hvq, map_mul, hψq, one_mul, map_mul]
  have hbig' : ∃ x : ↥ψ.range, x ≠ 1 ∧ x ≠ ψ' tV ∧ x ≠ ψ' lV ∧ x ≠ ψ' tV * ψ' lV := by
    obtain ⟨v, hvV₂, hvV₁⟩ := SetLike.not_le_iff_exists.mp hbig
    have hne_of : ∀ w : ↥V₂, (w : G) ∈ V₁ → ψ' ⟨v, hvV₂⟩ ≠ ψ' w := fun w hw hvw =>
      hvV₁ (hmemV₁ _ _ hw (hmem_of_psi _ _ hvw))
    refine ⟨ψ' ⟨v, hvV₂⟩, ?_, ?_, ?_, ?_⟩
    · have h1 := hne_of 1 (Subgroup.one_mem V₁)
      rwa [map_one] at h1
    · exact hne_of tV (by rw [htV]; exact ht)
    · exact hne_of lV (by rw [hlV]; exact hl)
    · rw [← map_mul]
      exact hne_of (tV * lV) (show (tV : G) * lV ∈ V₁ by rw [htV, hlV]; exact V₁.mul_mem ht hl)
  have hconj : ∀ g : ↥ψ.range, g * ψ' tV * g⁻¹ ≠ ψ' lV := by
    intro g hg
    obtain ⟨v, rfl⟩ := hψ' g
    have h1 : ψ' (lV⁻¹ * (v * tV * v⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hg]
      exact inv_mul_cancel _
    have h2 : (lV : G)⁻¹ * ((v : G) * (tV : G) * (v : G)⁻¹) ∈ K := (hone _).mp h1
    rw [htV, hlV] at h2
    exact hlam (v : G)⁻¹ _ h2 (by group)
  obtain ⟨MT, hMTidx, hMTa, hMTu⟩ := z18_T_lemma hpg hexp ha hb hab ha1 hb1 hne hC hbig' hconj
  obtain ⟨M, hMV, hMidx, hMmem⟩ := z18_lift_index_two ψ' hψ' MT hMTidx
  refine ⟨M, hMV, hMidx, ?_, ?_⟩
  · intro htM
    exact hMTa ((hMmem tV).mp (by rw [htV]; exact htM))
  · intro u hu hu2
    obtain ⟨uV, huV⟩ : ∃ uV : ↥V₂, (uV : G) = u := ⟨⟨u, hMV hu⟩, rfl⟩
    have h1 : ψ' uV ∈ MT := (hMmem uV).mp (by rw [huV]; exact hu)
    have h2 : ψ' uV * ψ' uV = 1 := by
      rw [← map_mul]
      have : uV * uV = 1 := Subtype.ext (show (uV : G) * uV = 1 by rw [huV]; exact hu2)
      rw [this, map_one]
    rcases hMTu _ h1 h2 with h3 | h3
    · left
      have := (hone uV).mp h3
      rwa [huV] at this
    · right
      have h4 := hmem_of_psi uV lV h3
      rw [hlV, huV] at h4
      exact ⟨lam⁻¹ * u, h4, by group⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
