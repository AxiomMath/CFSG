module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Red
public import CFSG.GH74.GLS.IVK.Proofs2.DihedralCenter

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section NI

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem mul_mem_innAut_of_not_mem (hF : L2Field F) (e : K ≃* L2 F) {x y : MulAut K}
    (hx : x ∈ innDiagSub e) (hy : y ∈ innDiagSub e) (hxI : x ∉ innAut K) (hyI : y ∉ innAut K) :
    x * y ∈ innAut K := by
  have hidx : ((innAut K).subgroupOf (innDiagSub e)).index = 2 := innAut_relIndex_two e hF
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  set H : Subgroup ↥(innDiagSub e) := (innAut K).subgroupOf (innDiagSub e) with hH
  have hxH : (⟨x, hx⟩ : ↥(innDiagSub e)) ∉ H := hxI
  have hyH : (⟨y, hy⟩ : ↥(innDiagSub e)) ∉ H := hyI
  have hyinvH : (⟨y, hy⟩ : ↥(innDiagSub e))⁻¹ ∉ H := fun h => hyH (by simpa using H.inv_mem h)
  have h1 : (⟨x, hx⟩ : ↥(innDiagSub e)) * a ∈ H := by
    rcases ha ⟨x, hx⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxH
  have h2 : (⟨y, hy⟩ : ↥(innDiagSub e))⁻¹ * a ∈ H := by
    rcases ha (⟨y, hy⟩ : ↥(innDiagSub e))⁻¹ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hyinvH
  have h3 : (⟨x, hx⟩ : ↥(innDiagSub e)) * ⟨y, hy⟩ ∈ H := by
    have := H.mul_mem h1 (H.inv_mem h2)
    have e : (⟨x, hx⟩ : ↥(innDiagSub e)) * a * ((⟨y, hy⟩ : ↥(innDiagSub e))⁻¹ * a)⁻¹ =
        ⟨x, hx⟩ * ⟨y, hy⟩ := by group
    rwa [e] at this
  exact h3

theorem card_fixedSubgroup_inndiag (hF : L2Field F) (e : K ≃* L2 F) :
    ∃ dI dD : ℕ, (dI = Nat.card F - 1 ∨ dI = Nat.card F + 1) ∧
      (dD = Nat.card F - 1 ∨ dD = Nat.card F + 1) ∧ dI ≠ dD ∧
      (∀ u : K, orderOf u = 2 → Nat.card ↥(fixedSubgroup K (MulAut.conj u)) = dI) ∧
      (∀ w : MulAut K, w ∈ innDiagSub e → w ∉ innAut K → orderOf w = 2 →
        Nat.card ↥(fixedSubgroup K w) = dD) := by
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  have hq4 := hF.2
  obtain ⟨dI, hdI⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨dD, hdD⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
    ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨dI, dD, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hε1 with rfl | rfl <;> omega
  · rcases hε1 with rfl | rfl <;> omega
  · rcases hε1 with rfl | rfl <;> omega
  · intro u hu
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε dI hdI u hu).2.1
    have : NeZero k := ⟨by omega⟩
    have hfix : fixedSubgroup K (MulAut.conj u) = centralizer ({u} : Set K) :=
      Lemma118.fixedSubgroup_conj u
    rw [hfix, Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    omega
  · intro w hw hwI hw2
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3b F hF K e ε hε1 hε dD hdD w hw hwI hw2).2.1
    have : NeZero k := ⟨by omega⟩
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    omega

theorem not_dvd_pm_one {q : ℕ} (hq : 5 ≤ q) : ¬ (q - 1 ∣ q + 1) ∧ ¬ (q + 1 ∣ q - 1) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hc
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  · intro h
    have := Nat.le_of_dvd (by omega) h
    omega

theorem not_dvd_of_pm_one {q a b : ℕ} (hq : 5 ≤ q) (ha : a = q - 1 ∨ a = q + 1)
    (hb : b = q - 1 ∨ b = q + 1) (hab : a ≠ b) : ¬ (a ∣ b) ∧ ¬ (b ∣ a) := by
  obtain ⟨h1, h2⟩ := not_dvd_pm_one hq
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩
  · exact absurd rfl hab

theorem not_fixed_le (hF : L2Field F) (hq : 11 ≤ Nat.card F) (e : K ≃* L2 F) (N : L2Notation e)
    {w₁ w₂ : MulAut K} (h1 : w₁ ^ 2 = 1) (h2 : w₂ ^ 2 = 1) (hne : w₁ ≠ w₂) (hw₁ : w₁ ≠ 1)
    (hw₂ : w₂ ≠ 1) (hcomm : w₁ * w₂ = w₂ * w₁) (hD₁ : w₁ ∈ innDiagSub e) :
    ¬ fixedSubgroup K w₂ ≤ fixedSubgroup K w₁ := by
  intro hle
  obtain ⟨dI, dD, hdI, hdD, hne', hI, hD⟩ := card_fixedSubgroup_inndiag hF e
  have hinj := conj_injective_of_L2 e
  have ho1 : orderOf w₁ = 2 := orderOf_eq_prime h1 hw₁
  have ho2 : orderOf w₂ = 2 := orderOf_eq_prime h2 hw₂
  have hdvd : Nat.card ↥(fixedSubgroup K w₂) ∣ Nat.card ↥(fixedSubgroup K w₁) :=
    Subgroup.card_dvd_of_le hle
  have hordc : ∀ u : K, orderOf (MulAut.conj u) = orderOf u := fun u => orderOf_injective _ hinj u
  have hnd := not_dvd_of_pm_one (q := Nat.card F) (by omega) hdI hdD hne'
  by_cases hD₂ : w₂ ∈ innDiagSub e
  · by_cases hI1 : w₁ ∈ innAut K
    · obtain ⟨u₁, rfl⟩ := hI1
      have hu₁ : orderOf u₁ = 2 := by rw [← hordc]; exact ho1
      have hc1 := hI u₁ hu₁
      by_cases hI2 : w₂ ∈ innAut K
      · obtain ⟨u₂, rfl⟩ := hI2
        have hu₂ : orderOf u₂ = 2 := by rw [← hordc]; exact ho2
        have hc2 := hI u₂ hu₂
        have heq : fixedSubgroup K (MulAut.conj u₂) = fixedSubgroup K (MulAut.conj u₁) :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
        rw [Lemma118.fixedSubgroup_conj, Lemma118.fixedSubgroup_conj] at heq
        obtain ⟨k, hk6, -, -, ⟨ψ⟩⟩ := exists_dihedral_inner hF hq e hu₁
        have hm1 : u₁ ∈ centralizer ({u₁} : Set K) := mem_centralizer_singleton_iff.2 rfl
        have hm2 : u₂ ∈ centralizer ({u₁} : Set K) := by
          rw [← heq]
          exact mem_centralizer_singleton_iff.2 rfl
        have hz := dihedral_central_unique (by omega : 3 ≤ k) ψ (z := ⟨u₁, hm1⟩) (z' := ⟨u₂, hm2⟩)
          (fun h' => by
            have : u₁ = 1 := congrArg Subtype.val h'
            rw [this, orderOf_one] at hu₁
            omega)
          (fun c => Subtype.ext (mem_centralizer_singleton_iff.1 c.2))
          (fun h' => by
            have : u₂ = 1 := congrArg Subtype.val h'
            rw [this, orderOf_one] at hu₂
            omega)
          (fun c => by
            have hc : (c : K) ∈ centralizer ({u₂} : Set K) := by rw [heq]; exact c.2
            exact Subtype.ext (mem_centralizer_singleton_iff.1 hc))
        have hu12 : u₁ = u₂ := congrArg Subtype.val hz
        exact hne (by rw [hu12])
      · rw [hc1, hD w₂ hD₂ hI2 ho2] at hdvd
        exact hnd.2 hdvd
    · by_cases hI2 : w₂ ∈ innAut K
      · obtain ⟨u₂, rfl⟩ := hI2
        have hu₂ : orderOf u₂ = 2 := by rw [← hordc]; exact ho2
        rw [hI u₂ hu₂, hD w₁ hD₁ hI1 ho1] at hdvd
        exact hnd.1 hdvd
      ·
        have hc1 := hD w₁ hD₁ hI1 ho1
        have hc2 := hD w₂ hD₂ hI2 ho2
        have heq : fixedSubgroup K w₂ = fixedSubgroup K w₁ :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
        obtain ⟨z, hz⟩ := mul_mem_innAut_of_not_mem hF e hD₁ hD₂ hI1 hI2
        have hz1 : z ≠ 1 := by
          rintro rfl
          rw [map_one] at hz
          apply hne
          have : w₂ = w₁⁻¹ := by
            calc w₂ = w₁⁻¹ * (w₁ * w₂) := by group
              _ = w₁⁻¹ := by rw [← hz, mul_one]
          rw [this]
          have : w₁ * w₁ = 1 := by rw [← pow_two]; exact h1
          exact (inv_eq_of_mul_eq_one_right this).symm
        have hz2 : z ^ 2 = 1 := by
          apply hinj
          rw [map_pow, map_one, pow_two, hz]
          calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
            _ = w₁ * (w₁ * w₂) * w₂ := by rw [hcomm]
            _ = (w₁ * w₁) * (w₂ * w₂) := by group
            _ = 1 := by rw [← pow_two, ← pow_two, h1, h2, one_mul]
        have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
        have hCz : fixedSubgroup K w₁ ≤ centralizer ({z} : Set K) := by
          intro c hc
          have hc' : w₁ c = c := hc
          have hc2' : c ∈ fixedSubgroup K w₂ := by
            rw [heq]
            exact hc
          have hc'' : w₂ c = c := hc2'
          rw [mem_centralizer_singleton_iff]
          have h3 : (MulAut.conj z) c = c := by
            rw [hz]
            show w₁ (w₂ c) = c
            rw [hc'', hc']
          rw [MulAut.conj_apply] at h3
          calc c * z = (z * c * z⁻¹) * z := by rw [h3]
            _ = z * c := by group
        have hdvd2 : Nat.card ↥(fixedSubgroup K w₁) ∣ Nat.card ↥(centralizer ({z} : Set K)) :=
          Subgroup.card_dvd_of_le hCz
        have hcz : Nat.card ↥(centralizer ({z} : Set K)) = dI := by
          have := hI z hzo
          rwa [Lemma118.fixedSubgroup_conj] at this
        rw [hc1, hcz] at hdvd2
        exact hnd.2 hdvd2
  ·
    obtain ⟨q₀, hq₀, hcard⟩ := card_fixedSubgroup_outer hF e N h2 hD₂
    have hC1 : Nat.card ↥(fixedSubgroup K w₁) ≤ Nat.card F + 1 := by
      by_cases hI1 : w₁ ∈ innAut K
      · obtain ⟨u, rfl⟩ := hI1
        have hu : orderOf u = 2 := by rw [← hordc]; exact ho1
        rw [hI u hu]
        rcases hdI with h | h <;> omega
      · rw [hD w₁ hD₁ hI1 ho1]
        rcases hdD with h | h <;> omega
    have hle2 := Nat.le_of_dvd Nat.card_pos hdvd
    rw [hcard] at hle2
    have hq04 : 4 ≤ q₀ := by
      by_contra h
      have h3 : q₀ ≤ 3 := by omega
      have : q₀ ^ 2 ≤ 9 := by nlinarith
      omega
    obtain ⟨m, hm⟩ : ∃ m, q₀ ^ 2 = m + 1 := ⟨q₀ ^ 2 - 1, by
      have : 1 ≤ q₀ ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega⟩
    rw [hm, Nat.add_sub_cancel] at hle2
    have hm10 : 10 ≤ m := by omega
    nlinarith

end NI

end CFSG.GH74.GLS.IVK.Proofs2
