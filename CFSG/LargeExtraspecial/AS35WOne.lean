module

public import CFSG.LargeExtraspecial.AS35WDefs
public import CFSG.LargeExtraspecial.AS35WOneAct
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

variable {X : Type} [Group X]

theorem card_le_of_forall_mem (E : Subgroup X) (s : Finset X) (h : ∀ e ∈ E, e ∈ s) :
    Nat.card E ≤ s.card := by
  classical
  have hinj : Function.Injective (fun e : E => (⟨(e : X), h e e.2⟩ : s)) := by
    intro e₁ e₂ he
    have := congrArg Subtype.val he
    exact Subtype.ext this
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_finsetCard] at this

theorem mem_oTwoCent_self {z : X} (hz : orderOf z = 2) : z ∈ oTwoCent z := by
  refine le_oTwoCent (P := zpowers z) ?_ ?_ ?_ (mem_zpowers z)
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  · intro c hc p hp
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hp
    rw [mem_centralizer_singleton_iff] at hc
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← conj_zpow, hc, mul_inv_cancel_right]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])

theorem W2Data.quatLike {z : X} (h : W2Data X z) (hone : ∀ x : X, orderOf x = 2 → IsConj z x) :
    QuatLike z (oTwoCent z) := by
  have hz2 := h.orderOf_eq
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  refine ⟨hzz, hz1, mem_oTwoCent_self hz2, fun r hr => ?_, fun r hr => ?_⟩
  · exact mem_centralizer_singleton_iff.1 (oTwoCent_le_centralizer z hr)
  · rcases h.sq_eq r hr with h1 | h1
    · by_cases hr1 : r = 1
      · exact Or.inl hr1
      · right; left
        exact h.weaklyClosed r hr (hone r (orderOf_eq_prime h1 hr1))
    · exact Or.inr (Or.inr h1)

variable [Finite X]

theorem W2Data.false_of_oneClass_of_le {z : X} (h : W2Data X z)
    (hone : ∀ x : X, orderOf x = 2 → IsConj z x) (E : Subgroup X)
    (hE : Open.IsElemAbelian 2 E) (hEz : E ≤ centralizer ({z} : Set X)) {k : ℕ}
    (hk : Nat.card E = 2 ^ k) (hk3 : 3 ≤ k) : False := by
  classical
  have hq := h.quatLike hone
  set R := oTwoCent z with hR
  have h8 : 8 ≤ Nat.card E := by
    rw [hk]
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hEz' : ∀ e ∈ E, e * z = z * e := fun e he =>
    mem_centralizer_singleton_iff.1 (hEz he)
  have hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := fun e he r hr =>
    conj_mem_oTwoCent (hEz he) hr
  have hfs : ∀ c : X, c * z = z * c → (∀ r ∈ R, c * r = r * c) → c ∈ R := fun c hc hcr =>
    h.selfCentralizing c (mem_centralizer_singleton_iff.2 hc) hcr
  have hE1 : ∀ e ∈ E, e ∈ R → e = 1 ∨ e = z := by
    intro e he heR
    rcases hq.cases e heR with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (h1.symm.trans (hE.2 e he)) hq.z_ne_one
  by_cases hA : ∀ r ∈ R, r = 1 ∨ r = z
  ·
    have hsub : ∀ e ∈ E, e ∈ ({1, z} : Finset X) := by
      intro e he
      have := hE1 e he (hfs e (hEz' e he) fun r hr => by
        rcases hA r hr with rfl | rfl
        · simp
        · exact hEz' e he)
      simpa using this
    have := card_le_of_forall_mem E _ hsub
    have h2 : ({1, z} : Finset X).card ≤ 2 := Finset.card_le_two
    omega
  push Not at hA
  obtain ⟨a, haR, ha1, haz⟩ := hA
  have ha : a ^ 2 = z := by
    rcases hq.cases a haR with h1 | h1 | h1
    · exact absurd h1 ha1
    · exact absurd h1 haz
    · exact h1
  by_cases hB : ∀ r ∈ R, r = 1 ∨ r = z ∨ r = a ∨ r = a * z
  ·
    have hconj : ∀ e ∈ E, e * a * e⁻¹ = a ∨ e * a * e⁻¹ = a * z := by
      intro e he
      rcases hB _ (hER e he a haR) with h1 | h1 | h1
      · refine absurd ?_ ha1
        have : a = e⁻¹ * (e * a * e⁻¹) * e := by group
        rw [this, h1]
        group
      · refine absurd ?_ haz
        have : a = e⁻¹ * (e * a * e⁻¹) * e := by group
        rw [this, h1]
        calc e⁻¹ * z * e = e⁻¹ * (z * e) := by group
          _ = e⁻¹ * (e * z) := by rw [hEz' e he]
          _ = z := by group
      · exact h1
    have hcomm : ∀ e ∈ E, e * a * e⁻¹ = a → e = 1 ∨ e = z := by
      intro e he hea
      refine hE1 e he (hfs e (hEz' e he) fun r hr => ?_)
      have hea' : e * a = a * e := by
        calc e * a = e * a * e⁻¹ * e := by group
          _ = a * e := by rw [hea]
      rcases hB r hr with rfl | rfl | rfl | rfl
      · simp
      · exact hEz' e he
      · exact hea'
      · exact (Commute.mul_right hea' (hEz' e he)).eq
    by_cases hall : ∀ e ∈ E, e * a * e⁻¹ = a
    · have hsub : ∀ e ∈ E, e ∈ ({1, z} : Finset X) := fun e he => by
        simpa using hcomm e he (hall e he)
      have := card_le_of_forall_mem E _ hsub
      have h2 : ({1, z} : Finset X).card ≤ 2 := Finset.card_le_two
      omega
    push Not at hall
    obtain ⟨e₀, he₀, he₀a⟩ := hall
    have he₀a' : e₀ * a * e₀⁻¹ = a * z := (hconj e₀ he₀).resolve_left he₀a
    have hsub : ∀ e ∈ E, e ∈ ({1, z, e₀⁻¹, e₀⁻¹ * z} : Finset X) := by
      intro e he
      rcases hconj e he with h1 | h1
      · rcases hcomm e he h1 with rfl | rfl <;> simp
      · have h2 : (e₀ * e) * a * (e₀ * e)⁻¹ = a := by
          calc (e₀ * e) * a * (e₀ * e)⁻¹ = e₀ * (e * a * e⁻¹) * e₀⁻¹ := by group
            _ = e₀ * (a * z) * e₀⁻¹ := by rw [h1]
            _ = e₀ * a * e₀⁻¹ * (e₀ * z * e₀⁻¹) := by group
            _ = a * z * z := by
              rw [he₀a', show e₀ * z * e₀⁻¹ = z by rw [hEz' e₀ he₀]; group]
            _ = a := by rw [mul_assoc, hq.z_mul_z, mul_one]
        rcases hcomm _ (E.mul_mem he₀ he) h2 with h3 | h3
        · have : e = e₀⁻¹ := eq_inv_of_mul_eq_one_right h3
          simp [this]
        · have : e = e₀⁻¹ * z := by rw [← h3]; group
          simp [this]
    have := card_le_of_forall_mem E _ hsub
    have h4 : ({1, z, e₀⁻¹, e₀⁻¹ * z} : Finset X).card ≤ 4 := Finset.card_le_four
    omega
  push Not at hB
  obtain ⟨b, hbR, hb1, hbz, hba, hbaz⟩ := hB
  have hb : b ^ 2 = z := by
    rcases hq.cases b hbR with h1 | h1 | h1
    · exact absurd h1 hb1
    · exact absurd h1 hbz
    · exact h1
  have := hq.card_le_four haR hbR ha hb ⟨hba, hbaz⟩ E
    (IsPGroup.of_card hk) hEz' hER hfs hE1
  omega

theorem W2Data.false_of_oneClass {z : X} (h : W2Data X z)
    (hone : ∀ x : X, orderOf x = 2 → IsConj z x) (hr : 3 ≤ Open.twoRank X) : False := by
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup X)
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨P', hP'⟩ := hE2.exists_le_sylow
  obtain ⟨P, hP⟩ := h.sylow_le
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P'
  have h' := h.map (MulAut.conj g)
  have hone' : ∀ x : X, orderOf x = 2 → IsConj (MulAut.conj g z) x := fun x hx =>
    (isConj_iff.2 ⟨g⁻¹, by simp [MulAut.conj_apply]; group⟩).trans (hone x hx)
  have hEz : E ≤ centralizer ({MulAut.conj g z} : Set X) := by
    intro e he
    rw [mem_centralizer_map_iff]
    have he' : e ∈ ((g • P : Sylow 2 X) : Subgroup X) := hg ▸ hP' he
    rw [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at he'
    have he'' : g⁻¹ * e * g ∈ (P : Subgroup X) := by
      simpa [MulAut.inv_def, MulAut.conj_symm_apply] using he'
    simpa [MulAut.conj_symm_apply] using hP he''
  exact h'.false_of_oneClass_of_le hone' E hE hEz hEcard hr

end AS35W

end CFSG.LargeExtraspecial
