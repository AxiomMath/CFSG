module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitStandard

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup Equiv Equiv.Perm

theorem isConj_or_exists_commute {K : Type*} [Group K] [Finite K] {t u : K} (ht : t * t = 1)
    (hu : u * u = 1) :
    IsConj t u ∨ ∃ z : K, orderOf z = 2 ∧ z * t = t * z ∧ z * u = u * z := by
  set w := t * u with hw
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hut : u = t * w := by rw [hw, ← mul_assoc, ht, one_mul]
  have htw : ∀ j : ℕ, t * w ^ j * t = (w ^ j)⁻¹ := by
    intro j
    have h1 : t * w * t⁻¹ = w⁻¹ := by
      rw [hw, htinv, mul_inv_rev, htinv, huinv]
      calc t * (t * u) * t = (t * t) * u * t := by group
        _ = u * t := by rw [ht, one_mul]
    have h2 : t * w ^ j * t⁻¹ = (t * w * t⁻¹) ^ j := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    rw [htinv] at h2 h1
    rw [h2, h1, inv_pow]
  have hm : 0 < orderOf w := orderOf_pos w
  rcases Nat.even_or_odd (orderOf w) with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    have hk0 : 0 < k := by omega
    refine ⟨w ^ k, ?_, ?_, ?_⟩
    · rw [orderOf_pow' w hk0.ne', hk, show k + k = 2 * k by ring, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ hk0]
    ·
      have h1 : w ^ k * w ^ k = 1 := by rw [← pow_add, ← hk, pow_orderOf_eq_one]
      have h2 : (w ^ k)⁻¹ = w ^ k := inv_eq_of_mul_eq_one_right h1
      have h3 := htw k
      rw [h2] at h3
      calc w ^ k * t = t * (t * w ^ k * t) := by rw [← mul_assoc, ← mul_assoc, ht, one_mul]
        _ = t * w ^ k := by rw [h3]
    · have h1 : w ^ k * w ^ k = 1 := by rw [← pow_add, ← hk, pow_orderOf_eq_one]
      have h2 : (w ^ k)⁻¹ = w ^ k := inv_eq_of_mul_eq_one_right h1
      have h3 := htw k
      rw [h2] at h3
      have hct : Commute (w ^ k) t := by
        show w ^ k * t = t * w ^ k
        calc w ^ k * t = t * (t * w ^ k * t) := by rw [← mul_assoc, ← mul_assoc, ht, one_mul]
          _ = t * w ^ k := by rw [h3]
      have hcw : Commute (w ^ k) w := (Commute.refl w).pow_left k
      have hcu : Commute (w ^ k) u := by
        rw [hut]
        exact hct.mul_right hcw
      exact hcu.eq
  · left
    rw [isConj_iff]
    refine ⟨(w ^ (k + 1))⁻¹, ?_⟩
    have h1 : (w ^ (k + 1))⁻¹ = t * w ^ (k + 1) * t := (htw (k + 1)).symm
    rw [inv_inv, h1, hut]
    calc t * w ^ (k + 1) * t * t * w ^ (k + 1) = t * w ^ (k + 1) * (t * t) * w ^ (k + 1) := by
          group
      _ = t * (w ^ (k + 1) * w ^ (k + 1)) := by rw [ht, mul_one, mul_assoc]
      _ = t * w := by
          rw [← pow_add, show k + 1 + (k + 1) = orderOf w + 1 by omega, pow_succ,
            pow_orderOf_eq_one, one_mul]

theorem isConj_of_isStronglyEmbedded {K : Type*} [Group K] [Finite K] {M : Subgroup K}
    (hM : IsStronglyEmbedded M) {t u : K} (ht : orderOf t = 2) (hu : orderOf u = 2) :
    IsConj t u := by
  obtain ⟨hMtop, hMeven, hMg⟩ := hM
  have hsq : ∀ s : K, orderOf s = 2 → s * s = 1 := fun s hs => by
    rw [← sq, ← hs, pow_orderOf_eq_one]
  have hMem : ∀ (s g : K), orderOf s = 2 → s ∈ M → s ∈ conjugate M g → g ∈ M := by
    intro s g hs hsM hsc
    by_contra hgM
    have hodd := hMg g hgM
    have h2 : 2 ∣ Nat.card ↥(M ⊓ conjugate M g) := by
      have h1 := orderOf_dvd_natCard (⟨s, hsM, hsc⟩ : ↥(M ⊓ conjugate M g))
      have h0 : orderOf (⟨s, hsM, hsc⟩ : ↥(M ⊓ conjugate M g)) = 2 :=
        (orderOf_injective _ (M ⊓ conjugate M g).subtype_injective _).symm.trans hs
      rwa [h0] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hC : ∀ s ∈ M, orderOf s = 2 → ∀ g : K, g * s = s * g → g ∈ M := by
    intro s hs hs2 g hg
    refine hMem s g hs2 hs ?_
    rw [SolAltLit.mem_conjugate_iff_conj, hg, mul_assoc, mul_inv_cancel, mul_one]
    exact hs
  obtain ⟨⟨s, hsM⟩, hs2⟩ := exists_prime_orderOf_dvd_card' (G := M) 2
    (even_iff_two_dvd.mp hMeven)
  rw [Subgroup.orderOf_mk] at hs2
  have hout : ∀ v : K, orderOf v = 2 → v ∉ M → IsConj s v := by
    intro v hv hvM
    rcases isConj_or_exists_commute (hsq s hs2) (hsq v hv) with h | ⟨z, hz, hzs, hzv⟩
    · exact h
    · exfalso
      exact hvM (hC z (hC s hsM hs2 z hzs) hz v hzv.symm)
  have hall : ∀ v : K, orderOf v = 2 → IsConj s v := by
    intro v hv
    by_cases hvM : v ∈ M
    · obtain ⟨g, hg⟩ : ∃ g : K, g ∉ M := by
        by_contra h
        push Not at h
        exact hMtop (eq_top_iff.mpr fun x _ => h x)
      have hv2 : orderOf (g⁻¹ * v * g) = 2 := by
        rw [show g⁻¹ * v * g = g⁻¹ * v * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
          MulEquiv.orderOf_eq, hv]
      have hv' : g⁻¹ * v * g ∉ M := by
        intro hmem
        refine hg (hMem _ g hv2 hmem ?_)
        rw [SolAltLit.mem_conjugate_iff_conj]
        rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group]
        exact hvM
      have h1 := hout _ hv2 hv'
      have h2 : IsConj (g⁻¹ * v * g) v := isConj_iff.mpr ⟨g, by group⟩
      exact h1.trans h2
    · exact hout v hv hvM
  exact (hall t ht).symm.trans (hall u hu)

@[expose] def dblTransposition {n : ℕ} (hn : 8 ≤ n) : Perm (Fin n) :=
  swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩

@[expose] def dblTransposition' {n : ℕ} (hn : 8 ≤ n) : Perm (Fin n) :=
  swap ⟨4, by omega⟩ ⟨5, by omega⟩ * swap ⟨6, by omega⟩ ⟨7, by omega⟩

theorem disjoint_swap_swap {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Perm.Disjoint (swap a b) (swap c d) := by
  rw [disjoint_iff_disjoint_support, support_swap hab, support_swap hcd]
  simp [Finset.disjoint_left, hac, had, hbc, hbd]

theorem dbl_disjoint {n : ℕ} (hn : 8 ≤ n) :
    Perm.Disjoint (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
      (swap (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩) :=
  disjoint_swap_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

theorem dbl'_disjoint {n : ℕ} (hn : 8 ≤ n) :
    Perm.Disjoint (swap (⟨4, by omega⟩ : Fin n) ⟨5, by omega⟩)
      (swap (⟨6, by omega⟩ : Fin n) ⟨7, by omega⟩) :=
  disjoint_swap_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

theorem dbl_dbl'_disjoint {n : ℕ} (hn : 8 ≤ n) :
    Perm.Disjoint (dblTransposition hn) (dblTransposition' hn) := by
  rw [dblTransposition, dblTransposition']
  refine Perm.Disjoint.mul_left (Perm.Disjoint.mul_right ?_ ?_)
    (Perm.Disjoint.mul_right ?_ ?_) <;>
  exact disjoint_swap_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff])

theorem card_support_dbl {n : ℕ} (hn : 8 ≤ n) : (dblTransposition hn).support.card = 4 := by
  rw [dblTransposition, (dbl_disjoint hn).card_support_mul,
    card_support_swap (by simp [Fin.ext_iff]), card_support_swap (by simp [Fin.ext_iff])]

theorem card_support_dbl' {n : ℕ} (hn : 8 ≤ n) : (dblTransposition' hn).support.card = 4 := by
  rw [dblTransposition', (dbl'_disjoint hn).card_support_mul,
    card_support_swap (by simp [Fin.ext_iff]), card_support_swap (by simp [Fin.ext_iff])]

theorem sign_dbl {n : ℕ} (hn : 8 ≤ n) : sign (dblTransposition hn) = 1 := by
  rw [dblTransposition, Perm.sign_mul, sign_swap (by simp [Fin.ext_iff]),
    sign_swap (by simp [Fin.ext_iff])]
  decide

theorem sign_dbl' {n : ℕ} (hn : 8 ≤ n) : sign (dblTransposition' hn) = 1 := by
  rw [dblTransposition', Perm.sign_mul, sign_swap (by simp [Fin.ext_iff]),
    sign_swap (by simp [Fin.ext_iff])]
  decide

theorem dbl_mul_self {n : ℕ} (hn : 8 ≤ n) : dblTransposition hn * dblTransposition hn = 1 := by
  rw [dblTransposition, mul_assoc, ← mul_assoc (swap _ _) (swap _ _) (swap _ _),
    ← (dbl_disjoint hn).commute.eq, mul_assoc, swap_mul_self, mul_one, swap_mul_self]

theorem dbl'_mul_self {n : ℕ} (hn : 8 ≤ n) : dblTransposition' hn * dblTransposition' hn = 1 := by
  rw [dblTransposition', mul_assoc, ← mul_assoc (swap _ _) (swap _ _) (swap _ _),
    ← (dbl'_disjoint hn).commute.eq, mul_assoc, swap_mul_self, mul_one, swap_mul_self]

theorem not_hasStronglyEmbedded_of_coreQuotient {K : Type*} [Group K] [Finite K] {n : ℕ}
    (hn : 8 ≤ n) (e : K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n)) :
    ¬ FooteLit.HasStronglyEmbedded K := by
  classical
  rintro ⟨M, hM⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : K →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' _) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : K, π x = 1 → x ∈ pPrimeCore 2 K := by
    intro x hx
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have hlift : ∀ σ : alternatingGroup (Fin n), σ * σ = 1 → σ ≠ 1 →
      ∃ y : K, orderOf y = 2 ∧ π y = σ := by
    intro σ hσ hσ1
    have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hσ1
    set Y := (zpowers σ).comap π with hY
    have hmap : Y.map π = zpowers σ := Subgroup.map_comap_eq_self_of_surjective hπs _
    have h2 : 2 ∣ Nat.card Y := by
      have h1 := Subgroup.card_map_dvd Y π
      rw [hmap, Nat.card_zpowers, hσ2] at h1
      exact h1
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 h2
    refine ⟨y, by rw [Subgroup.orderOf_coe, hy], ?_⟩
    have hyY : π y ∈ zpowers σ := y.2
    rcases (LocalB.mem_zpowers_iff_of_involution σ (π y) hσ2).mp hyY with h | h
    · exfalso
      have h1 := hker y h
      have h2 := orderOf_dvd_natCard (⟨y, h1⟩ : pPrimeCore 2 K)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy] at h2
      have h3 := pPrimeCore_coprime_card (p := 2) (G := K)
      exact absurd (Nat.Coprime.coprime_dvd_right h2 h3) (by norm_num)
    · exact h
  set σ₁ : alternatingGroup (Fin n) :=
    ⟨dblTransposition hn, mem_alternatingGroup.mpr (sign_dbl hn)⟩
  set σ₂ : alternatingGroup (Fin n) := ⟨dblTransposition hn * dblTransposition' hn,
    mem_alternatingGroup.mpr (by rw [Perm.sign_mul, sign_dbl, sign_dbl', mul_one])⟩
  have hσ₁ : σ₁ * σ₁ = 1 := Subtype.ext (dbl_mul_self hn)
  have hσ₂ : σ₂ * σ₂ = 1 := by
    apply Subtype.ext
    show dblTransposition hn * dblTransposition' hn * (dblTransposition hn * dblTransposition' hn) =
      1
    rw [mul_assoc, ← mul_assoc (dblTransposition' hn), ← (dbl_dbl'_disjoint hn).commute.eq,
      mul_assoc, dbl'_mul_self, mul_one, dbl_mul_self]
  have hsupp₁ : (σ₁ : Perm (Fin n)).support.card = 4 := card_support_dbl hn
  have hsupp₂ : (σ₂ : Perm (Fin n)).support.card = 8 := by
    show (dblTransposition hn * dblTransposition' hn).support.card = 8
    rw [(dbl_dbl'_disjoint hn).card_support_mul, card_support_dbl, card_support_dbl']
  have hne₁ : σ₁ ≠ 1 := fun h => by
    have : (σ₁ : Perm (Fin n)).support.card = 0 := by rw [h]; simp
    omega
  have hne₂ : σ₂ ≠ 1 := fun h => by
    have : (σ₂ : Perm (Fin n)).support.card = 0 := by rw [h]; simp
    omega
  obtain ⟨y₁, hy₁, hπ₁⟩ := hlift σ₁ hσ₁ hne₁
  obtain ⟨y₂, hy₂, hπ₂⟩ := hlift σ₂ hσ₂ hne₂
  have hc := π.map_isConj (isConj_of_isStronglyEmbedded hM hy₁ hy₂)
  rw [hπ₁, hπ₂] at hc
  obtain ⟨c, hcc⟩ := isConj_iff.mp ((alternatingGroup (Fin n)).subtype.map_isConj hc)
  have h1 := card_support_conj (σ := c) (τ := ((alternatingGroup (Fin n)).subtype σ₁))
  rw [hcc] at h1
  change (σ₂ : Perm (Fin n)).support.card = (σ₁ : Perm (Fin n)).support.card at h1
  omega

end CFSG.ComponentClassification.Sol78
