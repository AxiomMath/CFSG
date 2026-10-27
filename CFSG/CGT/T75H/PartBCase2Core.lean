module

public import CFSG.CGT.T75H.PartBLift
public import CFSG.CGT.T75H.PartBClassify
public import CFSG.CGT.T75H.PartBFl2

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {R : Type} [Group R] [Finite R]

theorem ker_jMap_invariant (φ : R ≃* R) {w : R} (hw : w ∈ (jMap R).ker) :
    φ w ∈ (jMap R).ker := by
  rw [mem_ker_jMap] at hw ⊢
  intro r
  have h := map_pCore_equiv' φ (hw (φ.symm r))
  rwa [map_commutatorElement, MulEquiv.apply_symm_apply] at h

theorem eq_one_of_mul_self_eq_one_of_odd_order {A : Type*} [Group A] {m : A}
    (hodd : Odd (orderOf m)) (h1 : m * m = 1) : m = 1 := by
  obtain ⟨r, hr⟩ := hodd
  have hmo : m ^ (2 * r + 1) = 1 := by rw [← hr]; exact pow_orderOf_eq_one m
  have hsq : m ^ 2 = 1 := by rw [sq]; exact h1
  have h3 : m ^ (2 * r + 1) = (m ^ 2) ^ r * m := by rw [pow_succ, pow_mul]
  rw [hsq, one_pow, one_mul, hmo] at h3
  exact h3.symm

omit [Finite R] in
theorem eq_one_of_mul_self_mem_pCore {m : R} (hodd : Odd (orderOf m))
    (h : m * m ∈ CFSG.pCore 2 R) : m = 1 := by
  have hodd2 : Odd (orderOf (m * m)) := by
    rw [← sq]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd 2)
  exact eq_one_of_mul_self_eq_one_of_odd_order hodd (eq_one_of_mem_pCore_of_odd h hodd2)

omit [Finite R] in
theorem mul_conj_eq_sq {ℓ m : R} (hℓℓ : ℓ * ℓ = 1) (hm : ℓ * m * ℓ⁻¹ = m⁻¹) :
    ℓ * (m⁻¹ * ℓ * m) = m * m := by
  have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓℓ
  rw [hℓinv] at hm
  have h1 : ℓ * m⁻¹ * ℓ = m := by
    have : ℓ * m⁻¹ * ℓ = (ℓ * m * ℓ)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hℓinv]
      group
    rw [this, hm, inv_inv]
  calc ℓ * (m⁻¹ * ℓ * m) = (ℓ * m⁻¹ * ℓ) * m := by group
    _ = m * m := by rw [h1]

omit [Finite R] in
theorem not_mem_ker_of_inverted {ℓ m : R} (hℓℓ : ℓ * ℓ = 1) (hm : ℓ * m * ℓ⁻¹ = m⁻¹)
    (hodd : Odd (orderOf m)) (hm1 : m ≠ 1) : m ∉ (jMap R).ker := by
  intro hker
  have hcomm : ⁅m, ℓ⁆ ∈ CFSG.pCore 2 R := mem_ker_jMap.1 hker ℓ
  have e : ⁅m, ℓ⁆ = m * m := by
    have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓℓ
    rw [commutatorElement_def]
    have : ℓ * m⁻¹ * ℓ⁻¹ = m := by
      have h1 : ℓ * m⁻¹ * ℓ⁻¹ = (ℓ * m * ℓ⁻¹)⁻¹ := by group
      rw [h1, hm, inv_inv]
    calc m * ℓ * m⁻¹ * ℓ⁻¹ = m * (ℓ * m⁻¹ * ℓ⁻¹) := by group
      _ = m * m := by rw [this]
  rw [e] at hcomm
  exact hm1 (eq_one_of_mul_self_mem_pCore hodd hcomm)

theorem case2_core {n : ℕ} (hInd : SimpleCaseUpTo n) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) (hn : Nat.card R < n) {T₁ : Subgroup R} (hT₁ : IsWC T₁)
    (hcl : Subgroup.normalClosure (T₁ : Set R) = ⊤) (h4 : Nat.card T₁ = 4) {ℓ y : R}
    (hℓT : ℓ ∈ T₁) (hyT : y ∈ T₁) (hℓℓ : ℓ * ℓ = 1) (hyy : y * y = 1) (hℓ1 : ℓ ≠ 1)
    (hy1 : y ≠ 1) (hyℓ : y ≠ ℓ) (hℓy : ℓ * y = y * ℓ)
    (hT : ∀ t ∈ T₁, t = 1 ∨ t = ℓ ∨ t = y ∨ t = y * ℓ) (φa φ₁ φ₂ : R ≃* R)
    (hφaℓ : φa ℓ = ℓ) (hφay : φa y = y * ℓ) {m₁ m₂ : R} (hm₁ : m₁ ≠ 1) (hm₂ : m₂ ≠ 1)
    (hQ : ∀ x ∈ Subgroup.closure ({m₁, m₂} : Set R), ∃ k : ℕ, x ^ (3 ^ k) = 1)
    (hℓm₁ : ℓ * m₁ * ℓ⁻¹ = m₁⁻¹) (hℓm₂ : ℓ * m₂ * ℓ⁻¹ = m₂⁻¹)
    (hφam₁ : φa m₁ = m₁) (hφam₂ : φa m₂ = m₂) (hφ₁m₁ : φ₁ m₁ = m₁) (hφ₁m₂ : φ₁ m₂ = m₂⁻¹)
    (hφ₂m₂ : φ₂ m₂ = m₂) (hφ₂m₁ : φ₂ m₁ = m₁⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 R with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓℓ
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hm₁Q : m₁ ∈ Subgroup.closure ({m₁, m₂} : Set R) := Subgroup.subset_closure (by simp)
  have hm₂Q : m₂ ∈ Subgroup.closure ({m₁, m₂} : Set R) := Subgroup.subset_closure (by simp)
  have hoddQ : ∀ x ∈ Subgroup.closure ({m₁, m₂} : Set R), Odd (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hQ x hx
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hk)
  have hodd₁ : Odd (orderOf m₁) := hoddQ m₁ hm₁Q
  have hodd₂ : Odd (orderOf m₂) := hoddQ m₂ hm₂Q
  have hTO : T₁ ⊓ O = ⊥ := by
    by_contra hne
    obtain ⟨t₀, ht₀⟩ : ∃ t : ↥(T₁ ⊓ O), t ≠ 1 := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have ht₀T : (t₀ : R) ∈ T₁ := t₀.2.1
    have ht₀O : (t₀ : R) ∈ O := t₀.2.2
    have ht₀1 : (t₀ : R) ≠ 1 := fun h => ht₀ (Subtype.ext h)
    have hℓO : ℓ ∈ O := by
      rcases hT _ ht₀T with h | h | h | h
      · exact absurd h ht₀1
      · rw [← h]; exact ht₀O
      · have hyO : y ∈ O := h ▸ ht₀O
        have h1 : φa y ∈ O := map_pCore_equiv' φa hyO
        rw [hφay] at h1
        have : ℓ = y * (y * ℓ) := by rw [← mul_assoc, hyy, one_mul]
        rw [this]
        exact O.mul_mem hyO h1
      · have hyℓO : y * ℓ ∈ O := h ▸ ht₀O
        have h1 : φa (y * ℓ) ∈ O := map_pCore_equiv' φa hyℓO
        rw [map_mul, hφay, hφaℓ, mul_assoc, hℓℓ, mul_one] at h1
        have : ℓ = y⁻¹ * (y * ℓ) := by group
        rw [this]
        exact O.mul_mem (O.inv_mem h1) hyℓO
    have h1 : m₁⁻¹ * ℓ * m₁ ∈ O := by
      have := hOn.conj_mem ℓ hℓO m₁⁻¹
      simpa using this
    have h2 : m₁ * m₁ ∈ O := by
      rw [← mul_conj_eq_sq hℓℓ hℓm₁]
      exact O.mul_mem hℓO h1
    exact hm₁ (eq_one_of_mul_self_mem_pCore hodd₁ h2)
  have hker : T₁ ⊓ (QuotientGroup.mk' O).ker = ⊥ := by rw [QuotientGroup.ker_mk', hTO]
  have h4' : 4 ≤ Nat.card (T₁.map (QuotientGroup.mk' O)) := by
    rw [card_map_eq_of_inf_ker_eq_bot' _ hker, h4]
  have hn' : Nat.card (R ⧸ O) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective O)) hn
  obtain ⟨hsimple, hlist, hWC, h4Y, hkerY⟩ := jCore' hInd h215 hT₁ hcl h4' hn'
  have : IsSimpleGroup (jQuot R) := hsimple
  have : Finite (jQuot R) := Finite.of_surjective _ (jMap_surjective (R := R))
  have hkerT : T₁ ⊓ (jMap R).ker = ⊥ := by rw [hkerY, hTO]
  have hinj : ∀ z ∈ T₁, jMap R z = 1 → z = 1 := by
    intro z hz hz1
    have : z ∈ T₁ ⊓ (jMap R).ker := ⟨hz, hz1⟩
    rw [hkerT, Subgroup.mem_bot] at this
    exact this
  have hcard4 : Nat.card (T₁.map (jMap R)) = 4 := by
    rw [card_map_eq_of_inf_ker_eq_bot' _ hkerT, h4]
  have hstd : StdPair (jQuot R) (T₁.map (jMap R)) := hI _ hlist _ hWC h4Y
  set π := jMap R with hπ
  have hπm₁ : π m₁ ≠ 1 := fun h => not_mem_ker_of_inverted hℓℓ hℓm₁ hodd₁ hm₁ h
  have hπm₂ : π m₂ ≠ 1 := fun h => not_mem_ker_of_inverted hℓℓ hℓm₂ hodd₂ hm₂ h
  have hoddπ₁ : Odd (orderOf (π m₁)) := Odd.of_dvd_nat hodd₁ (orderOf_map_dvd _ _)
  have hoddπ₂ : Odd (orderOf (π m₂)) := Odd.of_dvd_nat hodd₂ (orderOf_map_dvd _ _)
  have hindep : ∀ (a b : R) (ψ : R ≃* R), Odd (orderOf (π b)) → π b ≠ 1 → ψ a = a →
      ψ b = b⁻¹ → ∀ s : ℤ, π b ≠ (π a) ^ s := by
    intro a b ψ hoddb hb1 hψa hψb s h
    have hw : (b⁻¹ * a ^ s) ∈ (jMap R).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, ← h, inv_mul_cancel]
    have hw' := ker_jMap_invariant ψ hw
    rw [map_mul, map_inv, map_zpow, hψa, hψb, inv_inv, MonoidHom.mem_ker, map_mul, map_zpow,
      ← h] at hw'
    exact hb1 (eq_one_of_mul_self_eq_one_of_odd_order hoddb hw')
  have hA : ∀ s : ℤ, π m₂ ≠ (π m₁) ^ s := hindep m₁ m₂ φ₁ hoddπ₂ hπm₂ hφ₁m₁ hφ₁m₂
  have hA' : ∀ s : ℤ, π m₁ ≠ (π m₂) ^ s := hindep m₂ m₁ φ₂ hoddπ₁ hπm₁ hφ₂m₂ hφ₂m₁
  set Q : Subgroup R := Subgroup.closure ({m₁, m₂} : Set R) with hQdef
  set PH : Subgroup (jQuot R) := Q.map π with hPH
  have hPHp : IsPGroup 3 PH := by
    intro g
    obtain ⟨x, hxQ, hx⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨k, hk⟩ := hQ x hxQ
    refine ⟨k, Subtype.ext ?_⟩
    show (g : jQuot R) ^ (3 ^ k) = 1
    rw [← hx, ← map_pow, hk, map_one]
  have hπm₁PH : π m₁ ∈ PH := Subgroup.mem_map_of_mem _ hm₁Q
  have hπm₂PH : π m₂ ∈ PH := Subgroup.mem_map_of_mem _ hm₂Q
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 hPHp
  have hc2 : 2 ≤ c := by
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le (Nat.le_of_lt_succ hlt)) with h0 | h1
    ·
      have hc0 : c = 0 := by omega
      rw [hc0, pow_zero] at hc
      have := Subgroup.card_eq_one.1 hc
      rw [this, Subgroup.mem_bot] at hπm₁PH
      exact hπm₁ hπm₁PH
    ·
      have hc1 : c = 1 := by omega
      rw [hc1, pow_one] at hc
      have hdvd : orderOf (π m₁) ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard PH hπm₁PH
        rwa [hc] at this
      have hord : orderOf (π m₁) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hπm₁
        · exact h
      have hzle : Subgroup.zpowers (π m₁) ≤ PH := (Subgroup.zpowers_le).2 hπm₁PH
      have hzeq : Subgroup.zpowers (π m₁) = PH :=
        Subgroup.eq_of_le_of_card_ge hzle (by rw [hc, Nat.card_zpowers, hord])
      rw [← hzeq] at hπm₂PH
      obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 hπm₂PH
      exact hA s hs.symm
  have h9 : 9 ∣ Nat.card PH := by
    rw [hc]
    exact (pow_dvd_pow 3 hc2 : 3 ^ 2 ∣ 3 ^ c)
  have h9' : 9 ∣ Nat.card (jQuot R) := h9.trans (Subgroup.card_subgroup_dvd_card PH)
  obtain ⟨n', hn', ⟨e⟩⟩ : ∃ n' : ℕ, (n' = 6 ∨ n' = 7) ∧
      Nonempty (jQuot R ≃* alternatingGroup (Fin n')) := by
    rcases nine_dvd_classify hstd hcard4 h9' with he | he
    · exact ⟨6, Or.inl rfl, he⟩
    · exact ⟨7, Or.inr rfl, he⟩
  have hcard9 : Nat.card PH = 3 ^ 2 := by
    have hdvd : 3 ^ c ∣ Nat.card (alternatingGroup (Fin n')) := by
      rw [← Nat.card_congr e.toEquiv, ← hc]
      exact Subgroup.card_subgroup_dvd_card PH
    have hc3 : c ≤ 2 := by
      by_contra hlt
      push Not at hlt
      exact PermModel.card_alt_not_27 hn' ((pow_dvd_pow 3 hlt : 3 ^ 3 ∣ 3 ^ c).trans hdvd)
    have : c = 2 := le_antisymm hc3 hc2
    rw [hc, this]
  have : IsMulCommutative PH :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard9
  have hPHeq : PH = Subgroup.closure ({π m₁, π m₂} : Set (jQuot R)) := by
    rw [hPH, hQdef, MonoidHom.map_closure, Set.image_pair]
  have hcommPH : ∀ p ∈ PH, ∀ q ∈ PH, p * q = q * p := by
    intro p hp q hq
    have := mul_comm' (⟨p, hp⟩ : PH) ⟨q, hq⟩
    exact congrArg Subtype.val this
  have hinvPH : ∀ p ∈ PH, π ℓ * p * (π ℓ)⁻¹ = p⁻¹ := by
    intro p hp
    rw [hPHeq] at hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [← map_inv, ← map_mul, ← map_mul, hℓm₁]
        simp
      · rw [← map_inv, ← map_mul, ← map_mul, hℓm₂]
        simp
    | one => simp
    | mul a b ha hb iha ihb =>
      have haPH : a ∈ PH := hPHeq ▸ ha
      have hbPH : b ∈ PH := hPHeq ▸ hb
      calc π ℓ * (a * b) * (π ℓ)⁻¹ = (π ℓ * a * (π ℓ)⁻¹) * (π ℓ * b * (π ℓ)⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [iha, ihb]
        _ = (b * a)⁻¹ := by rw [mul_inv_rev]
        _ = (a * b)⁻¹ := by rw [hcommPH b hbPH a haPH]
    | inv a ha iha =>
      calc π ℓ * a⁻¹ * (π ℓ)⁻¹ = (π ℓ * a * (π ℓ)⁻¹)⁻¹ := by group
        _ = a⁻¹⁻¹ := by rw [iha]
  have hℓπ : π ℓ * π ℓ = 1 := by rw [← map_mul, hℓℓ, map_one]
  have hyπ : π y * π y = 1 := by rw [← map_mul, hyy, map_one]
  have hℓyπ : π ℓ * π y = π y * π ℓ := by rw [← map_mul, ← map_mul, hℓy]
  have hy1π : π y ≠ 1 := fun h => hy1 (hinj y hyT h)
  have hℓ1π : π ℓ ≠ 1 := fun h => hℓ1 (hinj ℓ hℓT h)
  have hyℓπ : π y ≠ π ℓ := fun h => hyℓ (by
    have hmem : y * ℓ⁻¹ ∈ T₁ := T₁.mul_mem hyT (T₁.inv_mem hℓT)
    have : π (y * ℓ⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h1 := hinj _ hmem this
    exact mul_inv_eq_one.1 h1)
  have hcard9' : Nat.card PH = 9 := by rw [hcard9]; norm_num
  obtain ⟨qh, hqhPH, hmis⟩ := PermModel.fl2_main hn' e hcard9' hℓπ hyπ hℓyπ hyℓπ hy1π hℓ1π hinvPH
  obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.1 hqhPH
  have hφq : ∀ g ∈ Q, φa g = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hφam₁
      · exact hφam₂
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, ha]
  have hφqq : φa q = q := hφq q hqQ
  have comm_iff : ∀ g h : R, (π g * π h = π h * π g) ↔ ⁅g, h⁆ ∈ π.ker := by
    intro g h
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have c1 : (π y * ((π q)⁻¹ * π y * π q) = ((π q)⁻¹ * π y * π q) * π y) ↔
      ⁅y, q⁻¹ * y * q⁆ ∈ π.ker := by
    rw [← comm_iff]
    simp only [map_mul, map_inv]
  have c2 : ((π y * π ℓ) * ((π q)⁻¹ * (π y * π ℓ) * π q) =
      ((π q)⁻¹ * (π y * π ℓ) * π q) * (π y * π ℓ)) ↔
      ⁅y * ℓ, q⁻¹ * (y * ℓ) * q⁆ ∈ π.ker := by
    rw [← comm_iff]
    simp only [map_mul, map_inv]
  have hφyℓ : φa (y * ℓ) = y := by
    rw [map_mul, hφay, hφaℓ, mul_assoc, hℓℓ, mul_one]
  have hφ1 : φa (q⁻¹ * y * q) = q⁻¹ * (y * ℓ) * q := by
    rw [map_mul, map_mul, map_inv, hφqq, hφay]
  have hφ2 : φa (q⁻¹ * (y * ℓ) * q) = q⁻¹ * y * q := by
    rw [map_mul, map_mul, map_inv, hφqq, hφyℓ]
  apply hmis
  rw [c1, c2]
  constructor
  · intro h
    have h' := ker_jMap_invariant φa h
    rwa [map_commutatorElement, hφay, hφ1] at h'
  · intro h
    have h' := ker_jMap_invariant φa h
    rwa [map_commutatorElement, hφyℓ, hφ2] at h'

end CFSG.CGT.T75H
