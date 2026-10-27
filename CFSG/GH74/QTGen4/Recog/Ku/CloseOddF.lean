module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseOddB
public import CFSG.GH74.QTGen4.Recog.Ku.CloseOdd
public import CFSG.Quasithin.Recognition.HSType129g

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

section AltOdd

theorem alt_odd_product {n : ℕ}
    (haut : ∀ α : ↥(alternatingGroup (Fin n)) ≃* ↥(alternatingGroup (Fin n)),
      ∃ ρ : Equiv.Perm (Fin n), ∀ σ : ↥(alternatingGroup (Fin n)),
        ((α σ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = ρ * σ * ρ⁻¹)
    (huniq : ∀ ρ : Equiv.Perm (Fin n),
      (∀ σ ∈ alternatingGroup (Fin n), ρ * σ = σ * ρ) → ρ = 1)
    (hodd : ∀ σ τ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = -1 → σ * σ = 1 →
      Equiv.Perm.sign τ = -1 → τ * τ = 1 → (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1)
    {Q : Type*} [Group Q] (eA : Q ≃* ↥(alternatingGroup (Fin n))) (φ₁ φ₂ : Q ≃* Q)
    (h₁ : ∀ y, φ₁ (φ₁ y) = y) (h₂ : ∀ y, φ₂ (φ₂ y) = y)
    (n₁ : ∀ q : Q, ∃ y, φ₁ y ≠ q * y * q⁻¹) (n₂ : ∀ q : Q, ∃ y, φ₂ y ≠ q * y * q⁻¹)
    {q : Q} (hq : ∀ y, φ₁ (φ₂ y) = q * y * q⁻¹) : q * q = 1 ∨ q ^ 3 = 1 := by
  classical
  have hρ : ∀ φ : Q ≃* Q, ∃ ρ : Equiv.Perm (Fin n), ∀ y : Q,
      ((eA (φ y) : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
        ρ * ((eA y : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) * ρ⁻¹ := by
    intro φ
    obtain ⟨ρ, hρ⟩ := haut ((eA.symm.trans φ).trans eA)
    refine ⟨ρ, fun y => ?_⟩
    have := hρ (eA y)
    simpa using this
  obtain ⟨ρ₁, hρ₁⟩ := hρ φ₁
  obtain ⟨ρ₂, hρ₂⟩ := hρ φ₂
  have hsq : ∀ (φ : Q ≃* Q) (ρ : Equiv.Perm (Fin n)), (∀ y, φ (φ y) = y) →
      (∀ y : Q, ((eA (φ y) : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
        ρ * ((eA y : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) * ρ⁻¹) →
      ρ * ρ = 1 := by
    intro φ ρ hφ hρ
    refine huniq (ρ * ρ) fun σ hσ => ?_
    obtain ⟨y, hy⟩ := eA.surjective ⟨σ, hσ⟩
    have h1 := hρ (φ y)
    rw [hφ, hρ y, hy] at h1
    simp only at h1
    calc ρ * ρ * σ = ρ * ρ * σ * (ρ * ρ)⁻¹ * (ρ * ρ) := by group
      _ = σ * (ρ * ρ) := by
        have : ρ * ρ * σ * (ρ * ρ)⁻¹ = σ := by
          calc ρ * ρ * σ * (ρ * ρ)⁻¹ = ρ * (ρ * σ * ρ⁻¹) * ρ⁻¹ := by group
            _ = σ := by rw [← h1]
        rw [this]
  have hodd' : ∀ (φ : Q ≃* Q) (ρ : Equiv.Perm (Fin n)),
      (∀ y : Q, ((eA (φ y) : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
        ρ * ((eA y : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) * ρ⁻¹) →
      (∀ q : Q, ∃ y, φ y ≠ q * y * q⁻¹) → Equiv.Perm.sign ρ = -1 := by
    intro φ ρ hρ hn
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with hs | hs
    · exfalso
      have hmem : ρ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hs
      obtain ⟨q₀, hq₀⟩ := eA.surjective ⟨ρ, hmem⟩
      obtain ⟨y, hy⟩ := hn q₀
      apply hy
      apply eA.injective
      apply Subtype.ext
      rw [hρ y, map_mul, map_mul, map_inv, hq₀]
      simp
    · exact hs
  have hs₁ := hodd' φ₁ ρ₁ hρ₁ n₁
  have hs₂ := hodd' φ₂ ρ₂ hρ₂ n₂
  have e₁ := hsq φ₁ ρ₁ h₁ hρ₁
  have e₂ := hsq φ₂ ρ₂ h₂ hρ₂
  have key := hodd ρ₁ ρ₂ hs₁ e₁ hs₂ e₂
  have hqρ : ((eA q : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = ρ₁ * ρ₂ := by
    have := huniq ((ρ₁ * ρ₂)⁻¹ * ((eA q : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)))
      fun σ hσ => by
        obtain ⟨y, hy⟩ := eA.surjective ⟨σ, hσ⟩
        have h1 := hq y
        have h2 := congrArg (fun a : Q => ((eA a : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) h1
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h2
        rw [hρ₁ (φ₂ y), hρ₂ y, hy] at h2
        have h3 : ρ₁ * (ρ₂ * σ * ρ₂⁻¹) * ρ₁⁻¹ = ((eA q : ↥(alternatingGroup (Fin n))) :
            Equiv.Perm (Fin n)) * σ * ((eA q : ↥(alternatingGroup (Fin n))) :
            Equiv.Perm (Fin n))⁻¹ := h2
        set a : Equiv.Perm (Fin n) := ((eA q : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        calc (ρ₁ * ρ₂)⁻¹ * a * σ = (ρ₁ * ρ₂)⁻¹ * (a * σ * a⁻¹) * a := by group
          _ = (ρ₁ * ρ₂)⁻¹ * (ρ₁ * (ρ₂ * σ * ρ₂⁻¹) * ρ₁⁻¹) * a := by rw [h3]
          _ = σ * ((ρ₁ * ρ₂)⁻¹ * a) := by group
    calc ((eA q : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        = (ρ₁ * ρ₂) * ((ρ₁ * ρ₂)⁻¹ * ((eA q : ↥(alternatingGroup (Fin n))) :
            Equiv.Perm (Fin n))) := by group
      _ = ρ₁ * ρ₂ := by rw [this, mul_one]
  rcases key with h | h
  · left
    apply eA.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, map_one, OneMemClass.coe_one]
    rw [hqρ, ← pow_two]
    exact h
  · right
    apply eA.injective
    apply Subtype.ext
    simp only [map_pow, Subgroup.coe_pow, map_one, OneMemClass.coe_one]
    rw [hqρ]
    exact h

theorem alt_four_five_odd_product {Q : Type*} [Group Q]
    (hQ : Nonempty (Q ≃* ↥(alternatingGroup (Fin 4))) ∨ Nonempty (Q ≃* ↥(alternatingGroup (Fin 5))))
    (φ₁ φ₂ : Q ≃* Q)
    (h₁ : ∀ y, φ₁ (φ₁ y) = y) (h₂ : ∀ y, φ₂ (φ₂ y) = y)
    (n₁ : ∀ q : Q, ∃ y, φ₁ y ≠ q * y * q⁻¹) (n₂ : ∀ q : Q, ∃ y, φ₂ y ≠ q * y * q⁻¹)
    {q : Q} (hq : ∀ y, φ₁ (φ₂ y) = q * y * q⁻¹) : q * q = 1 ∨ q ^ 3 = 1 := by
  rcases hQ with h4 | h5
  · obtain ⟨e⟩ := h4
    exact alt_odd_product alt_four_aut_conj
      (fun ρ hρ => eq_one_of_comm_alt_four ρ ⟨hρ _ aA4_mem, hρ _ bA4_mem⟩)
      perm_four_odd_mul_le_three e φ₁ φ₂ h₁ h₂ n₁ n₂ hq
  · obtain ⟨e⟩ := h5
    exact alt_odd_product alt_five_aut_conj
      (fun ρ hρ => eq_one_of_comm_alt_five ρ ⟨hρ _ aA5_mem, hρ _ bA5_mem⟩)
      perm_five_odd_mul_le_three e φ₁ φ₂ h₁ h₂ n₁ n₂ hq

end AltOdd

variable {G : Type} [Group G]

section Conj

theorem mul_mem_centralizer_of_inverts {x δ₁ δ₂ : G} (h₁ : δ₁ * x * δ₁⁻¹ = x⁻¹)
    (h₂ : δ₂ * x * δ₂⁻¹ = x⁻¹) : δ₁ * δ₂ ∈ Subgroup.centralizer ({x} : Set G) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc δ₁ * δ₂ * x = δ₁ * (δ₂ * x * δ₂⁻¹) * δ₂ := by group
    _ = δ₁ * x⁻¹ * δ₂ := by rw [h₂]
    _ = (δ₁ * x * δ₁⁻¹)⁻¹ * (δ₁ * δ₂) := by group
    _ = x * (δ₁ * δ₂) := by rw [h₁, inv_inv]

theorem cenConj_cenConj {x δ : G} (hδx : δ * x * δ⁻¹ = x⁻¹) (hδ : δ * δ = 1) (y : cenQuot x) :
    cenConj hδx (cenConj hδx y) = y := by
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [cenConj_mk, cenConj_mk]
  congr 1
  apply Subtype.ext
  rw [cenConjC_coe, cenConjC_coe, show δ * (δ * (y' : G) * δ⁻¹) * δ⁻¹ =
    (δ * δ) * y' * (δ * δ)⁻¹ by group, hδ]
  group

theorem cenConj_cenConj_mul {x δ₁ δ₂ : G} (h₁ : δ₁ * x * δ₁⁻¹ = x⁻¹) (h₂ : δ₂ * x * δ₂⁻¹ = x⁻¹)
    (hp : δ₁ * δ₂ ∈ Subgroup.centralizer ({x} : Set G)) (y : cenQuot x) :
    cenConj h₁ (cenConj h₂ y) =
      (QuotientGroup.mk (⟨δ₁ * δ₂, hp⟩ : ↥(Subgroup.centralizer ({x} : Set G))) : cenQuot x) * y *
        (QuotientGroup.mk (⟨δ₁ * δ₂, hp⟩ : ↥(Subgroup.centralizer ({x} : Set G))) : cenQuot x)⁻¹ := by
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [cenConj_mk, cenConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [cenConjC_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Conj

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

theorem cenConj_not_inner (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) {δ : G}
    (hδx : δ * x * δ⁻¹ = x⁻¹) (q : cenQuot x) : ∃ y : cenQuot x, cenConj hδx y ≠ q * y * q⁻¹ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  have hc : Commute (c : G) x := Subgroup.mem_centralizer_singleton_iff.mp c.2
  refine Ψ.no_central_mod_X hHN hxH hx (u := (c : G)⁻¹ * δ) ?_ ?_
  · calc (c : G)⁻¹ * δ * x * ((c : G)⁻¹ * δ)⁻¹ = (c : G)⁻¹ * (δ * x * δ⁻¹) * c := by group
      _ = (c : G)⁻¹ * x⁻¹ * c := by rw [hδx]
      _ = x⁻¹ := by
        rw [mul_assoc, ← hc.inv_right.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro g hg
    have h := hcon (QuotientGroup.mk ⟨g, hg⟩)
    rw [cenConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, mem_cenX] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, cenConjC_coe] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine ⟨-k, ?_⟩
    have e1 : δ * g * δ⁻¹ = c * g * (c : G)⁻¹ * x ^ (-k) := by
      rw [zpow_neg, hk]; group
    have hcx : Commute (c : G) (x ^ (-k)) := hc.zpow_right _
    have hgc : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgx : Commute g (x ^ (-k)) := hgc.zpow_right _
    have hcc : (c : G)⁻¹ * x ^ (-k) * c = x ^ (-k) := by
      rw [mul_assoc, ← hcx.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (c : G)⁻¹ * δ * g * ((c : G)⁻¹ * δ)⁻¹ = (c : G)⁻¹ * (δ * g * δ⁻¹) * c := by group
      _ = (c : G)⁻¹ * (c * g * (c : G)⁻¹ * x ^ (-k)) * c := by rw [e1]
      _ = g * ((c : G)⁻¹ * x ^ (-k) * c) := by group
      _ = g * x ^ (-k) := by rw [hcc]
      _ = x ^ (-k) * g := hgx.eq

end KuA6Model

theorem cube_eq_one_of_mem_zpowers [Finite G] {x w p : G} (hx : orderOf x = 3)
    (hw : orderOf w = 3) (hwx : w * x = x * w) (hwX : w ∉ Subgroup.zpowers x)
    (hpx : p * x = x * p) (h27 : ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)))
    (hp : p ^ 3 ∈ Subgroup.zpowers x) : p ^ 3 = 1 := by
  classical
  by_contra hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hwC : w ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwx
  have hpC : p ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hpx
  have hxw : Commute x w := hwx.symm
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hxw i j).eq
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgx, hgw⟩ := Subgroup.mem_inf.mp hg
    by_contra hg1
    have hg1' : g ≠ 1 := fun h => hg1 (Subgroup.mem_bot.mpr h)
    have hord : ∀ {y : G}, orderOf y = 3 → g ∈ Subgroup.zpowers y → orderOf g = 3 := by
      intro y hy hgy
      have hd : orderOf g ∣ 3 := hy ▸ orderOf_dvd_of_mem_zpowers hgy
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1'
      · exact h
    have hzx : Subgroup.zpowers g = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hord hx hgx])
    have hzw : Subgroup.zpowers g = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgw)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hw, hord hw hgw])
    apply hwX
    rw [← hzx, hzw]
    exact Subgroup.mem_zpowers w
  have hP9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers w) = 9 := by
    rw [card_sup_of_commute hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers, hx, hw]
  have hPexp : ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers w, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hg
    have ha3 : a ^ 3 = 1 := by
      have := orderOf_dvd_of_mem_zpowers ha
      rw [hx] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hb3 : b ^ 3 = 1 := by
      have := orderOf_dvd_of_mem_zpowers hb
      rw [hw] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hab : Commute a b := hcomm a ha b hb
    rw [hab.mul_pow, ha3, hb3, one_mul]
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers w ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le ((Subgroup.zpowers_le).mpr hxC) ((Subgroup.zpowers_le).mpr hwC)
  have hP9' : Nat.card ↥((Subgroup.zpowers x ⊔ Subgroup.zpowers w).subgroupOf
      (Subgroup.centralizer ({x} : Set G))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hP9]
  have hPexp' : ∀ g ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers w).subgroupOf
      (Subgroup.centralizer ({x} : Set G)), g ^ 3 = 1 := by
    intro g hg
    apply Subtype.ext
    exact hPexp _ (Subgroup.mem_subgroupOf.mp hg)
  have hmax : ∀ Q : Subgroup ↥(Subgroup.centralizer ({x} : Set G)), IsPGroup 3 ↥Q →
      Nat.card ↥Q ≤ 9 := by
    intro Q hQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    by_contra hlt
    push Not at hlt
    have h3 : 3 ≤ n := by
      by_contra hn3
      push Not at hn3
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd : 27 ∣ Nat.card ↥Q := by
      rw [hn]
      exact (pow_dvd_pow 3 h3 : 3 ^ 3 ∣ 3 ^ n)
    exact h27 (hdvd.trans (Subgroup.card_subgroup_dvd_card Q))
  have hp9 : orderOf (⟨p, hpC⟩ : ↥(Subgroup.centralizer ({x} : Set G))) = 9 := by
    rw [Subgroup.orderOf_mk]
    have hp9' : p ^ 9 = 1 := by
      have h3 : (p ^ 3) ^ 3 = 1 := by
        have := orderOf_dvd_of_mem_zpowers hp
        rw [hx] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      rw [← pow_mul] at h3
      exact h3
    have hd : orderOf p ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one hp9'
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases k
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk')) (fun h => hp3 (by rw [h]; simp))
    · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by rw [hk']; norm_num)) hp3
    · simpa using hk'
  exact orderOf_ne_nine_of_exponent_three hmax hP9' hPexp' _ hp9

end CFSG.GH74.QTGen4.Ku
