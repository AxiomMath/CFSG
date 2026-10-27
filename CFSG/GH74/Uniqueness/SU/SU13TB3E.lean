module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.SU.SU13TB1Main

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem false_of_oc_eq (hz : orderOf z = 2) (e : Elts G z) (l : Lem232 z e) (hE : EPart10 z e)
    (hoc : oc (centralizer ({e.s₁} : Set G)) = zpowers e.s₁)
    (h3 : 3 ^ 5 ∣ Nat.card (centralizer ({e.s₂} : Set G))) : False := by
  obtain ⟨E, Es, hs₁E, hEEs, hE27, hEab, hEsp, hEs81, hEsz, hmax, huniq, hcentE⟩ := hE.ex
  have hz_sq : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hXz : ∀ g : G, g * e.s₁ = e.s₁ * g → g * z = z * g := by
    intro g hg
    obtain ⟨c, k, hc, hcz, hk, hgck⟩ := l.a g hg
    rw [hoc] at hk
    have hkz : k * z = z * k := by
      obtain ⟨n, rfl⟩ := hk
      exact ((Commute.zpow_left (show Commute e.s₁ z from e.s₁_comm) n)).eq
    rw [hgck]
    calc c * k * z = c * (k * z) := by group
      _ = c * (z * k) := by rw [hkz]
      _ = (c * z) * k := by group
      _ = (z * c) * k := by rw [hcz]
      _ = z * (c * k) := by group
  have hCE : centralizer (E : Set G) = E ⊔ zpowers z := by
    rw [← hcentE]
    refine (inf_eq_left.mpr ?_).symm
    intro x hx
    rw [mem_centralizer_singleton_iff]
    refine hXz x ?_
    have := mem_centralizer_iff.mp hx e.s₁ hs₁E
    exact this.symm
  have hzCE : z ∈ centralizer (E : Set G) := by
    rw [hCE]; exact mem_sup_right (mem_zpowers z)
  have hNE : normalizer (E : Set G) ≤ centralizer ({z} : Set G) := by
    intro g hg
    have hgz : g * z * g⁻¹ ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ E := by
        have := (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
        simpa [mul_assoc] using this
      have := mem_centralizer_iff.mp hzCE _ hy'
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = (g * z * g⁻¹) * y := by group
    rw [hCE] at hgz
    obtain ⟨a, ha, b, hb, hab⟩ := SU1.mem_sup_of_commute (A := E) (B := zpowers z)
      (fun a ha b hb => by
        obtain ⟨n, rfl⟩ := hb
        exact (Commute.zpow_right (show Commute a z from (mem_centralizer_iff.mp hzCE a ha)) n).eq) hgz
    have hord : orderOf (g * z * g⁻¹) = 2 := by rw [orderOf_conj_eq]; exact hz
    have hb' : b = 1 ∨ b = z := by
      obtain ⟨n, rfl⟩ := hb
      beta_reduce
      have h1 : z ^ n = z ^ (n % (orderOf z : ℤ)) := (zpow_mod_orderOf z n).symm
      rw [hz] at h1
      have h2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
      rcases h2 with h2 | h2
      · left; rw [h1, h2, zpow_zero]
      · right; rw [h1, h2, zpow_one]
    have hoddE : ∀ a ∈ E, a * a = 1 → a = 1 := by
      intro a ha hsq
      have hodd : Odd (orderOf a) := by
        have : orderOf a ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E ha
        rw [hE27] at this
        exact Odd.of_dvd_nat (by decide) this
      obtain ⟨m, hm⟩ := hodd
      have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have : orderOf a = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · rw [h] at hm; omega
      exact orderOf_eq_one_iff.mp this
    have hgz' : g * z * g⁻¹ = z := by
      rcases hb' with hb1 | hbz
      · exfalso
        rw [hb1, mul_one] at hab
        have : orderOf (g * z * g⁻¹) ∣ Nat.card E := by
          rw [← hab]; exact Subgroup.orderOf_dvd_natCard E ha
        rw [hord, hE27] at this
        omega
      · rw [hbz] at hab
        have hcom : a * z = z * a := mem_centralizer_iff.mp hzCE a ha
        have hsq0 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
          rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hord
        have hsq : a * a = 1 := by
          rw [← hab] at hsq0
          calc a * a = a * a * (z * z) := by rw [hz_sq, mul_one]
            _ = a * (a * z) * z := by group
            _ = a * (z * a) * z := by rw [hcom]
            _ = (a * z) * (a * z) := by group
            _ = 1 := hsq0
        rw [← hab, hoddE a ha hsq, one_mul]
    have : g * z = z * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [hgz']
    exact mem_centralizer_singleton_iff.mpr this
  have hchar : ∀ g ∈ normalizer (Es : Set G), g ∈ normalizer (E : Set G) := by
    intro g hg
    have hA : E.map (MulAut.conj g).toMonoidHom ≤ Es := by
      rintro _ ⟨x, hx, rfl⟩
      have := (mem_normalizer_iff.mp hg x).mp (hEEs hx)
      simpa using this
    have hAcard : Nat.card (E.map (MulAut.conj g).toMonoidHom : Subgroup G) = 27 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hE27
    have hAab : ∀ a ∈ E.map (MulAut.conj g).toMonoidHom, ∀ b ∈ E.map (MulAut.conj g).toMonoidHom,
        a * b = b * a := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
        _ = g * (y * x) * g⁻¹ := by rw [hEab x hx y hy]
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
    have hAE := huniq _ hA hAcard hAab
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := ⟨x, hx, by simp⟩
      rwa [hAE] at this
    · intro hx
      rw [← hAE] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have := (MulAut.conj g).injective (a₁ := y) (a₂ := x) (by simpa using hyx)
        exact this
      rwa [← this]
  have hmaxG : ∀ R : Subgroup G, IsPGroup 3 R → Es ≤ R → R = Es := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    intro R hR hER
    exact eq_of_isPGroup_le_of_normalizer (p := 3) (H := centralizer ({z} : Set G)) (E := E) (Es := Es)
      hNE hchar (fun R' hR'H hR'p hEsR' => hmax R' (fun x hx => mem_centralizer_singleton_iff.mp (hR'H hx))
        hR'p hEsR') hR hER
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := hEsp.exists_le_sylow
  have hQeq : (Q : Subgroup G) = Es := hmaxG Q Q.isPGroup' hQ
  have hQcard : Nat.card Q = 81 := by
    have : Nat.card (Q : Subgroup G) = Nat.card Es := by rw [hQeq]
    rw [← hEs81]; exact this
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({e.s₂} : Set G)) 3 h3
  have hKp : IsPGroup 3 (K.map (centralizer ({e.s₂} : Set G)).subtype) :=
    (IsPGroup.of_card hK).map _
  obtain ⟨Q', hQ'⟩ := hKp.exists_le_sylow
  have hQ'card : Nat.card Q' = 81 := by
    have h1 : Nat.card Q' = 3 ^ (Nat.card G).factorization 3 := Sylow.card_eq_multiplicity Q'
    have h2 : Nat.card Q = 3 ^ (Nat.card G).factorization 3 := Sylow.card_eq_multiplicity Q
    rw [h1, ← h2, hQcard]
  have hle := Subgroup.card_le_of_le hQ'
  rw [Subgroup.card_map_of_injective (centralizer ({e.s₂} : Set G)).subtype_injective, hK] at hle
  have : Nat.card (Q' : Subgroup G) = 81 := hQ'card
  rw [this] at hle
  omega

end CFSG.GH74.Uniqueness.SU.SU13
