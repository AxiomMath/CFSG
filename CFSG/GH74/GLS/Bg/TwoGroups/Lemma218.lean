module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218f
public import CFSG.GH74.GLS.Bg.TwoGroups.Statements
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218b

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open L218 Subgroup

theorem iv2_2_18 : IV2_2_18 := by
  classical
  intro E _ _ h2 hE X S hS2 hS4 hC x hx hx1 hφ
  obtain ⟨φ⟩ := hφ
  by_contra hcon'
  have hcon : ∀ a b : ↥X, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → IsConj a b := by
    intro a b ha ha2 hb hb2
    by_contra hnc
    exact hcon' ⟨a, b, ha, ha2, hb, hb2, hnc⟩
  have c : Ctx E X S := ⟨h2, hE, hS2, hS4, hC⟩
  obtain ⟨v, hv3, hvn, hvs⟩ := c.exists_v hx hx1 φ hcon
  obtain ⟨u, t, hux, hu3, htu⟩ := exists_u_t x φ
  obtain ⟨e₀, he₀1, he₀S, hE0⟩ := c.exists_e0
  have hv0 : (v : MulAut E) e₀ = e₀ := v_fixes_e0 he₀1 he₀S hE0 hvn
  have hfree : ∀ s : ↥X, s ≠ 1 → s * s = 1 → Nat.card (fixE (s : MulAut E)) = 4 :=
    fun s hs1 hs2 => c.free_of_inv hx hx1 hcon hs1 hs2
  have hu1 : ∀ e : E, (u : MulAut E) e = e → e = 1 := by
    have hxx : (x : MulAut E) * (x : MulAut E) = 1 := congrArg Subtype.val (hS2 x hx)
    have hfx : Nat.card (fixE (x : MulAut E)) = 4 := c.free hx hx1
    have hcomm : (u : MulAut E) * (x : MulAut E) = (x : MulAut E) * (u : MulAut E) :=
      congrArg Subtype.val hux
    have hu3' : (u : MulAut E) ^ 3 = 1 := by
      have : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
      exact congrArg Subtype.val this
    have hu1' : (u : MulAut E) ≠ 1 := by
      intro h
      have : u = 1 := Subtype.ext h
      rw [this, orderOf_one] at hu3
      omega
    exact fixE_trivial_of_free h2 (x : MulAut E) (u : MulAut E) hxx hfx hcomm hu3' hu1'
  have h9 : 9 ∣ Nat.card ↥X := nine_dvd hu3 hv3 he₀1 hv0 hu1
  have hY := c.card_Y hfree he₀1 he₀S hv3 hv0
  have hXdvd : Nat.card ↥X ∣ 20160 := card_aut_E h2 hE ▸ Subgroup.card_subgroup_dvd_card X
  have h15 : Nat.card {e : E // e ≠ 1} = 15 := by
    have := Fintype.ofFinite E
    have hE' := hE
    rw [Nat.card_eq_fintype_card] at hE' ⊢
    have h := Fintype.card_subtype_compl (fun e : E => e = 1)
    simp only [Fintype.card_subtype_eq] at h
    rw [hE'] at h
    exact h
  have hidx : (MulAction.stabilizer ↥X e₀).index ≤ 15 := by
    rw [MulAction.index_stabilizer]
    have hsub : MulAction.orbit ↥X e₀ ⊆ {e : E | e ≠ 1} := by
      rintro _ ⟨g, rfl⟩ h
      apply he₀1
      have : (g : MulAut E) e₀ = (g : MulAut E) 1 := by rw [map_one]; exact h
      exact (g : MulAut E).injective this
    calc (MulAction.orbit ↥X e₀).ncard ≤ ({e : E | e ≠ 1} : Set E).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 15 := by rw [← Nat.card_coe_set_eq]; exact h15
  have hXcard : Nat.card ↥X = 12 * (MulAction.stabilizer ↥X e₀).index := by
    have := Subgroup.card_mul_index (MulAction.stabilizer ↥X e₀)
    rw [hY] at this
    exact this.symm
  have hX4 : Nat.card ↥X = 4 * (S : Subgroup ↥X).index := by
    have := Subgroup.card_mul_index (S : Subgroup ↥X)
    rw [hS4] at this
    exact this.symm
  have hSodd : ¬ 2 ∣ (S : Subgroup ↥X).index := S.not_dvd_index
  have hXc : Nat.card ↥X = 36 ∨ Nat.card ↥X = 180 := by
    generalize hi : (MulAction.stabilizer ↥X e₀).index = i at hidx hXcard
    rw [hXcard] at h9 hXdvd hX4
    interval_cases i <;> omega
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hS2 x hx) hx1
  have hC2 := c.cent_u_two hx hx1 φ hu3
  have hn3 := endgame u t x hu3 htu hx2 hux.symm hC2 hXc
  have h3f : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : Subsingleton (Sylow 3 ↥X) := (Nat.card_eq_one_iff_unique.mp hn3).1
  obtain ⟨R, hvR⟩ : ∃ R : Sylow 3 ↥X, Subgroup.zpowers v ≤ R :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv3]; norm_num)).exists_le_sylow
  have hRn : (R : Subgroup ↥X).Normal := Sylow.normal_of_subsingleton R
  have hR9 : Nat.card R = 9 := sylow3_card R (by omega)
  have hRS : ∀ r : ↥X, r ∈ (R : Subgroup ↥X) → r ∈ (S : Subgroup ↥X) → r = 1 := by
    intro r hrR hrS
    have h1 : orderOf r ∣ 9 := by
      have := orderOf_dvd_natCard (⟨r, hrR⟩ : (R : Subgroup ↥X))
      rwa [Subgroup.orderOf_mk, hR9] at this
    have h2' : orderOf r ∣ 4 := by
      have := orderOf_dvd_natCard (⟨r, hrS⟩ : (S : Subgroup ↥X))
      rwa [Subgroup.orderOf_mk, hS4] at this
    have h3 : orderOf r ∣ Nat.gcd 9 4 := Nat.dvd_gcd h1 h2'
    have h4 : orderOf r = 1 := by
      have : Nat.gcd 9 4 = 1 := by norm_num
      rw [this] at h3
      exact Nat.dvd_one.mp h3
    exact orderOf_eq_one_iff.mp h4
  obtain ⟨s, hs, hvsne⟩ := hvs
  apply hvsne
  have hvR' : v ∈ (R : Subgroup ↥X) := hvR (Subgroup.mem_zpowers v)
  have hcR : s * v⁻¹ * s⁻¹ ∈ (R : Subgroup ↥X) := hRn.conj_mem v⁻¹ (inv_mem hvR') s
  have h1 : v * s * v⁻¹ * s⁻¹ ∈ (R : Subgroup ↥X) := by
    have : v * s * v⁻¹ * s⁻¹ = v * (s * v⁻¹ * s⁻¹) := by group
    rw [this]
    exact mul_mem hvR' hcR
  have h2' : v * s * v⁻¹ * s⁻¹ ∈ (S : Subgroup ↥X) :=
    mul_mem ((hvn s).mp hs) (inv_mem hs)
  have h3 := hRS _ h1 h2'
  exact mul_inv_eq_one.mp h3

end CFSG.GH74.GLS.Bg.TwoGroups
