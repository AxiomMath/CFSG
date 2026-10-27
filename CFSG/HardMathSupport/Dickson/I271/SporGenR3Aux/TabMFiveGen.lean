module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Inverted

theorem tabMFive_quasisimple_of_simple_nonab {J : Type} [Group J] [IsSimpleGroup J]
    (hnab : ∃ a b : J, a * b ≠ b * a) : CFSG.Open.IsQuasisimple J := by
  have hZ : Subgroup.center J = ⊥ := center_eq_bot_of_simple_nonab hnab
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
  · exact h

variable {G : Type} [Group G] [Finite G]

theorem tabMFive_shapeRkAt'_of_inverted {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    {k α : G} (hk : orderOf k = p) (hα : α * k * α⁻¹ = k⁻¹) {H : Subgroup G}
    (hHα : H ≤ Subgroup.centralizer ({α} : Set G)) (hHk : H ≤ Subgroup.centralizer ({k} : Set G))
    (hs : IsSimpleGroup ↥H) (hnab : ∃ a b : ↥H, a * b ≠ b * a) (hpH : p ∣ Nat.card ↥H)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ p * Nat.card ↥H)
    (hG : Good ↥H) (hR : Rk ↥H) : ShapeRkAt' p Good Rk k := by
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Subgroup.centralizer ({k} : Set G) with hX
  have hkX : k ∈ X := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hinv : ∀ g ∈ Subgroup.zpowers k, α * g * α⁻¹ = g⁻¹ := by
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← conj_zpow, hα, inv_zpow]
  have hKH : ∀ g ∈ Subgroup.zpowers k, g ∈ H → g = 1 := by
    intro g hg hgH
    have hc : g * α = α * g := Subgroup.mem_centralizer_singleton_iff.1 (hHα hgH)
    have h1 : α * g * α⁻¹ = g := by rw [← hc]; simp
    have h2 : g * g = 1 := by
      have h3 := hinv g hg
      rw [h1] at h3
      exact mul_eq_one_iff_eq_inv.2 h3
    have h4 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    have h5 : orderOf g ∣ p := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk, pow_orderOf_eq_one,
        one_zpow]
    have h6 : orderOf g ∣ Nat.gcd 2 p := Nat.dvd_gcd h4 h5
    have h7 : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rw [h7] at h6
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)
  let f : Fin p × ↥H → ↥X := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), X.mul_mem (X.pow_mem hkX _) (hHk x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, h⟩ ⟨j, h'⟩ hij
    have hij' : k ^ (i : ℕ) * (h : G) = k ^ (j : ℕ) * (h' : G) := congrArg Subtype.val hij
    have h1 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) = (h' : G) * (h : G)⁻¹ := by
      calc (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ)
          = (k ^ (j : ℕ))⁻¹ * (k ^ (i : ℕ) * (h : G)) * (h : G)⁻¹ := by group
        _ = (k ^ (j : ℕ))⁻¹ * (k ^ (j : ℕ) * (h' : G)) * (h : G)⁻¹ := by rw [hij']
        _ = (h' : G) * (h : G)⁻¹ := by group
    have h2 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) ∈ Subgroup.zpowers k :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _))
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _)
    have h3 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) ∈ H := by
      rw [h1]
      exact H.mul_mem h'.2 (H.inv_mem h.2)
    have h4 := hKH _ h2 h3
    have h5 : k ^ (j : ℕ) = k ^ (i : ℕ) := inv_mul_eq_one.1 h4
    have h6 : (i : ℕ) = (j : ℕ) := by
      have hi : (i : ℕ) ∈ Set.Iio (orderOf k) := by rw [hk]; exact i.2
      have hj : (j : ℕ) ∈ Set.Iio (orderOf k) := by rw [hk]; exact j.2
      exact (pow_injOn_Iio_orderOf hi hj h5.symm)
    have h7 : (h' : G) * (h : G)⁻¹ = 1 := by rw [← h1, h6]; simp
    have hij2 : i = j := Fin.ext h6
    subst hij2
    have : (h' : G) = h := mul_inv_eq_one.1 h7
    exact Prod.ext rfl (Subtype.ext this.symm)
  have hbij : Function.Bijective f := by
    refine hf.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]
    exact hbound
  have hdec : ∀ x ∈ X, ∃ (i : ℕ) (h : G), h ∈ H ∧ x = k ^ i * h := by
    intro x hx
    obtain ⟨⟨i, h⟩, hih⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨i, h, h.2, (congrArg Subtype.val hih).symm⟩
  have hcomm : ∀ (i : ℕ) (y : G), y ∈ H → k ^ i * y * (k ^ i)⁻¹ = y := by
    intro i y hy
    have hyk : Commute y k := Subgroup.mem_centralizer_singleton_iff.1 (hHk hy)
    have h1 : y * k ^ i = k ^ i * y := (hyk.pow_right i).eq
    rw [← h1]
    simp
  have hLn : ∀ g ∈ X, ∀ l ∈ H, g * l * g⁻¹ ∈ H := by
    intro g hg l hl
    obtain ⟨i, h, hh, rfl⟩ := hdec g hg
    have hmem : h * l * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hl) (H.inv_mem hh)
    have e1 : k ^ i * h * l * (k ^ i * h)⁻¹ = k ^ i * (h * l * h⁻¹) * (k ^ i)⁻¹ := by group
    rw [e1, hcomm i _ hmem]
    exact hmem
  have hZ : Subgroup.center ↥H = ⊥ := center_eq_bot_of_simple_nonab hnab
  have hcentle : X ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.zpowers k := by
    rintro c ⟨hcX, hcH⟩
    obtain ⟨i, h, hh, rfl⟩ := hdec c hcX
    have hh1 : h = 1 := by
      have hcomm' : ∀ y ∈ H, y * h = h * y := by
        intro y hy
        have h1 := Subgroup.mem_centralizer_iff.1 hcH y hy
        have hyk : Commute y k := Subgroup.mem_centralizer_singleton_iff.1 (hHk hy)
        have h2 : y * k ^ i = k ^ i * y := (hyk.pow_right i).eq
        have h3 : k ^ i * (y * h) = k ^ i * (h * y) := by
          calc k ^ i * (y * h) = (k ^ i * y) * h := by rw [mul_assoc]
            _ = (y * k ^ i) * h := by rw [h2]
            _ = y * (k ^ i * h) := by rw [mul_assoc]
            _ = (k ^ i * h) * y := h1
            _ = k ^ i * (h * y) := by rw [mul_assoc]
        exact mul_left_cancel h3
      have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.center ↥H :=
        Subgroup.mem_center_iff.2 fun b => Subtype.ext (hcomm' b b.2)
      rw [hZ, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    rw [hh1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _
  have hKp : IsPGroup p ↥(Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, pow_one])
  have hcent : IsPGroup p ↥(X ⊓ Subgroup.centralizer (H : Set G)) := hKp.to_le hcentle
  haveI := hs
  have hLq : CFSG.Open.IsQuasisimple ↥H := tabMFive_quasisimple_of_simple_nonab hnab
  have hcoreH : GLAPPrimeCore p ↥H = ⊥ := glaPPrimeCore_eq_bot_of_simple hp hpH
  have hG' : Good (PSimple p H) :=
    hGood ↥H (PSimple p H) (pSimpleEquivSelf H hcoreH hZ).symm hG
  have hR' : Rk (PQuot p H) := hRk ↥H (PQuot p H) (pQuotEquivSelf H hcoreH).symm hR
  exact (shapeRkAt_of_normal_quasisimple hp hHk hLn hLq hpH hcent hG' hR').toWeak hp

end Inverted

end CFSG.HardMathSupport.Dickson.I271
