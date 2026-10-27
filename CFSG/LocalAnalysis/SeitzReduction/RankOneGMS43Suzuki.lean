module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace GMS43

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_pow_central_of_ne (hQ : IsPGroup 2 Q) {j j' : Q} (hj : j * j = 1)
    (hj' : j' * j' = 1) (hj'1 : j' ≠ 1) (hne : j ≠ j') :
    ∃ n : ℕ, (j * j') ^ n ≠ 1 ∧ (j * j') ^ n * (j * j') ^ n = 1 ∧
      j * (j * j') ^ n = (j * j') ^ n * j ∧ (j * j') ^ n ≠ j := by
  classical
  set c := j * j' with hc
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hj'inv : j'⁻¹ = j' := inv_eq_of_mul_eq_one_right hj'
  have hc1 : c ≠ 1 := by
    intro h1
    apply hne
    rw [eq_inv_of_mul_eq_one_right h1, hjinv]
  obtain ⟨k, hk⟩ := hQ c
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hc1 hm
  have hm1 : 2 ^ (m - 1) * 2 = 2 ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
  have hjc : j * c * j⁻¹ = c⁻¹ := by
    calc j * c * j⁻¹ = (j * j) * j' * j⁻¹ := by rw [hc]; group
      _ = j'⁻¹ * j⁻¹ := by rw [hj, one_mul, hj'inv]
      _ = c⁻¹ := by rw [hc, mul_inv_rev]
  have hz2 : c ^ 2 ^ (m - 1) * c ^ 2 ^ (m - 1) = 1 := by
    rw [← pow_add, ← two_mul, mul_comm, hm1, ← hm, pow_orderOf_eq_one]
  have hzinv : (c ^ 2 ^ (m - 1))⁻¹ = c ^ 2 ^ (m - 1) := inv_eq_of_mul_eq_one_right hz2
  refine ⟨2 ^ (m - 1), ?_, hz2, ?_, ?_⟩
  · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hm]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · have h1 : j * c ^ 2 ^ (m - 1) * j⁻¹ = c ^ 2 ^ (m - 1) := by
      rw [← conj_pow, hjc, inv_pow, hzinv]
    calc j * c ^ 2 ^ (m - 1) = j * c ^ 2 ^ (m - 1) * j⁻¹ * j := by group
      _ = c ^ 2 ^ (m - 1) * j := by rw [h1]
  · intro hzj
    by_cases hm2 : m = 1
    · subst hm2
      apply hj'1
      have h1 : j * j' = j := by simpa [hc] using hzj
      calc j' = j⁻¹ * (j * j') := by group
        _ = 1 := by rw [h1, inv_mul_cancel]
    ·
      have hcomm : j * c = c * j := by
        rw [← hzj, ← pow_succ', ← pow_succ]
      have h1 : c = c⁻¹ := by
        rw [← hjc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : c ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [h1]
        exact mul_inv_cancel c
      have h3 : 2 ^ m ∣ 2 := hm ▸ orderOf_dvd_of_pow_eq_one h2
      have h4 : 2 ^ m ≤ 2 := Nat.le_of_dvd (by norm_num) h3
      have h5 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

omit [Finite Q] in
theorem comm_of_mul_self {V : Subgroup Q} (hV2 : ∀ v ∈ V, v * v = 1) :
    ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV2 a ha)
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV2 b hb)
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hV2 _ (mul_mem ha hb))
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

theorem card_le_four_of_centralizer_le (hQ : IsPGroup 2 Q) {V : Subgroup Q} {j : Q}
    (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1) (hjV : j ∈ V)
    (hC : centralizer ({j} : Set Q) ≤ V) {B : Subgroup Q} (hB : ∀ b ∈ B, b * b = 1) :
    Nat.card B ≤ 4 := by
  have hVcomm := comm_of_mul_self hV2
  have hVab : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by rw [sq]; exact hV2 v hv
  have hcent : centralizer (V : Set Q) = V := by
    refine le_antisymm (fun x hx => hC ?_) (fun v hv => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hx j hjV).symm
    · exact mem_centralizer_iff.mpr fun w hw => hVcomm w hw v hv
  have hBexp : ∀ b ∈ B, b ^ 2 = 1 := fun b hb => by rw [sq]; exact hB b hb
  rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hQ V hVab hVexp hV4 hcent with
    ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective]
    refine CFSG.QuasithinUnique.dihedral_card_le_four (m := n - 1) (by omega) _ ?_
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hBexp b hb, map_one]
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective]
    refine CFSG.ABGDGroups.semidihedral_card_le_four hn _ ?_
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hBexp b hb, map_one]

theorem card_le_two_of_inf_eq_bot (hQ : IsPGroup 2 Q) {V : Subgroup Q} {j : Q}
    (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1) (hjV : j ∈ V)
    (hC : centralizer ({j} : Set Q) ≤ V) {B : Subgroup Q} (hB : ∀ b ∈ B, b * b = 1)
    (hBV : B ⊓ V = ⊥) : Nat.card B ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ1 : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    have := card_le_card_group V
    omega)
  have hZ : Nontrivial (center Q) := hQ.center_nontrivial
  obtain ⟨k, hk⟩ := (hQ.to_subgroup (center Q)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have := Finite.one_lt_card_iff_nontrivial.mpr hZ
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hzo : orderOf (z : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzz : (z : Q) * z = 1 := by rw [← sq, ← hzo, pow_orderOf_eq_one]
  have hz1 : (z : Q) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  have hzc : ∀ x : Q, x * z = z * x := fun x => (mem_center_iff.mp z.2 x)
  have hzV : (z : Q) ∈ V := hC (mem_centralizer_singleton_iff.mpr (hzc j).symm)
  have hzB : (z : Q) ∉ B := fun hzB => hz1 (by
    have : (z : Q) ∈ B ⊓ V := mem_inf.mpr ⟨hzB, hzV⟩
    rwa [hBV, mem_bot] at this)
  have hzN : zpowers (z : Q) ≤ normalizer (B : Set Q) := by
    refine zpowers_le.mpr (mem_normalizer_iff.mpr fun b => ?_)
    rw [show (z : Q) * b * (z : Q)⁻¹ = b by rw [← hzc b]; group]
  have hB' : ∀ x ∈ B ⊔ zpowers (z : Q), x * x = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers hzz hzN hx
    · exact hB b hb
    · calc b * z * (b * z) = (b * b) * (z * z) := by
            rw [mul_assoc b, ← mul_assoc (z : Q), ← hzc b]; group
        _ = 1 := by rw [hB b hb, hzz, one_mul]
  have h4 := card_le_four_of_centralizer_le hQ hV4 hV2 hjV hC hB'
  have hdvd := card_dvd_of_le (le_sup_left : B ≤ B ⊔ zpowers (z : Q))
  have hne : Nat.card B ≠ Nat.card (B ⊔ zpowers (z : Q) : Subgroup Q) := by
    intro heq
    have := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ zpowers (z : Q)) heq.ge
    exact hzB (this ▸ mem_sup_right (mem_zpowers _))
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < Nat.card B := Nat.card_pos
  rcases c with _ | _ | c
  · rw [hc, mul_zero] at h4
    have : 0 < Nat.card (B ⊔ zpowers (z : Q) : Subgroup Q) := Nat.card_pos
    omega
  · exact absurd (by rw [hc]; ring) hne
  · have : 2 * Nat.card B ≤ Nat.card (B ⊔ zpowers (z : Q) : Subgroup Q) := by
      rw [hc]
      nlinarith
    omega

end GMS43

end CFSG.SeitzReduction.RankOne
