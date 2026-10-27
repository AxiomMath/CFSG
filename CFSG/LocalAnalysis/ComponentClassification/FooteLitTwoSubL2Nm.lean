module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Model

public section

namespace CFSG.ComponentClassification.FooteLit.TwoSub

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.FooteLit.Aut5L2

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem twist_pow' (ε : Bool) (x : Fˣ) (j : ℕ) : twist F ε (x ^ j) = twist F ε x ^ j := by
  cases ε
  · rfl
  · simp [inv_pow]

theorem finite_pGammaL2 : Finite (PGammaL2 F) := by
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) fun x y hxy =>
    SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

theorem mem_zpowers_sq_iff (hodd : IsOddPrimePower (Nat.card F)) (b : Fˣ) :
    b ∈ zpowers (stdGen F ^ 2) ↔ b ^ 2 ^ (twoVal F - 1) = 1 := by
  have hc := orderOf_stdGen_sq hodd
  constructor
  · intro h
    have h1 := orderOf_dvd_of_mem_zpowers h
    rw [hc] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  · intro h
    apply mem_zpowers_of_orderOf_dvd
    rw [hc]
    exact orderOf_dvd_of_pow_eq_one h

theorem pow_half_mul_self (hodd : IsOddPrimePower (Nat.card F)) (b : Fˣ) :
    b ^ 2 ^ (twoVal F - 1) * b ^ 2 ^ (twoVal F - 1) = b ^ 2 ^ twoVal F := by
  rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (one_le_twoVal hodd)]

theorem stdGen_pow_half (hodd : IsOddPrimePower (Nat.card F)) :
    stdGen F ^ 2 ^ (twoVal F - 1) = -1 := by
  have h1 := one_le_twoVal hodd
  have h2 : stdGen F ^ 2 ^ (twoVal F - 1) * stdGen F ^ 2 ^ (twoVal F - 1) = 1 := by
    rw [pow_half_mul_self hodd, ← orderOf_stdGen, pow_orderOf_eq_one]
  rcases eq_one_or_neg_one_of_mul_self h2 with h | h
  · exfalso
    have h3 := orderOf_le_of_pow_eq_one (by positivity) h
    rw [orderOf_stdGen] at h3
    have : 2 ^ (twoVal F - 1) < 2 ^ twoVal F := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact h

theorem pow_half_eq_one_or (hodd : IsOddPrimePower (Nat.card F)) {b : Fˣ}
    (hb : b ^ 2 ^ twoVal F = 1) : b ^ 2 ^ (twoVal F - 1) = 1 ∨ b ^ 2 ^ (twoVal F - 1) = -1 := by
  apply eq_one_or_neg_one_of_mul_self
  rw [pow_half_mul_self hodd, hb]

theorem nm_mem_stdT_iff (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (b : Fˣ) (ε : Bool) :
    nm F b ε 1 ∈ (stdT F).map (incl F) ↔ b ^ 2 ^ (twoVal F - 1) = 1 := by
  rw [mem_map_stdT_iff hsq, ← mem_zpowers_sq_iff hodd]
  constructor
  · rintro ⟨y, hy, ε', h⟩
    rw [(nm_eq_nm_iff.mp h).1]
    exact hy
  · intro h
    exact ⟨b, h, ε, rfl⟩

theorem exists_nm_of_mem (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (hn : 3 ≤ twoVal F) {Q : Subgroup (PGammaL2 F)}
    (hQ : IsPGroup 2 Q) (hTQ : (stdT F).map (incl F) ≤ Q) {x : PGammaL2 F} (hx : x ∈ Q) :
    ∃ b ε, b ^ 2 ^ twoVal F = 1 ∧ x = nm F b ε x.right := by
  have hnorm := conj_mem_of_mem (stdSylow F hodd hsq hq4) Q hQ (by rw [coe_stdSylow]; exact hTQ)
    hx
  rw [coe_stdSylow] at hnorm
  obtain ⟨b, ε, hxb⟩ := exists_nm_of_normalizes_stdT hodd hsq hn x hnorm
  refine ⟨b, ε, ?_, hxb⟩
  have hs : nm F 1 true 1 ∈ (stdT F).map (incl F) :=
    (nm_mem_stdT_iff hodd hsq 1 true).mpr (one_pow _)
  obtain ⟨y, hy, ε', hy'⟩ := (mem_map_stdT_iff hsq _).mp (hnorm _ hs)
  have h1 : x * nm F 1 true 1 = nm F y ε' 1 * x := by rw [← hy']; group
  rw [hxb, nm_mul, nm_mul] at h1
  simp only [map_one, twist_one, mul_one, fu_one, one_mul, nm_eq_nm_iff] at h1
  obtain ⟨h1a, h1b, -⟩ := h1
  have hε' : ε' = true := by
    revert h1b
    cases ε <;> cases ε' <;> decide
  rw [hε', twist_true] at h1a
  have hyb : y = b * b := (mul_inv_eq_iff_eq_mul.mp h1a.symm)
  rw [mem_zpowers_sq_iff hodd, hyb, ← pow_two, ← pow_mul, ← pow_succ',
    Nat.sub_add_cancel (by omega)] at hy
  exact hy

theorem sq_form (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (hn : 3 ≤ twoVal F) {Q : Subgroup (PGammaL2 F)}
    (hQ : IsPGroup 2 Q) (hTQ : (stdT F).map (incl F) ≤ Q) {x : PGammaL2 F} (hx : x ∈ Q) :
    ∃ c : Fˣ, c ^ 2 ^ (twoVal F - 1) = 1 ∧ x * x = nm F c false (x.right * x.right) := by
  obtain ⟨b, ε, hb, hxb⟩ := exists_nm_of_mem hodd hsq hq4 hn hQ hTQ hx
  refine ⟨b * twist F ε (fu F x.right b), ?_, ?_⟩
  · have hmm : b ^ 2 ^ (twoVal F - 1) * b ^ 2 ^ (twoVal F - 1) = 1 := by
      rw [pow_half_mul_self hodd, hb]
    rw [mul_pow, ← twist_pow', ← map_pow, fu_of_mul_self _ hmm, twist_of_mul_self _ hmm, hmm]
  · conv_lhs => rw [hxb, nm_mul, Bool.xor_self]

theorem exists_central_of_good {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hn : 3 ≤ twoVal F)
    {Q : Subgroup (PGammaL2 F)} (hTQ : (stdT F).map (incl F) ≤ Q) {b : Fˣ}
    (hb : b ^ 2 ^ (twoVal F - 1) = 1) {ε : Bool} {σ : F ≃+* F} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hmem : nm F b ε σ ∈ Q) :
    ∃ β ∈ Q, β * β = 1 ∧ β.right ≠ 1 ∧ ∀ g ∈ (stdT F).map (incl F), β * g = g * β := by
  have hσ0 : nm F 1 false σ ∈ Q := by
    have h1 : nm F 1 false σ = (nm F b ε 1)⁻¹ * nm F b ε σ := by
      rw [eq_inv_mul_iff_mul_eq, nm_mul]
      simp [fu_one]
    rw [h1]
    exact Q.mul_mem (Q.inv_mem (hTQ ((nm_mem_stdT_iff hodd hsq b ε).mpr hb))) hmem
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
  rcases fix_or_inv_of_order_two hp hp2 hF σ (by rw [pow_one]; exact hσ2) (stdGen F ^ 2)
    (orderOf_stdGen_sq hodd) (by omega) with h | h
  · refine ⟨nm F 1 false σ, hσ0, ?_, hσ1, ?_⟩
    · rw [nm_mul, hσσ, map_one, twist_false, mul_one, Bool.xor_self, nm_one]
    · intro g hg
      obtain ⟨y', hy', ε', rfl⟩ := (mem_map_stdT_iff hsq _).mp hg
      obtain ⟨i, rfl⟩ := hy'
      rw [nm_mul, nm_mul, map_zpow, h, twist_false, one_mul, fu_one, twist_one, mul_one,
        mul_one, one_mul, Bool.false_xor, Bool.xor_false]
  · have hs : nm F 1 true 1 ∈ Q := hTQ ((nm_mem_stdT_iff hodd hsq 1 true).mpr (one_pow _))
    refine ⟨nm F 1 true σ, ?_, ?_, hσ1, ?_⟩
    · have h1 : nm F 1 true σ = nm F 1 true 1 * nm F 1 false σ := by
        rw [nm_mul]
        simp [fu_one]
      rw [h1]
      exact Q.mul_mem hs hσ0
    · rw [nm_mul, hσσ, map_one, twist_one, mul_one, Bool.xor_self, nm_one]
    · intro g hg
      obtain ⟨y', hy', ε', rfl⟩ := (mem_map_stdT_iff hsq _).mp hg
      obtain ⟨i, rfl⟩ := hy'
      rw [nm_mul, nm_mul, map_zpow, h, twist_true, inv_zpow, inv_inv, one_mul, fu_one,
        twist_one, mul_one, mul_one, one_mul, Bool.true_xor, Bool.xor_true]

theorem right_mul_self_of_not_good (hodd : IsOddPrimePower (Nat.card F))
    (hsq : IsSquare (-1 : F)) (hq4 : Nat.card F % 4 = 1) (hn : 3 ≤ twoVal F)
    {Q : Subgroup (PGammaL2 F)} (hQ : IsPGroup 2 Q) (hTQ : (stdT F).map (incl F) ≤ Q)
    (hng : ¬ ∃ b : Fˣ, b ^ 2 ^ (twoVal F - 1) = 1 ∧
      ∃ ε σ, σ * σ = 1 ∧ σ ≠ 1 ∧ nm F b ε σ ∈ Q) {x : PGammaL2 F} (hx : x ∈ Q) :
    x.right * x.right = 1 := by
  by_contra hne
  obtain ⟨j, hj⟩ := hQ ⟨x, hx⟩
  have hxj : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hσj : x.right ^ 2 ^ j = 1 := by
    have h1 := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut F)) x (2 ^ j)
    rw [hxj, map_one] at h1
    exact h1.symm
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσj)
  have hm2 : 2 ≤ m := by
    by_contra h
    apply hne
    interval_cases m
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      rw [hm, mul_one]
    · rw [pow_one] at hm
      have h1 := pow_orderOf_eq_one x.right
      rwa [hm, pow_two] at h1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hyQ : x ^ 2 ^ m' ∈ Q := Q.pow_mem hx _
  obtain ⟨c, hc, hyy⟩ := sq_form hodd hsq hq4 hn hQ hTQ hyQ
  have hyr : (x ^ 2 ^ m').right * (x ^ 2 ^ m').right = x.right ^ 2 ^ (m' + 1) := by
    have h1 := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut F)) x (2 ^ m')
    rw [SemidirectProduct.rightHom_eq_right] at h1
    rw [h1, ← pow_add, ← two_mul, ← pow_succ']
  apply hng
  refine ⟨c, hc, false, _, ?_, ?_, hyy ▸ Q.mul_mem hyQ hyQ⟩
  · rw [hyr, ← pow_add, ← two_mul, ← pow_succ', ← hm, pow_orderOf_eq_one]
  · rw [hyr]
    exact pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [hm]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))

end CFSG.ComponentClassification.FooteLit.TwoSub
