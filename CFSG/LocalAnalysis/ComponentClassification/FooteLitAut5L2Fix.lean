module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Base
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47Central
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

theorem right_eq_one_of_odd {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f) (hfo : ¬ Even f)
    (x : PGammaL2 F) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x.right = 1 := by
  have h1 : x.right ^ 2 ^ k = 1 := by
    rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, hk, map_one]
  have h2 : orderOf x.right ∣ f := by
    rw [← card_ringAut F hp hF]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    rw [hj] at h2
    exact hfo (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2))

theorem even_of_right_ne_one {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f) (x : PGammaL2 F)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) (hx : x.right ≠ 1) : Even f := by
  by_contra hfo
  exact hx (right_eq_one_of_odd hp hF hfo x hk)

omit [Finite F] in
theorem mem_sylowMap_iff (R : Sylow 2 Y) (r : Y) :
    e r ∈ (sylowMap e R : Subgroup (PSL2 F)) ↔ r ∈ (R : Subgroup Y) := by
  rw [coe_sylowMap, mem_map_equiv, MulEquiv.symm_apply_apply]

theorem eight_le_of_noncomm (hodd : IsOddPrimePower (Nat.card F)) (R : Sylow 2 Y)
    (hna : ∃ a ∈ (R : Subgroup Y), ∃ b ∈ (R : Subgroup Y), a * b ≠ b * a) :
    8 ≤ Nat.card (sylowMap e R) := by
  obtain ⟨m, hm, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv e hodd R
  have hcard : Nat.card (sylowMap e R) = 2 ^ (m + 1) := by
    rw [show Nat.card (sylowMap e R) = Nat.card (R : Subgroup Y) from card_sylowMap e R,
      Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  rw [hcard]
  by_contra hlt
  have hm1 : m = 1 := by
    by_contra hne
    have : 2 ^ 3 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hm1
  obtain ⟨a, ha, b, hb, hab⟩ := hna
  apply hab
  have hD2 : ∀ x y : DihedralGroup (2 ^ 1), x * y = y * x := by decide
  have h1 := hD2 (ρ ⟨a, ha⟩) (ρ ⟨b, hb⟩)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (ρ.injective h1)

include e in
theorem not_even_of_abelian {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (R : Sylow 2 Y)
    (hab : ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y), a * b = b * a) :
    Nat.card (R : Subgroup Y) = 4 ∧ ¬ Even f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  obtain ⟨m, hm, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv e hodd R
  have hcard : Nat.card (R : Subgroup Y) = 2 ^ (m + 1) := by
    rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm1 : m = 1 := by
    have hcomm : IsMulCommutative (DihedralGroup (2 ^ m)) := ⟨⟨fun a b => by
      obtain ⟨a', rfl⟩ := ρ.surjective a
      obtain ⟨b', rfl⟩ := ρ.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hab _ a'.2 _ b'.2)⟩⟩
    rcases DihedralGroup.commutative_iff.mp hcomm with h | h
    · exact absurd h (Nat.one_lt_two_pow (by omega)).ne'
    · exact Nat.pow_right_injective le_rfl (show 2 ^ m = 2 ^ 1 by rw [h, pow_one])
  subst hm1
  refine ⟨hcard, fun hfe => ?_⟩
  obtain ⟨t, rfl⟩ := hfe
  have h8 : 2 ^ 3 ∣ Nat.card Y := by
    rw [Nat.card_congr e.toEquiv, psl2_card_formula F hodd, hF, ← two_mul, pow_mul']
    exact eight_dvd_card_of_sq (hp.odd_of_ne_two hp2).pow
  have h4 := R.pow_dvd_card_of_pow_dvd_card h8
  rw [hcard] at h4
  norm_num at h4

theorem pgl_fixed_l2
    (hodd : IsOddPrimePower (Nat.card F)) (R : Sylow 2 Y) (α : MulAut Y) (hα : α ∈ linL2 e)
    (hαI : α ∉ innAut5 Y) (hα2 : α * α = 1) :
    Nat.card ↥((R : Subgroup Y) ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := (autEquiv e α).left with hg
  have hxg : autEquiv e α = SemidirectProduct.inl g :=
    eq_inl_of_right_eq_one ((mem_linL2 e α).mp hα)
  have hgJ : g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rintro ⟨z, hz⟩
    apply hαI
    rw [mem_innAut5_iff e, hxg, ← hz]
    exact ⟨z, rfl⟩
  have hg2 : orderOf g = 2 := by
    apply orderOf_eq_prime
    · have h1 : SemidirectProduct.inl (g ^ 2) = (1 : PGammaL2 F) := by
        rw [map_pow, ← hxg, sq, ← map_mul, hα2, map_one]
      exact SemidirectProduct.inl_injective (by rw [h1, map_one])
    · intro h1
      apply hgJ
      rw [h1]
      exact one_mem _
  have hq : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℤ, (Nat.card F : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with h | h
    · exact ⟨1, by rw [Int.ModEq]; omega, Or.inl rfl⟩
    · exact ⟨-1, by rw [Int.ModEq]; omega, Or.inr rfl⟩
  obtain ⟨m, hm, ⟨φ⟩⟩ := CFSG.ABGDGroups.pgl2_inf_centralizer_outer_involution_dihedral hodd hε hε1
    hg2 hgJ
  set C := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
    centralizer ({g} : Set (PGL2 F)) with hC
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : (0 : ℤ) ≤ Nat.card F - 2 := by
      have := Finite.one_lt_card (α := F)
      rcases Nat.odd_iff.mp hq with h
      omega
    rcases hε1 with rfl | rfl <;> omega
  have : NeZero m := ⟨hm0⟩
  have hCcard : Nat.card C = 2 * m := by rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  set Q := (R : Subgroup Y) ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y) with hQ
  have hQC : Q.map ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
      e.toMonoidHom) ≤ C := by
    rintro _ ⟨y, ⟨hyR, hyα⟩, rfl⟩
    refine ⟨⟨e y, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := (apply_eq_iff_commute e α y).mp hyα
    rw [hxg, incl_apply, ← map_mul, ← map_mul] at h1
    exact (SemidirectProduct.inl_injective h1).symm
  have hQcard : Nat.card Q ∣ 2 * m := by
    rw [← hCcard, ← card_map_of_injective (f := (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := F)).comp e.toMonoidHom)
      (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective)]
    exact card_dvd_of_le hQC
  have hQ2 : IsPGroup 2 Q := R.isPGroup'.to_le inf_le_left
  obtain ⟨j, hj⟩ := hQ2.exists_card_eq
  have h4 : ¬ 4 ∣ 2 * m := by
    intro h
    have hm' : (2 * m : ℤ) % 4 = 2 := by
      rw [hm]
      rcases hε1 with rfl | rfl <;> rw [Int.ModEq] at hε <;> omega
    omega
  rw [hj] at hQcard ⊢
  by_contra hlt
  have hj2 : 2 ≤ j := by
    by_contra h
    interval_cases j <;> simp at hlt
  exact h4 ((Nat.pow_dvd_pow 2 hj2).trans hQcard)

end CFSG.ComponentClassification.FooteLit.Aut5L2
