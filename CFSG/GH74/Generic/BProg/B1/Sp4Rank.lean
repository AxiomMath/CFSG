module

public import CFSG.GH74.Generic.ClassicalCerts

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Subgroup

theorem ringChar_ne_two_of_odd_natCard {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have h0 := FiniteField.even_card_iff_char_two.1 h2
  rw [← Nat.card_eq_fintype_card] at h0
  have h1 := Nat.odd_iff.1 hF
  omega

theorem rankCertified_statedSp2 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    RankCertified ↥(StatedSp 2 F) 3 :=
  RankCertified.of_quotient ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F))
    (rankCertified_PSp4 (ringChar_ne_two_of_odd_natCard hF))

theorem scalar_sq_eq_one_gl {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {F : Type}
    [Field F] (c : Fˣ)
    (h : Matrix.GeneralLinearGroup.scalar ι c * Matrix.GeneralLinearGroup.scalar ι c = 1) :
    c = 1 ∨ c = -1 := by
  have h1 := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h1
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h2 := congrFun (congrFun h1 i) i
  rw [← map_mul, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
  rcases mul_self_eq_one_iff.1 h2 with h3 | h3
  · exact Or.inl (Units.ext h3)
  · exact Or.inr (Units.ext (by simpa using h3))

theorem scalar_neg_one_gl {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] :
    (Matrix.GeneralLinearGroup.scalar ι (-1 : Fˣ) : GL ι F) = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, Units.val_neg,
    Units.val_one, map_neg, map_one]

theorem statedSp2_central_involutions_eq {F : Type} [Field F] [Finite F]
    {z w : ↥(StatedSp 2 F)} (hz : z ∈ Subgroup.center ↥(StatedSp 2 F))
    (hw : w ∈ Subgroup.center ↥(StatedSp 2 F)) (hz2 : z * z = 1) (hw2 : w * w = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) : z = w := by
  have key : ∀ u : ↥(StatedSp 2 F), u ∈ Subgroup.center ↥(StatedSp 2 F) → u * u = 1 → u ≠ 1 →
      (u : GL (Fin 2 ⊕ Fin 2) F) = -1 := by
    intro u hu hu2 hu1
    rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hu
    obtain ⟨c, hc⟩ := hu
    have hsq : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c *
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = 1 := by
      rw [hc]
      exact congrArg Subtype.val hu2
    rcases scalar_sq_eq_one_gl c hsq with rfl | rfl
    · exact absurd (Subtype.ext (by rw [← hc, map_one]; rfl)) hu1
    · rw [← hc, scalar_neg_one_gl]
  exact Subtype.ext ((key z hz hz2 hz1).trans (key w hw hw2 hw1).symm)

theorem false_of_commuting_involution_sp4 {X : Type} [Group X] (hX : Gen4 X) {K : Subgroup X}
    {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) (e : ↥K ≃* ↥(StatedSp 2 F))
    {z : X} (hz2 : z * z = 1) (hzc : ∀ k ∈ K, z * k = k * z) (hzK : z ∉ K) : False := by
  have hKY : K ≤ Subgroup.centralizer ({z} : Set X) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzc k hk).symm
  have hz : z ∈ Subgroup.centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hK3 : RankCertified ↥K 3 := (rankCertified_statedSp2 hF).of_mulEquiv e.symm
  have hK3' : RankCertified ↥(K.subgroupOf (Subgroup.centralizer ({z} : Set X))) 3 :=
    hK3.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKY).symm
  have h4 : RankCertified ↥(Subgroup.centralizer ({z} : Set X)) 4 :=
    RankCertified.of_central_involution (K := K.subgroupOf (Subgroup.centralizer ({z} : Set X)))
      (c := ⟨z, hz⟩)
      (fun y => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2))
      (Subtype.ext hz2) (fun h => hzK (Subgroup.mem_subgroupOf.1 h)) hK3'
  exact h4.not_gen4 (le_refl 4) (Gen4.subgroup _ hX)

end CFSG.GH74.Generic.BProg.B1
