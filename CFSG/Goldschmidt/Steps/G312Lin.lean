module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections

public section

namespace CFSG.Goldschmidt.G312

open CFSG.SectionRank.Ccomm

section MulAut

variable {p : ℕ} [hp : Fact p.Prime]

theorem GL_comm_of_le_one {d : ℕ} (hd : d ≤ 1) (a b : GL (Fin d) (ZMod p)) :
    a * b = b * a := by
  interval_cases d
  · apply Units.ext
    exact Subsingleton.elim _ _
  · exact GL_one_comm a b

theorem exists_central_involution_mulAut (hp2 : p ≠ 2) {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1)
    (hcard : Nat.card W ≤ p ^ 2) :
    ∃ ζ₀ ∈ Subgroup.center (MulAut W), ∀ y ∈ commutator (MulAut W), y ^ 2 = 1 →
      y = 1 ∨ y = ζ₀ := by
  have hWp : IsPGroup p W := fun w => ⟨1, by rw [pow_one, hpow]⟩
  obtain ⟨d, hd⟩ := hWp.exists_card_eq
  have hd2 : d ≤ 2 := by
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hd
  set φ := elemAutEquivGL e with hφ
  have hdet : ∀ y ∈ commutator (MulAut W),
      Matrix.GeneralLinearGroup.det (φ y) = 1 := by
    intro y hy
    have hy' : φ y ∈ commutator (GL (Fin d) (ZMod p)) := by
      have := Subgroup.mem_map_of_mem φ.toMonoidHom hy
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        φ.surjective, ← commutator_def] at this
      exact this
    exact Abelianization.commutator_subset_ker Matrix.GeneralLinearGroup.det hy'
  rcases Nat.lt_or_ge d 2 with hlt | hge
  ·
    refine ⟨1, Subgroup.one_mem _, fun y hy _ => Or.inl ?_⟩
    have hab : ∀ a b : MulAut W, a * b = b * a := fun a b =>
      φ.injective (by rw [map_mul, map_mul, GL_comm_of_le_one (by omega)])
    have hbot : commutator (MulAut W) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact hab b a
    rw [hbot] at hy
    exact (Subgroup.mem_bot).1 hy
  · have hd2' : d = 2 := le_antisymm hd2 hge
    subst hd2'
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := Nat.le_of_dvd (by norm_num) h'
      have := hp.out.two_le
      omega
    refine ⟨φ.symm (-1), ?_, fun y hy hy2 => ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Units.ext
      simp
    · by_cases hy1 : y = 1
      · exact Or.inl hy1
      right
      set A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
        ⟨(φ y : Matrix (Fin 2) (Fin 2) (ZMod p)), by
          have := congrArg Units.val (hdet y hy)
          simpa using this⟩ with hA
      have hA2 : A ^ 2 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
        have h := congrArg (fun g : GL (Fin 2) (ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)))
          (congrArg φ hy2)
        simpa using h
      have hA1 : A ≠ 1 := by
        intro h1
        apply hy1
        apply φ.injective
        apply Units.ext
        rw [map_one]
        have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
          (g : Matrix (Fin 2) (Fin 2) (ZMod p))) h1
        simpa [hA] using this
      have hneg := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 A hA2 hA1
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      apply Units.ext
      simpa [hA] using hneg

end MulAut

section Perfect

variable {X : Type*} [Group X] [Finite X]

theorem eq_one_or_eq_of_isPerfect (X₁ : Subgroup X) [X₁.Normal] (hodd : Odd (Nat.card X₁))
    {ζ : X} (hUI : ∀ y ∈ commutator X, y ^ 2 = 1 → y = 1 ∨ y = ζ) (J : Subgroup (X ⧸ X₁))
    (hJ : ⁅J, J⁆ = J) : ∀ u ∈ J, u ^ 2 = 1 → u = 1 ∨ u = (ζ : X ⧸ X₁) := by
  intro u hu hu2
  set Y := J.comap (QuotientGroup.mk' X₁) with hY
  have hYJ : Y.map (QuotientGroup.mk' X₁) = J :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J
  have hu' : u ∈ ⁅Y, Y⁆.map (QuotientGroup.mk' X₁) := by
    rw [Subgroup.map_commutator, hYJ, hJ]
    exact hu
  obtain ⟨y, hy, rfl⟩ := hu'
  have hyX : y ∈ commutator X := Subgroup.commutator_mono le_top le_top hy
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set y₂ := y ^ b with hy₂
  have hmk : (QuotientGroup.mk' X₁ y₂ : X ⧸ X₁) = QuotientGroup.mk' X₁ y := by
    obtain ⟨c, rfl⟩ := hb
    rw [hy₂, map_pow, pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hy₂pow : y₂ ^ 2 ^ a = 1 := by
    rw [hy₂, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hy₂sq : y₂ ^ 2 ∈ X₁ := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hmk]
    exact hu2
  have hy₂sq1 : y₂ ^ 2 = 1 := by
    have h1 : orderOf (y₂ ^ 2) ∣ 2 ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hy₂pow, one_pow]
    have h2 : orderOf (y₂ ^ 2) ∣ Nat.card X₁ := by
      rw [← Subgroup.orderOf_mk _ hy₂sq]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ a) (Nat.card X₁) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rcases hUI y₂ (Subgroup.pow_mem _ hyX b) hy₂sq1 with h | h
  · left
    rw [← hmk, h, map_one]
  · right
    rw [← hmk, h]
    rfl

end Perfect

end CFSG.Goldschmidt.G312
