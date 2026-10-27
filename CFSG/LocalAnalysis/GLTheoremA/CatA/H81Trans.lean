module

public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Generic

variable {K K' : Type} [Group K] [Group K'] [Finite K]

theorem coprime_inf_ker {p : ℕ} (hp : p.Prime) (ψ : K →* K')
    (hψ : Nat.Coprime p (Nat.card ψ.ker)) (A : Subgroup K) :
    Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker)) := by
  have hd : Nat.card ↥(A ⊓ ψ.ker) ∣ Nat.card ψ.ker :=
    Subgroup.card_dvd_of_le (inf_le_right : A ⊓ ψ.ker ≤ ψ.ker)
  exact Nat.Coprime.coprime_dvd_right hd hψ

theorem component_eq_of_map_eq {p : ℕ} (hp : p.Prime) (ψ : K →* K')
    (hψ : ∀ A : Subgroup K, Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) {A S₁ S₂ : Subgroup K}
    (h₁ : GLAPComponent p A S₁) (h₂ : GLAPComponent p A S₂) (h : S₁.map ψ = S₂.map ψ) : S₁ = S₂ := by
  have hinj := lcEquiv hp ψ A (hψ A)
  apply glaPComponent_unique h₁ h₂
  have e1 := lcEquiv_barX hp ψ A (hψ A) h₁.1
  have e2 := lcEquiv_barX hp ψ A (hψ A) h₂.1
  have : (barX p A S₁).map (lcMonoidHom hp ψ A (hψ A)) =
      (barX p A S₂).map (lcMonoidHom hp ψ A (hψ A)) := by
    rw [e1, e2, h]
  exact Subgroup.map_injective (lcEquiv hp ψ A (hψ A)).injective this

theorem layer_eq_of_unique {p : ℕ} {A S : Subgroup K}
    (hS : GLAPComponent p A S) (hall : ∀ T : Subgroup K, GLAPComponent p A T → T = S) :
    GLAPLayer p A = S := by
  unfold GLAPLayer
  apply le_antisymm
  · exact sSup_le fun T hT => (hall T hT).le
  · exact le_sSup hS

theorem component_ne_bot {p : ℕ} {A S : Subgroup K} (hS : GLAPComponent p A S) : S ≠ ⊥ := by
  intro h
  have hnt := isQuasisimple_nontrivial hS.2.2.1.2.2
  have hbar : barX p A S = ⊥ := by
    rw [barX, h, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hbar

theorem map_inf_centralizer_eq {p : ℕ} (hp : p.Prime) (ψ : K →* K')
    (hψ : ∀ A : Subgroup K, Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker)))
    {A : Subgroup K} {y : K} (hy : IsPGroup p (Subgroup.zpowers y))
    (hyA : y ∈ Subgroup.normalizer (A : Set K)) :
    (A ⊓ Subgroup.centralizer ({y} : Set K)).map ψ =
      A.map ψ ⊓ Subgroup.centralizer ({ψ y} : Set K') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · rintro _ ⟨a, ⟨haA, hay⟩, rfl⟩
    refine ⟨Subgroup.mem_map.2 ⟨a, haA, rfl⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := Subgroup.mem_centralizer_iff.1 hay y (Set.mem_singleton y)
    rw [← map_mul, ← map_mul, this]
  · rintro h ⟨hhA, hhC⟩
    obtain ⟨a0, ha0A, rfl⟩ := Subgroup.mem_map.1 hhA
    have hC1 : Commute (ψ y) (ψ a0) := Subgroup.mem_centralizer_iff.1 hhC (ψ y) (Set.mem_singleton _)
    have hCz : ∀ g ∈ Subgroup.zpowers y, Commute (ψ a0) (ψ g) := by
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [map_zpow]
      exact hC1.symm.zpow_right n
    have hzA : Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set K) := Subgroup.zpowers_le.2 hyA
    let X := {a : K // a ∈ A ∧ ψ a = ψ a0}
    have hstab : ∀ g ∈ Subgroup.zpowers y, ∀ a : X,
        (g * a.1 * g⁻¹ ∈ A ∧ ψ (g * a.1 * g⁻¹) = ψ a0) := by
      intro g hg a
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hzA hg) a.1).1 a.2.1, ?_⟩
      rw [map_mul, map_mul, map_inv, a.2.2, ← (hCz g hg).eq, mul_inv_cancel_right]
    have hcardX : Nat.card X = Nat.card ↥(A ⊓ ψ.ker) := by
      apply Nat.card_congr
      exact
        { toFun := fun a => ⟨a0⁻¹ * a.1, Subgroup.mem_inf.2 ⟨A.mul_mem (A.inv_mem ha0A) a.2.1,
            MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, a.2.2, inv_mul_cancel])⟩⟩
          invFun := fun n => ⟨a0 * n.1, ⟨A.mul_mem ha0A (Subgroup.mem_inf.1 n.2).1,
            by rw [map_mul, MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 n.2).2, mul_one]⟩⟩
          left_inv := fun a => Subtype.ext (by simp)
          right_inv := fun n => Subtype.ext (by simp) }
    letI : MulAction (Subgroup.zpowers y) X :=
      { smul := fun g a => ⟨(g : K) * a.1 * (g : K)⁻¹, hstab (g : K) g.2 a⟩
        one_smul := fun a => Subtype.ext (by
          show (1 : K) * a.1 * (1 : K)⁻¹ = a.1
          rw [inv_one, mul_one, one_mul])
        mul_smul := fun g g' a => Subtype.ext (by
          show ((g : K) * (g' : K)) * a.1 * ((g : K) * (g' : K))⁻¹ = (g : K) * ((g' : K) * a.1 * (g' : K)⁻¹) * (g : K)⁻¹
          simp only [mul_inv_rev, mul_assoc]) }
    have hmod := hy.card_modEq_card_fixedPoints X
    have hcop : ¬ p ∣ Nat.card X := by
      rw [hcardX]
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 (hψ A)
    have hFne : 0 < Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) X) := by
      rcases Nat.eq_zero_or_pos (Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) X)) with h0 | h0
      · exfalso
        apply hcop
        rw [h0] at hmod
        exact Nat.modEq_zero_iff_dvd.1 hmod
      · exact h0
    obtain ⟨⟨a', ha'⟩, -⟩ := Nat.card_pos_iff.1 hFne
    have hfix : ∀ g : Subgroup.zpowers y, g • a' = a' := MulAction.mem_fixedPoints.1 ha'
    have hy1 : y * a'.1 * y⁻¹ = a'.1 := congrArg Subtype.val (hfix ⟨y, Subgroup.mem_zpowers y⟩)
    have hyc : y * a'.1 = a'.1 * y := mul_inv_eq_iff_eq_mul.1 hy1
    refine Subgroup.mem_map.2 ⟨a'.1, Subgroup.mem_inf.2 ⟨a'.2.1,
      Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩, a'.2.2⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hyc

theorem coprime_ker_quot {p : ℕ} (hp : p.Prime) (L : Subgroup K) :
    Nat.Coprime p (Nat.card (QuotientGroup.mk' (GLAPPrimeCore p ↥L)).ker) := by
  rw [QuotientGroup.ker_mk']
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.pPrimeCore_coprime_card

theorem coprime_inf_quot {p : ℕ} (hp : p.Prime) (L : Subgroup K) (A : Subgroup ↥L) :
    Nat.Coprime p (Nat.card ↥(A ⊓ (QuotientGroup.mk' (GLAPPrimeCore p ↥L)).ker)) :=
  coprime_inf_ker hp _ (coprime_ker_quot hp L) A

theorem component_lift {p : ℕ} (hp : p.Prime) (ψ : K →* K')
    (hψ : ∀ A : Subgroup K, Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) (A : Subgroup K) {M : Subgroup K'}
    (hM : GLAPComponent p (A.map ψ) M) : ∃ S : Subgroup K, GLAPComponent p A S ∧ S.map ψ = M :=
  exists_glaPComponent_map_eq hp ψ (hψ A) hM

theorem component_image {p : ℕ} (hp : p.Prime) (ψ : K →* K')
    (hψ : ∀ A : Subgroup K, Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) (A : Subgroup K) {S : Subgroup K}
    (hS : GLAPComponent p A S) : GLAPComponent p (A.map ψ) (S.map ψ) :=
  glaPComponent_map hp ψ (hψ A) hS

end Generic

end CFSG.LocalAnalysis.GLTheoremA.H81
