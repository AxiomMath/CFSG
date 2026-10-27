module

public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot
public import CFSG.ClassicalInvolution.SmallCases.NobqSmall

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def NoQ8Datum (F : Type) [Group F] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], Nonempty (↥N ≃* F) →
    Subgroup.centralizer (N : Set G) = ⊥ → TwoSubgroupsFourGenerated N →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) → False

theorem smallSimpleLeaf_of_noQ8Datum {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → NoQ8Datum F) : SmallSimpleLeaf P := by
  intro Y _ _ _ _ hnab hG hPF R S t hd hc _
  exfalso
  have := genFittingFStar_normal Y
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hG R S t hd hc.1

theorem smallSimpleLeaf_of_split {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hsplit : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : SmallSimpleLeaf Q₃)
    (h : SmallSimpleLeaf Q) : SmallSimpleLeaf P :=
  fun Y _ _ _ hA hnab hG hPF => (hsplit _ hPF).elim (h₃ Y hA hnab hG) (h Y hA hnab hG)

section Outer

variable {G : Type*} [Group G]

@[expose] noncomputable def outerHom (N : Subgroup G) [N.Normal] : G →* Outer N :=
  (QuotientGroup.mk' (inner N)).comp (MulAut.conjNormal : G →* MulAut N)

theorem outerHom_eq_one_iff {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {y : G} : outerHom N y = 1 ↔ y ∈ N := by
  constructor
  · intro hy
    have h2 : (MulAut.conjNormal y : MulAut N) ∈ inner N := (QuotientGroup.eq_one_iff _).mp hy
    obtain ⟨f, hf⟩ := h2
    have hg : y⁻¹ * (f : G) ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have key := congrArg (fun α : MulAut N => ((α ⟨x, hx⟩ : N) : G)) hf
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at key
      calc x * (y⁻¹ * (f : G)) = y⁻¹ * (y * x * y⁻¹) * f := by group
        _ = y⁻¹ * ((f : G) * x * (f : G)⁻¹) * f := by rw [key]
        _ = y⁻¹ * f * x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hg
    rw [hg]
    exact f.2
  · intro hy
    show (QuotientGroup.mk' (inner N)) (MulAut.conjNormal y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨y, hy⟩, ?_⟩
    ext x
    simp [MulAut.conjNormal_apply]

end Outer

section Datum

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.mem_of_mem_of_ne_one (hD : TightDatum R S t) {N : Subgroup G} {x : G}
    (hxR : x ∈ R) (hxN : x ∈ N) {k : ℕ} (hx : x ^ 2 ^ k = 1) (hx1 : x ≠ 1) : t ∈ N := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact absurd hm hx1
    · exact h
  have hy : orderOf (x ^ 2 ^ (m - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)), hm,
      Nat.pow_div (Nat.sub_le m 1) two_pos]
    have : m - (m - 1) = 1 := by omega
    rw [this, pow_one]
  rw [← hD.eq_of_orderOf_eq_two (R.pow_mem hxR _) hy]
  exact N.pow_mem hxN _

theorem TightDatum.mem_of_noQ8Outer (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hO : ∀ φ : QuaternionGroup 2 →* Outer N, ¬ Function.Injective φ) : t ∈ N := by
  by_contra htN
  obtain ⟨φ, hφ, hφR, -⟩ := datum_exists_q8 hD
  apply hO ((outerHom N).comp φ)
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hxN : φ x ∈ N := (outerHom_eq_one_iff hC).mp hx
  have hφx : φ x ≠ 1 := fun h => hx1 (hφ (h.trans (map_one φ).symm))
  have h8' : x ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp (orderOf_q8_dvd x)
  have h8 : φ x ^ 2 ^ 3 = 1 := by
    rw [← map_pow, show (2 : ℕ) ^ 3 = 8 by norm_num, h8', map_one]
  exact htN (TightDatum.mem_of_mem_of_ne_one hD (hφR x) hxN h8 hφx)

end Datum

end CFSG.ClassicalInvolution.Q3.TA3
