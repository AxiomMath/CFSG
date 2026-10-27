module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
import all CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.FixedPointProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

open CFSG.Wielandt

section Internal

variable {A J : Type} [Group A] [Finite A] [Group J] [Finite J]
    [MulDistribMulAction A J]

@[expose] def actionFixedCard (B : Subgroup A) : ℕ :=
  letI : MulDistribMulAction B J := MulDistribMulAction.compHom J B.subtype
  Nat.card (fixedPointSubgroup B J)

omit [Finite A] [Finite J] in
theorem mem_zpowers_kleinFour_iff [IsKleinFour A] (a x : A) :
    x ∈ Subgroup.zpowers a ↔ x = 1 ∨ x = a := by
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hmod : a ^ (z % 2) = a ^ z := by
      exact (zpow_eq_zpow_emod' z (show a ^ (2 : ℕ) = 1 by
        simpa only [pow_two] using IsKleinFour.mul_self a)).symm
    have hnonneg : 0 ≤ z % 2 := Int.emod_nonneg _ (by decide)
    have hlt : z % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    have hcases : z % 2 = 0 ∨ z % 2 = 1 := by omega
    rcases hcases with h | h
    · left
      rw [← hmod, h]
      simp
    · right
      rw [← hmod, h]
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem fourgroup_fixed_order_identity [IsKleinFour A]
    (hcop : Nat.Coprime (Nat.card J) (Nat.card A))
    (hsolv : Group.IsSolvable J) (a b : A)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    Nat.card J * actionFixedCard (J := J) (⊤ : Subgroup A) ^ 2 =
      actionFixedCard (J := J) (Subgroup.zpowers a) *
      actionFixedCard (J := J) (Subgroup.zpowers b) *
      actionFixedCard (J := J) (Subgroup.zpowers (a * b)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let B : Fin 5 → Subgroup A :=
    ![⊥, ⊤, Subgroup.zpowers a, Subgroup.zpowers b, Subgroup.zpowers (a * b)]
  let m : Fin 5 → ℕ := ![2, 1, 0, 0, 0]
  let n : Fin 5 → ℕ := ![0, 0, 1, 1, 1]
  have hcoeff : ∀ g : A,
      (∑ i : Fin 5, if g ∈ B i then m i else 0) =
        ∑ i : Fin 5, if g ∈ B i then n i else 0 := by
    intro g
    have hg : g ∈ ({a * b, a, b, (1 : A)} : Finset A) := by
      rw [IsKleinFour.eq_finset_univ ha hb hab]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    have habone : a * b ≠ 1 := by
      intro h
      exact hab (by simpa only [IsKleinFour.inv_eq_self] using mul_eq_one_iff_eq_inv.mp h)
    have habne_a : a * b ≠ a := by simpa using hb
    have habne_b : a * b ≠ b := by simpa using ha
    rcases hg with rfl | rfl | rfl | rfl <;>
      simp [B, m, n, Fin.sum_univ_succ, mem_zpowers_kleinFour_iff,
        ha, hb, hab, hab.symm, habone, habne_a, habne_b,
        Ne.symm habne_a, Ne.symm habne_b]
  have hcard (x : A) (hx : x ≠ 1) : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    have hdiv : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa only [pow_two] using IsKleinFour.mul_self x)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact (hx (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have habone : a * b ≠ 1 := by
    intro h
    exact hab (by simpa only [IsKleinFour.inv_eq_self] using mul_eq_one_iff_eq_inv.mp h)
  have hbot : actionFixedCard (J := J) (⊥ : Subgroup A) = Nat.card J := by
    simp only [actionFixedCard, fixedPointSubgroup_bot_subgroup_eq_top, Subgroup.card_top]
  have hprod := fixedPointSubgroup_product_card_eq_of_coeff_sum_eq hcop hsolv B m n hcoeff
  change (∏ i : Fin 5, actionFixedCard (J := J) (B i) ^ (m i * Nat.card (B i))) =
    ∏ i : Fin 5, actionFixedCard (J := J) (B i) ^ (n i * Nat.card (B i)) at hprod
  simp only [B, m, n, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Subgroup.card_bot, Subgroup.card_top,
    IsKleinFour.card_four, hcard a ha, hcard b hb, hcard (a * b) habone,
    Nat.zero_mul, pow_zero, mul_one, one_mul] at hprod
  rw [hbot] at hprod
  apply (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp
  simpa only [mul_pow, ← pow_mul, show 2 * 2 = 4 by decide, mul_assoc] using hprod

end Internal

variable {G : Type} [Group G] [Finite G]

theorem ambient_fourgroup_fixed_order_identity (V J : Subgroup G)
    (hV : IsKleinFour V) (hodd : Odd (Nat.card J))
    (hsolv : Group.IsSolvable J) (hnorm : NormalizedBy J V)
    (a b : G) (haV : a ∈ V) (hbV : b ∈ V)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    Nat.card J * Nat.card (J ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ^ 2 =
      Nat.card (J ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
      Nat.card (J ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) *
      Nat.card (J ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) := by
  let : IsKleinFour V := hV
  let : MulDistribMulAction V J := SignalizerFunctor.Helpers.conjugationAction V J hnorm
  have hfixed (B : Subgroup V) :
      actionFixedCard (J := J) B =
        Nat.card (J ⊓ Subgroup.centralizer (B.map V.subtype : Set G) : Subgroup G) := by
    let : MulDistribMulAction B J := MulDistribMulAction.compHom J B.subtype
    let F : Subgroup J := fixedPointSubgroup B J
    have heq : F.map J.subtype = J ⊓ Subgroup.centralizer (B.map V.subtype : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro v hv
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
        have h := congrArg Subtype.val (hy (⟨w, hw⟩ : B))
        change (w : G) * (y : G) * (w : G)⁻¹ = y at h
        exact mul_inv_eq_iff_eq_mul.mp h
      · rintro ⟨hx, hc⟩
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        intro w
        apply Subtype.ext
        change (w : G) * x * (w : G)⁻¹ = x
        exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hc w
          (Subgroup.mem_map_of_mem V.subtype w.property))
    change Nat.card F = _
    rw [← heq, Subgroup.card_map_of_injective J.subtype_injective]
  have hz (x : V) : actionFixedCard (J := J) (Subgroup.zpowers x) =
      Nat.card (J ⊓ Subgroup.centralizer ({(x : G)} : Set G) : Subgroup G) := by
    rw [hfixed, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
    rfl
  have htop : actionFixedCard (J := J) (⊤ : Subgroup V) =
      Nat.card (J ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    rw [hfixed, Subgroup.map_top, Subgroup.range_subtype]
  have hcop : Nat.Coprime (Nat.card J) (Nat.card V) := by
    rw [hV.card_four]
    simpa using hodd.coprime_two_right.pow_right 2
  have h := fourgroup_fixed_order_identity hcop hsolv (⟨a, haV⟩ : V) (⟨b, hbV⟩ : V)
    (fun h => ha (congrArg Subtype.val h)) (fun h => hb (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h))
  rw [htop, hz, hz, hz] at h
  exact h

end CFSG.DihedralBlueprint
