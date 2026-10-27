module

public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.CharacterTheory.Burnside
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

section Lemma18

open CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups

theorem isSolvable_of_normal_comm_sup_cyclic {H : Type*} [Group H] (E C : Subgroup H) [E.Normal]
    [IsMulCommutative E] (hC : IsCyclic C) (hsup : E ⊔ C = ⊤) : Group.IsSolvable H := by
  have hmem : ∀ x : H, ∃ c ∈ C, (x : H ⧸ E) = (c : H ⧸ E) := by
    intro x
    have hx : x ∈ (E : Set H) * (C : Set H) := by
      rw [← Subgroup.normal_mul, hsup]
      exact Set.mem_univ x
    obtain ⟨e, he, c, hc, rfl⟩ := hx
    refine ⟨c, hc, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).mpr he, one_mul]
  have hcyc : IsCyclic (H ⧸ E) :=
    isCyclic_of_surjective ((QuotientGroup.mk' E).comp C.subtype) (by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨c, hc, h⟩ := hmem m
      exact ⟨⟨c, hc⟩, h.symm⟩)
  have : Group.IsSolvable (H ⧸ E) := by
    have := IsCyclic.isMulCommutative (α := H ⧸ E)
    infer_instance
  exact Group.isSolvable_of_ker_le_range E.subtype (QuotientGroup.mk' E) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem nonsolvable_cases
    (hF : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (hH : ¬ Group.IsSolvable H) :
    (Nonempty (H ≃* alternatingGroup (Fin 5)) ∧ (p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5])) ∨
    (∃ m, m ∣ f ∧ Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
    (∃ m, 2 * m ∣ f ∧ Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  rcases dickson_psl2_subgroup_list hF H with
    ⟨m, hm, hcard, hel⟩ | ⟨z, -, hcard, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
    ⟨m, t, hm1, hmf, htm, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith, -⟩ |
    ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  · exfalso
    have : IsMulCommutative H := hel.toIsMulCommutative
    exact hH inferInstance
  · exfalso
    have : IsMulCommutative H := IsCyclic.isMulCommutative
    exact hH inferInstance
  · exfalso
    have : NeZero z := ⟨by omega⟩
    have : Group.IsSolvable (DihedralGroup z) := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact hH (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · exfalso
    have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact hH (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · exfalso
    have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hH (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · exact Or.inl ⟨⟨e⟩, h5⟩
  · exfalso
    have := hEel.toIsMulCommutative
    exact hH (isSolvable_of_normal_comm_sup_cyclic E C hCcyc hsup)
  · exact Or.inr (Or.inl ⟨m, hmf, ⟨e⟩⟩)
  · exact Or.inr (Or.inr ⟨m, hmf, ⟨e⟩⟩)

theorem ivk_1_8_i :
    ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
      ∀ L : Subgroup K, ¬ Group.IsSolvable ↥L →
        (∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = ringChar F ∧
          Nat.card F₀ ≤ Nat.card F ∧ (Nonempty (↥L ≃* L2 F₀) ∨ Nonempty (↥L ≃* PGL2 F₀))) ∨
        IsL2 ↥L (fun q₀ => q₀ = 5) := by
  intro F _ _ hF K _ _ e L hL
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcharF : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hq)
  have hringF : ringChar F = p := ringChar.eq F p
  let φ : K ≃* PSL2 F := toPSL e
  let L' : Subgroup (PSL2 F) := L.map φ.toMonoidHom
  let eL : L ≃* L' := Subgroup.equivMapOfInjective L φ.toMonoidHom φ.injective
  have hL' : ¬ Group.IsSolvable L' := fun h =>
    hL (Group.isSolvable_of_isSolvable_injective (f := eL.toMonoidHom) eL.injective)
  have hmn : ∀ m : ℕ, m ∣ n → p ^ m ≤ Nat.card F := fun m hm => by
    rw [hq]
    exact Nat.pow_le_pow_right hp.pos (Nat.le_of_dvd (by omega) hm)
  rcases nonsolvable_cases hq L' hL' with ⟨⟨e5⟩, -⟩ | ⟨m, hm, ⟨e1⟩⟩ | ⟨m, hm, ⟨e1⟩⟩
  · right
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e5'⟩ := CFSG.Glauberman.Dickson.MaxCases.nonempty_psl2_galoisField_five
    exact ⟨GaloisField 5 1, inferInstance, inferInstance, by
      rw [GaloisField.card 5 1 one_ne_zero, pow_one],
      ⟨eL.trans (e5.trans (e5'.symm.trans (L2.equivPSL (GaloisField 5 1)).symm))⟩⟩
  · left
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      omega
    refine ⟨GaloisField p m, inferInstance, inferInstance, by rw [ringChar.eq (GaloisField p m) p, hringF],
      by rw [GaloisField.card p m hm0]; exact hmn m hm, Or.inl ⟨?_⟩⟩
    exact eL.trans (e1.trans (L2.equivPSL (GaloisField p m)).symm)
  · left
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hm
      omega
    refine ⟨GaloisField p m, inferInstance, inferInstance, by rw [ringChar.eq (GaloisField p m) p, hringF],
      by rw [GaloisField.card p m hm0]; exact hmn m (Dvd.dvd.trans (dvd_mul_left m 2) hm), Or.inr ⟨?_⟩⟩
    exact eL.trans e1

theorem ivk_1_8_ii :
    ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
      ∀ n : ℕ, Nat.card F = 3 ^ n → Odd n → ∀ L : Subgroup K, ¬ Group.IsSolvable ↥L →
        ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = 3 ∧
          Nonempty (↥(⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆) ≃* L2 F₀) := by
  intro F _ _ hF K _ _ e n hn hnodd L hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : K ≃* PSL2 F := toPSL e
  let L' : Subgroup (PSL2 F) := L.map φ.toMonoidHom
  let eL : L ≃* L' := Subgroup.equivMapOfInjective L φ.toMonoidHom φ.injective
  have hL' : ¬ Group.IsSolvable L' := fun h =>
    hL (Group.isSolvable_of_isSolvable_injective (f := eL.toMonoidHom) eL.injective)
  have hn0 : n ≠ 0 := by
    obtain ⟨k, hk⟩ := hnodd
    omega
  rcases nonsolvable_cases hn L' hL' with ⟨⟨e5⟩, h5⟩ | ⟨m, hm, ⟨e1⟩⟩ | ⟨m, hm, ⟨e1⟩⟩
  · exfalso
    rcases h5 with h | h
    · omega
    · obtain ⟨k, hk⟩ := hnodd
      have h4 : (3 ^ n) ^ 2 % 5 = 4 := by
        have h81 : (3 ^ (2 * k + 1)) ^ 2 = 81 ^ k * 9 := by
          rw [← pow_mul, show (2 * k + 1) * 2 = 4 * k + 2 by ring, pow_add, pow_mul]
          norm_num
        rw [hk, h81, Nat.mul_mod, Nat.pow_mod]
        norm_num
      have h1 : (3 ^ n) ^ 2 % 5 = 1 % 5 := h
      omega
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      exact hn0 hm
    have hcardF : Nat.card (GaloisField 3 m) = 3 ^ m := GaloisField.card 3 m hm0
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hL'
      have h12 : Nat.card (PSL2MatrixGroup (GaloisField 3 1)) = 12 := by
        rw [CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (by norm_num) one_ne_zero]
        norm_num
      have : Fintype L' := Fintype.ofFinite _
      refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := 2) (q := 3) (a := 2) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
      rw [← Nat.card_eq_fintype_card, Nat.card_congr e1.toEquiv, h12]
      norm_num
    have hsimple : IsSimpleGroup (PSL2MatrixGroup (GaloisField 3 m)) :=
      BenderSuzuki.External.huppert_II_6_13 2 le_rfl
        (Or.inr (by
          rw [hcardF]
          intro h
          have h3 : 3 ∣ 3 ^ m := dvd_pow_self 3 hm0
          rw [h] at h3
          omega))
        (Or.inr (by
          rw [hcardF]
          intro h
          exact hm1 (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h))))
    let ψ : L ≃* PSL2MatrixGroup (GaloisField 3 m) := eL.trans e1
    have hcomm : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆) = ⊤ := by
      have hnorm : (commutator (PSL2MatrixGroup (GaloisField 3 m))).Normal := inferInstance
      have hG0 : (⁅(⊤ : Subgroup (PSL2MatrixGroup (GaloisField 3 m))),
          (⊤ : Subgroup (PSL2MatrixGroup (GaloisField 3 m)))⁆) =
          (⊤ : Subgroup (PSL2MatrixGroup (GaloisField 3 m))) := by
        rcases hsimple.eq_bot_or_eq_top_of_normal (commutator (PSL2MatrixGroup (GaloisField 3 m)))
          with hbot | htop
        · exfalso
          apply hL'
          have hsolv : Group.IsSolvable (PSL2MatrixGroup (GaloisField 3 m)) :=
            ⟨⟨1, by rw [derivedSeries_one]; exact hbot⟩⟩
          exact Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective
        · exact htop
      apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective, hG0]
    have hchar : ringChar (GaloisField 3 m) = 3 := ringChar.eq (GaloisField 3 m) 3
    exact ⟨GaloisField 3 m, inferInstance, inferInstance, hchar,
      ⟨(MulEquiv.subgroupCongr hcomm).trans (Subgroup.topEquiv.trans
        (ψ.trans (L2.equivPSL (GaloisField 3 m)).symm))⟩⟩
  · exfalso
    obtain ⟨c, hc⟩ := hm
    obtain ⟨k, hk⟩ := hnodd
    have h2 : n = 2 * (m * c) := by rw [hc]; ring
    omega

end Lemma18

end CFSG.GH74.GLS.IVK.Proofs2
