module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2CharacteristicSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectSubnormal
public import CFSG.Dihedral.GorensteinWalter.Helpers
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG

open scoped MatrixGroups

namespace GorensteinWalter.ExternalSimpleAdapter

open GorensteinWalter

theorem conclusion_of_isDGroup
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n))
    (hD : IsDGroup G) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (G ≃* PSL(2, GaloisField p k)) := by
  classical
  obtain ⟨n, ⟨eP⟩⟩ := hdih
  have hPcard : Nat.card P = 2 * n :=
    (Nat.card_congr eP.toEquiv).trans DihedralGroup.nat_card
  have hEven : 2 ∣ Nat.card G := by
    have hTwo : 2 ∣ Nat.card P := by rw [hPcard]; exact dvd_mul_right 2 n
    exact hTwo.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup G))
  have hCore : pPrimeCore 2 G = ⊥ := pPrimeCore_eq_bot_of_simple_of_even hEven
  let eQ : (G ⧸ pPrimeCore 2 G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq (G := G) hCore).trans
      (QuotientGroup.quotientBot (G := G))
  let : IsSimpleGroup (G ⧸ pPrimeCore 2 G) := eQ.isSimpleGroup
  let : Group.IsPerfect G :=
    Group.isPerfect_def.mpr (Helpers.commutator_eq_top_of_noncommutative hnonab)
  rcases hD with ⟨_, hTwo⟩ | ⟨_, hSeven⟩ | ⟨_, K, hK, L, hLnormal, hLindex, hLmodel⟩
  · have hGTwo : IsPGroup 2 G := hTwo.of_equiv eQ
    let : Nontrivial (Subgroup.center G) := hGTwo.center_nontrivial
    have hCenter := Helpers.center_eq_bot_of_noncommutative hnonab
    have hCard := Finite.one_lt_card (α := Subgroup.center G)
    simp [hCenter] at hCard
  · exact Or.inl ⟨eQ.symm.trans hSeven.some⟩
  · have hLtop : L = ⊤ := by
      rcases hLnormal.eq_bot_or_eq_top with hbot | htop
      · have hOddG : Odd (Nat.card G) := by
          rw [hbot, Subgroup.index_bot] at hLindex
          simpa only [Nat.card_congr eQ.toEquiv] using hLindex
        exact (hOddG.not_two_dvd_nat hEven).elim
      · exact htop
    let eGL : G ≃* L := eQ.symm.trans
      ((Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) ≃*
        (G ⧸ pPrimeCore 2 G)).symm.trans (MulEquiv.subgroupCongr hLtop.symm))
    have hOdd : Odd (Nat.card K) := by
      obtain ⟨p, k, _, hp, _, hcard⟩ := hK
      rw [hcard]
      exact hp.pow
    rcases hLmodel with hPSL | hPGL
    · let eG : G ≃* PSL2 K := eGL.trans hPSL.some
      let : Group.IsPerfect (PSL2 K) :=
        Group.IsPerfect.ofSurjective (f := eG.toMonoidHom) eG.surjective
      let : Nontrivial (PSL2 K) := eG.symm.toEquiv.nontrivial
      have hGt : 3 < Nat.card K :=
        (psl2_perfect_subnormal_eq_top K hK ⊤ top_ne_bot inferInstance
          Subgroup.IsSubnormal.top).1
      have hFive : 5 ≤ Nat.card K := by obtain ⟨k, hk⟩ := hOdd; omega
      let : Fintype K := Fintype.ofFinite K
      exact Or.inr (FieldTransport.conclusion_of_psl_over_finite_field eG
        (by simpa only [Fintype.card_eq_nat_card] using hOdd)
        (by simpa only [Fintype.card_eq_nat_card] using hFive))
    · let eG : G ≃* PGL2 K := eGL.trans hPGL.some
      let : Group.IsPerfect (PGL2 K) :=
        Group.IsPerfect.ofSurjective (f := eG.toMonoidHom) eG.surjective
      exact ((pgl2_commutator_ne_bot_ne_top K hK).2
        (Group.isPerfect_def.mp inferInstance)).elim

theorem hasDihedralSylowTwo
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    HasDihedralSylowTwo G := by
  obtain ⟨n, hdih⟩ := hdih
  obtain ⟨m, hm, hn⟩ := Helpers.dihedralIndex_eq_two_pow_pos hnonab P hdih
  subst n
  intro Q
  exact ⟨m, hm, ⟨(P.equiv Q).symm.trans hdih.some⟩⟩

end GorensteinWalter.ExternalSimpleAdapter

#print axioms GorensteinWalter.ExternalSimpleAdapter.conclusion_of_isDGroup
#print axioms GorensteinWalter.ExternalSimpleAdapter.hasDihedralSylowTwo

end CFSG
