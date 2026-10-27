module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import CFSG.CharacterTheory.PSL2Table.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem psl2_exists_torus_containing_order_three {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hFcard : Nat.card F = p ^ f)
    (z : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) (hz : orderOf z = 3) :
    ∃ T : Subgroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F),
      IsCyclic T ∧ z ∈ T ∧ (Nat.card F - 1) / 2 ≤ Nat.card T := by
  classical
  haveI : Finite (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
    Finite.of_surjective (CFSG.PSL2Table.mk : Matrix.SpecialLinearGroup (Fin 2) F →* _)
      CFSG.PSL2Table.mk_surjective
  obtain ⟨P⟩ : Nonempty (Sylow p (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) :=
    inferInstance
  obtain ⟨U, S, hUc, hUcard, hSc, hScard, hcover⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_5_a_psl2_cover hFcard P
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨T, ⟨hzT, hT⟩, -⟩ := hcover z hz1
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hodd' : Odd (Nat.card F) := by
      rw [hFcard]
      exact hodd.pow
    have h2d : 2 ∣ Nat.card F - 1 := by
      have := Nat.odd_iff.mp hodd'
      omega
    exact Nat.gcd_eq_right h2d
  rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  ·
    exfalso
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzT
    have hyord : orderOf y = 3 := by
      rw [← hz, ← hyz, orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
    have hyk : y ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h3 : 3 ∣ p ^ k := by
      rw [← hyord]
      exact orderOf_dvd_of_pow_eq_one hyk
    have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp h3p).symm
  · have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    refine ⟨U.map (MulAut.conj g).toMonoidHom, ?_, hzT, ?_⟩
    · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U _ hf)).mp hUc
    · rw [Subgroup.card_map_of_injective hf, hUcard, hgcd]
  · have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    refine ⟨S.map (MulAut.conj g).toMonoidHom, ?_, hzT, ?_⟩
    · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective S _ hf)).mp hSc
    · rw [Subgroup.card_map_of_injective hf, hScard, hgcd]
      omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
