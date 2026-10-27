module

public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.PrimePowerArith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.GroupLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.CharTwoCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.PSL2InvolutionCentralizer

public section

namespace CFSG.QuasithinUnique

open scoped MatrixGroups
open CFSG.QuasithinUnique.I43Dihedral

theorem i43_dihedral
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (heven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) (P : Sylow 2 G) {k : ℕ}
    (hk : 3 ≤ k) (hP : Nonempty ((P : Subgroup G) ≃* DihedralGroup (2 ^ k))) :
    ∃ p : ℕ, p.Prime ∧ 7 < p ∧
      ((∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∨ (∃ j : ℕ, 2 ≤ j ∧ p = 2 ^ j - 1)) ∧
      Nonempty (G ≃* PSL(2, ZMod p)) := by
  classical
  obtain ⟨eP⟩ := hP
  have hcardP : Nat.card (P : Subgroup G) = 2 ^ (k + 1) := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card, pow_succ]; ring
  rcases CFSG.GorensteinWalter.gorenstein_walter G hnonab P ⟨2 ^ k, ⟨eP⟩⟩ with
    ⟨⟨e7⟩⟩ | ⟨p, f, hpf, hodd, h5, ⟨e⟩⟩
  · exfalso
    have hdvd : 2 ^ (k + 1) ∣ Nat.card G :=
      hcardP ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G)
    rw [Nat.card_congr e7.toEquiv] at hdvd
    have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    rw [h2520] at hdvd
    have h16 : 2 ^ 4 ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    omega
  · have hf0 : 0 < f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at h5
      · exact hf
    have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0.ne'
    have hF : ringChar (GaloisField p f) ≠ 2 := by
      rw [ringChar.eq (GaloisField p f) p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have hq : 5 ≤ Nat.card (GaloisField p f) := by rw [hcardF]; exact h5
    have hnt : Nontrivial (P : Subgroup G) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardP]
      exact Nat.one_lt_two_pow (by omega)
    obtain ⟨z, hzP, hz2, hzc⟩ := exists_central_involution_of_sylow_two P hnt
    have hzC : (P : Subgroup G) ≤ Subgroup.centralizer {z} := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hx)
    have hCharC := charTwo_centralizer_of_central_involution heven hz2 hzC
    have hg : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz2
    obtain ⟨A, hAC, hAcomm, hCA, hmod⟩ := psl2_involution_centralizer hF hq hg
    obtain ⟨A', hA'C, hA'comm, hA'card, hCA'⟩ :=
      exists_comm_subgroup_of_mulEquiv e z hAC hAcomm hCA
    have hidx : (A'.subgroupOf (Subgroup.centralizer {z})).index = 2 := by
      have h1 := Subgroup.card_mul_index (A'.subgroupOf (Subgroup.centralizer {z}))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'C).toEquiv, hCA'] at h1
      have hpos : 0 < Nat.card A' := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
    have hnormal : (A'.subgroupOf (Subgroup.centralizer {z})).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    have hA'2 : IsPGroup 2 A' := isPGroup_of_charTwo_of_normal_comm hCharC hA'C hnormal hA'comm
    obtain ⟨a, ha⟩ := hA'2.exists_card_eq
    have hC2 : IsPGroup 2 (Subgroup.centralizer {z} : Subgroup G) :=
      IsPGroup.of_card (n := a + 1) (by rw [hCA', ha]; ring)
    have hcardC := card_eq_of_sylow_le_of_isPGroup P hzC hC2
    have hak : a = k := by
      have h2 : 2 ^ (a + 1) = 2 ^ (k + 1) := by
        rw [← hcardP, ← hcardC, hCA', ha]; ring
      exact Nat.succ_injective (Nat.pow_right_injective le_rfl h2)
    subst hak
    have hAcard : Nat.card A = 2 ^ a := by rw [← hA'card, ha]
    have hmain : p ^ f = 2 ^ (a + 1) + 1 ∨ p ^ f + 1 = 2 ^ (a + 1) := by
      rw [← hcardF]
      rcases hmod with ⟨-, hm⟩ | ⟨-, hm⟩
      · left; rw [hAcard] at hm; rw [pow_succ]; linarith
      · right; rw [hAcard] at hm; rw [pow_succ]; linarith
    obtain ⟨hf1, hp7, hfm⟩ := fermat_or_mersenne_of_primePow hpf.out hf0 hk hmain
    subst hf1
    refine ⟨p, hpf.out, hp7, hfm, ⟨?_⟩⟩
    exact e.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod p) p 1 Nat.one_pos
        (by rw [Nat.card_zmod, pow_one])) (Fin 2)).symm

end CFSG.QuasithinUnique
