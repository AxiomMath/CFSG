module

public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.GF2Type.Aschbacher1976Full.LeafDihedralBasic
public import CFSG.Milestones.LR_dihedral_simple_recognition
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint
open CFSG.GF2Type.Aschbacher1976Full.LeafDihedral

theorem psl2_conclusion_of_centralizer {G : Type} [Group G] {z : G} (hz : orderOf z = 2) {n : ℕ}
    (hn : 3 ≤ n) (hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ n) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hSC : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f) : PSL2Conclusion G := by
  have hSC' := hSC
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hSC
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  let e2 : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    φ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have ht : orderOf (e2 z) = 2 := (orderOf_injective e2.toMonoidHom e2.injective z).trans hz
  have hcT : Nat.card (Subgroup.centralizer
      ({e2 z} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) = 2 ^ n := by
    rw [card_centralizer_transport e2 z, hcard]
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K hKcard hodd (by omega) ht
  have hpodd : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd.pow
  have hLie : LieModel G .PSL 2 p f := Or.inl ⟨by decide, hSC'⟩
  refine ⟨p, f, n, hp, hp2, hf, hn, ?_, hLie⟩
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h4 | h4
  · obtain ⟨hc, -⟩ := h1 h4
    rw [hc] at hcT
    omega
  · obtain ⟨hc, -⟩ := h3 h4
    rw [hc] at hcT
    omega

section Certs

theorem false_of_alternatingSeven {G : Type} [Group G] {z : G} (hz : orderOf z = 2) {n : ℕ}
    (hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ n)
    (φ : G ≃* alternatingGroup (Fin 7)) : False := by
  have hxo : orderOf (φ z) = 2 := (orderOf_injective φ.toMonoidHom φ.injective z).trans hz
  have hx1 : φ z ≠ 1 := fun h => by simp [h] at hxo
  have hx2 : φ z ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  have hxI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (φ z) := ⟨hx1, hx2⟩
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.aSeven_involutions_conjugate (φ z)
    CFSG.GorensteinWalter.a7t hxI CFSG.GorensteinWalter.a7t_involution
  have hc1 : Nat.card (Subgroup.centralizer ({φ z} : Set (alternatingGroup (Fin 7)))) = 24 := by
    have h := card_centralizer_transport (MulAut.conj g) (φ z)
    rw [MulAut.conj_apply, hg] at h
    rw [← h]
    exact CFSG.GorensteinWalter.a7t_centralizer_card
  have hc2 : Nat.card (Subgroup.centralizer ({φ z} : Set (alternatingGroup (Fin 7)))) = 2 ^ n := by
    rw [card_centralizer_transport φ z]
    exact hcard
  have h24 : 2 ^ n = 24 := hc2.symm.trans hc1
  have h3 : 3 ∣ 2 ^ n := ⟨8, by omega⟩
  have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h32

theorem leafDihedral_holds : Asc76LeafDihedral := by
  unfold Asc76LeafDihedral
  intro G _ _ z hset n hn hH he
  obtain ⟨hsimp, hnab, hz, -⟩ := hset
  haveI := hsimp
  obtain ⟨e⟩ := he
  have hn2 : 2 ≤ n := by omega
  have hm : Even (2 ^ (n - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hm2 : 2 ^ (n - 1) ≠ 2 := by
    have h4 : 4 ≤ 2 ^ (n - 1) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  let e' : ↥(Hz z) ≃* DihedralGroup (2 ^ (n - 1)) := (MulEquiv.subgroupCongr hH).trans e
  have hcard : Nat.card (Hz z) = 2 ^ n := by
    rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card, ← pow_succ']
    congr 1
    omega
  obtain ⟨S, hS⟩ := exists_sylow_two_centralizer hz hm hm2 hcard e'
  have hSe : Nonempty ((S : Subgroup G) ≃* DihedralGroup (2 ^ (n - 1))) :=
    ⟨(MulEquiv.subgroupCongr hS).trans e'⟩
  rcases CFSG.Milestones.lr_dihedral_simple_recognition G hnab S n hn2 hSe with hPSL | hA7
  · obtain ⟨p, f, hp, hp2, hf, hSC⟩ := hPSL
    exact psl2_conclusion_of_centralizer hz hn hcard hp hp2 hf hSC
  · obtain ⟨φ⟩ := hA7
    exact (false_of_alternatingSeven hz hcard φ).elim

end Certs

end CFSG.GF2Type.Aschbacher1976Full
