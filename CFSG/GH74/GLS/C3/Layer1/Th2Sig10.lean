module

public import CFSG.GH74.GLS.C3.Layer1.Th2Sig6
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig8

public section

namespace CFSG.GH74.GLS.Th2Sig10

open Subgroup

variable {G : Type} [Group G]

theorem le_normalizer_AG {A D : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) (hDA : D ≤ A) :
    A ≤ normalizer (AG D : Set G) := fun _ hq =>
  Th2Sig8.mem_normalizer_AG (fun _ ha _ hb => Th2Sig8.mul_comm_of_isElementaryAbelian hA ha hb) hDA hq

theorem coprime_card_AG_of_isE [Finite G] {j : ℕ} (hj : 1 ≤ j) {X D : Subgroup G} (hD : IsE j X D) :
    Nat.Coprime 2 (Nat.card ↥(AG D)) := by
  obtain ⟨d, hdD, hd1⟩ := Th2Sig8.exists_ne_one hD.2.1 (hj.trans hD.2.2)
  exact Th2Sig8.coprime_card_AG hdD hd1

theorem commutator_inf_centralizer_le {k : ℕ} {A D X : Subgroup G} (hweak : IsWeakKBal k A)
    (hD : IsE k A D) (hXA : X ≤ A) : ⁅AG D ⊓ centralizer (X : Set G), A⁆ ≤ AG X := by
  refine Th2Sig8.le_AG fun x hx hx1 => Subgroup.commutator_le.mpr fun c hc b hb => ?_
  exact hweak D hD x (hXA hx) hx1 c
    ⟨hc.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx) hc.2⟩ b hb

theorem commutator_AG_le_thetaHalf_self {k : ℕ} {X D : Subgroup G} (hD : IsE k X D) :
    ⁅AG D, X⁆ ≤ thetaHalf k X := by
  unfold thetaHalf
  refine le_trans ?_ le_sup_left
  exact le_iSup₂_of_le D hD le_rfl

theorem AG_le_thetaHalf_self {k : ℕ} {X : Subgroup G} : AG X ≤ thetaHalf k X := by
  unfold thetaHalf
  exact le_sup_right

theorem thetaHalf_le_of_le [Finite G] {k : ℕ} {A B : Subgroup G} (hAe : CFSG.IsElementaryAbelian 2 ↥A)
    (hbal : IsKBal (k + 1) A) (hB : IsE (k + 1) A B) : thetaHalf k B ≤ thetaHalf k A := by
  have := hAe
  refine sup_le (iSup₂_le fun D hD => ?_) ?_
  · have hDA : IsE k A D := ⟨hD.1.trans hB.1, hD.2.1, hD.2.2⟩
    exact (Subgroup.commutator_mono le_rfl hB.1).trans (commutator_AG_le_thetaHalf_self hDA)
  · have hcop := coprime_card_AG_of_isE (Nat.succ_pos k) hB
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
      Nat.prime_two A (AG B) (CFSG.IsElementaryAbelian.isPGroup 2 ↥A) (le_normalizer_AG hAe hB.1) hcop
    refine hfac.symm.le.trans (sup_le ?_ ?_)
    · have hBk : IsE k A B := ⟨hB.1, hB.2.1, (Nat.le_succ k).trans hB.2.2⟩
      exact commutator_AG_le_thetaHalf_self hBk
    · exact (Th2Sig6.AG_inf_centralizer_le hbal hB le_rfl).trans AG_le_thetaHalf_self

theorem AG_le_thetaHalf_of_card [Finite G] {k : ℕ} {A B F : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hbal : IsKBal (k + 1) A) (hB : IsE (k + 1) A B)
    (hFA : F ≤ A) (hF : Nat.card ↥F = 2 ^ (k + 1)) : AG F ≤ thetaHalf k B := by
  have := hB.2.1
  have hFE : IsE (k + 1) A F := Th2Sig8.isE_of_card hAe hFA hFA hF
  have hcopY : Nat.Coprime 2 (Nat.card ↥(AG F)) := coprime_card_AG_of_isE (Nat.succ_pos k) hFE
  have hnormY : B ≤ normalizer (AG F : Set G) := fun _ hq => le_normalizer_AG hAe hFA (hB.1 hq)
  have hBe' : CFSG.Open.IsElemAbelian 2 B :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).mp hB.2.1
  have hlarge : 2 ^ (k + 1) ≤ Nat.card ↥B := Th2Sig8.two_pow_le_card hB.2.1 hB.2.2
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 k
    Nat.prime_two B (AG F) hBe' hlarge hnormY hcopY
  refine hgen.symm.le.trans (iSup₂_le fun S hS => ?_)
  obtain ⟨hSB, hScard⟩ := hS
  have hSE : IsE k B S := Th2Sig8.isE_of_card hB.2.1 hSB hSB hScard
  have hZS : AG F ⊓ centralizer (S : Set G) ≤ AG S :=
    Th2Sig6.AG_inf_centralizer_le hbal hFE (hSB.trans hB.1)
  have hZB : AG F ⊓ centralizer (B : Set G) ≤ AG B :=
    Th2Sig6.AG_inf_centralizer_le hbal hFE hB.1
  have hnormZ : B ≤ normalizer ((AG F ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro q hq
    have hqC : q ∈ centralizer (S : Set G) := mem_centralizer_iff.mpr fun s hs =>
      Th2Sig8.mul_comm_of_isElementaryAbelian hB.2.1 (hSB hs) hq
    have h1 := mem_normalizer_iff.mp (hnormY hq)
    have h2 := mem_normalizer_iff.mp (Subgroup.le_normalizer hqC)
    rw [mem_normalizer_iff]
    intro x
    exact and_congr (h1 x) (h2 x)
  have hcopZ : Nat.Coprime 2 (Nat.card ↥(AG F ⊓ centralizer (S : Set G))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopY
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two B (AG F ⊓ centralizer (S : Set G)) (CFSG.IsElementaryAbelian.isPGroup 2 ↥B)
    hnormZ hcopZ
  refine hfac.symm.le.trans (sup_le ?_ ?_)
  · exact (Subgroup.commutator_mono hZS le_rfl).trans (commutator_AG_le_thetaHalf_self hSE)
  · exact ((inf_le_inf_right _ inf_le_left).trans hZB).trans AG_le_thetaHalf_self

theorem commutator_AG_le_thetaHalf [Finite G] {k : ℕ} (hk : 1 ≤ k) {A B D : Subgroup G}
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hAr : k + 2 ≤ CFSG.pRank 2 ↥A)
    (hbal : IsKBal (k + 1) A) (hweak : IsWeakKBal k A) (hB : IsE (k + 1) A B) (hD : IsE k A D) :
    ⁅AG D, A⁆ ≤ thetaHalf k B := by
  have := hAe
  have hcop := coprime_card_AG_of_isE hk hD
  have hsolv : Group.IsSolvable ↥(AG D) :=
    CFSG.Milestones.odd_order_solvable (Nat.coprime_two_left.mp hcop)
  have hnorm := le_normalizer_AG hAe hD.1
  have hAe' : CFSG.Open.IsElemAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).mp hAe
  have hlarge : 2 ^ (k + 1 + 1) ≤ Nat.card ↥A := Th2Sig8.two_pow_le_card hAe hAr
  have hcentA : A ≤ centralizer (A : Set G) := fun a ha => mem_centralizer_iff.mpr fun h hh =>
    Th2Sig8.mul_comm_of_isElementaryAbelian hAe hh ha
  have hgen := CFSG.SignalizerFunctor.Helpers.solvable_normalized_order_fixed_commutator_generation
    2 (k + 1) 2 Nat.prime_two Nat.prime_two A A (AG D) hAe' hlarge
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥A) hsolv hnorm hnorm hcentA hcop hcop
  refine hgen.le.trans (iSup₂_le fun F hF => ?_)
  exact (commutator_inf_centralizer_le hweak hD hF.1).trans
    (AG_le_thetaHalf_of_card hAe hbal hB hF.1 hF.2)

end CFSG.GH74.GLS.Th2Sig10

namespace CFSG.GH74.GLS

theorem b_ig_21_10 : B_IG_21_10 := by
  intro G _ _ k hk A B hA hbal hweak hB
  refine le_antisymm (Th2Sig10.thetaHalf_le_of_le hA.2.1 hbal hB) ?_
  unfold thetaHalf
  refine sup_le (iSup₂_le fun D hD => ?_) ?_
  · exact Th2Sig10.commutator_AG_le_thetaHalf hk hA.2.1 hA.2.2 hbal hweak hB hD
  · exact (Th2Sig6.AG_anti hB.1).trans Th2Sig10.AG_le_thetaHalf_self

end CFSG.GH74.GLS
