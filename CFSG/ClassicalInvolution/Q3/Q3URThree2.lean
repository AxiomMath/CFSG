module

public import CFSG.ClassicalInvolution.Q3.Q3URThree1
public import CFSG.ClassicalInvolution.Q3.Q3URChart3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (conjSign)
open scoped MatrixGroups


section Middle

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.exists_middle_three {ι : Type} (c : UCtx3 3 Ω K z) (nd : UNodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hlast : Commutes β (nd.j 2)) :
    ∃ N : Subgroup G, N ∈ centralizingMembers Ω {z} ∧ N ≠ K ∧ Commutes β N ∧
      ¬ Commutes (nd.j 0) N ∧ ¬ Commutes N (nd.j 2) ∧
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (nd.j 0) N) ∧
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W N (nd.j 2)) := by
  classical
  have h2 := two_ne_zero_gf9
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  have htz : t * z * t⁻¹ = z := fix_of_stdpair3U c.hz hwβ hpair
  have htt : t * t = 1 := mul_self_of_isClassicalMember3 hwβ
  have attach := fun (N : Subgroup G) (hN : N ∈ Ω) (hNK : Commutes N K) =>
    c.commutes_partner_iff hMFZ D hsingle hβ hwβ hnK hN hNK
  have hσ2 : ∀ y, locAut hconj htz (locAut hconj htz y) = y := locAut_locAut hconj htz htt
  have hstab := c.locAut_stab nd htz
  have hfix : ∀ A : Su (GaloisField 3 2) 3 1 2,
      locAut hconj htz (c.d.ψ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A)) =
        c.d.ψ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A) := by
    intro A
    have hle : nd.j 2 ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hlast t hwβ.mem n hn).symm
    exact (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem 2 (by omega))).mp hle _
      (by rw [nd.locImg_eq (by omega)]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hmove : ∃ A : Su (GaloisField 3 2) 3 1 2,
      locAut hconj htz (c.d.ψ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A)) ≠
        c.d.ψ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), locAut hconj htz a = a := by
      intro a ha
      rw [nd.locImg_eq (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem 0 (by omega))).mpr hfx
    exact hfirst (Gaps.commutes_symm
      ((attach (nd.j 0) (nd.mem 0 (by omega)).1
        (Gaps.commutes_symm (nd.commK 0 (by omega)))).mpr hle))
  obtain ⟨P, hP⟩ := unitary_partner_chart_three3 card_gf9 (by norm_num) le_rfl
    su2_pow_three_mem_commutator (fun x hx => center_orderOf_not_dvd_three_su3 (by omega) hx)
    c.d.ψ c.d.ker_le (locAut hconj htz) hσ2 hstab hfix hmove
  set H : Su (GaloisField 3 2) 3 1 (3 + 1) :=
    blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ P with hH
  have hHmem : H ∈ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩).range := ⟨P, rfl⟩
  have hcinj : Function.Injective (MulAut.conj H).toMonoidHom := (MulAut.conj H).injective
  have hα0 : (LcU (GaloisField 3 2) 3 1 (nodePair 3 0 (by omega))).map
      (MulAut.conj H).toMonoidHom = LcU (GaloisField 3 2) 3 1 (nodePair 3 0 (by omega)) := by
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by omega : 0 < 3)]
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hHmem hx) (Subgroup.inv_mem _ hHmem)
    · intro hy
      exact ⟨H⁻¹ * y * H, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hHmem) hy)
        hHmem, by group⟩
  have hh2 : ∀ A : Su (GaloisField 3 2) 3 1 2,
      H * blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A * H⁻¹ =
        blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A := fun A =>
    mul_inv_eq_iff_eq_mul.mpr (blockEmb2_comm 3 ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp) P A)
  have hα2 : (LcU (GaloisField 3 2) 3 1 (nodePair 3 2 (by omega))).map
      (MulAut.conj H).toMonoidHom = LcU (GaloisField 3 2) 3 1 (nodePair 3 2 (by omega)) := by
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by omega : 2 < 3)]
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, ⟨A, rfl⟩, rfl⟩
      exact ⟨A, (hh2 A).symm⟩
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨A, rfl⟩, hh2 A⟩
  have hroot : ∀ T : Pair (3 + 1),
      IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn
        ((LcU (GaloisField 3 2) 3 1 T).map (MulAut.conj H).toMonoidHom)
        (H * zEltU (GaloisField 3 2) 3 1 T * H⁻¹) := fun T =>
    (isLongRootSU2_LcU h2 c.hn T).conj H
  obtain ⟨N, hN, hNK, hNR⟩ := exists_member_of_rootU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
    (R := (LcU (GaloisField 3 2) 3 1 (nodePair 3 1 (by omega))).map (MulAut.conj H).toMonoidHom)
    ⟨_, hroot _⟩
  have hfixN : ∀ a ∈ locImg Ω z N, locAut hconj htz a = a := by
    intro a ha
    rw [hNR] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    have hx' : x ∈ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨1, by omega⟩).range := by
      rw [range_blockEmb2_eq_LcU_nodePair h2 (by omega : 1 < 3)]
      exact hx
    obtain ⟨A, rfl⟩ := hx'
    have := hP (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨1, by omega⟩ A)
    rw [conjSign_blockEmb2_of_eq card_gf9 (partnerSigns 3 0) ⟨1, by omega⟩
      (by simp [partnerSigns]) A] at this
    exact this
  have hNK' : Commutes N K :=
    (commutes_K_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hN hNK).symm
  have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz hN).mpr hfixN
  have hcβ : Commutes β N := Gaps.commutes_symm ((attach N hN.1 hNK').mpr hle)
  have hcomm : ∀ T T' : Pair (3 + 1), Commute (H * zEltU (GaloisField 3 2) 3 1 T * H⁻¹)
      (H * zEltU (GaloisField 3 2) 3 1 T' * H⁻¹) := fun T T' =>
    commute_conj (signGroupU_comm (zEltU_mem_signGroupU T) (zEltU_mem_signGroupU T')) H
  have hne : ∀ a b : ℕ, (ha : a < 3) → (hb : b < 3) → a ≠ b →
      H * zEltU (GaloisField 3 2) 3 1 (nodePair 3 a ha) * H⁻¹ ≠
        H * zEltU (GaloisField 3 2) 3 1 (nodePair 3 b hb) * H⁻¹ := by
    intro a b ha hb hab hh
    exact hab ((nodePair_eq_iff ha hb).mp
      (typeU_zEltU_injective h2 (mul_left_cancel (mul_right_cancel hh))))
  have hnc : ∀ a : ℕ, (ha : a + 2 < 3 + 1) →
      ¬ Commutes ((LcU (GaloisField 3 2) 3 1 (nodePair 3 a (by omega))).map
          (MulAut.conj H).toMonoidHom)
        ((LcU (GaloisField 3 2) 3 1 (nodePair 3 (a + 1) (by omega))).map
          (MulAut.conj H).toMonoidHom) := by
    intro a ha hc'
    exact not_commutes_LcU_overlap card_gf9 (by norm_num) c.hn3 (i := ⟨a, by omega⟩)
      (j := ⟨a + 1, by omega⟩) (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) ((commutes_map_iff _ hcinj).mp hc')
  have himg0 : locImg Ω z (nd.j 0) = ((LcU (GaloisField 3 2) 3 1 (nodePair 3 0 (by omega))).map
      (MulAut.conj H).toMonoidHom).map c.d.ψ := by rw [hα0, nd.img 0 (by omega)]
  have himg2 : locImg Ω z (nd.j 2) = ((LcU (GaloisField 3 2) 3 1 (nodePair 3 2 (by omega))).map
      (MulAut.conj H).toMonoidHom).map c.d.ψ := by rw [hα2, nd.img 2 (by omega)]
  refine ⟨N, hN, hNK, hcβ, ?_, ?_, ?_, ?_⟩
  · intro hc
    exact hnc 0 (by omega)
      ((c.commutes_iff_root (nd.mem 0 (by omega)) hN (hroot (nodePair 3 0 (by omega)))
        himg0 hNR).mp hc)
  · intro hc
    exact hnc 1 (by omega)
      ((c.commutes_iff_root hN (nd.mem 2 (by omega)) (hroot (nodePair 3 1 (by omega)))
        hNR himg2).mp hc)
  · exact c.stdpair_of_root (nd.mem 0 (by omega)) hN (hroot (nodePair 3 0 (by omega)))
      (hroot (nodePair 3 1 (by omega))) himg0 hNR (hcomm _ _)
      (hne 0 1 (by omega) (by omega) (by omega)) (hnc 0 (by omega))
  · exact c.stdpair_of_root hN (nd.mem 2 (by omega)) (hroot (nodePair 3 1 (by omega)))
      (hroot (nodePair 3 2 (by omega))) hNR himg2 (hcomm _ _)
      (hne 1 2 (by omega) (by omega) (by omega)) (hnc 1 (by omega))

end Middle

end CFSG.ClassicalInvolution.Q3.Q3W
