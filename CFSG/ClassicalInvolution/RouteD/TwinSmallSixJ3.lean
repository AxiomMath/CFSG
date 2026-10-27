module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixNorm
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixMod
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixStd
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLeaf
public import CFSG.ClassicalInvolution.RouteD.GapsMoved
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem pair_in_layer {J : Subgroup G} {wJ : G} (cJ : TCtx p f .POmegaMinus 6 Ω J wJ)
    {A B : Subgroup G} (hAx : A ∈ centralizingMembers Ω {wJ})
    (hBx : B ∈ centralizingMembers Ω {wJ}) {wA wB : G} (hwA : IsClassicalMember p f A wA)
    (hwB : IsClassicalMember p f B wB)
    (hW : ∃ W, LinearBlockStandardPair (GaloisField p f) W A B) :
    ∃ RA RB : Subgroup (SpinM p f 6),
      RA ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) ∧
      RB ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) ∧
      locImg Ω wJ A = RA.map cJ.d.ψ ∧ locImg Ω wJ B = RB.map cJ.d.ψ ∧
      ModelAdj (Subgroup.center (SpinM p f 6)) RA RB ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W RA RB := by
  obtain ⟨W, hW⟩ := hW
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f cJ.hp2
  have hnAB : ¬ Commutes A B := not_commutes_of_linearBlockStandardPair hW
  have hne : A ≠ B := ne_of_linearBlockStandardPair hW
  have hAL := IsLayerMember.of_not_commutes cJ hAx hBx hne hnAB
  have hBL := IsLayerMember.of_not_commutes cJ hBx hAx hne.symm
    (fun h => hnAB (commutes_symm h))
  obtain ⟨RA, hRA, hAR⟩ := hAL.exists_fund
  obtain ⟨RB, hRB, hBR⟩ := hBL.exists_fund
  have hcw : Commute wA wB := standardPair_involutions_commute h2 hW hwA.mem hwB.mem
    hwA.orderOf_eq_two hwB.orderOf_eq_two
  have hnorm : conjSub wB A = A :=
    conjSub_eq_of_standardPair h2 hW hwB.mem hwB.orderOf_eq_two
  have hadj := modelAdj_of_adj cJ hAx hBx hRA hRB hAR hBR hwA hwB hne hnAB hcw hnorm
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cJ.hP1 hAx hBx hW
  rw [hAR, hBR] at hW'
  have hF := orthFacts_minus cJ.hp2 (by norm_num : 5 ≤ 6) cJ.hq
  exact ⟨RA, RB, hRA, hRB, hAR, hBR, hadj, hF.lift cJ.d.ψ cJ.d.ker_le RA hRA RB hRB ⟨W', hW'⟩⟩

theorem false_of_fixed_zero_three {K : Subgroup G} {z : G} (c : TCtx p f .POmegaMinus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 6 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {J : Subgroup G} {wJ : G}
    (hJΩ : J ∈ Ω) (hwJ : IsClassicalMember p f J wJ) (hKJ : Commutes K J)
    (hβJ : Commutes β J) {M : Subgroup G} (hMΩ : M ∈ Ω) {wM : G}
    (hwM : IsClassicalMember p f M wM) (hMK : Commutes M K) (hMβ : Commutes M β)
    (hMJ : Commutes M J) (x : SpinM p f 6) (tM : Bool)
    (hJimg : locImg Ω z J = ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 1 2
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M = ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4
      (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hfix : ∀ y ∈ (rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 0 3 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y) : False := by
  classical
  have hΩ := c.hΩ
  have hp2 := c.hp2
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have hMFZ : FundNoncentral p := CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p
  have cq := ctx_centralQuot c (by norm_num : 4 ≤ 6)
  have hJz : J ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hJΩ c.hz.mem (commutes_symm hKJ)
  have hMz : M ∈ centralizingMembers Ω {z} := mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  have hR03 : (rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 0 3 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) :=
    rootSL2_conj_mem_gen hq4 cq _ _ _ _ _ _ x
  obtain ⟨N, hNz, hNK, -, hNimg⟩ := c.exists_member_of_fund hR03
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNz.1
  have hNJ : Commutes N J :=
    (c.commutes_iff_fund hNz hJz hR03 hNimg hJimg).mpr (commutes_map_of_commutes _
      (commutes_rootSL2_disjoint _ (a := 0) (b := 3) (c := 1) (d := 2) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        true false true false))
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := by
    refine (locAut_fixed_iff hΩ c.hP1 htz hNz).mpr fun a ha => ?_
    rw [hNimg] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact hfix y hy
  have hNβ : Commutes β N :=
    commutes_partner_of_centralizes_gen hMFZ c hsingle hshape hβ ht hKβ hNz hNt
      (commutes_symm hNK')
  obtain ⟨W₀, hW₀⟩ := stdPair_zero_three hp2 x tM
  obtain ⟨W₁, hW₁⟩ := c.stdPair_of_fund hNz hMz hW₀ hNimg hMimg
  obtain ⟨cJ⟩ := exists_ctx_member c hsingle hshape hJΩ hwJ
  have hKx : K ∈ centralizingMembers Ω {wJ} := mem_centralizingMembers_of_commutes c.hK hwJ.mem hKJ
  have hβx : β ∈ centralizingMembers Ω {wJ} := mem_centralizingMembers_of_commutes hβ hwJ.mem hβJ
  have hNx : N ∈ centralizingMembers Ω {wJ} := mem_centralizingMembers_of_commutes hNz.1 hwJ.mem hNJ
  have hMx : M ∈ centralizingMembers Ω {wJ} := mem_centralizingMembers_of_commutes hMΩ hwJ.mem hMJ
  obtain ⟨RK, Rβ, hRK, hRβ, hKR, hβR, hadj₀, hlin₀⟩ := pair_in_layer cJ hKx hβx c.hz ht hKβ
  obtain ⟨RN, RM, hRN, hRM, hNR, hMR, hadj₁, hlin₁⟩ :=
    pair_in_layer cJ hNx hMx hwN hwM ⟨W₁, hW₁⟩
  have cKN : Commutes RK RN := (cJ.commutes_iff_fund hKx hNx hRK hKR hNR).mp (commutes_symm hNK')
  have cKM : Commutes RK RM := (cJ.commutes_iff_fund hKx hMx hRK hKR hMR).mp (commutes_symm hMK)
  have cβN : Commutes Rβ RN := (cJ.commutes_iff_fund hβx hNx hRβ hβR hNR).mp hNβ
  have cβM : Commutes Rβ RM := (cJ.commutes_iff_fund hβx hMx hRβ hβR hMR).mp (commutes_symm hMβ)
  let R : Fin 2 → Fin 2 → Subgroup (SpinM p f 6) := ![![RK, Rβ], ![RN, RM]]
  refine false_of_two_linear_pairs_six hp2 c.hq R ?_ ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hRK
    · exact hRβ
    · exact hRN
    · exact hRM
  · intro i
    fin_cases i
    · exact hadj₀
    · exact hadj₁
  · intro i
    fin_cases i
    · exact hlin₀
    · exact hlin₁
  · intro i i' hii' j j'
    fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;> first
      | exact absurd rfl hii'
      | exact cKN
      | exact cKM
      | exact cβN
      | exact cβM
      | exact commutes_symm cKN
      | exact commutes_symm cKM
      | exact commutes_symm cβN
      | exact commutes_symm cβM

end Layer

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem normalizes_map_conj {R R' : Subgroup G} (x : G)
    (h : ∀ r', InvOf R' r' → ∀ y ∈ R, r' * y * r'⁻¹ ∈ R) :
    ∀ r', InvOf (R'.map (MulAut.conj x).toMonoidHom) r' → ∀ y ∈ R.map (MulAut.conj x).toMonoidHom,
      r' * y * r'⁻¹ ∈ R.map (MulAut.conj x).toMonoidHom := by
  intro r' hr' y hy
  obtain ⟨r₀, hr₀, rfl⟩ := invOf_map_conj hr'
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  refine ⟨r₀ * y₀ * r₀⁻¹, h r₀ hr₀ y₀ hy₀, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_fixed_adjacent_pair {K : Subgroup G} {z : G} (c : TCtx p f .POmegaMinus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 6 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {J : Subgroup G} {wJ : G}
    (hJΩ : J ∈ Ω) (hwJ : IsClassicalMember p f J wJ) (hKJ : Commutes K J)
    (hβJ : Commutes β J) {R₁ : Subgroup (SpinM p f 6)}
    (hJR₁ : locImg Ω z J = R₁.map c.d.ψ) :
    ∃ R R' : Subgroup (SpinM p f 6),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) ∧
      R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) ∧
      ModelAdj (Subgroup.center (SpinM p f 6)) R R' ∧ Commutes R R₁ ∧ Commutes R' R₁ ∧
      (∀ y ∈ R, locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y) ∧
      (∀ y ∈ R', locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y) := by
  classical
  have hΩ := c.hΩ
  have hp2 := c.hp2
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have : Invertible (2 : GaloisField p f) :=
    invertibleOfNonzero (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2)
  have hJz : J ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hJΩ c.hz.mem (commutes_symm hKJ)
  obtain ⟨cJ⟩ := exists_ctx_member c hsingle hshape hJΩ hwJ
  have cq := ctx_centralQuot cJ (by norm_num : 4 ≤ 6)
  have hKx : K ∈ centralizingMembers Ω {wJ} := mem_centralizingMembers_of_commutes c.hK hwJ.mem hKJ
  have hβx : β ∈ centralizingMembers Ω {wJ} := mem_centralizingMembers_of_commutes hβ hwJ.mem hβJ
  obtain ⟨RK, Rβ, hRK, hRβ, hKR, hβR, hadj₀, hlin₀⟩ := pair_in_layer cJ hKx hβx c.hz ht hKβ
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f 6 (by omega)]
    omega
  have hQ : (quadMinus 6 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 6 (GaloisField p f) (minusCoeffs_irr p f))
  obtain ⟨xJ, hx0, hx1⟩ := exists_spin_pair_gen c.hp2 c.hq hQ (by norm_num : 4 ≤ 6 - 1)
    (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) hdim cq hRK hRβ hadj₀ hlin₀
  obtain ⟨Rl, hRl, hcommL, hncL, hneL, hnormL, hinvL⟩ := exists_leaf_subgroup_norm (p := p)
    (f := f) hp2 c.hq (m := 6) (by norm_num) (i := ⟨3, by omega⟩) (j := ⟨4, by omega⟩)
    (by simp [Fin.ext_iff]) true false
  have hD : rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4 (by omega)
      (by omega) (by omega) true false ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) :=
    rootSL2_mem_fund c.hq (by norm_num) hp2 (by omega) (by omega) (by omega) true false
  have hncL' : ¬ Commutes (rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4
      (by omega) (by omega) (by omega) true false) Rl := hncL
  have hneL' : Rl ≠ rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4
      (by omega) (by omega) (by omega) true false := hneL
  have hnormL' : ∀ r', InvOf Rl r' → ∀ y ∈ rootSL2
      (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4 (by omega) (by omega)
      (by omega) true false, r' * y * r'⁻¹ ∈ rootSL2
        (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4 (by omega) (by omega)
        (by omega) true false := hnormL
  have hRN : (rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj xJ).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) :=
    map_conj_mem_fund cq hD xJ
  have hRN' : Rl.map (MulAut.conj xJ).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)) :=
    map_conj_mem_fund cq hRl xJ
  obtain ⟨N, hNx, hNJ, -, hNimg⟩ := cJ.exists_member_of_fund hRN
  obtain ⟨N', hN'x, hN'J, -, hN'img⟩ := cJ.exists_member_of_fund hRN'
  have cKN : Commutes RK ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4
      (by omega) (by omega) (by omega) true false).map (MulAut.conj xJ).toMonoidHom) := by
    rw [hx0]
    exact commutes_map_of_commutes _ (commutes_rootSL2_disjoint _ (a := 0) (b := 1) (c := 3)
      (d := 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) true false true false)
  have cβN : Commutes Rβ ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4
      (by omega) (by omega) (by omega) true false).map (MulAut.conj xJ).toMonoidHom) := by
    rw [hx1]
    exact commutes_map_of_commutes _ (commutes_rootSL2_disjoint _ (a := 1) (b := 2) (c := 3)
      (d := 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) true false true false)
  have cKN' : Commutes RK (Rl.map (MulAut.conj xJ).toMonoidHom) := by
    rw [hx0]
    exact commutes_symm (commutes_map_of_commutes _ (hcommL 0 1 (by omega) (by omega)
      (by omega) (by simp) (by simp) (by simp) (by simp) true false))
  have cβN' : Commutes Rβ (Rl.map (MulAut.conj xJ).toMonoidHom) := by
    rw [hx1]
    exact commutes_symm (commutes_map_of_commutes _ (hcommL 1 2 (by omega) (by omega)
      (by omega) (by simp) (by simp) (by simp) (by simp) true false))
  have hz : ∀ (L : Subgroup G) (R : Subgroup (SpinM p f 6)), L ∈ centralizingMembers Ω {wJ} →
      L ≠ J → Commutes RK R → Commutes Rβ R → locImg Ω wJ L = R.map cJ.d.ψ →
      Commutes L K ∧ Commutes L J ∧ Commutes β L ∧ L ∈ centralizingMembers Ω {z} ∧
        L ≤ Subgroup.centralizer ({t} : Set G) := by
    intro L R hLx hLJ hcK hcβ hLR
    have hKL : Commutes K L := (cJ.commutes_iff_fund hKx hLx hRK hKR hLR).mpr hcK
    have hβL : Commutes β L := (cJ.commutes_iff_fund hβx hLx hRβ hβR hLR).mpr hcβ
    refine ⟨commutes_symm hKL, commutes_symm (cJ.commutes_K_of_ne hLx hLJ), hβL,
      mem_centralizingMembers_of_commutes hLx.1 c.hz.mem (commutes_symm hKL), fun n hn => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hβL t ht.mem n hn).symm
  obtain ⟨hNK, hNJ', hβN, hNz, hNt⟩ := hz N _ hNx hNJ cKN cβN hNimg
  obtain ⟨hN'K, hN'J', hβN', hN'z, hN't⟩ := hz N' _ hN'x hN'J cKN' cβN' hN'img
  have hnc : ¬ Commutes N N' := by
    intro hc
    have := (cJ.commutes_iff_fund hNx hN'x hRN hNimg hN'img).mp hc
    exact hncL' ((commutes_map_conj_iff xJ).mp this)
  have hNN' : N ≠ N' := by
    intro e
    rw [e] at hNimg
    have h1 := hNimg.symm.trans hN'img
    have h2' := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect cJ.d.ψ cJ.d.ker_le
      (cq.perf _ hRN) (cq.perf _ hRN') h1
    exact hneL' (Subgroup.map_injective (MulAut.conj xJ).injective h2').symm
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNx.1
  obtain ⟨wN', hwN'⟩ := hΩ.classical N' hN'x.1
  have hinv : ∀ r r', InvOf ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4
      (by omega) (by omega) (by omega) true false).map (MulAut.conj xJ).toMonoidHom) r →
      InvOf (Rl.map (MulAut.conj xJ).toMonoidHom) r' → r * r' = r' * r :=
    invs_commute_map_conj xJ fun r r' hr hr' => (hinvL r' r hr' hr).symm
  have hcw : Commute wN wN' :=
    commute_w_of_model cJ hNx hN'x hRN hRN' hNimg hN'img hwN hwN' hinv
  have hnormG : conjSub wN' N = N :=
    conjSub_eq_of_normalizes cJ hNx hN'x hRN' hNimg hN'img hwN' (normalizes_map_conj xJ hnormL')
  have hNL : IsLayerMember c N := IsLayerMember.of_not_commutes c hNz hN'z hNN' hnc
  have hN'L : IsLayerMember c N' :=
    IsLayerMember.of_not_commutes c hN'z hNz hNN'.symm (fun h => hnc (commutes_symm h))
  obtain ⟨Rz, hRzf, hNzimg⟩ := hNL.exists_fund
  obtain ⟨Rz', hRzf', hN'zimg⟩ := hN'L.exists_fund
  have hadjz := modelAdj_of_adj c hNz hN'z hRzf hRzf' hNzimg hN'zimg hwN hwN' hNN' hnc hcw hnormG
  refine ⟨Rz, Rz', hRzf, hRzf', hadjz,
    (c.commutes_iff_fund hNz hJz hRzf hNzimg hJR₁).mp hNJ',
    (c.commutes_iff_fund hN'z hJz hRzf' hN'zimg hJR₁).mp hN'J', fun y hy => ?_, fun y hy => ?_⟩
  · exact (locAut_fixed_iff hΩ c.hP1 htz hNz).mp hNt (c.d.ψ y) (by rw [hNzimg]; exact ⟨y, hy, rfl⟩)
  · exact (locAut_fixed_iff hΩ c.hP1 htz hN'z).mp hN't (c.d.ψ y)
      (by rw [hN'zimg]; exact ⟨y, hy, rfl⟩)

end Pair

end CFSG.ClassicalInvolution.RouteD.TwinSmall
