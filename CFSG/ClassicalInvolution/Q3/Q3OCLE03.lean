module

public import CFSG.ClassicalInvolution.Q3.Q3OCLE01
public import CFSG.ClassicalInvolution.Q3.Q3OCLE02
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSp
public import CFSG.ClassicalInvolution.Q3.Q3T7S23DY01
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (toInducedAutOn_apply_coe)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (OuterL4.twin_std)
open CFSG.ClassicalInvolution.Models (longRootSet)
open scoped commutatorElement MatrixGroups

section Induced

variable {H : Type} [Group H]

theorem toInducedAutOn_comm (L : Subgroup H) (n m : ↥(Subgroup.normalizer (L : Set H)))
    (h : (n : H) * (m : H) = (m : H) * (n : H)) :
    toInducedAutOn L n * toInducedAutOn L m = toInducedAutOn L m * toInducedAutOn L n := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem commute_of_toInducedAutOn_eq_one (L : Subgroup H)
    (n : ↥(Subgroup.normalizer (L : Set H))) (h : toInducedAutOn L n = 1) {l : H} (hl : l ∈ L) :
    (n : H) * l = l * (n : H) := by
  have h1 := toInducedAutOn_apply_coe n ⟨l, hl⟩
  rw [h] at h1
  have h2 : (n : H) * l * (n : H)⁻¹ = l := by simpa using h1.symm
  calc (n : H) * l = (n : H) * l * (n : H)⁻¹ * (n : H) := by group
    _ = l * (n : H) := by rw [h2]

theorem odd_orderOf_toInducedAutOn (L : Subgroup H) (n : ↥(Subgroup.normalizer (L : Set H)))
    (hodd : Odd (orderOf (n : H))) : Odd (orderOf (toInducedAutOn L n)) := by
  have h1 : orderOf (toInducedAutOn L n) ∣ orderOf n := orderOf_map_dvd _ n
  rw [Subgroup.orderOf_coe] at hodd
  exact hodd.of_dvd_nat h1

end Induced


section Rows

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (proj_surjective ker_proj) in
theorem oddCentralizes_layer_sp [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥)
    (hY : Q3T8.Asc77.LayerOrthType Ω u 5 true) {n : G}
    (hn : n ∈ Subgroup.centralizer ({u} : Set G)) (hodd : Odd (orderOf n))
    (hnJ : ∀ x ∈ conjSub g K, n * x = x * n) (hnJ' : ∀ x ∈ conjSub g K', n * x = x * n) :
    ∀ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u, n * y = y * n := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls : ∀ M ∈ Ω, ∃ z', Q3T8.Generic.IsClassicalMember M z' := hΩ.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨-, -, -, -, -, hJt, hJ't, -⟩ := Q3T8.Asc77.T7L.exists_uFrame hs hd
  have hJΩ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJt).2
  have hJ'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJ't).2
  have hJΦ : conjSub g K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJΩ, hJu⟩
  have hJ'Φ : conjSub g K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'u⟩
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have hexeq : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField 3 1)) := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hcls L hL
    exact Q3T7S23.nonempty_equiv_galoisField3
      ((hzL.toQ3 (by norm_num)).nonempty_equiv_sl2 (hex L hL))
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne (conjSub_injective g h).symm
  obtain ⟨t', n', ht', D, hcard, i', hit, hir⟩ :=
    Q3T8.Asc77.T7Z.exists_omegaLie_of_layerOrth hOY hY
  have htn : t' = .PSp ∧ n' = 2 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i' = 1 := by
    rcases D.exp_eq i' with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := T7Z.nonempty_modelLayer_of_omegaLie D hcard i' (hit.trans htn.1)
    (hir.trans htn.2) hie
  have hrange : P.ψ.range = Q3T8.Asc77.ExactLayer.exactLayer Ω u := by
    rw [P.range_eq, Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  have hadm : StatedLieAdmissible .PSp 2 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 hp2
  have hfin : Finite (modelUniv .PSp 2 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (by trivial) hadm
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have hi₁ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ hJR
    (hexeq _ hJΩ)
  have hi₂ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ' hJ'R
    (hexeq _ hJ'Ω)
  have hlong : ∀ R : Subgroup (modelUniv .PSp 2 3 1 Fact.out).K,
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Fact.out).D →
        ∃ i, IsLongRootSp2 (K := GaloisField 3 1) (n := 2) R i :=
    fun R hR => (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).1 hR
  obtain ⟨x, hxRJ, hψx⟩ : ∃ x ∈ RJ, P.ψ x = u * e := by
    have : u * e ∈ RJ.map P.ψ := hJR ▸ htJ.mem
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx, hxe⟩
  obtain ⟨x', hx'RJ', hψx'⟩ : ∃ x' ∈ RJ', P.ψ x' = u * e := by
    have : u * e ∈ RJ'.map P.ψ := hJ'R ▸ htJ'.mem
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx, hxe⟩
  have hx2 : x * x = 1 := hi₁ _ (RJ.mul_mem hxRJ hxRJ) (by rw [map_mul, hψx, htJ.sq])
  have hx'2 : x' * x' = 1 := hi₂ _ (RJ'.mul_mem hx'RJ' hx'RJ') (by rw [map_mul, hψx', htJ'.sq])
  have hx1 : x ≠ 1 := fun h => htJ.ne_one (by rw [← hψx, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => htJ'.ne_one (by rw [← hψx', h, map_one])
  have hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)) :=
    P.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψx', hψx, mul_inv_cancel])
  have hne' : RJ ≠ RJ' := by
    intro h
    apply hJJ'
    rw [hJR, hJ'R, h]
  have : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial hadm).1.1
  have hnY : n ∈ Subgroup.normalizer (P.ψ.range : Set G) := by
    rw [hrange, Subgroup.mem_normalizer_iff]
    intro h
    have h1 := mem_conjSub_iff (n := n) (K := Q3T8.Asc77.ExactLayer.exactLayer Ω u)
      (x := n * h * n⁻¹)
    rw [Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hn] at h1
    have e : n⁻¹ * (n * h * n⁻¹) * n = h := by group
    rw [e] at h1
    exact h1.symm
  set v : ↥(inducedAutOn P.ψ.range) := toInducedAutOn P.ψ.range ⟨n, hnY⟩ with hv
  have hcomm : ∀ r : (modelUniv .PSp 2 3 1 Fact.out).K, n * P.ψ r = P.ψ r * n →
      v * innerHom P.ψ r = innerHom P.ψ r * v := by
    intro r hr
    rw [innerHom_apply]
    exact toInducedAutOn_comm _ _ _ hr
  have hv1 : v = 1 := by
    refine eq_one_of_odd_of_autSq P.ψ P.ker_le (proj 2 (GaloisField 3 1)) proj_surjective
      (ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm)
      (R := RJ) (R' := RJ') ?_ v ?_ ?_ ?_
    · intro φ hφ hφ'
      exact Q3OT.psp4_autSq3 (hlong RJ hRJ) (hlong RJ' hRJ') hne' hxRJ hx2 hx1 hx'RJ' hx'2 hx'1
        hc φ hφ hφ'
    · intro r hr
      exact hcomm r (hnJ _ (by rw [hJR]; exact Subgroup.mem_map_of_mem _ hr))
    · intro r hr
      exact hcomm r (hnJ' _ (by rw [hJ'R]; exact Subgroup.mem_map_of_mem _ hr))
    · exact odd_orderOf_toInducedAutOn _ ⟨n, hnY⟩ hodd
  intro y hy
  rw [← hrange] at hy
  exact commute_of_toInducedAutOn_eq_one P.ψ.range ⟨n, hnY⟩ hv1 hy

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (proj proj_surjective ker_proj
  scalars_eq_center) in
theorem oddCentralizes_layer_psl [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥)
    (hY : Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1)) {n : G}
    (hn : n ∈ Subgroup.centralizer ({u} : Set G)) (hodd : Odd (orderOf n))
    (hnJ : ∀ x ∈ conjSub g K, n * x = x * n) (hnJ' : ∀ x ∈ conjSub g K', n * x = x * n) :
    ∀ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u, n * y = y * n := by
  classical
  have hπ : (!piSign 3 1) = true := by decide
  rw [hπ] at hY
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls : ∀ M ∈ Ω, ∃ z', Q3T8.Generic.IsClassicalMember M z' := hΩ.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨-, -, -, -, -, hJt, hJ't, -⟩ := Q3T8.Asc77.T7L.exists_uFrame hs hd
  have hJΩ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJt).2
  have hJ'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJ't).2
  have hJΦ : conjSub g K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJΩ, hJu⟩
  have hJ'Φ : conjSub g K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'u⟩
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have hexeq : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField 3 1)) := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hcls L hL
    exact Q3T7S23.nonempty_equiv_galoisField3
      ((hzL.toQ3 (by norm_num)).nonempty_equiv_sl2 (hex L hL))
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne (conjSub_injective g h).symm
  obtain ⟨t', n', ht', D, hcard, i', hit, hir⟩ :=
    Q3T8.Asc77.T7Z.exists_omegaLie_of_layerOrth hOY hY
  have htn : t' = .PSL ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i' = 1 := by
    rcases D.exp_eq i' with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := T7Z.nonempty_pslLayer_of_omegaLie D hcard i' (hit.trans htn.1)
    (hir.trans htn.2) hie
  have hrange : P.ψ.range = Q3T8.Asc77.ExactLayer.exactLayer Ω u := by
    rw [P.range_eq, Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hfin := Q3T7S23.finite_U3
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have hRJl : RJ ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num) :=
    RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hRJ
  have hRJ'l : RJ' ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num) :=
    RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hRJ'
  have hi₁ := Q3T7S23.injOn_fund_psl3 P hRJ hJR (hexeq _ hJΩ)
  have hi₂ := Q3T7S23.injOn_fund_psl3 P hRJ' hJ'R (hexeq _ hJ'Ω)
  obtain ⟨x, hxRJ, hψx⟩ : ∃ x ∈ RJ, P.ψ x = u * e := by
    have : u * e ∈ RJ.map P.ψ := hJR ▸ htJ.mem
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx, hxe⟩
  obtain ⟨x', hx'RJ', hψx'⟩ : ∃ x' ∈ RJ', P.ψ x' = u * e := by
    have : u * e ∈ RJ'.map P.ψ := hJ'R ▸ htJ'.mem
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx, hxe⟩
  have hx2 : x * x = 1 := hi₁ _ (RJ.mul_mem hxRJ hxRJ) (by rw [map_mul, hψx, htJ.sq])
  have hx'2 : x' * x' = 1 := hi₂ _ (RJ'.mul_mem hx'RJ' hx'RJ') (by rw [map_mul, hψx', htJ'.sq])
  have hx1 : x ≠ 1 := fun h => htJ.ne_one (by rw [← hψx, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => htJ'.ne_one (by rw [← hψx', h, map_one])
  have hc : x' * x⁻¹ ∈ Subgroup.center SL(4, GaloisField 3 1) :=
    P.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψx', hψx, mul_inv_cancel])
  have hne' : RJ ≠ RJ' := by
    intro h
    apply hJJ'
    rw [hJR, hJ'R, h]
  have : Group.IsPerfect (modelUniv .PSL 4 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial
        Q3T7S23.admissible_psl4_three).1.1
  have hπk : (proj 4 (GaloisField 3 1)).ker = Subgroup.center SL(4, GaloisField 3 1) :=
    (ker_proj (n := 4) (K := GaloisField 3 1)).trans (scalars_eq_center 4 (GaloisField 3 1))
  have hnY : n ∈ Subgroup.normalizer (P.ψ.range : Set G) := by
    rw [hrange, Subgroup.mem_normalizer_iff]
    intro h
    have h1 := mem_conjSub_iff (n := n) (K := Q3T8.Asc77.ExactLayer.exactLayer Ω u)
      (x := n * h * n⁻¹)
    rw [Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hn] at h1
    have e : n⁻¹ * (n * h * n⁻¹) * n = h := by group
    rw [e] at h1
    exact h1.symm
  set v : ↥(inducedAutOn P.ψ.range) := toInducedAutOn P.ψ.range ⟨n, hnY⟩ with hv
  have hcomm : ∀ r : (modelUniv .PSL 4 3 1 Fact.out).K, n * P.ψ r = P.ψ r * n →
      v * innerHom P.ψ r = innerHom P.ψ r * v := by
    intro r hr
    rw [innerHom_apply]
    exact toInducedAutOn_comm _ _ _ hr
  have hv1 : v = 1 := by
    refine eq_one_of_odd_of_autSq P.ψ P.ker_le (proj 4 (GaloisField 3 1))
      (proj_surjective 4 (GaloisField 3 1)) hπk (R := RJ) (R' := RJ') ?_ v ?_ ?_ ?_
    · intro φ hφ hφ'
      exact psl4_autSq3 h2 hF hRJl hRJ'l hne' hxRJ hx2 hx1 hx'RJ' hx'2 hx'1 hc φ hφ hφ'
    · intro r hr
      exact hcomm r (hnJ _ (by rw [hJR]; exact Subgroup.mem_map_of_mem _ hr))
    · intro r hr
      exact hcomm r (hnJ' _ (by rw [hJ'R]; exact Subgroup.mem_map_of_mem _ hr))
    · exact odd_orderOf_toInducedAutOn _ ⟨n, hnY⟩ hodd
  intro y hy
  rw [← hrange] at hy
  exact commute_of_toInducedAutOn_eq_one P.ψ.range ⟨n, hnY⟩ hv1 hy

end Rows

end CFSG.ClassicalInvolution.Q3.Q3OCL
