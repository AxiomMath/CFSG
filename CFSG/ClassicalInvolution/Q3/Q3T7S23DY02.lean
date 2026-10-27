module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23DY01
public import CFSG.ClassicalInvolution.Asc77.AscCHN5
public import CFSG.ClassicalInvolution.Asc77.AscCHN6
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.CHN
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagConj2 range_comp_mulEquiv
  ker_comp_mulEquiv_le_center coe_diagConj2)
open CFSG.ClassicalInvolution.Phan (blockMat_apply)
open CFSG.ClassicalInvolution.Models (negBlock_eq_diagonal)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (OuterL4.twin_std)
open CFSG.ClassicalInvolution.Models (longRootSet)
open scoped Matrix MatrixGroups

section Blocks

variable {F : Type} [Field F]

theorem blk1_neg_one_conj_blk0 (s : SL(2, F)) :
    blk F 1 (-1) * blk F 0 s * (blk F 1 (-1))⁻¹ = blk F 0 (diagConj2 (-1) 1 s) := by
  rw [blk_neg_one_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk_neg_one,
    coe_blk, coe_blk, coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negBlock_eq_diagonal, blockMat_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four]

end Blocks

theorem sl2_neg_one_ne_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  apply h2
  linear_combination -this



section YSide

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem ySideD4_3 [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : CFSG.Open.classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥)
    (hY : Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1)) :
    ∃ (K₁ : Subgroup G) (z₁ : G), D4YData Ω K K' u e g K₁ z₁ := by
  classical
  have hπ : (!piSign 3 1) = true := by decide
  rw [hπ] at hY
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls : ∀ M ∈ Ω, ∃ z', Q3T8.Generic.IsClassicalMember M z' := hΩ.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R₂, R₂', a₂, b₂, v', hJt, hJ't, -⟩ := Q3T8.Asc77.T7L.exists_uFrame hs hd
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
    exact nonempty_equiv_galoisField3 ((hzL.toQ3 (by norm_num)).nonempty_equiv_sl2 (hex L hL))
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
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hneg : ¬ IsSquare (-1 : GaloisField 3 1) := by
    have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 3 1) = 3 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using GaloisField.card 3 1 one_ne_zero
    rw [FiniteField.isSquare_neg_one_iff, hcard]
    omega
  have hRJl : RJ ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num) :=
    RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hRJ
  have hRJ'l : RJ' ∈ longRootSet (K := GaloisField 3 1) (show 2 ≤ 4 by norm_num) :=
    RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hRJ'
  have hi₁ := injOn_fund_psl3 P hRJ hJR (hexeq _ hJΩ)
  have hi₂ := injOn_fund_psl3 P hRJ' hJ'R (hexeq _ hJ'Ω)
  have hne : RJ' ≠ RJ := by
    intro h
    apply hJJ'
    rw [hJR, hJ'R, h]
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
  have hc : x * x'⁻¹ ∈ Subgroup.center SL(4, GaloisField 3 1) :=
    P.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψx, hψx', mul_inv_cancel])
  obtain ⟨g₀, hRg', hRg, -⟩ := OuterL4.twin_std h2 hRJ'l hRJl hne hx'RJ' hx'2 hx'1 hxRJ hx2 hx1 hc
  set F := GaloisField 3 1 with hF
  set ψ₀ : SL(4, F) →* G := P.ψ.comp (MulAut.conj g₀).toMonoidHom with hψ₀
  have hker : ψ₀.ker ≤ Subgroup.center SL(4, F) :=
    ker_comp_mulEquiv_le_center P.ker_le (MulAut.conj g₀)
  have hrange : ψ₀.range = Q3T8.Asc77.ExactLayer.exactLayer Ω u := by
    have h1 : ψ₀.range = P.ψ.range := range_comp_mulEquiv P.ψ (MulAut.conj g₀)
    rw [h1, P.range_eq, Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
  have hJ'0 : (blk F 0).range.map ψ₀ = conjSub g K' := by
    rw [hJ'R, hRg']
    exact (Subgroup.map_map _ _ _).symm
  have hJ0 : (blk F 2).range.map ψ₀ = conjSub g K := by
    rw [hJR, hRg]
    exact (Subgroup.map_map _ _ _).symm
  have hinvol : ∀ (i : Fin 3) (L : Subgroup G) (t : G), IsUniqueInvolution L t →
      (blk F i).range.map ψ₀ = L → ψ₀ (blk F i (-1)) = t := by
    intro i L t ht hL
    have hmem : ψ₀ (blk F i (-1)) ∈ L := by
      rw [← hL]
      exact ⟨_, ⟨-1, rfl⟩, rfl⟩
    have hsq : ψ₀ (blk F i (-1)) * ψ₀ (blk F i (-1)) = 1 := by
      rw [← map_mul, ← map_mul]
      simp
    rcases ht.unique _ hmem hsq with h | h
    · exfalso
      have h1 := hker (MonoidHom.mem_ker.mpr h)
      exact sl2_neg_one_ne_one h2 (eq_one_of_blk_mem_center i _ h1)
    · exact h
  have hψ2 : ψ₀ (blk F 2 (-1)) = u * e := hinvol 2 _ _ htJ hJ0
  have hψ0' : ψ₀ (blk F 0 (-1)) = u * e := hinvol 0 _ _ htJ' hJ'0
  have hψ : ψ₀ (blk F 0 (-1) * blk F 2 (-1)) = 1 := by
    rw [map_mul, hψ0', hψ2]
    exact htJ.sq
  have hu : ∀ x ∈ ψ₀.range, u * x = x * u := by
    intro x hx
    rw [hrange] at hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hx)).symm
  have he : u * ψ₀ (blk F 2 (-1)) = e := by
    rw [hψ2, ← mul_assoc, hd.hu2, one_mul]
  have hnode : node ψ₀ = conjSub (ψ₀ permSL) (conjSub g K) := by
    ext k
    rw [mem_node_iff]
    constructor
    · rintro ⟨s, rfl⟩
      have h1 : ψ₀ (blk F 1 s) = ψ₀ permSL * ψ₀ (blk F 2 s) * (ψ₀ permSL)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, permSL_conj_blk2]
      rw [h1]
      refine conj_mem_conjSub ?_
      rw [← hJ0]
      exact ⟨_, ⟨s, rfl⟩, rfl⟩
    · intro hk
      rw [mem_conjSub_iff, ← hJ0] at hk
      obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hk
      refine ⟨s, ?_⟩
      have h1 : ψ₀ (blk F 1 s) = ψ₀ permSL * ψ₀ (blk F 2 s) * (ψ₀ permSL)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, permSL_conj_blk2]
      rw [h1, hs]
      group
  have hz₁ : ψ₀ (blk F 1 (-1)) = ψ₀ permSL * (u * e) * (ψ₀ permSL)⁻¹ := by
    rw [← hψ2, ← map_inv, ← map_mul, ← map_mul, permSL_conj_blk2]
  have hClaim : ∀ a : G, a * u = u * a → (∀ x ∈ conjSub g K, a * x = x * a) →
      (∀ x ∈ conjSub g K', a * x = x * a) → a * ψ₀ (blk F 1 (-1)) = ψ₀ (blk F 1 (-1)) * a := by
    intro a ha hcJ hcJ'
    have hnorm : ∀ n ∈ Subgroup.centralizer ({u} : Set G), ∀ x : SL(4, F),
        ∃ y, ψ₀ y = n * ψ₀ x * n⁻¹ := by
      intro n hn x
      have h1 := Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hn
      have h2' : n * ψ₀ x * n⁻¹ ∈ conjSub n (Q3T8.Asc77.ExactLayer.exactLayer Ω u) :=
        conj_mem_conjSub (by rw [← hrange]; exact ⟨x, rfl⟩)
      rw [h1, ← hrange] at h2'
      obtain ⟨y, hy⟩ := h2'
      exact ⟨y, hy⟩
    have hac : a ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr ha
    refine fix_z_of_centralizes h2 hneg ψ₀ hker hψ a (hnorm a hac) (fun x => ?_) ?_ ?_
    · obtain ⟨y, hy⟩ := hnorm a⁻¹ (inv_mem hac) x
      exact ⟨y, by rw [hy, inv_inv]⟩
    · intro r hr
      exact hcJ' (ψ₀ r) (by rw [← hJ'0]; exact ⟨r, hr, rfl⟩)
    · intro r hr
      exact hcJ (ψ₀ r) (by rw [← hJ0]; exact ⟨r, hr, rfl⟩)
  refine ⟨node ψ₀, ψ₀ (blk F 1 (-1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hClaim⟩
  · rw [hnode]
    exact hΩ.conjInvariant _ _ hJΩ
  · rw [hnode, hz₁]
    exact htJ.conj _
  · rw [← hrange]
    exact Subgroup.map_le_range ψ₀ _
  · obtain ⟨W₁, hW₁⟩ := blk_pair_one_two (F := F)
    have := Balance.linearBlockStandardPair_map_of_ker_le_center hW₁ ψ₀ hker
    rw [hJ0] at this
    exact ⟨_, this⟩
  · rw [← hrange, range_eq_sup_nodes ψ₀, hJ'0, hJ0]
  · rw [← he]
    exact z₁_comm_e ψ₀ hu
  · refine ⟨ψ₀.comp (blk F 2), ?_, fun s => chart_node ψ₀ s⟩
    rw [MonoidHom.range_comp, hJ0]
  · refine ⟨ψ₀.comp (blk F 0), ?_, fun s => ?_⟩
    · rw [MonoidHom.range_comp, hJ'0]
    · show ψ₀ (blk F 1 (-1)) * ψ₀ (blk F 0 s) * (ψ₀ (blk F 1 (-1)))⁻¹ =
        ψ₀ (blk F 0 (diagConj2 (-1) 1 s))
      rw [← map_inv, ← map_mul, ← map_mul, blk1_neg_one_conj_blk0]

end YSide

end CFSG.ClassicalInvolution.Q3.Q3T7S23

