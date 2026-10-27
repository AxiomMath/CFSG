module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RelayRigid
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear pairEmbed)
open CFSG.SeitzReduction.SymplecticPilot (zThreeSL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat elt mat_elt)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm)
open CFSG.Timmesfeld.LieEmbed (a5Root)
open CFSG.LieType.Ree (ReeTag)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

local instance f4PilotQ2E6RelayBlockNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6RelayBlockNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Matrix

variable {K : Type} [Field K] {n : ℕ}

theorem relay_col_of_commute_transvection {h : SpecialLinearGroup (Fin n) K} {p q : Fin n}
    (hpq : p ≠ q) (hc : h * SpecialLinearGroup.transvection hpq 1 =
      SpecialLinearGroup.transvection hpq 1 * h) :
    (∀ x, x ≠ p → (h : Matrix (Fin n) (Fin n) K) x p = 0) ∧
      (h : Matrix (Fin n) (Fin n) K) p p = (h : Matrix (Fin n) (Fin n) K) q q := by
  have hm : (h : Matrix (Fin n) (Fin n) K) * Matrix.single p q 1 =
      Matrix.single p q 1 * (h : Matrix (Fin n) (Fin n) K) := by
    have h0 : (h : Matrix (Fin n) (Fin n) K) *
        (SpecialLinearGroup.transvection hpq (1 : K) : Matrix (Fin n) (Fin n) K) =
        (SpecialLinearGroup.transvection hpq (1 : K) : Matrix (Fin n) (Fin n) K) * h :=
      congrArg Subtype.val hc
    rw [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h0
    exact add_left_cancel h0
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 := congrFun (congrFun hm x) q
    rw [Matrix.mul_single_apply_same, mul_one, Matrix.single_mul_apply_of_ne (h := hx)] at h1
    exact h1
  · have h1 := congrFun (congrFun hm p) q
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, mul_one, one_mul] at h1
    exact h1

theorem relay_eq_one_of_commute (hK : Nat.card K = 2) {I : Finset (Fin n)}
    {h : SpecialLinearGroup (Fin n) K} (hI : h ∈ blockSpecialLinear I) {i i' j j' : Fin n}
    (hii : i ≠ i') (hjj : j ≠ j') (hcov : ∀ y ∈ I, y = i ∨ y = i' ∨ y = j ∨ y = j')
    (h1 : h * SpecialLinearGroup.transvection hii 1 = SpecialLinearGroup.transvection hii 1 * h)
    (h2 : h * SpecialLinearGroup.transvection hii.symm 1 =
      SpecialLinearGroup.transvection hii.symm 1 * h)
    (h3 : h * SpecialLinearGroup.transvection hjj 1 = SpecialLinearGroup.transvection hjj 1 * h)
    (h4 : h * SpecialLinearGroup.transvection hjj.symm 1 =
      SpecialLinearGroup.transvection hjj.symm 1 * h) :
    h = 1 := by
  obtain ⟨c1, d1⟩ := relay_col_of_commute_transvection hii h1
  obtain ⟨c2, -⟩ := relay_col_of_commute_transvection hii.symm h2
  obtain ⟨c3, d3⟩ := relay_col_of_commute_transvection hjj h3
  obtain ⟨c4, -⟩ := relay_col_of_commute_transvection hjj.symm h4
  have hdet : (h : Matrix (Fin n) (Fin n) K).det = 1 := h.2
  have hnz : ∀ p : Fin n, (∀ x, x ≠ p → (h : Matrix (Fin n) (Fin n) K) x p = 0) →
      (h : Matrix (Fin n) (Fin n) K) p p = 1 := by
    intro p hp
    refine SymplecticPilot.q2_eq_one_of_ne_zero hK fun h0 => ?_
    have hz : (h : Matrix (Fin n) (Fin n) K).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero p fun x => by
        by_cases hx : x = p
        · rw [hx]; exact h0
        · exact hp x hx
    rw [hdet] at hz
    exact one_ne_zero hz
  have key : ∀ p, (∀ x, x ≠ p → (h : Matrix (Fin n) (Fin n) K) x p = 0) →
      (h : Matrix (Fin n) (Fin n) K) p p = 1 →
        ∀ x, (h : Matrix (Fin n) (Fin n) K) x p = (1 : Matrix (Fin n) (Fin n) K) x p := by
    intro p hp hpp x
    by_cases hx : x = p
    · rw [hx, hpp, Matrix.one_apply_eq]
    · rw [hp x hx, Matrix.one_apply_ne hx]
  have hi1 := hnz i c1
  have hj1 := hnz j c3
  apply Subtype.ext
  change (h : Matrix (Fin n) (Fin n) K) = 1
  ext x y
  by_cases hy : y ∈ I
  · rcases hcov y hy with hyi | hyi | hyi | hyi
    · rw [hyi]; exact key i c1 hi1 x
    · rw [hyi]; exact key i' c2 (d1 ▸ hi1) x
    · rw [hyi]; exact key j c3 hj1 x
    · rw [hyi]; exact key j' c4 (d3 ▸ hj1) x
  · exact hI x y (Or.inr hy)

end Matrix

section Plane

variable {K : Type} [Field K]

theorem relaySp_x_root021 (c : K) : Sp.x 3 K ![0, 2, 1] c = elt (.positiveLong 1) c :=
  Sp.x_eq (by decide) c

theorem relaySp_x_neg_root021 (c : K) : Sp.x 3 K (-![0, 2, 1]) c = elt (.negativeLong 1) c :=
  Sp.x_eq (by decide) c

theorem relayMat_sp_x_root021 (c : K) :
    mat 3 K (Sp.x 3 K ![0, 2, 1] c) = 1 + c • single (.inl 1) (.inr 1) 1 := by
  rw [relaySp_x_root021, mat_elt]
  rfl

theorem relayMat_sp_x_neg_root021 (c : K) :
    mat 3 K (Sp.x 3 K (-![0, 2, 1]) c) = 1 + c • single (.inr 1) (.inl 1) 1 := by
  rw [relaySp_x_neg_root021, mat_elt]
  rfl

theorem relaySp6ToSL6_x_root021 (c : K) :
    sp6ToSL6 (Sp.x 3 K ![0, 2, 1] c) =
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) c := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, relayMat_sp_x_root021, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv,
    smul_single, smul_eq_mul, mul_one]
  rfl

theorem relaySp6ToSL6_x_neg_root021 (c : K) :
    sp6ToSL6 (Sp.x 3 K (-![0, 2, 1]) c) =
      SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) c := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, relayMat_sp_x_neg_root021, SpecialLinearGroup.transvection_coe, map_add,
    map_one, map_smul, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, smul_single, smul_eq_mul, mul_one]
  rfl

theorem relay_transvection_five_four_ne :
    SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) (1 : K) ≠
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg Subtype.val h) 5) 4
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply] at h1
  simp at h1

theorem relay_transvection_four_three_ne :
    SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 3 by decide) (1 : K) ≠
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg Subtype.val h) 4) 3
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply] at h1
  simp at h1

theorem relay_a5Root_rho_check :
    a5Root (graphSwapPerm.symm 4) (graphSwapPerm.symm 3) = Pi.single (rhoPerm 0) 1 ∧
      a5Root (graphSwapPerm.symm 5) (graphSwapPerm.symm 4) = Pi.single (rhoPerm 2) 1 := by
  decide +kernel

end Plane

section Glue

theorem relay_subgroupToG_le {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (A : Subgroup (adjointGroup .F4 K)) : subgroupToG e A ≤ L :=
  Subgroup.map_subtype_le _

theorem relay_conj_mem_centralizerPerfectCore {G : Type} [Group G] [Finite G] {J : Subgroup G}
    {t : G} (ht : ∀ y ∈ J, t * y = y * t) {a : G} (ha : a ∈ centralizerPerfectCore J) :
    t * a * t⁻¹ ∈ centralizerPerfectCore J := by
  have hJ : J.map (MulAut.conj t).toMonoidHom = J := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht z hz, mul_inv_cancel_right]
      exact hz
    · intro hy
      exact ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht y hy,
        mul_inv_cancel_right]⟩
  have h := map_centralizerPerfectCore (MulAut.conj t) J
  rw [hJ] at h
  rw [← h]
  exact ⟨a, ha, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

end Glue

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem relay_chainSL6_sp6ToSL6_mem {e : L ≃* adjointGroup .F4 K}
    {ΦA : e6ScLevi K e6A5Nodes →* G} (hn : IsLeviNormalizedA e ΦA) (s : StatedSp 3 K) :
    chainSL6 ΦA (sp6ToSL6 s) ∈ L := by
  rw [chainSL6_sp6ToSL6 hn, levi6Hom, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact SetLike.coe_mem _

theorem relay_conj_chainSL6_transvection {t : G} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hconj : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    {i j i₂ j₂ : Fin 6} (hij : i ≠ j) (hij₂ : i₂ ≠ j₂) {k : Fin (Tag.rank .E6)}
    (hk : a5Root (graphSwapPerm.symm i) (graphSwapPerm.symm j) = Pi.single k 1)
    (hk₂ : a5Root (graphSwapPerm.symm i₂) (graphSwapPerm.symm j₂) = Pi.single (rhoPerm k) 1)
    (c : K) :
    t * chainSL6 ΦA (SpecialLinearGroup.transvection hij c) * t⁻¹ =
      chainSL6 ΦA (SpecialLinearGroup.transvection hij₂ c) := by
  rw [chainSL6_apply, chainSL6_apply]
  apply hconj
  rw [coe_graphParamEquiv, coe_graphParamEquiv, graphParamHom_transvection,
    graphParamHom_transvection, hk, hk₂, CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single]
  rfl

theorem relay_range_scLeviRestrict_zero_le (ΦA : e6ScLevi K e6A5Nodes →* G) :
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range ≤
      (blockSpecialLinear ({0, 1} : Finset (Fin 6))).map (chainSL6 ΦA) := by
  rintro _ ⟨y, rfl⟩
  refine e6ScLevi_map_mem _ _ (fun j hj γ hγ c hx => ?_) y
  rw [Finset.mem_singleton] at hj
  subst hj
  rw [scLeviRestrict_apply]
  rcases hγ with rfl | rfl
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (0 : Fin 6) ≠ 1 by decide)
      (by decide) (by decide) c, chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_zero_one.1 _⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (1 : Fin 6) ≠ 0 by decide)
      (by decide) (by decide) c, chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_zero_one.2 _⟩

theorem relay_range_scLeviRestrict_two_le (ΦA : e6ScLevi K e6A5Nodes →* G) :
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range ≤
      (blockSpecialLinear ({1, 2} : Finset (Fin 6))).map (chainSL6 ΦA) := by
  rintro _ ⟨y, rfl⟩
  refine e6ScLevi_map_mem _ _ (fun j hj γ hγ c hx => ?_) y
  rw [Finset.mem_singleton] at hj
  subst hj
  rw [scLeviRestrict_apply]
  rcases hγ with rfl | rfl
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (1 : Fin 6) ≠ 2 by decide)
      (by decide) (by decide) c,
      chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_check.2.2.1 _⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (2 : Fin 6) ≠ 1 by decide)
      (by decide) (by decide) c,
      chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_check.2.2.2.2.1 _⟩

theorem relay_mem_alignedSubgroup_of_edge (hK : Nat.card K = 2) {e : L ≃* adjointGroup .F4 K}
    {t : G} (ht : t ∈ centralizer (L : Set G)) {ΦA : e6ScLevi K e6A5Nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hinj : Function.Injective (chainSL6 ΦA)) {a b : Fin 6} (hab : a ≠ b)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G))
    {i i' j j' : Fin 6} (hii : i ≠ i') (hjj : j ≠ j')
    (hcov : ∀ y ∈ ({a, b} : Finset (Fin 6))ᶜ, y = i ∨ y = i' ∨ y = j ∨ y = j')
    (hmi : i ∈ ({a, b} : Finset (Fin 6))ᶜ) (hmi' : i' ∈ ({a, b} : Finset (Fin 6))ᶜ)
    (hmj : j ∈ ({a, b} : Finset (Fin 6))ᶜ) (hmj' : j' ∈ ({a, b} : Finset (Fin 6))ᶜ)
    (hL1 : chainSL6 ΦA (SpecialLinearGroup.transvection hii 1) ∈ L)
    (hL2 : chainSL6 ΦA (SpecialLinearGroup.transvection hii.symm 1) ∈ L)
    (hL3 : chainSL6 ΦA (SpecialLinearGroup.transvection hjj 1) ∈ L)
    (hL4 : chainSL6 ΦA (SpecialLinearGroup.transvection hjj.symm 1) ∈ L)
    (htm : ∃ x ∈ blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ,
      t * chainSL6 ΦA x * t⁻¹ ≠ chainSL6 ΦA x)
    {α' : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ →* G}
    (hα' : Function.Injective α')
    (hα'r : α'.range ≤
      centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))))
    (hα'S : ∀ x : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ,
      chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x)
    {M : Subgroup (SpecialLinearGroup (Fin 6) K)}
    (hM : M ≤ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ) {S : Subgroup G}
    (hS : S ≤ M.map (chainSL6 ΦA)) {v : adjointGroup .F4 K}
    (hv : ∀ x : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ,
      (x : SpecialLinearGroup (Fin 6) K) ∈ M → Commute ((e.symm v : L) : G) (α' x)) :
    v ∈ alignedSubgroup e S := by
  set I : Finset (Fin 6) := ({a, b} : Finset (Fin 6))ᶜ with hIdef
  set B := blockSpecialLinear (K := K) I with hB
  set E := centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)))
    with hE
  set α : B →* G := (chainSL6 ΦA).comp B.subtype with hαdef
  have hαinj : Function.Injective α := hinj.comp Subtype.val_injective
  have hαr : α.range = E := by
    rw [hαdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact le_antisymm
      (le_centralizerPerfectCore_chain hr hab (subgroupToG_zpowers_chainZ_le hab hβ hx hx'))
      (centralizerPerfectCore_chain_le hK hr hinj hab (chainSL6_pairEmbed_mem hab hx hx'))
  have hcard : 3 ≤ I.card := by
    rw [hIdef, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    norm_num
  have χ : E ≃* LinearFlag.projectiveSL I.card K := by
    have e0 : B ≃* E := (MonoidHom.ofInjective hαinj).trans (MulEquiv.subgroupCongr hαr)
    have e1 : SpecialLinearGroup I K ≃* B :=
      (MonoidHom.ofInjective (LinearPilot.blockEmbed_injective I)).trans
        (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed I))
    have e2 : SpecialLinearGroup I K ≃* SpecialLinearGroup (Fin I.card) K :=
      LinearPilot.reindexSpecialLinear I.equivFin
    have e3 : SpecialLinearGroup (Fin I.card) K ≃* LinearFlag.projectiveSL I.card K :=
      MulEquiv.ofBijective (LinearFlag.proj I.card K)
        ⟨LinearPilot.proj_injective_of_card_two hK, LinearFlag.proj_surjective I.card K⟩
    exact e0.symm.trans ((e1.symm.trans e2).trans e3)
  have hC : ∀ x ∈ E, (∀ s ∈ L ⊓ E, x * s = s * x) → x = 1 := by
    intro x hx hcomm
    rw [← hαr] at hx
    obtain ⟨y, rfl⟩ := hx
    have hcomm' : ∀ (p q : Fin 6) (hpq : p ≠ q), p ∈ I → q ∈ I →
        chainSL6 ΦA (SpecialLinearGroup.transvection hpq 1) ∈ L →
          (y : SpecialLinearGroup (Fin 6) K) * SpecialLinearGroup.transvection hpq 1 =
            SpecialLinearGroup.transvection hpq 1 * (y : SpecialLinearGroup (Fin 6) K) := by
      intro p q hpq hp hq hLpq
      have hmem : SpecialLinearGroup.transvection hpq (1 : K) ∈ B :=
        LinearPilot.transvection_mem_blockSpecialLinear hpq hp hq 1
      have hs : α ⟨_, hmem⟩ ∈ L ⊓ E := ⟨hLpq, hαr ▸ ⟨⟨_, hmem⟩, rfl⟩⟩
      have h1 := hcomm _ hs
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hαinj h1)
    have hy1 : (y : SpecialLinearGroup (Fin 6) K) = 1 :=
      relay_eq_one_of_commute hK y.2 hii hjj hcov (hcomm' _ _ hii hmi hmi' hL1)
        (hcomm' _ _ hii.symm hmi' hmi hL2) (hcomm' _ _ hjj hmj hmj' hL3)
        (hcomm' _ _ hjj.symm hmj' hmj hL4)
    have hy : y = 1 := Subtype.ext hy1
    rw [hy, map_one]
  have hJL : subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)) ≤ L :=
    sup_le (relay_subgroupToG_le e _) (relay_subgroupToG_le e _)
  have hJ : ∀ y ∈ subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)), t * y = y * t :=
    fun y hy => (mem_centralizer_iff.1 ht y (hJL hy)).symm
  have hJ' : ∀ y ∈ subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)),
      t⁻¹ * y = y * t⁻¹ :=
    fun y hy => (mem_centralizer_iff.1 (inv_mem ht) y (hJL hy)).symm
  have htE : ∀ x ∈ E, t * x * t⁻¹ ∈ E := fun x hx => relay_conj_mem_centralizerPerfectCore hJ hx
  have htE' : ∀ x ∈ E, t⁻¹ * x * t ∈ E := fun x hx => by
    have h := relay_conj_mem_centralizerPerfectCore hJ' hx
    rwa [inv_inv] at h
  have htS : ∀ s ∈ L ⊓ E, t * s * t⁻¹ = s := fun s hs => by
    rw [← mem_centralizer_iff.1 ht s hs.1, mul_inv_cancel_right]
  have htm' : ∃ x ∈ E, t * x * t⁻¹ ≠ x := by
    obtain ⟨x, hxB, hx⟩ := htm
    exact ⟨chainSL6 ΦA x, hαr ▸ ⟨⟨x, hxB⟩, rfl⟩, hx⟩
  have hrig := eq_or_eq_conj_of_agree_projectiveSL hK hcard χ inf_le_right hC htE htE' htS htm'
    hαinj hα' hαr hα'r (fun x hx => hα'S x hx.1)
  have hvt : Commute ((e.symm v : L) : G) t := mem_centralizer_iff.1 ht _ (e.symm v).2
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro s hs
  obtain ⟨k, hkM, rfl⟩ := hS hs
  have h := commute_of_eq_or_eq_conj hrig hvt (x := ⟨k, hM hkM⟩) (hv ⟨k, hM hkM⟩ hkM)
  exact h.eq.symm

theorem relay_mem_alignedSubgroup_two_of_edge {e : L ≃* adjointGroup .F4 K} {t : G}
    (hw : F4Work L K t 1) {X₀ : Subgroup (adjointGroup .F4 K)} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hconj : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hn : IsLeviNormalizedA e ΦA)
    {α' : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ →* G}
    (hα' : Function.Injective α')
    (hα'r : α'.range ≤ centralizerPerfectCore
      (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K rootE1mE2Align))))
    (hα'S : ∀ x : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
      chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x) {v : adjointGroup .F4 K}
    (hv : ∀ x : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
      (x : SpecialLinearGroup (Fin 6) K) ∈ blockSpecialLinear ({1, 2} : Finset (Fin 6)) →
        Commute ((e.symm v : L) : G) (α' x)) :
    v ∈ alignedSubgroup e
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range := by
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hinj := chainSL6_injective hK hker
  have hL1 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) 1) ∈
      L := by
    rw [← relaySp6ToSL6_x_root021]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have hL2 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) 1) ∈
      L := by
    rw [← relaySp6ToSL6_x_neg_root021]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have hL3 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) 1) ∈
      L := by
    rw [← sp6ToSL6_x_single_two]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have hL4 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 2 by decide) 1) ∈
      L := by
    rw [← sp6ToSL6_x_neg_single_two]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have htm : ∃ x ∈ blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
      t * chainSL6 ΦA x * t⁻¹ ≠ chainSL6 ΦA x := by
    refine ⟨_, LinearPilot.transvection_mem_blockSpecialLinear
      (show (1 : Fin 6) ≠ 2 by decide) (by decide) (by decide) (1 : K), ?_⟩
    rw [relay_conj_chainSL6_transvection hconj (show (1 : Fin 6) ≠ 2 by decide)
      (show (5 : Fin 6) ≠ 4 by decide) a5Root_graphSwapPerm_check.2.2.1
      relay_a5Root_rho_check.2 1]
    exact fun h => relay_transvection_five_four_ne (hinj h)
  exact relay_mem_alignedSubgroup_of_edge hK hw.mem_centralizer hr hinj
    (show (0 : Fin 6) ≠ 3 by decide) isRoot_rootE1mE2Align (chainSL6_transvection_zero_three hn)
    (chainSL6_transvection_three_zero hn) (show (1 : Fin 6) ≠ 4 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hL1 hL2 hL3 hL4 htm hα' hα'r hα'S (LinearPilot.blockSpecialLinear_mono (by decide))
    (relay_range_scLeviRestrict_two_le ΦA) hv

theorem relay_mem_alignedSubgroup_zero_of_edge {e : L ≃* adjointGroup .F4 K} {t : G}
    (hw : F4Work L K t 1) {X₀ : Subgroup (adjointGroup .F4 K)} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hconj : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hn : IsLeviNormalizedA e ΦA)
    {α' : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ →* G}
    (hα' : Function.Injective α')
    (hα'r : α'.range ≤ centralizerPerfectCore
      (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K (Pi.single 1 1)))))
    (hα'S : ∀ x : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
      chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x) {v : adjointGroup .F4 K}
    (hv : ∀ x : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
      (x : SpecialLinearGroup (Fin 6) K) ∈ blockSpecialLinear ({0, 1} : Finset (Fin 6)) →
        Commute ((e.symm v : L) : G) (α' x)) :
    v ∈ alignedSubgroup e
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range := by
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hinj := chainSL6_injective hK hker
  have hL1 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide) 1) ∈
      L := by
    rw [← sp6ToSL6_x_root221]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have hL2 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 0 by decide) 1) ∈
      L := by
    rw [← sp6ToSL6_x_neg_root221]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have hL3 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) 1) ∈
      L := by
    rw [← relaySp6ToSL6_x_root021]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have hL4 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) 1) ∈
      L := by
    rw [← relaySp6ToSL6_x_neg_root021]
    exact relay_chainSL6_sp6ToSL6_mem hn _
  have htm : ∃ x ∈ blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
      t * chainSL6 ΦA x * t⁻¹ ≠ chainSL6 ΦA x := by
    refine ⟨_, LinearPilot.transvection_mem_blockSpecialLinear
      (show (0 : Fin 6) ≠ 1 by decide) (by decide) (by decide) (1 : K), ?_⟩
    rw [relay_conj_chainSL6_transvection hconj (show (0 : Fin 6) ≠ 1 by decide)
      (show (4 : Fin 6) ≠ 3 by decide) a5Root_graphSwapPerm_zero_one.1
      relay_a5Root_rho_check.1 1]
    exact fun h => relay_transvection_four_three_ne (hinj h)
  exact relay_mem_alignedSubgroup_of_edge hK hw.mem_centralizer hr hinj
    (show (2 : Fin 6) ≠ 5 by decide) (isRoot_single _ 1) (chainSL6_transvection_two_five hn)
    (chainSL6_transvection_five_two hn) (show (0 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hL1 hL2 hL3 hL4 htm hα' hα'r hα'S (LinearPilot.blockSpecialLinear_mono (by decide))
    (relay_range_scLeviRestrict_zero_le ΦA) hv

end Param

end CFSG.SeitzReduction.F4Pilot
