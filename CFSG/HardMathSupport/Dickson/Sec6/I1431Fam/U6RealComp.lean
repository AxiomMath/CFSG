module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsUniAux.Block
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslType
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Central

theorem u6r_le_of_map_le {Xs T : Type*} [Group Xs] [Group T] (π : Xs →* T)
    (hker : π.ker ≤ Subgroup.center Xs) {M N : Subgroup Xs} (hM : ⁅M, M⁆ = M)
    (hMN : M.map π ≤ N.map π) : M ≤ N := by
  rw [← hM, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨u, hu, hux⟩ := hMN (Subgroup.mem_map_of_mem π hx)
  obtain ⟨v, hv, hvy⟩ := hMN (Subgroup.mem_map_of_mem π hy)
  have hz : u⁻¹ * x ∈ Subgroup.center Xs := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel])
  have hz' : v⁻¹ * y ∈ Subgroup.center Xs := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvy, inv_mul_cancel])
  have e : ⁅x, y⁆ = ⁅u, v⁆ := by
    have hx' : x = u * (u⁻¹ * x) := by group
    have hy' : y = v * (v⁻¹ * y) := by group
    rw [hx', hy']
    exact commutatorElement_mul_mul' ((Subgroup.mem_center_iff.mp hz v).symm)
      ((Subgroup.mem_center_iff.mp hz _).symm) ((Subgroup.mem_center_iff.mp hz' u).symm)
  rw [e, commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem hu hv) (N.inv_mem hu)) (N.inv_mem hv)

theorem u6r_isTypeL2_map {Xs T : Type} [Group Xs] [Group T] (π : Xs →* T)
    (hker : π.ker ≤ Subgroup.center Xs) {N : Subgroup Xs} (hN : Group.IsPerfect ↥N) {r : ℕ} :
    IsTypeL2 r ↥N ↔ IsTypeL2 r ↥(N.map π) := by
  refine isTypeL2_congr_of_central hN (π.subgroupMap N) (π.subgroupMap_surjective N) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx1 : π (x : Xs) = 1 := congrArg Subtype.val hx
  have hxc : (x : Xs) ∈ Subgroup.center Xs := hker hx1
  rw [Subgroup.mem_center_iff]
  intro x'
  exact Subtype.ext ((Subgroup.mem_center_iff.mp hxc) (x' : Xs))

theorem u6r_three_dvd_of_isTypeL2 {Y : Type} [Group Y] {r : ℕ} (hT : IsTypeL2 r Y) :
    3 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
  obtain ⟨F, hF, hFin, -, ⟨e⟩⟩ := hT
  rw [Nat.card_congr e.toEquiv]
  exact l2fld_three_dvd_card_psl2

theorem u6r_isTypeL2_barOf {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥H) {r : ℕ} (hT : IsTypeL2 r ↥H) : IsTypeL2 r (barOf 3 H) := by
  have hdvd := u6r_three_dvd_of_isTypeL2 hT
  have hpK : 3 ∣ Nat.card ↥H := hdvd.trans (Subgroup.card_quotient_dvd_card _)
  have hOp : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥H) := by
    have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three H
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h
  have hOne : GLAPPrimeCore 3 ↥H ≠ ⊤ := by
    intro h
    apply hOp
    rw [h, Subgroup.card_top]
    exact hpK
  have hOZ : GLAPPrimeCore 3 ↥H ≤ Subgroup.center ↥H :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq
      (GLAPPrimeCore.normal 3 ↥H) hOne
  refine (isTypeL2_congr_of_central (Group.isPerfect_def.2 hq.1)
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H)) (QuotientGroup.mk'_surjective _) ?_).1 hT
  rw [QuotientGroup.ker_mk']
  exact hOZ

end Central

section Comp

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  (B : primeFormUnitary h (idGram K n))

omit B in
theorem u6r_ker_le_center :
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
      Subgroup.center ↥(gramSU h (idGram K n)) := by
  rw [QuotientGroup.ker_mk']
  exact normOneScalars_le_center h _ n

theorem u6r_map_fix_le :
    (fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) ≤
      Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B) :=
  map_fixSubgroup_le _ u6r_ker_le_center (t6psub_actSU h n B) (primeFormConjHom h (idGram K n) B)
    (fun x => t6psub_hact B x)

theorem u6r_map_fix_normal :
    (((fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))).subgroupOf
      (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B))).Normal :=
  normal_map_fixSubgroup _ u6r_ker_le_center (t6psub_actSU h n B)
    (primeFormConjHom h (idGram K n) B) (fun x => t6psub_hact B x) (QuotientGroup.mk'_surjective _)

theorem u6r_comp_le {H : Subgroup (primeFormP h (idGram K n))}
    (hH : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B)) H) :
    H ≤ (fixSubgroup (t6psub_actSU h n B)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) :=
  le_map_fixSubgroup_of_perfect _ u6r_ker_le_center (t6psub_actSU h n B)
    (primeFormConjHom h (idGram K n) B) (fun x => t6psub_hact B x) (QuotientGroup.mk'_surjective _)
    hH.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hH)

theorem u6r_comp_sub {H : Subgroup (primeFormP h (idGram K n))}
    (hH : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B)) H) :
    GLAPComponent 3 ((fixSubgroup (t6psub_actSU h n B)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) H := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le Nat.prime_three hH (u6r_comp_le B hH)
    (u6r_map_fix_le B)

theorem u6r_block_le (i : t6psub_Idx h n B) :
    (t6psub_block B i).map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) ≤
      (fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) :=
  Subgroup.map_mono (t6psub_block_le_fix B i)

theorem u6r_block_normal (i : t6psub_Idx h n B) :
    ∀ c ∈ (fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)),
      ∀ m ∈ (t6psub_block B i).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)),
        c * m * c⁻¹ ∈ (t6psub_block B i).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := by
  intro c hc m hm
  obtain ⟨c0, hc0, rfl⟩ := hc
  obtain ⟨m0, hm0, rfl⟩ := hm
  exact ⟨c0 * m0 * c0⁻¹, t6psub_block_normal B i c0 hc0 m0 hm0, by simp⟩

theorem u6r_block_quasisimple (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B))
    (i : t6psub_Idx h n B) :
    CFSG.IsQuasisimple ↥((t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hq := t6psub_isQuasisimple_block B H i
  refine CFSG.LocalCores.isQuasisimple_map hq _ fun hle => ?_
  have hle' : t6psub_block B i ≤ Subgroup.centralizer (t6psub_block B i : Set _) := fun x hx =>
    (Subgroup.mem_centralizer_iff).2 fun y _ =>
      (Subgroup.mem_center_iff.mp (u6r_ker_le_center (hle hx)) y)
  exact not_le_centralizer_of_isQuasisimple (isQuasisimple_open hq) hle'

theorem u6r_block_derived (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B)) :
    ∃ k : ℕ, ∀ x ∈ derivedSeries ↥((fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) k,
      (x : primeFormP h (idGram K n)) ∈ ⨆ i : t6psub_Idx h n B, (t6psub_block B i).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := by
  obtain ⟨k, hk⟩ := t6psub_derived B H
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hπ
  set C := fixSubgroup (t6psub_actSU h n B) with hC
  have hmemX : ∀ x : ↥C, π (x : ↥(gramSU h (idGram K n))) ∈ C.map π := fun x => ⟨_, x.2, rfl⟩
  let π' : ↥C →* ↥(C.map π) := (π.comp C.subtype).codRestrict (C.map π) hmemX
  have hπ's : Function.Surjective π' := by
    rintro ⟨z, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨k, fun x hx => ?_⟩
  rw [← map_derivedSeries_eq hπ's k] at hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have hmem := hk x0 hx0
  have h2 : π (x0 : ↥(gramSU h (idGram K n))) ∈ (⨆ i : t6psub_Idx h n B, t6psub_block B i).map π :=
    ⟨_, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact h2

theorem u6r_exists_block (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B))
    {J : Subgroup (primeFormP h (idGram K n))}
    (hJ : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B)) J) :
    ∃ i : t6psub_Idx h n B,
      barX 3 ((fixSubgroup (t6psub_actSU h n B)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) J =
        barX 3 ((fixSubgroup (t6psub_actSU h n B)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))
          ((t6psub_block B i).map
            (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  exact exists_barX_eq_of_blocks (u6r_comp_sub B hJ) _ (u6r_block_le B) (u6r_block_normal B)
    (u6r_block_quasisimple B H) (u6r_block_derived B H)

theorem u6r_block_comp (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B))
    (i : t6psub_Idx h n B) {r : ℕ}
    (hT : IsTypeL2 r ↥((t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))) :
    GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B))
      ((t6psub_block B i).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hq := isQuasisimple_open (u6r_block_quasisimple B H i)
  have hn : (((t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))).subgroupOf
        ((fixSubgroup (t6psub_actSU h n B)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (u6r_block_le B i)]
    exact fun x c hx hc => u6r_block_normal B i c hc x hx
  have hsub : IsSubnormal ((t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))
      (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B)) :=
    IsSubnormal.step (u6r_block_le B i) hn
      (IsSubnormal.step (u6r_map_fix_le B) (u6r_map_fix_normal B) (IsSubnormal.refl _))
  exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three hsub hq
    (u6r_three_dvd_of_isTypeL2 hT)

theorem u6r_eq_block (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B))
    {J : Subgroup (primeFormP h (idGram K n))}
    (hJ : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B)) J)
    (i : t6psub_Idx h n B)
    (hbar : barX 3 ((fixSubgroup (t6psub_actSU h n B)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) J =
        barX 3 ((fixSubgroup (t6psub_actSU h n B)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))
          ((t6psub_block B i).map
            (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))))
    {r : ℕ} (hT : IsTypeL2 r ↥((t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))) :
    J = (t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hN := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le Nat.prime_three
    (u6r_block_comp B H i hT) (u6r_block_le B i) (u6r_map_fix_le B)
  exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_unique (u6r_comp_sub B hJ) hN hbar

theorem u6r_isTypeL2_SL2 {F : Type} [Field F] [Finite F] :
    IsTypeL2 (Nat.card F) (Matrix.SpecialLinearGroup (Fin 2) F) :=
  ⟨F, inferInstance, inferInstance, rfl,
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩

theorem u6r_isTypeL2_block (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B))
    (i : t6psub_Idx h n B) (hself : dualPoly h.bar (i.1 : K[X]) = i.1)
    (hm2 : primaryMultiplicity ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (i.1 : K[X]) = 2) :
    IsTypeL2 (ℓ ^ (f * (i.1 : K[X]).natDegree)) ↥((t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) := by
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e1⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.nonempty_specialBlock_mulEquiv_sesqSU hself
      (selfDualPrimaryBlock H i.1 hself)
  obtain ⟨e2⟩ :=
    CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hm2
  haveI := hE.finite
  have hT0 := u6r_isTypeL2_SL2 (F := hE.fixedField)
  rw [UnitaryFieldData.card_fixedField hE] at hT0
  have e0 : ↥(t6psub_block B i) ≃* ↥(specialBlock (idForm h n) (t6psub_toLin B) (i.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (t6psub_block B i) (t6psuh_toLinSU h n)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psub_map_block B H i))
  have hTb := p6_isTypeL2_of_equiv ((e0.trans e1).trans e2).symm hT0
  exact (u6r_isTypeL2_map _ u6r_ker_le_center (t6psub_isQuasisimple_block B H i).1).1 hTb

end Comp

end CFSG.HardMathSupport.Dickson.Sec6.I1431
