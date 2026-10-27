module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open

namespace Gen2318E64InAux

section Generic

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl

@[expose] def beta0L : List ℤ := [1, 0, 0, 0, 0, 0]

@[expose] def orb0L : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0], [-1, 0, -1, -1, -1, 0]]

@[expose] def fixRootsL (M : List (List ℤ)) : List (List ℤ) :=
  Tag.E6.artifactRoots.filter fun β => lmulVec 6 M β = β

theorem orbit_check : ∀ M ∈ dMats,
    (∀ i j : Fin 6, lget (lmul 6 M (lmul 6 M M)) i j = lget (lid 6) i j) →
    lmulVec 6 M beta0L ∉ orb0L → fixRootsL M ≠ [] ∧ (fixRootsL M).length ≤ 8 := by
  decide +kernel

theorem beta0L_mem : beta0L ∈ Tag.E6.artifactRoots := by
  decide +kernel

theorem toVec_ofFn6 (v : Fin Tag.E6.rank → ℤ) : toVec Tag.E6.rank (List.ofFn v) = v := by
  funext i
  simp [toVec, vget]

theorem ofFn_toVec6 {l : List ℤ} (hl : l.length = Tag.E6.rank) :
    List.ofFn (toVec Tag.E6.rank l) = l := by
  refine List.ext_getElem (by simp [hl]) fun n h1 h2 => ?_
  simp [toVec, vget, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem lmulVec_ofFn6 (M : List (List ℤ)) (v : Fin Tag.E6.rank → ℤ) :
    lmulVec 6 M (List.ofFn v) = List.ofFn ((toMat Tag.E6.rank M).mulVec v) := by
  have h := toVec_lmulVec 6 M (List.ofFn v)
  have hlen : (lmulVec 6 M (List.ofFn v)).length = Tag.E6.rank := by
    simp [lmulVec, vofFn]
    rfl
  have h' : toVec Tag.E6.rank (lmulVec 6 M (List.ofFn v)) = (toMat Tag.E6.rank M).mulVec v := by
    have h'' : toVec Tag.E6.rank (lmulVec 6 M (List.ofFn v)) =
        (toMat Tag.E6.rank M).mulVec (toVec Tag.E6.rank (List.ofFn v)) := h
    rw [h'', toVec_ofFn6]
  calc lmulVec 6 M (List.ofFn v) = List.ofFn (toVec Tag.E6.rank (lmulVec 6 M (List.ofFn v))) :=
        (ofFn_toVec6 hlen).symm
    _ = List.ofFn ((toMat Tag.E6.rank M).mulVec v) := by rw [h']

theorem exists_conj_le_of_not_dvd {G : Type*} [Group G] [Finite G] {A N P : Subgroup G}
    (hPA : P ≤ A) (hP : IsPGroup 3 P) (h3 : ¬ 3 ∣ N.relIndex A) :
    ∃ u ∈ A, ∀ x ∈ P, u⁻¹ * x * u ∈ N := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' : IsPGroup 3 (P.subgroupOf A) := hP.comap_of_injective A.subtype A.subtype_injective
  have hcard : ¬ 3 ∣ Nat.card (↥A ⧸ N.subgroupOf A) := h3
  obtain ⟨Q, hQ⟩ := hP'.nonempty_fixed_point_of_prime_not_dvd_card (↥A ⧸ N.subgroupOf A) hcard
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  refine ⟨z, z.2, fun x hx => ?_⟩
  have hxA : x ∈ A := hPA hx
  have hfix := hQ ⟨⟨x, hxA⟩, Subgroup.mem_subgroupOf.2 hx⟩
  change ((⟨x, hxA⟩ * z : A) : A ⧸ N.subgroupOf A) = (z : A ⧸ N.subgroupOf A) at hfix
  rw [QuotientGroup.eq] at hfix
  have h2 : z⁻¹ * ⟨x, hxA⟩ * z ∈ N.subgroupOf A := by
    have := inv_mem hfix
    simpa [mul_assoc] using this
  exact Subgroup.mem_subgroupOf.1 h2

theorem charP_two_of_card_four (K' : Type) [Field K'] [Finite K'] (h : Nat.card K' = 4) :
    CharP K' 2 := by
  classical
  haveI : Fintype K' := Fintype.ofFinite K'
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K'
  rw [Fintype.card_eq_nat_card, h] at hcard
  have hdvd : p ∣ 4 := by
    rw [hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hp2 : p = 2 := by
    interval_cases p <;> first | rfl | exact absurd hdvd (by decide) | exact absurd hp (by decide)
  rw [hp2] at hchar
  exact hchar

end Generic

section Weyl

set_option linter.unusedSectionVars false

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl


theorem smul_eq_of_weylMatrix {w : WeylGroup Tag.E6} {M : List (List ℤ)}
    (hM : weylMatrix w = toMat Tag.E6.rank M) (v : Fin Tag.E6.rank → ℤ) :
    w • v = (toMat Tag.E6.rank M).mulVec v := by
  rw [← weylMatrix_mulVec, hM]

theorem cube_of_pow {w : WeylGroup Tag.E6} (hw : w ^ 3 = 1) {M : List (List ℤ)}
    (hM : weylMatrix w = toMat Tag.E6.rank M) :
    ∀ i j : Fin 6, lget (lmul 6 M (lmul 6 M M)) i j = lget (lid 6) i j := by
  intro i j
  have h := congrArg weylMatrix hw
  rw [weylMatrix_pow, weylMatrix_one, hM] at h
  have h' : toMat Tag.E6.rank (lmul 6 M (lmul 6 M M)) = toMat Tag.E6.rank (lid 6) := by
    rw [toMat_lid6, toMat_lmul6, toMat_lmul6, ← pow_three]
    exact h
  exact congrFun (congrFun h' i) j

theorem exists_root_orbit_subset {B : Subgroup (WeylGroup Tag.E6)} (hBP : B ≤ Pw)
    (hB : IsElemAbelian 3 B) :
    ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧
      ∃ T : Finset (Fin Tag.E6.rank → ℤ), T.card ≤ 8 ∧ ∀ b ∈ B, b • β ∈ T := by
  classical
  set β₀ : Fin Tag.E6.rank → ℤ := toVec Tag.E6.rank beta0L with hβ₀
  set T₀ : Finset (Fin Tag.E6.rank → ℤ) := (orb0L.map (toVec Tag.E6.rank)).toFinset with hT₀
  by_cases hA : ∀ b ∈ B, b • β₀ ∈ T₀
  · refine ⟨β₀, ?_, T₀, ?_, hA⟩
    · refine isRoot_iff_mem_artifactRoots.2 ?_
      rw [hβ₀, ofFn_toVec6 (by rfl)]
      exact beta0L_mem
    · refine (List.toFinset_card_le _).trans ?_
      simp [orb0L]
  · push Not at hA
    obtain ⟨b, hb, hbT⟩ := hA
    obtain ⟨M, hM, hbM⟩ := exists_mem_dMats_of_mem_Pw (hBP hb)
    have hcube := cube_of_pow (hB.2 b hb) hbM
    have hnot : lmulVec 6 M beta0L ∉ orb0L := by
      intro hmem
      apply hbT
      have h1 : b • β₀ = toVec Tag.E6.rank (lmulVec 6 M beta0L) := by
        rw [smul_eq_of_weylMatrix hbM]
        exact (toVec_lmulVec 6 M beta0L).symm
      rw [h1]
      exact List.mem_toFinset.2 (List.mem_map_of_mem hmem)
    obtain ⟨hne, hlen⟩ := orbit_check M hM hcube hnot
    obtain ⟨βl, hβl⟩ := List.exists_mem_of_ne_nil _ hne
    have hβl' := List.mem_filter.1 hβl
    have hlenβ : βl.length = Tag.E6.rank := length_of_mem_artifactRoots hβl'.1
    set β : Fin Tag.E6.rank → ℤ := toVec Tag.E6.rank βl with hβdef
    have hβofFn : List.ofFn β = βl := ofFn_toVec6 hlenβ
    have hβroot : IsRoot Tag.E6 β := isRoot_iff_mem_artifactRoots.2 (by rw [hβofFn]; exact hβl'.1)
    have hbβ : b • β = β := by
      rw [smul_eq_of_weylMatrix hbM]
      apply List.ofFn_injective
      rw [← lmulVec_ofFn6, hβofFn]
      exact of_decide_eq_true hβl'.2
    refine ⟨β, hβroot, ((fixRootsL M).map (toVec Tag.E6.rank)).toFinset, ?_, ?_⟩
    · refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      exact hlen
    · intro u hu
      have hub : u * b = b * u := congrArg Subtype.val (hB.1.is_comm.comm ⟨u, hu⟩ ⟨b, hb⟩)
      have hγroot : IsRoot Tag.E6 (u • β) := IsRoot.smul hβroot u
      have hbγ : b • (u • β) = u • β := by
        rw [smul_smul, ← hub, mul_smul, hbβ]
      have hmem : List.ofFn (u • β) ∈ fixRootsL M := by
        refine List.mem_filter.2 ⟨isRoot_iff_mem_artifactRoots.1 hγroot, decide_eq_true ?_⟩
        rw [lmulVec_ofFn6, ← smul_eq_of_weylMatrix hbM, hbγ]
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨_, hmem, toVec_ofFn6 _⟩)

theorem relIndex_stabilizer_le_three {B : Subgroup (WeylGroup Tag.E6)} (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    {γ : Fin Tag.E6.rank → ℤ} {T : Finset (Fin Tag.E6.rank → ℤ)} (hT : T.card ≤ 8)
    (hBT : ∀ b ∈ B, b • γ ∈ T) :
    (MulAction.stabilizer (WeylGroup Tag.E6) γ).relIndex B ≤ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB3 g g.2)⟩
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hdvd : (MulAction.stabilizer (WeylGroup Tag.E6) γ).relIndex B ∣ 3 ^ k :=
    hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hle8 : (MulAction.stabilizer (WeylGroup Tag.E6) γ).relIndex B ≤ 8 := by
    have h1 : (MulAction.stabilizer (WeylGroup Tag.E6) γ).subgroupOf B =
        MulAction.stabilizer ↥B γ := by
      ext x
      simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rw [Subgroup.relIndex, h1, MulAction.index_stabilizer]
    calc (MulAction.orbit ↥B γ).ncard ≤ (T : Set (Fin Tag.E6.rank → ℤ)).ncard := by
          refine Set.ncard_le_ncard ?_ T.finite_toSet
          rintro _ ⟨⟨b, hb⟩, rfl⟩
          exact hBT b hb
      _ = T.card := Set.ncard_coe_finset T
      _ ≤ 8 := hT
  rw [hjeq] at hle8 ⊢
  have hj : j ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases j <;> norm_num

theorem exists_conj_le_Pw {B : Subgroup (WeylGroup Tag.E6)} (hB3 : ∀ b ∈ B, b ^ 3 = 1) :
    ∃ v : WeylGroup Tag.E6, ∀ b ∈ B, v⁻¹ * b * v ∈ Pw := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 Pw := IsPGroup.of_card (n := 4) (by rw [card_Pw]; norm_num)
  have hidx : ¬ 3 ∣ Pw.index := by
    have h := Subgroup.card_mul_index Pw
    rw [card_Pw, card_weylGroup_E6] at h
    have : Pw.index = 640 := by omega
    rw [this]
    norm_num
  let P0 : Sylow 3 (WeylGroup Tag.E6) := hP.toSylow hidx
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB3 g g.2)⟩
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) P0 Q
  refine ⟨g, fun b hb => ?_⟩
  have hbQ : b ∈ (Q : Subgroup (WeylGroup Tag.E6)) := hQ hb
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hbQ
  have : (MulAut.conj g)⁻¹ • b = g⁻¹ * b * g := by
    rw [MulAut.smul_def]
    simp
  rw [this] at hbQ
  exact hbQ

end Weyl

section Group

set_option linter.unusedSectionVars false

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.DiagTorus CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl
open scoped Pointwise

variable {K : Type} [Field K]


@[expose] noncomputable def Chat (K : Type) [Field K] : Subgroup (ModGL Tag.E6 K) :=
  Dgrp K ⊔ adjointGroup Tag.E6 K

@[expose] noncomputable def Nhat (K : Type) [Field K] : Subgroup (ModGL Tag.E6 K) :=
  Dgrp K ⊔ monomialSubgroup Tag.E6 K

theorem Nhat_le_Chat : Nhat K ≤ Chat K :=
  sup_le_sup_left monomialSubgroup_le_adjointGroup' _

theorem Chat_le_normalizer :
    Chat K ≤ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) :=
  sup_le Dgrp_le_normalizer_adjoint Subgroup.le_normalizer

theorem not_three_dvd_relIndex_Nhat [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (Nhat K).relIndex (Chat K) := by
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  by_cases hDC : Dgrp K ≤ adjointGroup Tag.E6 K
  · have hC : Chat K = adjointGroup Tag.E6 K := sup_eq_right.2 hDC
    have hle : Nhat K ≤ adjointGroup Tag.E6 K := hC ▸ Nhat_le_Chat
    have hmul := Subgroup.relIndex_mul_relIndex (monomialSubgroup Tag.E6 K) (Nhat K)
      (adjointGroup Tag.E6 K) le_sup_right hle
    rw [hC]
    intro h
    apply not_three_dvd_relIndex_monomial h3
    rw [← hmul]
    exact Dvd.dvd.mul_left h _
  · have hinf : Dgrp K ⊓ adjointGroup Tag.E6 K = Dgrp K ⊓ monomialSubgroup Tag.E6 K :=
      (inf_Dgrp_adjoint_eq h3 hDC).trans (inf_Dgrp_monomial_eq h3 hDC).symm
    rw [Nhat, Chat, DiagGroup.relIndex_sup_sup _ _ _ monomialSubgroup_le_adjointGroup'
      Dgrp_le_normalizer_adjoint Dgrp_le_normalizer_monomial hinf]
    exact not_three_dvd_relIndex_monomial h3

theorem exists_decomp_Nhat {g : ModGL Tag.E6 K} (hg : g ∈ Nhat K) :
    ∃ d ∈ Dgrp K, ∃ w : WeylGroup Tag.E6, g = d * canonicalRep (coxeterSystem Tag.E6) K w := by
  have h : g ∈ ((Dgrp K : Set (ModGL Tag.E6 K)) *
      (monomialSubgroup Tag.E6 K : Set (ModGL Tag.E6 K))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ Dgrp_le_normalizer_monomial]
    exact hg
  obtain ⟨d, hd, m, hm, rfl⟩ := h
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hm
  exact ⟨d * k, mul_mem hd (torusGroup_le_Dgrp hk), w, (mul_assoc _ _ _).symm⟩

theorem mapsRootLines_decomp [Finite K] {d : ModGL Tag.E6 K} (hd : d ∈ Dgrp K)
    (w : WeylGroup Tag.E6) :
    MapsRootLines ((d * canonicalRep (coxeterSystem Tag.E6) K w : ModGL Tag.E6 K) :
      (Module.End K (RootModule Tag.E6 K))ˣ) w := by
  have := (mapsRootLines_of_mem_Dgrp hd).mul (mapsRootLines_canonicalRep (R := K) w)
  rwa [one_mul] at this

theorem exists_mapsRootLines_Nhat [Finite K] {g : ModGL Tag.E6 K} (hg : g ∈ Nhat K) :
    ∃ w, MapsRootLines (g : (Module.End K (RootModule Tag.E6 K))ˣ) w := by
  obtain ⟨d, hd, w, rfl⟩ := exists_decomp_Nhat hg
  exact ⟨w, mapsRootLines_decomp hd w⟩

variable (K) in
@[expose] noncomputable def rhoHat [Finite K] : ↥(Nhat K) →* WeylGroup Tag.E6 where
  toFun g := (exists_mapsRootLines_Nhat g.2).choose
  map_one' := ((exists_mapsRootLines_Nhat (one_mem (Nhat K))).choose_spec).unique
    mapsRootLines_one
  map_mul' g h := ((exists_mapsRootLines_Nhat (g * h).2).choose_spec).unique
    ((exists_mapsRootLines_Nhat g.2).choose_spec.mul (exists_mapsRootLines_Nhat h.2).choose_spec)

theorem mapsRootLines_rhoHat [Finite K] (g : ↥(Nhat K)) :
    MapsRootLines ((g : ModGL Tag.E6 K) : (Module.End K (RootModule Tag.E6 K))ˣ) (rhoHat K g) :=
  (exists_mapsRootLines_Nhat g.2).choose_spec

theorem rhoHat_eq [Finite K] {g : ↥(Nhat K)} {w : WeylGroup Tag.E6}
    (h : MapsRootLines ((g : ModGL Tag.E6 K) : (Module.End K (RootModule Tag.E6 K))ˣ) w) :
    rhoHat K g = w :=
  (mapsRootLines_rhoHat g).unique h

theorem decomp_rhoHat [Finite K] (g : ↥(Nhat K)) :
    ∃ d ∈ Dgrp K,
      (g : ModGL Tag.E6 K) = d * canonicalRep (coxeterSystem Tag.E6) K (rhoHat K g) := by
  obtain ⟨d, hd, w, hw⟩ := exists_decomp_Nhat g.2
  have : rhoHat K g = w := rhoHat_eq (by rw [hw]; exact mapsRootLines_decomp hd w)
  exact ⟨d, hd, by rw [this]; exact hw⟩

theorem conj_mem_rootSubgroup [Finite K] (g : ↥(Nhat K)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (hw : rhoHat K g • β = β) {x : ModGL Tag.E6 K}
    (hx : x ∈ rootSubgroup Tag.E6 K β) :
    (g : ModGL Tag.E6 K) * x * (g : ModGL Tag.E6 K)⁻¹ ∈ rootSubgroup Tag.E6 K β := by
  obtain ⟨d, hd, hgd⟩ := decomp_rhoHat g
  set n := canonicalRep (coxeterSystem Tag.E6) K (rhoHat K g) with hn
  have h1 : n * x * n⁻¹ ∈ rootSubgroup Tag.E6 K β := by
    have h := (canonical_weyl_root_transport Tag.E6 K).2.1 (rhoHat K g) β hβ
    rw [hw] at h
    rw [← h]
    exact ⟨x, hx, rfl⟩
  obtain ⟨a, rfl⟩ := hd
  have h2 := map_conj_rootDiagUnit_rootSubgroup (K := K) a hβ
  rw [hgd]
  have e : rootDiagUnitHom Tag.E6 K a * n * x * (rootDiagUnitHom Tag.E6 K a * n)⁻¹ =
      rootDiagUnit Tag.E6 a * (n * x * n⁻¹) * (rootDiagUnit Tag.E6 a)⁻¹ := by
    rw [rootDiagUnitHom_apply]
    group
  rw [e, ← h2]
  exact ⟨_, h1, rfl⟩

theorem conj_mem_posUnipotent (a : Fin Tag.E6.rank → Kˣ) {u : ModGL Tag.E6 K}
    (hu : u ∈ posUnipotent Tag.E6 K) :
    rootDiagUnit Tag.E6 a * u * (rootDiagUnit Tag.E6 a)⁻¹ ∈ posUnipotent Tag.E6 K := by
  have hmap : (posUnipotent Tag.E6 K).map (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom =
      posUnipotent Tag.E6 K :=
    map_rootSpan_of_forall (fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1)
  rw [← hmap]
  exact ⟨u, hu, rfl⟩

theorem eq_one_of_commute [Finite K] (g : ↥(Nhat K))
    (hg : ∀ c ∈ adjointGroup Tag.E6 K, (g : ModGL Tag.E6 K) * c = c * g) : g = 1 := by
  obtain ⟨d, hd, hgd⟩ := decomp_rhoHat g
  set n := canonicalRep (coxeterSystem Tag.E6) K (rhoHat K g) with hn
  have hw : rhoHat K g = 1 := by
    apply eq_one_of_canonicalRep_conj_posUnipotent_le (K := K)
    intro u hu
    have huC : u ∈ adjointGroup Tag.E6 K := posUnipotent_le_adjointGroup hu
    have hgu : (g : ModGL Tag.E6 K) * u * (g : ModGL Tag.E6 K)⁻¹ = u := by
      rw [hg u huC]
      group
    have hnd : n = d⁻¹ * g := by
      rw [hgd]
      group
    have hconj : n * u * n⁻¹ = d⁻¹ * u * d⁻¹⁻¹ := by
      rw [hnd]
      calc d⁻¹ * ↑g * u * (d⁻¹ * ↑g)⁻¹ = d⁻¹ * (↑g * u * (↑g)⁻¹) * d⁻¹⁻¹ := by group
        _ = d⁻¹ * u * d⁻¹⁻¹ := by rw [hgu]
    rw [← hn, hconj]
    obtain ⟨a, ha⟩ := inv_mem hd
    have hmem := conj_mem_posUnipotent a hu
    rw [← rootDiagUnitHom_apply (K := K), ha] at hmem
    exact (le_sup_right : posUnipotent Tag.E6 K ≤ borelGroup Tag.E6 K) hmem
  have hgd' : (g : ModGL Tag.E6 K) = d := by
    rw [hgd, hn, hw, canonicalRep_one, mul_one]
  obtain ⟨a, ha⟩ := hd
  have haut : rootDiagAutHom Tag.E6 K a = rootDiagAutHom Tag.E6 K 1 := by
    rw [map_one]
    refine MulEquiv.ext fun c => Subtype.ext ?_
    change ((rootDiagAut Tag.E6 K a c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = c
    rw [coe_rootDiagAut, ← rootDiagUnitHom_apply (K := K), ha, ← hgd', hg c c.2]
    group
  have ha1 : a = 1 := rootDiagAutHom_injective haut
  apply Subtype.ext
  rw [hgd', ← ha, ha1, map_one]
  rfl

theorem core [Finite K] {P₁ : Subgroup (ModGL Tag.E6 K)} (hP₁ : P₁ ≤ Nhat K)
    (hel : IsElemAbelian 3 P₁) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ ∃ E₁ : Subgroup (ModGL Tag.E6 K), E₁ ≤ P₁ ∧
      Nat.card P₁ ≤ 3 * Nat.card E₁ ∧
      ∀ x ∈ E₁, ∀ y ∈ rootSubgroup Tag.E6 K γ, x * y * x⁻¹ ∈ rootSubgroup Tag.E6 K γ := by
  classical
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  let f : ↥P₁ →* WeylGroup Tag.E6 := (rhoHat K).comp (Subgroup.inclusion hP₁)
  have hf3 : ∀ b ∈ f.range, b ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hel.2 x x.2)
    rw [this, map_one]
  have hfc : ∀ b ∈ f.range, ∀ b' ∈ f.range, b * b' = b' * b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, hel.1.is_comm.comm x y]
  have hrange : IsElemAbelian 3 f.range :=
    ⟨⟨⟨fun a b => Subtype.ext (hfc a a.2 b b.2)⟩⟩, hf3⟩
  obtain ⟨v, hv⟩ := exists_conj_le_Pw hf3
  set B₂ : Subgroup (WeylGroup Tag.E6) := f.range.map (MulAut.conj v⁻¹).toMonoidHom with hB₂
  have hB₂P : B₂ ≤ Pw := by
    rintro _ ⟨b, hb, rfl⟩
    have := hv b hb
    simpa [MulAut.conj_apply] using this
  obtain ⟨β, hβ, T, hT, hBT⟩ := exists_root_orbit_subset hB₂P (hrange.map _)
  set γ : Fin Tag.E6.rank → ℤ := v • β with hγdef
  have hγ : IsRoot Tag.E6 γ := IsRoot.smul hβ v
  have hT' : (T.image (fun t => v • t)).card ≤ 8 := Finset.card_image_le.trans hT
  have hBT' : ∀ b ∈ f.range, b • γ ∈ T.image (fun t => v • t) := by
    intro b hb
    have h1 : v⁻¹ * b * v ∈ B₂ := ⟨b, hb, by simp [MulAut.conj_apply]⟩
    refine Finset.mem_image.2 ⟨(v⁻¹ * b * v) • β, hBT _ h1, ?_⟩
    rw [hγdef, smul_smul, smul_smul]
    congr 1
    group
  have hidx := relIndex_stabilizer_le_three hf3 hT' hBT'
  set E₁' : Subgroup ↥P₁ := (MulAction.stabilizer (WeylGroup Tag.E6) γ).comap f with hE₁'
  have hE₁'idx : E₁'.index ≤ 3 := by
    rw [hE₁', Subgroup.index_comap]
    exact hidx
  refine ⟨γ, hγ, E₁'.map P₁.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 := Subgroup.card_mul_index E₁'
    have h2 : Nat.card (E₁'.map P₁.subtype) = Nat.card E₁' :=
      Subgroup.card_map_of_injective P₁.subtype_injective
    rw [h2, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ hE₁'idx
  · rintro _ ⟨x, hx, rfl⟩ y hy
    have hfx : rhoHat K ⟨(x : ModGL Tag.E6 K), hP₁ x.2⟩ • γ = γ := hx
    exact conj_mem_rootSubgroup ⟨_, hP₁ x.2⟩ hγ hfx hy

variable (K) in
@[expose] noncomputable def Phi : ↥(Chat K) →* MulAut ↥(adjointGroup Tag.E6 K) :=
  (adjointGroup Tag.E6 K).normalizerMonoidHom.comp (Subgroup.inclusion Chat_le_normalizer)

theorem coe_Phi_apply (x : ↥(Chat K)) (c : ↥(adjointGroup Tag.E6 K)) :
    ((Phi K x c : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      (x : ModGL Tag.E6 K) * c * (x : ModGL Tag.E6 K)⁻¹ :=
  rfl

theorem exists_Phi_eq [Finite K] (hK : Nat.card K = 4) (α : MulAut ↥(adjointGroup Tag.E6 K))
    (hα : α ^ 3 = 1) : ∃ x : ↥(Chat K), Phi K x = α := by
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hΘ : Θ α = 1 := by
    have h3 : Θ α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
    have hcardR : Nat.card (RingAut K) = 2 :=
      (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.ringAut_card_and_cyclic (F := K)
        (n := 2) (by rw [hK]; norm_num)).1
    have hcardE : Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      simp [exactE]
    have hcard : Nat.card (RingAut K × Multiplicative (ZMod (exactE Tag.E6))) = 4 := by
      rw [Nat.card_prod, hcardR, hcardE]
    haveI : Finite (RingAut K × Multiplicative (ZMod (exactE Tag.E6))) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have h4 : orderOf (Θ α) ∣ 4 := hcard ▸ orderOf_dvd_natCard _
    have h3' : orderOf (Θ α) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h1 : orderOf (Θ α) = 1 := Nat.dvd_one.1 (by simpa using Nat.dvd_gcd h3' h4)
    exact orderOf_eq_one_iff.1 h1
  obtain ⟨g, a, hga⟩ := (hker α).1 (MonoidHom.mem_ker.2 hΘ)
  refine ⟨⟨(g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a,
    mul_mem (Subgroup.mem_sup_right g.2) (Subgroup.mem_sup_left (rootDiagUnit_mem_Dgrp a))⟩, ?_⟩
  refine MulEquiv.ext fun c => Subtype.ext ?_
  rw [coe_Phi_apply, hga c]
  group

theorem rootSubgroup_sq_eq_one [CharP K 2] {γ : Fin Tag.E6.rank → ℤ} {x : ModGL Tag.E6 K}
    (hx : x ∈ rootSubgroup Tag.E6 K γ) : x ^ 2 = 1 := by
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hx
  have h2 : t + t = 0 := by
    rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
  rw [sq, ← pinnedX_add, h2, pinnedX_zero]

theorem model_main [Finite K] (hK : Nat.card K = 4)
    (A' : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))) (hA : IsElemAbelian 3 A') :
    ∃ E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)), E ≤ A' ∧ Nat.card A' ≤ 3 * Nat.card E ∧
      ∃ U : Subgroup ↥(adjointGroup Tag.E6 K), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
        ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  classical
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := charP_two_of_card_four K hK
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]
  set X : Subgroup ↥(Chat K) := A'.comap (Phi K) with hX
  let f : ↥X →* ↥A' := ((Phi K).comp X.subtype).codRestrict A' (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨α, hα⟩
    obtain ⟨x, hx⟩ := exists_Phi_eq hK α (hA.2 α hα)
    refine ⟨⟨x, show Phi K x ∈ A' by rw [hx]; exact hα⟩, Subtype.ext ?_⟩
    exact hx
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥X) := inferInstance
  have hA3 : IsPGroup 3 ↥A' := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have htop : (Q.mapSurjective hf : Subgroup ↥A') = ⊤ :=
    ((Q.mapSurjective hf).is_maximal' (hA3.to_subgroup ⊤) le_top).symm
  set P : Subgroup ↥(Chat K) := (Q : Subgroup ↥X).map X.subtype with hP
  have hPp : IsPGroup 3 ↥P := Q.isPGroup'.map X.subtype
  have hPA : ∀ p ∈ P, Phi K p ∈ A' := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hPsurj : ∀ α ∈ A', ∃ p ∈ P, Phi K p = α := by
    intro α hα
    have hmem : (⟨α, hα⟩ : ↥A') ∈ (Q.mapSurjective hf : Subgroup ↥A') := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨x, hx, hxα⟩ := Subgroup.mem_map.1 hmem
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxα⟩
  set PG : Subgroup (ModGL Tag.E6 K) := P.map (Chat K).subtype with hPG
  have hPGle : PG ≤ Chat K := Subgroup.map_subtype_le P
  have hPGp : IsPGroup 3 ↥PG := hPp.map _
  obtain ⟨u, huA, hu⟩ := exists_conj_le_of_not_dvd hPGle hPGp (not_three_dvd_relIndex_Nhat h3)
  set uC : ↥(Chat K) := ⟨u, huA⟩ with huC
  have hinj : ∀ p ∈ P, Phi K p = 1 → p = 1 := by
    intro p hp hΦ
    have hpN : u⁻¹ * (p : ModGL Tag.E6 K) * u ∈ Nhat K := hu _ ⟨p, hp, rfl⟩
    have hcomm : ∀ c ∈ adjointGroup Tag.E6 K,
        (u⁻¹ * (p : ModGL Tag.E6 K) * u) * c = c * (u⁻¹ * (p : ModGL Tag.E6 K) * u) := by
      intro c hc
      have hc' : u * c * u⁻¹ ∈ adjointGroup Tag.E6 K :=
        (Subgroup.mem_normalizer_iff.1 (Chat_le_normalizer huA) c).1 hc
      have h1 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.E6 K) =>
        ((φ ⟨u * c * u⁻¹, hc'⟩ : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K)) hΦ
      simp only [coe_Phi_apply, MulAut.one_apply] at h1
      calc u⁻¹ * (p : ModGL Tag.E6 K) * u * c =
          u⁻¹ * ((p : ModGL Tag.E6 K) * (u * c * u⁻¹) * (p : ModGL Tag.E6 K)⁻¹) *
            (p : ModGL Tag.E6 K) * u := by group
        _ = u⁻¹ * (u * c * u⁻¹) * (p : ModGL Tag.E6 K) * u := by rw [h1]
        _ = c * (u⁻¹ * (p : ModGL Tag.E6 K) * u) := by group
    have h1 := eq_one_of_commute ⟨_, hpN⟩ hcomm
    have h2 : u⁻¹ * (p : ModGL Tag.E6 K) * u = 1 := congrArg Subtype.val h1
    apply Subtype.ext
    calc (p : ModGL Tag.E6 K) = u * (u⁻¹ * (p : ModGL Tag.E6 K) * u) * u⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
    intro p hp q hq
    have hc : Phi K p * Phi K q = Phi K q * Phi K p :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hPA p hp⟩ ⟨_, hPA q hq⟩)
    have h1 : Phi K (p * q * p⁻¹ * q⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h2 := hinj _ (mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)) h1
    calc p * q = (p * q * p⁻¹ * q⁻¹) * q * p := by group
      _ = q * p := by rw [h2]; group
  have hPcube : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    refine hinj _ (pow_mem hp 3) ?_
    rw [map_pow]
    exact hA.2 _ (hPA p hp)
  set P₁ : Subgroup (ModGL Tag.E6 K) := PG.map (MulAut.conj u⁻¹).toMonoidHom with hP₁
  have hP₁N : P₁ ≤ Nhat K := by
    rintro _ ⟨x, hx, rfl⟩
    have := hu x hx
    simpa [MulAut.conj_apply] using this
  have hP₁el : IsElemAbelian 3 P₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨p, hp, rfl⟩, hpa⟩ := a.2
      obtain ⟨_, ⟨q, hq, rfl⟩, hqb⟩ := b.2
      change (a : ModGL Tag.E6 K) * b = b * a
      rw [← hpa, ← hqb]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      have hpq := congrArg Subtype.val (hPcomm p hp q hq)
      simp only [Subgroup.coe_mul] at hpq
      calc u⁻¹ * (p : ModGL Tag.E6 K) * u⁻¹⁻¹ * (u⁻¹ * (q : ModGL Tag.E6 K) * u⁻¹⁻¹) =
          u⁻¹ * ((p : ModGL Tag.E6 K) * q) * u := by group
        _ = u⁻¹ * ((q : ModGL Tag.E6 K) * p) * u := by rw [hpq]
        _ = u⁻¹ * (q : ModGL Tag.E6 K) * u⁻¹⁻¹ * (u⁻¹ * (p : ModGL Tag.E6 K) * u⁻¹⁻¹) := by group
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have h1 : (p : ModGL Tag.E6 K) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hPcube p hp, Subgroup.coe_one]
      rw [← map_pow]
      simp [h1]
  obtain ⟨γ, hγ, E₁, hE₁P, hcard₁, hE₁U⟩ := core hP₁N hP₁el
  set E_P : Subgroup ↥(Chat K) := (E₁.map (MulAut.conj u).toMonoidHom).comap (Chat K).subtype
    with hE_P
  have hE_P_le : E_P ≤ P := by
    intro p hp
    obtain ⟨x, hx, hxp⟩ := hp
    obtain ⟨y, ⟨q, hq, rfl⟩, hyx⟩ := hE₁P hx
    have e1 : u * x * u⁻¹ = (p : ModGL Tag.E6 K) := hxp
    have e2 : u⁻¹ * (q : ModGL Tag.E6 K) * u⁻¹⁻¹ = x := hyx
    have : p = q := by
      apply Subtype.ext
      rw [← e1, ← e2]
      group
    rw [this]
    exact hq
  refine ⟨E_P.map (Phi K), ?_, ?_, ((rootSubgroup Tag.E6 K γ).subgroupOf
    (adjointGroup Tag.E6 K)).map (Phi K uC).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hPA p (hE_P_le hp)
  ·
    have c1 : Nat.card A' ≤ Nat.card P := by
      refine Nat.card_le_card_of_surjective (fun p : ↥P => (⟨Phi K p, hPA p p.2⟩ : ↥A')) ?_
      rintro ⟨α, hα⟩
      obtain ⟨p, hp, hpα⟩ := hPsurj α hα
      exact ⟨⟨p, hp⟩, Subtype.ext hpα⟩
    have c2 : Nat.card P = Nat.card P₁ := by
      rw [hP₁, Subgroup.card_map_of_injective (f := (MulAut.conj u⁻¹).toMonoidHom)
        (MulAut.conj u⁻¹).injective, hPG,
        Subgroup.card_map_of_injective (f := (Chat K).subtype) (Chat K).subtype_injective]
    have c3 : Nat.card E_P = Nat.card E₁ := by
      have hle : E₁.map (MulAut.conj u).toMonoidHom ≤ Chat K := by
        rintro _ ⟨x, hx, rfl⟩
        have hxC : x ∈ Chat K := Nhat_le_Chat (hP₁N (hE₁P hx))
        exact mul_mem (mul_mem huA hxC) (inv_mem huA)
      rw [hE_P, ← Subgroup.card_map_of_injective (f := (MulAut.conj u).toMonoidHom)
        (MulAut.conj u).injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have c4 : Nat.card E_P ≤ Nat.card (E_P.map (Phi K)) := by
      refine Nat.card_le_card_of_injective
        (fun p : ↥E_P => (⟨Phi K p, ⟨p, p.2, rfl⟩⟩ : ↥(E_P.map (Phi K)))) ?_
      intro p q hpq
      have h1 : Phi K p = Phi K q := congrArg Subtype.val hpq
      have h2 : Phi K ((p : ↥(Chat K)) * (q : ↥(Chat K))⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := hinj _ (mul_mem (hE_P_le p.2) (inv_mem (hE_P_le q.2))) h2
      exact Subtype.ext (mul_inv_eq_one.1 h3)
    calc Nat.card A' ≤ Nat.card P₁ := c2 ▸ c1
      _ ≤ 3 * Nat.card E₁ := hcard₁
      _ = 3 * Nat.card E_P := by rw [c3]
      _ ≤ 3 * Nat.card (E_P.map (Phi K)) := Nat.mul_le_mul_left _ c4
  ·
    intro hbot
    have hx1 : pinnedX Tag.E6 K γ 1 ∈ adjointGroup Tag.E6 K := pinnedX_mem_adjointGroup γ 1
    have hxU : (⟨pinnedX Tag.E6 K γ 1, hx1⟩ : ↥(adjointGroup Tag.E6 K)) ∈
        (rootSubgroup Tag.E6 K γ).subgroupOf (adjointGroup Tag.E6 K) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨1, rfl⟩)
    have hmem := Subgroup.mem_map_of_mem (Phi K uC).toMonoidHom hxU
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 : (⟨pinnedX Tag.E6 K γ 1, hx1⟩ : ↥(adjointGroup Tag.E6 K)) = 1 :=
      (Phi K uC).injective (hmem.trans (map_one (Phi K uC)).symm)
    have h3 : pinnedX Tag.E6 K γ 1 = pinnedX Tag.E6 K γ 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h2
    exact one_ne_zero (pinnedX_injective Tag.E6 K γ h3)
  ·
    refine IsPGroup.map (fun c => ⟨1, ?_⟩) _
    have hc : ((c : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) ∈ rootSubgroup Tag.E6 K γ :=
      Subgroup.mem_subgroupOf.1 c.2
    have h2 := rootSubgroup_sq_eq_one hc
    apply Subtype.ext
    apply Subtype.ext
    simpa using h2
  ·
    rintro _ ⟨p, hp, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨x, hx, hxp⟩ := hp
    have hxC : x ∈ Chat K := Nhat_le_Chat (hP₁N (hE₁P hx))
    set xC : ↥(Chat K) := ⟨x, hxC⟩ with hxC'
    have e1 : u * x * u⁻¹ = (p : ModGL Tag.E6 K) := hxp
    have hpx : p = uC * xC * uC⁻¹ := by
      apply Subtype.ext
      exact e1.symm
    have hcU : ((c : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) ∈ rootSubgroup Tag.E6 K γ :=
      Subgroup.mem_subgroupOf.1 hc
    refine ⟨Phi K xC c, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · rw [coe_Phi_apply]
      exact hE₁U x hx _ hcU
    · simp only [MulEquiv.coe_toMonoidHom]
      rw [hpx, map_mul, map_mul, map_inv]
      simp [MulAut.mul_apply]

end Group

end Gen2318E64InAux

section Main

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem gen2318E64Core_holds : Gen2318E64Core := by
  intro S _ _ d hd hiso A hA hrank
  obtain ⟨eL⟩ := hiso
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | E6 q =>
    obtain ⟨hq1, hq2⟩ := hd
    have hK4 : Nat.card (GaloisField 2 2) = TauCeti.PrimePower.card q := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card 2 2 (by norm_num), hq1, hq2]
    obtain ⟨eB⟩ :=
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq1 (GaloisField 2 2) hK4
    let eZ : AdjointQuotient Tag.E6 (GaloisField 2 2) ≃*
        ↥(adjointGroup Tag.E6 (GaloisField 2 2)) :=
      (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := Tag.E6) (K := GaloisField 2 2))).trans
        QuotientGroup.quotientBot
    let eS : S ≃* ↥(adjointGroup Tag.E6 (GaloisField 2 2)) := eL.trans (eB.symm.trans eZ)
    have hF : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    set e := MulAut.congr eS with he
    obtain ⟨E', hE'A', hcard, U', hU'0, hU'2, hU'⟩ :=
      Gen2318E64InAux.model_main hF (A.map e.toMonoidHom) (hA.map _)
    have hEA : E'.map e.symm.toMonoidHom ≤ A := by
      rintro _ ⟨φ', hφ', rfl⟩
      obtain ⟨ψ, hψ, rfl⟩ := hE'A' hφ'
      simpa using hψ
    refine ⟨E'.map e.symm.toMonoidHom, hEA, ?_, U'.map eS.symm.toMonoidHom, ?_, hU'2.map _, ?_⟩
    · obtain ⟨r, hr⟩ := i271_exists_card_eq Nat.prime_three hA
      have hrr : CFSG.Open.pRank 3 A = r := i271_pRank_eq Nat.prime_three hA hr
      have hEel : IsElemAbelian 3 (E'.map e.symm.toMonoidHom) := i271_isElemAbelian_of_le hA hEA
      obtain ⟨m, hm⟩ := i271_exists_card_eq Nat.prime_three hEel
      rw [i271_pRank_eq Nat.prime_three hEel hm]
      have hcA : Nat.card (A.map e.toMonoidHom) = 3 ^ r := by
        rw [Subgroup.card_map_of_injective e.injective, hr]
      have hcE : Nat.card E' = 3 ^ m := by
        rw [← hm, Subgroup.card_map_of_injective e.symm.injective]
      rw [hcA, hcE] at hcard
      have hrm : r ≤ m + 1 := by
        have h' : 3 ^ r ≤ 3 ^ (m + 1) := by
          rw [pow_succ]
          linarith
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h'
      omega
    · intro h
      exact hU'0 ((Subgroup.map_eq_bot_iff_of_injective U' (f := eS.symm.toMonoidHom)
        eS.symm.injective).1 h)
    · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨u', hu', rfl⟩
      refine ⟨φ' u', hU' φ' hφ' u' hu', ?_⟩
      simp [he, MulAut.congr_apply]
  | _ => exact absurd hd (by simp [IsE6FourIndex])

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
