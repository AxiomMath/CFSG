module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6JBound
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.AGLEmbedding.R3 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent.DiagTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.SporadicRank CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.LieType.Steinberg.Isogeny CFSG.Open CFSG.SectionRank
  CFSG.Timmesfeld.ExceptionalOrders
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Matrix Pointwise

instance instFiniteHopfCover (R : Type) [Group R] [Finite R] [Group.IsPerfect R] :
    Finite (CFSG.RankThree.PerfectCover.HopfCover R) :=
  CFSG.RankThree.PerfectCover.finite_hopfCover (X := R) inferInstance


@[expose] def e6FixPairCheck (_ : Unit := ()) : Bool :=
  let O := (e6SylL ()).filter isO3L
  O.all fun A =>
    let fa := (allVecs 3 6).filter fun v => matVecA6 A.toArray v == v
    O.all fun B =>
      (A == B || B == mmulL 3 6 A A || mmulL 3 6 A B != mmulL 3 6 B A) ||
        decide ((fa.filter fun v => matVecA6 B.toArray v == v).length ≤ 9)

theorem e6FixPairCheck_true : e6FixPairCheck () = true := by decide +kernel

theorem e6FixPairCheck_spec {A B : List ℕ} (hA : A ∈ (e6SylL ()).filter isO3L)
    (hB : B ∈ (e6SylL ()).filter isO3L) (hAB : A ≠ B) (hAB2 : B ≠ mmulL 3 6 A A)
    (hc : mmulL 3 6 A B = mmulL 3 6 B A) :
    (((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).filter
      fun v => matVecA6 B.toArray v == v).length ≤ 9 := by
  have h := e6FixPairCheck_true
  simp only [e6FixPairCheck, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq,
    decide_eq_true_eq] at h
  have h1 := h A hA B hB
  simp only [beq_iff_eq, bne_iff_ne, hc, ne_eq, not_false_eq_true, hAB, hAB2, false_or,
    not_true_eq_false, or_false, decide_eq_true_eq] at h1
  exact h1

theorem card_inter_fixMat6_le (A B : List ℕ) :
    Nat.card ↥(fixMat6 (toMatL 3 6 A) ∩ fixMat6 (toMatL 3 6 B)) ≤
      (((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).filter
        fun v => matVecA6 B.toArray v == v).length := by
  classical
  have hsub : vecList6 '' (fixMat6 (toMatL 3 6 A) ∩ fixMat6 (toMatL 3 6 B)) ⊆
      ((((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).filter
        fun v => matVecA6 B.toArray v == v).toFinset : Set (List ℕ)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvA : v ∈ fixMat6 (toMatL 3 6 A) := hv.1
    have hvB : v ∈ fixMat6 (toMatL 3 6 B) := hv.2
    have key : ∀ {M : List ℕ}, v ∈ fixMat6 (toMatL 3 6 M) →
        matVecA6 M.toArray (vecList6 v) = vecList6 v := by
      intro M hM
      rw [matVecA6_toArray]
      have hm : matVecL 3 6 M (vecList6 v) ∈ allVecs 3 6 :=
        (mem_allVecs 3 6 _).2 ⟨length_matVecL 3 6 M _, lt_matVecL (by norm_num) 6 M _⟩
      have h2 : vecOf 3 6 (matVecL 3 6 M (vecList6 v)) = vecOf 3 6 (vecList6 v) := by
        rw [vecOf_matVecL, vecOf_vecList6]
        exact hM
      exact vecOf_inj hm (vecList6_mem v) h2
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_filter, beq_iff_eq]
    exact ⟨⟨vecList6_mem v, key hvA⟩, key hvB⟩
  calc Nat.card ↥(fixMat6 (toMatL 3 6 A) ∩ fixMat6 (toMatL 3 6 B))
      = Nat.card (vecList6 '' (fixMat6 (toMatL 3 6 A) ∩ fixMat6 (toMatL 3 6 B))) :=
        (Nat.card_image_of_injective vecList6_injective _).symm
    _ ≤ Nat.card ((((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).filter
          fun v => matVecA6 B.toArray v == v).toFinset : Set (List ℕ)) :=
        Nat.card_mono (Finset.finite_toSet _) hsub
    _ = ((((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).filter
          fun v => matVecA6 B.toArray v == v).toFinset).card :=
        Nat.card_coe_set_eq _ |>.trans (Set.ncard_coe_finset _)
    _ ≤ _ := List.toFinset_card_le _

theorem card_fixMat6_inter_le_nine {w w' : WeylGroup Tag.E6} (hw : w ∈ e6Syl)
    (hw' : w' ∈ e6Syl) (hw1 : w ≠ 1) (hw1' : w' ≠ 1) (h1 : w ^ 3 = 1) (h1' : w' ^ 3 = 1)
    (hne : w' ≠ w) (hne2 : w' ≠ w ^ 2) (hc : w * w' = w' * w) :
    Nat.card ↥(fixMat6 (e6WeylMat w) ∩ fixMat6 (e6WeylMat w')) ≤ 9 := by
  obtain ⟨A, hA, hAM, hOA⟩ := exists_isO3L hw hw1 h1
  obtain ⟨B, hB, hBM, hOB⟩ := exists_isO3L hw' hw1' h1'
  have hA' : A ∈ (e6SylL ()).filter isO3L := List.mem_filter.2 ⟨hA, hOA⟩
  have hB' : B ∈ (e6SylL ()).filter isO3L := List.mem_filter.2 ⟨hB, hOB⟩
  have hAB : A ≠ B := fun h => hne (e6WeylMat_injective (by rw [← hBM, ← h, hAM]))
  have hAB2 : B ≠ mmulL 3 6 A A := by
    intro h
    exact hne2 (e6WeylMat_injective (by rw [← hBM, h, toMatL_mmulL, hAM, ← map_mul, ← pow_two]))
  have hcAB : mmulL 3 6 A B = mmulL 3 6 B A := by
    apply toMatL_inj6 (mmulL_spec _ _) (mmulL_spec _ _)
    rw [toMatL_mmulL, toMatL_mmulL, hAM, hBM, ← map_mul, ← map_mul, hc]
  have hspec := e6FixPairCheck_spec hA' hB' hAB hAB2 hcAB
  calc Nat.card ↥(fixMat6 (e6WeylMat w) ∩ fixMat6 (e6WeylMat w'))
      = Nat.card ↥(fixMat6 (toMatL 3 6 A) ∩ fixMat6 (toMatL 3 6 B)) := by
          rw [← hAM, ← hBM]
    _ ≤ _ := card_inter_fixMat6_le A B
    _ ≤ 9 := hspec

theorem card_e6Fix_le_nine_of_le (F : Subgroup (WeylGroup Tag.E6)) (hF : IsElemAbelian 3 F)
    (hFP : F ≤ e6Syl) (h9 : 9 ≤ Nat.card F) : Nat.card (e6Fix F) ≤ 9 := by
  classical
  haveI : Fintype F := Fintype.ofFinite _
  have hone : 1 < Nat.card F := by omega
  obtain ⟨x, hx⟩ : ∃ x : F, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 fun y hy => by
      have := congrArg Subtype.val (hcon ⟨y, hy⟩)
      simpa using this
    rw [hbot, Subgroup.card_bot] at hone
    exact absurd hone (by norm_num)
  have hxne : (x : WeylGroup Tag.E6) ≠ 1 := fun h => hx (Subtype.ext h)
  have hx3 : (x : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (x : WeylGroup Tag.E6) x.2
  have hnotle : ¬ F ≤ Subgroup.zpowers (x : WeylGroup Tag.E6) := by
    intro hle
    have hdvd : Nat.card F ∣ Nat.card (Subgroup.zpowers (x : WeylGroup Tag.E6)) :=
      Subgroup.card_dvd_of_le hle
    have hzcard : Nat.card (Subgroup.zpowers (x : WeylGroup Tag.E6)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
    rw [hzcard] at hdvd
    have hle3 : Nat.card F ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨y, hyF, hyz⟩ : ∃ y ∈ F, (y : WeylGroup Tag.E6) ∉ Subgroup.zpowers (x : WeylGroup Tag.E6) := by
    by_contra hcon
    push Not at hcon
    exact hnotle fun z hz => hcon z hz
  have hyne : (y : WeylGroup Tag.E6) ≠ 1 := fun h =>
    (h ▸ hyz) (Subgroup.one_mem _)
  have hyne' : (y : WeylGroup Tag.E6) ≠ (x : WeylGroup Tag.E6) :=
    fun h => (h ▸ hyz) (Subgroup.mem_zpowers _)
  have hyne2 : (y : WeylGroup Tag.E6) ≠ (x : WeylGroup Tag.E6) ^ 2 :=
    fun h => (h ▸ hyz) ((Subgroup.zpowers (x : WeylGroup Tag.E6)).pow_mem
      (Subgroup.mem_zpowers _) 2)
  have hc : (x : WeylGroup Tag.E6) * (y : WeylGroup Tag.E6) =
      (y : WeylGroup Tag.E6) * (x : WeylGroup Tag.E6) :=
    congrArg Subtype.val (hF.1.is_comm.comm x ⟨y, hyF⟩)
  have hy3 : (y : WeylGroup Tag.E6) ^ 3 = 1 := hF.2 (y : WeylGroup Tag.E6) hyF
  have hsub : e6Fix F ⊆ fixMat6 (e6WeylMat (x : WeylGroup Tag.E6)) ∩
      fixMat6 (e6WeylMat (y : WeylGroup Tag.E6)) := by
    intro v hv
    exact ⟨hv x x.2, hv y hyF⟩
  calc Nat.card (e6Fix F) ≤ Nat.card ↥(fixMat6 (e6WeylMat (x : WeylGroup Tag.E6)) ∩
        fixMat6 (e6WeylMat (y : WeylGroup Tag.E6))) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ 9 := card_fixMat6_inter_le_nine (hFP x.2) (hFP hyF) hxne hyne hx3 hy3 hyne' hyne2 hc

private theorem isElemAbelian_map' {G H : Type*} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} (f : G →* H) (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨?_, ?_⟩
  · haveI := hE.1
    infer_instance
  · rintro y ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem card_e6Fix_mul_card_le_of_ne_bot (F : Subgroup (WeylGroup Tag.E6))
    (hF : IsElemAbelian 3 F) (hne : F ≠ ⊥) :
    Nat.card (e6Fix F) * Nat.card F ≤ 3 ^ 5 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 F := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hF.2 g g.2)⟩
  obtain ⟨Q, hFQ⟩ := hp.exists_le_sylow
  let P : Sylow 3 (WeylGroup Tag.E6) := Sylow.ofCard e6Syl
    (by rw [card_e6Syl, card_weylGroup_E6', factorization_51840]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) Q P
  have hle : F.map (MulAut.conj g).toMonoidHom ≤ e6Syl := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj g) • x ∈ (MulAut.conj g) • (Q : Subgroup (WeylGroup Tag.E6)) :=
      Subgroup.smul_mem_pointwise_smul x _ _ (hFQ hx)
    rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard] at h1
    exact h1
  have hF' : IsElemAbelian 3 (F.map (MulAut.conj g).toMonoidHom) :=
    isElemAbelian_map' (MulAut.conj g).toMonoidHom hF
  have hne' : F.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have h1 : (MulAut.conj g) x ∈ F.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot] at h1
    exact (MulAut.conj g).injective (by simpa using h1)
  have hmain : Nat.card (e6Fix (F.map (MulAut.conj g).toMonoidHom)) *
      Nat.card (F.map (MulAut.conj g).toMonoidHom) ≤ 3 ^ 5 := by
    obtain ⟨k, hk⟩ := exists_card_pow_of_isElemAbelian hF'
    have hdvd : 3 ^ k ∣ 3 ^ 4 := by
      rw [← hk]
      have := Subgroup.card_dvd_of_le hle
      rwa [card_e6Syl] at this
    have hk4 : k ≤ 4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · exfalso
        apply hne'
        exact Subgroup.card_eq_one.1 (by rw [hk, h0, pow_zero])
      · exact h
    have hnt : ∃ w ∈ F.map (MulAut.conj g).toMonoidHom, w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne' (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
    interval_cases k
    ·
      obtain ⟨w, hw, h1⟩ := hnt
      have hle81 : Nat.card (e6Fix (F.map (MulAut.conj g).toMonoidHom)) ≤ 81 := by
        have hsub : e6Fix (F.map (MulAut.conj g).toMonoidHom) ⊆ fixMat6 (e6WeylMat w) :=
          fun v hv => hv w hw
        exact (Nat.card_mono (Set.toFinite _) hsub).trans
          (card_fixMat6_le_81 (hle hw) h1 (hF'.2 w hw))
      rw [hk]
      exact (Nat.mul_le_mul_right _ hle81).trans (by norm_num)
    ·
      have h9 : Nat.card (e6Fix (F.map (MulAut.conj g).toMonoidHom)) ≤ 9 :=
        card_e6Fix_le_nine_of_le _ hF' hle (by rw [hk]; norm_num)
      rw [hk]
      exact (Nat.mul_le_mul_right _ h9).trans (by norm_num)
    ·
      have h9 : Nat.card (e6Fix (F.map (MulAut.conj g).toMonoidHom)) ≤ 9 :=
        card_e6Fix_le_nine_of_le _ hF' hle (by rw [hk]; norm_num)
      rw [hk]
      exact (Nat.mul_le_mul_right _ h9).trans (by norm_num)
    ·
      exfalso
      have hFeq : F.map (MulAut.conj g).toMonoidHom = e6Syl :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [card_e6Syl, hk]; norm_num)
      have ht := wordProd_mem_e6Syl 0 (by norm_num)
      have hc := wordProd_mem_e6Syl 1 (by norm_num)
      rw [← hFeq] at ht hc
      have hcomm := congrArg Subtype.val (hF'.1.is_comm.comm ⟨_, ht⟩ ⟨_, hc⟩)
      simp only [Subgroup.coe_mul] at hcomm
      have hM := congrArg e6WeylMat hcomm
      rw [map_mul, map_mul, e6WeylMat_wordProd, e6WeylMat_wordProd, e6SylWordsF_getD_val 0
        (by norm_num), e6SylWordsF_getD_val 1 (by norm_num), ← toMatL_mmulL, ← toMatL_mmulL] at hM
      exact e6SylFacts.noncomm (toMatL_inj6 (mmulL_spec _ _) (mmulL_spec _ _) hM)
  rwa [card_e6Fix_map_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective] at hmain

section E6Sc


variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def e6ScH (K : Type) [Field K] [Finite K] :
    Subgroup ↥(e6Data_valid.minGroup K) :=
  Subgroup.comap (e6Isogeny K) ((torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K))

@[expose] noncomputable def e6ScN (K : Type) [Field K] [Finite K] :
    Subgroup ↥(e6Data_valid.minGroup K) :=
  Subgroup.comap (e6Isogeny K)
    ((monomialSubgroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K))

@[expose] noncomputable def e6ScNTomono (K : Type) [Field K] [Finite K] :
    e6ScN K →* monomialSubgroup Tag.E6 K :=
  MonoidHom.codRestrict
    (((adjointGroup Tag.E6 K).subtype).comp ((e6Isogeny K).comp (e6ScN K).subtype))
    (monomialSubgroup Tag.E6 K) fun n => (Subgroup.mem_subgroupOf).1 n.2

@[expose] noncomputable def e6ScMono (n : e6ScN K) : monomialSubgroup Tag.E6 K :=
  ⟨(((e6Isogeny K (n : ↥(e6Data_valid.minGroup K))) : ↥(adjointGroup Tag.E6 K)) :
    ModGL Tag.E6 K), (Subgroup.mem_subgroupOf).1 n.2⟩

@[expose] noncomputable def e6ScPhi (K : Type) [Field K] [Finite K] :
    e6ScN K →* WeylGroup Tag.E6 :=
  (weylQuotientHom Tag.E6 K).comp (e6ScNTomono K)

theorem e6ScPhi_apply (n : e6ScN K) :
    e6ScPhi K n = weylQuotientHom Tag.E6 K (e6ScMono n) := rfl

theorem e6ScPhi_eq_one_iff (n : e6ScN K) :
    e6ScPhi K n = 1 ↔ (n : ↥(e6Data_valid.minGroup K)) ∈ e6ScH K := by
  rw [e6ScPhi_apply]
  constructor
  · intro h
    have hmem : (e6ScMono n : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K := by
      obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets (e6ScMono n).2
      have hmaps : MapsRootLines (e6ScMono n : ModGL Tag.E6 K) w := by
        rw [hgk]
        simpa using ((mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w))
      have hw : w = 1 := (weylQuotientHom_eq hmaps).symm.trans h
      rw [hgk, hw, canonicalRep_one, mul_one]
      exact hk
    exact hmem
  · intro h
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup h)

theorem e6ScPhi_surjective : Function.Surjective (e6ScPhi K) := by
  intro w
  have hm : canonicalRep (coxeterSystem Tag.E6) K w ∈ monomialSubgroup Tag.E6 K :=
    canonicalRep_mem_monomialSubgroup w
  obtain ⟨g, hg⟩ := e6Isogeny_surjective K
    (⟨canonicalRep (coxeterSystem Tag.E6) K w, monomialSubgroup_le_adjointGroup' hm⟩ :
      ↥(adjointGroup Tag.E6 K))
  have hgN : g ∈ e6ScN K := by
    rw [e6ScN, Subgroup.mem_comap]
    rw [hg]
    exact (Subgroup.mem_subgroupOf).2 hm
  refine ⟨⟨g, hgN⟩, ?_⟩
  rw [e6ScPhi_apply]
  refine weylQuotientHom_eq ?_
  have hval : ((e6ScMono (⟨g, hgN⟩ : e6ScN K) : monomialSubgroup Tag.E6 K) : ModGL Tag.E6 K) =
      canonicalRep (coxeterSystem Tag.E6) K w := by
    rw [show ((e6ScMono (⟨g, hgN⟩ : e6ScN K) : monomialSubgroup Tag.E6 K) : ModGL Tag.E6 K) =
      ((e6Isogeny K g : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) from rfl]
    exact congrArg Subtype.val hg
  rw [hval]
  exact mapsRootLines_canonicalRep w

private theorem torusGroup_le_adjointGroup : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
  fun _ hx => monomialSubgroup_le_adjointGroup' (CFSG.LieType.Chevalley.torusGroup_le_monomialSubgroup hx)

private theorem card_e6ScH (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card ↥(e6ScH K) = (Nat.card K - 1) ^ 6 := by
  classical
  haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup' e6Data_valid
  have hker3 : Nat.card (e6Isogeny K).ker = 3 := by
    rw [e6Isogeny_ker_eq_center, (card_center_e6 (k := K)).1, Nat.gcd_eq_left h3]
  have hkerH : (e6Isogeny K).ker ≤ e6ScH K := by
    intro x hx
    rw [e6ScH, Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.1 hx]
    exact Subgroup.one_mem _
  have h := Subgroup.card_ker_mul_card_range ((e6Isogeny K).comp (e6ScH K).subtype)
  have hker : ((e6Isogeny K).comp (e6ScH K).subtype).ker =
      (e6Isogeny K).ker.subgroupOf (e6ScH K) := rfl
  have hrange : ((e6Isogeny K).comp (e6ScH K).subtype).range =
      (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, e6ScH, Subgroup.map_comap_eq_self]
    rw [MonoidHom.range_eq_top.2 (e6Isogeny_surjective K)]
    exact le_top
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerH).toEquiv,
    hker3] at h
  have hTC : Nat.card ↥((torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)) =
      Nat.card (torusGroup Tag.E6 K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe torusGroup_le_adjointGroup).toEquiv
  have h3' : Nat.card (torusGroup Tag.E6 K) * 3 = (Nat.card K - 1) ^ 6 := by
    have := card_torusGroup_E6 (K := K)
    rwa [Nat.gcd_eq_right h3] at this
  rw [hTC] at h
  rw [← h, mul_comm, h3']

theorem e6ScH_eq_minTorus_range (h3 : 3 ∣ Nat.card K - 1) :
    e6ScH K = (minTorus e6Data_valid K).range := by
  classical
  haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup' e6Data_valid
  have hTH : (minTorus e6Data_valid K).range ≤ e6ScH K := by
    rintro _ ⟨u, rfl⟩
    rw [e6ScH, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [e6Isogeny_minTorus]
    have hc : rootDiagUnit Tag.E6 (e6RootParams u) ∈ torusGroup Tag.E6 K := by
      have e : e6RootParams u = CFSG.LieType.Chevalley.cartanChar (τ := Tag.E6) u := by
        funext j
        simp only [e6RootParams, CFSG.LieType.Chevalley.cartanChar]
      rw [e]
      rw [← CFSG.LieType.Chevalley.list_prod_torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := K) u]
      exact Subgroup.list_prod_mem _ fun g hg => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
        exact CFSG.LieType.Chevalley.torusElt_mem_torusGroup i _
    exact hc
  have hTcard : Nat.card (minTorus e6Data_valid K).range = (Nat.card K - 1) ^ 6 := by
    have hinj : Function.Injective (minTorus e6Data_valid K) :=
      minTorus_injective e6Data_valid K
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun]
    simp only [Nat.card_units, Nat.card_fin]
    rw [show Tag.E6.rank = 6 from rfl]
  have hHcard := card_e6ScH (K := K) h3
  exact (Subgroup.eq_of_le_of_card_ge hTH (le_of_eq (hHcard.trans hTcard.symm))).symm

theorem not_three_dvd_e6ScN_index (h3 : 3 ∣ Nat.card K - 1) : ¬ 3 ∣ (e6ScN K).index := by
  have h1 : ((monomialSubgroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)).relIndex
      (⊤ : Subgroup ↥(adjointGroup Tag.E6 K)) =
      (monomialSubgroup Tag.E6 K).relIndex (adjointGroup Tag.E6 K) := by
    have h := Subgroup.relIndex_subgroupOf (H := monomialSubgroup Tag.E6 K)
      (K := adjointGroup Tag.E6 K) (L := adjointGroup Tag.E6 K) le_rfl
    rwa [Subgroup.subgroupOf_self] at h
  have h2 : ((monomialSubgroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)).index =
      (monomialSubgroup Tag.E6 K).relIndex (adjointGroup Tag.E6 K) := by
    rw [← Subgroup.relIndex_top_right]
    exact h1
  rw [e6ScN, Subgroup.index_comap_of_surjective _ (e6Isogeny_surjective K), h2]
  exact not_three_dvd_relIndex_monomial h3


@[expose] noncomputable def e6RootParamsHom (K : Type) [Field K] :
    (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → Kˣ) where
  toFun := e6RootParams
  map_one' := by
    funext j
    simp [e6RootParams]
  map_mul' u v := by
    funext j
    simp only [e6RootParams, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem e6RootParamsHom_apply (K : Type) [Field K] (u : Fin Tag.E6.rank → Kˣ) :
    e6RootParamsHom K u = e6RootParams u := rfl

theorem e6RootParamsHom_ker (K : Type) [Field K] :
    (e6RootParamsHom K).ker =
      CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.centerChars Tag.E6 K := by
  ext u
  rw [MonoidHom.mem_ker, CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.mem_centerChars]
  constructor
  · intro h j
    have := congrFun h j
    simpa [e6RootParamsHom_apply, e6RootParams] using this
  · intro h
    funext j
    simpa [e6RootParamsHom_apply, e6RootParams] using h j

theorem card_mul_le_of_e6ScTorus (h3 : 3 ∣ Nat.card K - 1)
    {F : Subgroup (WeylGroup Tag.E6)} {S : Subgroup ↥(e6Data_valid.minGroup K)}
    (hF : IsElemAbelian 3 F) (hS : IsElemAbelian 3 S) (hSH : S ≤ e6ScH K)
    (hfix : ∀ h ∈ S, ∀ e : e6ScN K, e6ScPhi K e ∈ F →
      (e : ↥(e6Data_valid.minGroup K)) * h * (e : ↥(e6Data_valid.minGroup K))⁻¹ = h) :
    Nat.card S * Nat.card F ≤ 3 ^ 6 := by
  classical
  haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup' e6Data_valid
  have hST : S ≤ (minTorus e6Data_valid K).range :=
    hSH.trans (le_of_eq (e6ScH_eq_minTorus_range (K := K) h3))
  set c := e6RootParamsHom K with hcdef
  set S₀ : Subgroup (Fin Tag.E6.rank → Kˣ) := S.comap (minTorus e6Data_valid K) with hS₀def
  have hinjT : Function.Injective (minTorus e6Data_valid K) := minTorus_injective e6Data_valid K
  have hS₀card : Nat.card S₀ = Nat.card S := by
    rw [← Subgroup.card_map_of_injective hinjT, Subgroup.map_comap_eq_self hST]
  have hS₀exp : ∀ u ∈ S₀, u ^ 3 = 1 := by
    intro u hu
    have h2 : (minTorus e6Data_valid K u) ^ 3 = 1 := hS.2 _ hu
    apply hinjT
    rw [map_pow, map_one, h2]
  set R : Subgroup (Fin Tag.E6.rank → Kˣ) := S₀.map c with hRdef
  have hcenter : Nat.card
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.centerChars Tag.E6 K) = 3 := by
    have e := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.centerEquiv e6Data_valid K
      isFiniteType_cartan_E6 (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K)
      (e6Datum_bruhatExtras K)
    rw [Nat.card_congr e.toEquiv, (card_center_e6 (k := K)).1, Nat.gcd_eq_left h3]
  have hcomp := Subgroup.card_ker_mul_card_range (c.comp S₀.subtype)
  have hcomprange : (c.comp S₀.subtype).range = R := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hRdef]
  have hcompker : (c.comp S₀.subtype).ker = (S₀ ⊓ c.ker).subgroupOf S₀ := by
    ext u
    constructor
    · intro h
      exact ⟨u.2, h⟩
    · rintro ⟨-, h⟩
      exact h
  have hcompker_card : Nat.card ↥((S₀ ⊓ c.ker).subgroupOf S₀) =
      Nat.card ↥(S₀ ⊓ c.ker) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcomprange, hcompker, hcompker_card] at hcomp
  have hker3 : Nat.card ↥(S₀ ⊓ c.ker) ≤ 3 := by
    have hle : S₀ ⊓ c.ker ≤
        CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.centerChars Tag.E6 K := by
      rw [hcdef, e6RootParamsHom_ker]
      exact inf_le_right
    exact (Nat.card_mono (Set.toFinite _) (fun u hu => hle hu)).trans (le_of_eq hcenter)
  have hRea : IsElemAbelian 3 R := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      show (a : Fin Tag.E6.rank → Kˣ) * b = (b : Fin Tag.E6.rank → Kˣ) * a
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 b.2
      rw [← hxa, ← hya, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 ha
      rw [← hxa, ← map_pow, hS₀exp x hx, map_one]
  have hRfix : ∀ a ∈ R, ∀ w ∈ F, weylAct w a = a := by
    intro a ha w hw
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.1 ha
    rw [← hua]
    obtain ⟨e, he⟩ := e6ScPhi_surjective (K := K) w
    have hfixu := hfix (minTorus e6Data_valid K u) hu e (by rw [he]; exact hw)
    have h2 : (e6ScMono e : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 (e6RootParams u) *
        (e6ScMono e : ModGL Tag.E6 K)⁻¹ = rootDiagUnit Tag.E6 (e6RootParams u) := by
      have h1 := congrArg (e6Isogeny K) hfixu
      rw [map_mul, map_mul, map_inv] at h1
      have h1' := congrArg (fun x : ↥(adjointGroup Tag.E6 K) => (x : ModGL Tag.E6 K)) h1
      simpa [e6Isogeny_minTorus, e6ScMono] using h1'
    have h3 := monomial_conj_rootDiagUnit (e6ScMono e) (e6RootParams u)
    rw [show weylQuotientHom Tag.E6 K (e6ScMono e) = e6ScPhi K e from rfl, he] at h3
    have h4 : rootDiagUnit Tag.E6 (weylAct w (e6RootParams u)) = rootDiagUnit Tag.E6 (e6RootParams u) := by
      rw [← h3]
      exact h2
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective h4
  have hRle : Nat.card R ≤ Nat.card (e6Fix F) := card_le_card_e6Fix h3 F R hRea hRfix
  have hSle : Nat.card S ≤ 3 * Nat.card (e6Fix F) := by
    rw [← hS₀card, ← hcomp]
    exact Nat.mul_le_mul hker3 hRle
  by_cases hFbot : F = ⊥
  ·
    rw [hFbot, Subgroup.card_bot, mul_one]
    have hμ : Nat.card S₀ ≤ 3 ^ 6 := by
      have hmem : ∀ u : S₀, ∀ j, ((u : Fin Tag.E6.rank → Kˣ) j) ∈ rootsOfUnity 3 K := by
        intro u j
        rw [mem_rootsOfUnity]
        exact congrFun (hS₀exp u u.2) j
      have hinj : Function.Injective
          (fun u : S₀ => fun j =>
            (⟨(u : Fin Tag.E6.rank → Kˣ) j, hmem u j⟩ : rootsOfUnity 3 K)) := by
        intro a b hab
        apply Subtype.ext
        funext j
        exact congrArg Subtype.val (congrFun hab j)
      calc Nat.card S₀ ≤ Nat.card (Fin Tag.E6.rank → rootsOfUnity 3 K) :=
            Nat.card_le_card_of_injective _ hinj
        _ = 3 ^ 6 := by
            rw [Nat.card_fun]
            haveI : Fintype K := Fintype.ofFinite K
            have hfac : Nat.card (rootsOfUnity 3 K) = 3 := by
              rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.card_rootsOfUnity_eq_gcd,
                Fintype.card_eq_nat_card, Nat.gcd_eq_left h3]
            simp only [hfac, Finset.prod_const, Nat.card_fin, show Tag.E6.rank = 6 from rfl]
    rw [← hS₀card]
    exact hμ
  · have hbound := card_e6Fix_mul_card_le_of_ne_bot F hF hFbot
    calc Nat.card S * Nat.card F ≤ (3 * Nat.card (e6Fix F)) * Nat.card F :=
          Nat.mul_le_mul_right _ hSle
      _ = 3 * (Nat.card (e6Fix F) * Nat.card F) := by ring
      _ ≤ 3 * 3 ^ 5 := Nat.mul_le_mul_left _ hbound
      _ = 3 ^ 6 := by norm_num

instance instFiniteE6ScMinGroup (K : Type) [Field K] [Finite K] :
    Finite ↥(e6Data_valid.minGroup K) :=
  finite_minGroup' e6Data_valid

theorem pRank_three_e6Sc_le_six (h3 : 3 ∣ Nat.card K - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(e6Data_valid.minGroup K)) ≤ 6 := by
  classical
  haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup' e6Data_valid
  have hHc : ∀ a ∈ e6ScH K, ∀ b ∈ e6ScH K, a * b = b * a := by
    intro a ha b hb
    rw [e6ScH_eq_minTorus_range (K := K) h3] at ha hb
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    rw [← map_mul, ← map_mul, mul_comm]
  exact pRank_le_of_torus_normalizer Nat.prime_three (e6ScN K) (e6ScH K) hHc
    (not_three_dvd_e6ScN_index (K := K) h3) (e6ScPhi K)
    (fun n => e6ScPhi_eq_one_iff n)
    (fun F S hF hS hSH hfix => card_mul_le_of_e6ScTorus (K := K) h3 hF hS hSH hfix)

end E6Sc

section HopfCoverBridge

open CFSG.RankThree.PerfectCover

theorem pRank_eq_hopfCover_of_ker {p : ℕ} (hp : p.Prime) {R K : Type} [Group R] [Finite R]
    [Group.IsPerfect R] [Group K] [Finite K] [Group.IsPerfect K] (κ : K →* R)
    (hκ : Function.Surjective κ) (hcen : κ.ker ≤ Subgroup.center K)
    (hpart : (Nat.card κ.ker).factorization p =
      (Nat.card (hopfMultiplier R)).factorization p) :
    CFSG.Open.pRank p (⊤ : Subgroup K) = CFSG.Open.pRank p (⊤ : Subgroup (HopfCover R)) := by
  haveI : Finite (HopfCover R) := finite_hopfCover (X := R) inferInstance
  obtain ⟨-, h, hcomp, -, hsurj, hmap, -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier κ hκ hcen
  have hker_le : h.ker ≤ hopfMultiplier R := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← hcomp, MonoidHom.comp_apply, hu, map_one]
  have hcard : Nat.card (hopfMultiplier R) = Nat.card h.ker * Nat.card κ.ker := by
    have hh := Subgroup.card_ker_mul_card_range (h.comp (hopfMultiplier R).subtype)
    have hrange : (h.comp (hopfMultiplier R).subtype).range = κ.ker := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    have hker : (h.comp (hopfMultiplier R).subtype).ker =
        h.ker.subgroupOf (hopfMultiplier R) := by
      ext u
      constructor
      · intro hu
        exact Subgroup.mem_subgroupOf.2 hu
      · intro hu
        exact Subgroup.mem_subgroupOf.1 hu
    rw [hker, hrange, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv] at hh
    exact hh.symm
  have hfact : (Nat.card (hopfMultiplier R)).factorization p =
      (Nat.card h.ker).factorization p + (Nat.card κ.ker).factorization p := by
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply]
  have hzero : (Nat.card h.ker).factorization p = 0 := by omega
  have hpp : ¬ p ∣ Nat.card h.ker := by
    intro hdvd
    have hpos : 1 ≤ (Nat.card h.ker).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp (Nat.card_pos.ne')).1 hdvd
    omega
  haveI : h.ker.Normal := inferInstance
  have e : HopfCover R ⧸ h.ker ≃* K := QuotientGroup.quotientKerEquivOfSurjective h hsurj
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p K,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top p (HopfCover R)]
  have h1 : CFSG.pRank p (HopfCover R ⧸ h.ker) = CFSG.pRank p K := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact pRank_top_eq_of_mulEquiv (p := p) hp.one_lt e
  have h2 : CFSG.pRank p (HopfCover R ⧸ h.ker) = CFSG.pRank p (HopfCover R) :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp h.ker hpp
  exact h1.symm.trans h2

theorem pRank_le_of_hopfCover {p : ℕ} (hp : p.Prime) {R K G : Type} [Group R] [Finite R]
    [Group.IsPerfect R] [Group K] [Finite K] [Group.IsPerfect K] [Group G] [Finite G]
    [Group.IsPerfect G] (κ : K →* R) (hκ : Function.Surjective κ)
    (hcen : κ.ker ≤ Subgroup.center K)
    (hpart : (Nat.card κ.ker).factorization p =
      (Nat.card (hopfMultiplier R)).factorization p)
    (γ : G →* R) (hγ : Function.Surjective γ) (hcen' : γ.ker ≤ Subgroup.center G)
    (hpart' : (Nat.card γ.ker).factorization p =
      (Nat.card (hopfMultiplier R)).factorization p) :
    CFSG.Open.pRank p (⊤ : Subgroup K) = CFSG.Open.pRank p (⊤ : Subgroup G) := by
  rw [pRank_eq_hopfCover_of_ker hp κ hκ hcen hpart,
    pRank_eq_hopfCover_of_ker hp γ hγ hcen' hpart']

end HopfCoverBridge

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
