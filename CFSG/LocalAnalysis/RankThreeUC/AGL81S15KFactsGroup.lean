module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblySections
import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
import CFSG.GroupTheory.HuppertProduct.RankBound
import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality
import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped Pointwise

@[expose] def KSch : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S →
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)

theorem kSch_of_catalog (h : CFSG.AGLEmbedding.KFactCatalogSchreier) : KSch := h

theorem KSch.schreierSections (h : KSch) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) :
    CFSG.ComponentClassification.LBalance.SchreierSections X :=
  CFSG.ComponentClassification.LBalance.SchreierSections.of_isKGroup
    (fun S _ _ _ hnc hcat => h S ‹_› hnc hcat) hX

@[expose] def KWiel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A B : Subgroup X) (p : ℕ), p.Prime →
    (∀ x : X, ∃ a ∈ A, ∃ b ∈ B, x = a * b) →
    ∃ P₁ P₂ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p P₁ A ∧ CFSG.ABGLocalTools.IsSylowOf p P₂ B ∧
      (∃ Q : Sylow p X, (Q : Subgroup X) = P₁ ⊔ P₂) ∧
      ((P₁ ⊔ P₂ : Subgroup X) : Set X) = (P₁ : Set X) * (P₂ : Set X)

@[expose] def KHupAt (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (W A B : Subgroup X),
    IsPGroup p W → A ≤ W → B ≤ W → IsCyclic A → IsCyclic B →
    (∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b) → CFSG.Open.pRank p W ≤ 2

theorem kHupAt_three : KHupAt 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro X _ _ W A B hW hA hB hAc hBc hprod
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E hEW hE
  by_contra hlt
  have hlt : 3 ^ 2 < Nat.card E := not_le.mp hlt
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have h27 : 3 ^ 3 ∣ Nat.card E := by
    rw [hn] at hlt ⊢
    have h2n : 2 < n := by
      by_contra h
      have h' : n ≤ 2 := not_lt.mp h
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h'
      omega
    exact pow_dvd_pow 3 h2n
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
  have hle : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  have hE'card : Nat.card (K.map E.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num
  have hcomm := hE.1
  have hE'el : CFSG.Open.IsElemAbelian 3 (K.map E.subtype) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hle hx)⟩
    apply Subtype.ext
    have h := congrArg Subtype.val (mul_comm' (⟨a.1, hle a.2⟩ : E) ⟨b.1, hle b.2⟩)
    exact h
  exact CFSG.GroupTheory.HuppertProduct.kFactHuppertProductThree_holds X W A B (K.map E.subtype)
    hW hA hB hAc hBc hprod (hle.trans hEW) hE'el hE'card

@[expose] def KComp : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (L L' : Subgroup X),
      CFSG.Open.IsComponentOf L ⊤ → CFSG.Open.IsComponentOf L' ⊤ → L ≠ L' → ⁅L, L'⁆ = ⊥) ∧
  (∀ (X : Type) [Group X] [Finite X] (L N : Subgroup X), N.Normal →
      CFSG.Open.IsComponentOf L ⊤ → L ≤ N ∨ ⁅L, N⁆ = ⊥)

theorem kComp_holds : KComp := by
  refine ⟨fun X _ _ L L' hL hL' hne =>
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne, ?_⟩
  intro X _ _ L N hN hL
  haveI := hN
  exact CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes L N hL

@[expose] def KSubn : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup X),
    CFSG.Open.IsSubnormal P ⊤ → IsPGroup 2 P → P ≤ CFSG.pCore 2 X

private theorem pCoreOf_top_eq (X : Type) [Group X] :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) = CFSG.pCore 2 X := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := X)).symm,
    Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom =
      MonoidHom.id X := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem kSubn_holds : KSubn := by
  intro X _ _ P hsub hP
  have h := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub hP
  rwa [pCoreOf_top_eq] at h

@[expose] def KCop : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) (h : X), IsPGroup 2 N →
    h ∈ Subgroup.normalizer (N : Set X) → Odd (orderOf h) →
    (N ⊓ Subgroup.centralizer ({h} : Set X)) ⊔ ⁅N, Subgroup.zpowers h⁆ = N ∧
    ⁅⁅N, Subgroup.zpowers h⁆, Subgroup.zpowers h⁆ = ⁅N, Subgroup.zpowers h⁆

section Wiel

variable {X : Type} [Group X] [Finite X]

private def conjS (g : X) (S : Subgroup X) : Subgroup X := S.map (MulAut.conj g).toMonoidHom

private theorem mem_conjS {g x : X} {S : Subgroup X} : x ∈ conjS g S ↔ g⁻¹ * x * g ∈ S := by
  unfold conjS
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem conjS_mul (g h : X) (S : Subgroup X) : conjS g (conjS h S) = conjS (g * h) S := by
  ext x
  simp only [mem_conjS, mul_inv_rev, mul_assoc]

private theorem conjS_eq_of_mem {K : Subgroup X} {a : X} (ha : a ∈ K) : conjS a K = K := by
  ext x
  rw [mem_conjS]
  constructor
  · intro h
    have := K.mul_mem (K.mul_mem ha h) (K.inv_mem ha)
    simpa [mul_assoc] using this
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem ha) h) ha

private theorem conjS_inf (g : X) (S T : Subgroup X) :
    conjS g (S ⊓ T) = conjS g S ⊓ conjS g T := by
  ext x
  simp [mem_conjS]

private theorem card_conjS (g : X) (S : Subgroup X) : Nat.card (conjS g S) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

open CFSG.ABGLocalTools in
theorem kWiel_holds : KWiel := by
  intro X _ _ A B p hp hAB
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ∀ K : Subgroup X, ∃ S : Sylow p X, IsSylowOf p ((S : Subgroup X) ⊓ K) K := by
    intro K
    obtain ⟨R, hR⟩ := exists_isSylowOf p K
    obtain ⟨S, hS⟩ := hR.isPGroup.exists_le_sylow
    refine ⟨S, ?_⟩
    have h1 : (S : Subgroup X) ⊓ K = R :=
      hR.eq_of_le (le_inf hS hR.le) inf_le_right S.isPGroup'.to_inf_left
    rw [h1]
    exact hR
  have conj_good : ∀ (K S : Subgroup X) (a : X), a ∈ K →
      IsSylowOf p (S ⊓ K) K → IsSylowOf p (conjS a S ⊓ K) K := by
    intro K S a ha h
    have e : conjS a S ⊓ K = conjS a (S ⊓ K) := by rw [conjS_inf, conjS_eq_of_mem ha]
    apply isSylowOf_of_card
    · exact inf_le_right
    · rw [e, card_conjS]
      exact h.card_eq
  obtain ⟨SA, hSA⟩ := key A
  obtain ⟨SB, hSB⟩ := key B
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X SA SB
  have hgS : (SB : Subgroup X) = conjS g (SA : Subgroup X) := by
    rw [← hg]
    rfl
  obtain ⟨a, ha, b, hb, hab⟩ := hAB g⁻¹
  have hgeq : g = b⁻¹ * a⁻¹ := by
    have h1 : g = (g⁻¹)⁻¹ := (inv_inv g).symm
    rw [h1, hab, mul_inv_rev]
  set R : Subgroup X := conjS a⁻¹ (SA : Subgroup X) with hR
  have hRA : IsSylowOf p (R ⊓ A) A := conj_good A SA a⁻¹ (A.inv_mem ha) hSA
  have hRB : IsSylowOf p (R ⊓ B) B := by
    have h1 : R = conjS b (SB : Subgroup X) := by
      rw [hgS, hgeq, conjS_mul, mul_inv_cancel_left]
    rw [h1]
    exact conj_good B SB b hb hSB
  set P₁ : Subgroup X := R ⊓ A with hP₁
  set P₂ : Subgroup X := R ⊓ B with hP₂
  have hRcard : Nat.card R = p ^ (Nat.card X).factorization p := by
    rw [hR, card_conjS, Sylow.card_eq_multiplicity]
  have hsub : ((P₁ : Set X) * (P₂ : Set X)) ⊆ (R : Set X) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact R.mul_mem hx.1 hy.1
  have hprod1 := CFSG.SignalizerFunctor.Helpers.subgroup_product_cardinality P₁ P₂
  have hprod2 := CFSG.SignalizerFunctor.Helpers.subgroup_product_cardinality A B
  have hAB_univ : CFSG.SignalizerFunctor.Helpers.subgroupProduct A B = Set.univ :=
    (CFSG.SignalizerFunctor.Helpers.subgroup_product_eq_univ_iff A B).2 (fun x => by
      obtain ⟨a, ha, b, hb, h⟩ := hAB x
      exact ⟨a, ha, b, hb, h.symm⟩)
  rw [hAB_univ, Nat.card_univ] at hprod2
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hAB0 : Nat.card (A ⊓ B : Subgroup X) ≠ 0 := Nat.card_pos.ne'
  have hval := congrArg (fun n => n.factorization p) hprod2
  simp only [Nat.factorization_mul hA0 hB0, Nat.factorization_mul hX0 hAB0,
    Finsupp.add_apply] at hval
  have hcA := hRA.card_eq
  have hcB := hRB.card_eq
  obtain ⟨k, hk⟩ := (hRA.isPGroup.to_le (inf_le_left : P₁ ⊓ P₂ ≤ P₁)).exists_card_eq
  have hkdvd : p ^ k ∣ Nat.card (A ⊓ B : Subgroup X) := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le (inf_le_inf inf_le_right inf_le_right)
  have hkle : k ≤ (Nat.card (A ⊓ B : Subgroup X)).factorization p :=
    (hp.pow_dvd_iff_le_factorization hAB0).1 hkdvd
  have hle : (R : Set X).ncard ≤ ((P₁ : Set X) * (P₂ : Set X)).ncard := by
    have e1 : (R : Set X).ncard = Nat.card R := (Nat.card_coe_set_eq _).symm
    have e2 : ((P₁ : Set X) * (P₂ : Set X)).ncard =
        Nat.card (CFSG.SignalizerFunctor.Helpers.subgroupProduct P₁ P₂) :=
      (Nat.card_coe_set_eq _).symm
    rw [e1, e2]
    by_contra hlt
    rw [not_le] at hlt
    rw [hRcard] at hlt
    rw [hcA, hcB, hk] at hprod1
    have h1 : Nat.card (CFSG.SignalizerFunctor.Helpers.subgroupProduct P₁ P₂) * p ^ k <
        p ^ (Nat.card X).factorization p * p ^ k :=
      Nat.mul_lt_mul_of_pos_right hlt (pow_pos hp.pos _)
    have h2 : p ^ (Nat.card X).factorization p * p ^ k ≤
        p ^ (Nat.card X).factorization p *
          p ^ (Nat.card (A ⊓ B : Subgroup X)).factorization p :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos hkle)
    have h3 : p ^ (Nat.card A).factorization p * p ^ (Nat.card B).factorization p =
        p ^ (Nat.card X).factorization p *
          p ^ (Nat.card (A ⊓ B : Subgroup X)).factorization p := by
      rw [← pow_add, ← pow_add, hval]
    omega
  have heq : (P₁ : Set X) * (P₂ : Set X) = (R : Set X) :=
    Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hsup : P₁ ⊔ P₂ = R := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro r hr
      have : r ∈ (P₁ : Set X) * (P₂ : Set X) := heq ▸ hr
      obtain ⟨x, hx, y, hy, rfl⟩ := this
      exact Subgroup.mul_mem_sup hx hy
  refine ⟨P₁, P₂, hRA, hRB, ⟨Sylow.ofCard R hRcard, ?_⟩, ?_⟩
  · rw [Sylow.coe_ofCard, hsup]
  · rw [hsup]
    exact heq.symm

end Wiel

section Cop

variable {X : Type} [Group X] [Finite X]

private noncomputable def copAct (N : Subgroup X) (h : X)
    (hh : h ∈ Subgroup.normalizer (N : Set X)) : Subgroup.zpowers h →* MulAut N :=
  CFSG.LargeEvenClassification.Helpers.invariantSubgroupConjugation (Subgroup.zpowers h).subtype N
    (fun a x hx => by
      have ha : (a : X) ∈ Subgroup.normalizer (N : Set X) :=
        (Subgroup.zpowers_le.2 hh) a.2
      exact (Subgroup.mem_normalizer_iff.mp ha x).mp hx)

private theorem copAct_fixed (N : Subgroup X) (h : X) (hh : h ∈ Subgroup.normalizer (N : Set X)) :
    letI : MulDistribMulAction (Subgroup.zpowers h) N :=
      MulDistribMulAction.compHom N (copAct N h hh)
    (CFSG.fixedPointSubgroup (Subgroup.zpowers h) N).map N.subtype =
      N ⊓ Subgroup.centralizer ({h} : Set X) := by
  letI : MulDistribMulAction (Subgroup.zpowers h) N :=
    MulDistribMulAction.compHom N (copAct N h hh)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h1 : ((⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) • y : N) = y := hy _
    have h2 := congrArg Subtype.val h1
    change z * (y : X) * z⁻¹ = y at h2
    calc z * (y : X) = z * (y : X) * z⁻¹ * z := by group
      _ = (y : X) * z := by rw [h2]
  · rintro ⟨hxN, hxc⟩
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    intro a
    apply Subtype.ext
    change (a : X) * x * (a : X)⁻¹ = x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hc : Commute h x := (Subgroup.mem_centralizer_iff.mp hxc h rfl)
    have hc' : Commute ((a : X)) x := by rw [← hj]; exact hc.zpow_left j
    rw [hc'.eq]
    group

open scoped commutatorElement in
private theorem copComm_map (N : Subgroup X) (h : X) (hh : h ∈ Subgroup.normalizer (N : Set X))
    (H : Subgroup N) :
    letI : MulDistribMulAction (Subgroup.zpowers h) N :=
      MulDistribMulAction.compHom N (copAct N h hh)
    (CFSG.commutatorSubgroup (Subgroup.zpowers h) N H).map N.subtype =
      ⁅H.map N.subtype, Subgroup.zpowers h⁆ := by
  letI : MulDistribMulAction (Subgroup.zpowers h) N :=
    MulDistribMulAction.compHom N (copAct N h hh)
  unfold CFSG.commutatorSubgroup
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, y, hy, rfl⟩, rfl⟩
    refine ⟨((y⁻¹ : N) : X), ⟨y⁻¹, H.inv_mem hy, rfl⟩, (a : X), a.2, ?_⟩
    change ((y : X)⁻¹ * (a : X) * (((y : X)⁻¹)⁻¹) * (a : X)⁻¹) =
      (y : X)⁻¹ * ((a : X) * y * (a : X)⁻¹)
    group
  · rintro ⟨_, ⟨y, hy, rfl⟩, g, hg, rfl⟩
    refine ⟨_, ⟨⟨g, hg⟩, y⁻¹, H.inv_mem hy, rfl⟩, ?_⟩
    show ((y⁻¹⁻¹ : N) : X) * ((g : X) * ((y⁻¹ : N) : X) * (g : X)⁻¹) = ⁅((y : N) : X), g⁆
    simp only [inv_inv, Subgroup.coe_inv, commutatorElement_def]
    group

theorem kCop_holds : KCop := by
  intro X _ _ N h hN hh hodd
  letI : MulDistribMulAction (Subgroup.zpowers h) N :=
    MulDistribMulAction.compHom N (copAct N h hh)
  haveI : Group.IsNilpotent N := hN.isNilpotent
  have hsolv : Group.IsSolvable N := inferInstance
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers h)) (Nat.card N) := by
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk, Nat.card_zpowers]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  have h1 := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := N) (A := Subgroup.zpowers h) hsolv hcop
  have h2 := CFSG.commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    (G := N) (A := Subgroup.zpowers h) hsolv hcop
  have hfix := copAct_fixed N h hh
  have hcomm := copComm_map N h hh ⊤
  have htop : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htop] at hcomm
  have hcomm2 := copComm_map N h hh (CFSG.commutatorAction (Subgroup.zpowers h) N)
  have hK : (CFSG.commutatorAction (Subgroup.zpowers h) N).map N.subtype =
      ⁅N, Subgroup.zpowers h⁆ := hcomm
  rw [hK] at hcomm2
  constructor
  · have := congrArg (Subgroup.map N.subtype) h1
    rw [Subgroup.map_sup, hfix, hcomm, htop] at this
    exact this
  · have := congrArg (Subgroup.map N.subtype) h2
    rw [hcomm2, hK] at this
    exact this

end Cop

end CFSG.LocalAnalysis.RankThreeUC.S15
