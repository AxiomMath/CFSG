module

public import CFSG.Open.RankThreeDefs
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.LocalAnalysis.GLTheoremA.Lemma48
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem relPPrimeCore_facts {p : ℕ} [Fact p.Prime] (N : Subgroup G) :
    CFSG.Open.rankThreePrimeCore p N ≤ N ∧
      N ≤ Subgroup.normalizer (CFSG.Open.rankThreePrimeCore p N : Set G) ∧
      Nat.Coprime p (Nat.card (CFSG.Open.rankThreePrimeCore p N)) := by
  have hdef : CFSG.Open.rankThreePrimeCore p N = (CFSG.pPrimeCore p ↥N).map N.subtype :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
      Fact.out N
  have hKN : CFSG.Open.rankThreePrimeCore p N ≤ N := by
    rw [hdef]
    exact Subgroup.map_subtype_le _
  refine ⟨hKN, ?_, ?_⟩
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKN]
    have h : (CFSG.Open.rankThreePrimeCore p N).subgroupOf N = CFSG.pPrimeCore p ↥N := by
      rw [hdef]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [h]
    infer_instance
  · rw [hdef, Subgroup.card_map_of_injective N.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card

private theorem le_centralizer_of_isPGroup_of_not_dvd_card_mulAut {p : ℕ} (hp : p.Prime)
    {P A : Subgroup G} (hP : IsPGroup p P) (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hAut : ¬ p ∣ Nat.card (MulAut ↥A)) :
    P ≤ Subgroup.centralizer (A : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Subgroup.Normalizes P A := ⟨hPA⟩
  let phi : P →* MulAut A := MulDistribMulAction.toMulAut P A
  have hRangeDvdAut : Nat.card phi.range ∣ Nat.card (MulAut A) :=
    Subgroup.card_subgroup_dvd_card phi.range
  have hRangeDvdP : Nat.card phi.range ∣ Nat.card P := Subgroup.card_range_dvd phi
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (hn ▸ hRangeDvdP)
  have hj0 : j = 0 := by
    by_contra hne
    exact hAut ((dvd_pow_self p hne).trans (hj ▸ hRangeDvdAut))
  have hRangeBot : phi.range = ⊥ := by
    rw [← Subgroup.card_eq_one, hj, hj0, pow_zero]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hphiA : phi ⟨a, ha⟩ = 1 := by
    have hmem : phi ⟨a, ha⟩ ∈ phi.range := ⟨⟨a, ha⟩, rfl⟩
    have hbot : phi ⟨a, ha⟩ ∈ (⊥ : Subgroup (MulAut A)) := by
      simpa [hRangeBot] using hmem
    simpa using hbot
  have hsmul : (⟨a, ha⟩ : P) • (⟨x, hx⟩ : A) = ⟨x, hx⟩ := by
    have h := congrArg (fun g : MulAut A => g ⟨x, hx⟩) hphiA
    simpa [phi, MulDistribMulAction.toMulAut_apply] using h
  have hconj : a * x * a⁻¹ = x := by
    have h := congrArg Subtype.val hsmul
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using h
  have hcomm : a * x = x * a := by
    have h := congrArg (fun t => t * a) hconj
    simpa [mul_assoc] using h
  exact hcomm.symm

private theorem le_normalizer_of_weaklyClosed {p : ℕ} {P₀ : Subgroup G} (P : Sylow p G)
    (hP₀P : P₀ ≤ (P : Subgroup G))
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀) :
    (P : Subgroup G) ≤ Subgroup.normalizer (P₀ : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : CFSG.Open.rankThreeConj x⁻¹ P₀ ≤ (P : Subgroup G) := by
    rw [CFSG.Open.rankThreeConj, inv_inv]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hxP : x ∈ (P : Subgroup G) := hx
    have hzP : z ∈ (P : Subgroup G) := hP₀P hz
    have h1 : x * z ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem hxP hzP
    exact (P : Subgroup G).mul_mem h1 ((P : Subgroup G).inv_mem hx)
  have h2 : CFSG.Open.rankThreeConj x⁻¹ P₀ = P₀ := hwc x⁻¹ hle
  simpa [CFSG.Open.rankThreeConj, inv_inv] using h2

private theorem subgroupOf_le_op_p'p {p : ℕ} [Fact p.Prime] {N P₀ : Subgroup G}
    (hsolv : Group.IsSolvable ↥N) (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N)
    (hP₀N : P₀ ≤ N) (hP₀P : P₀ ≤ (P : Subgroup G))
    (hPcent : (P : Subgroup G) ≤ Subgroup.centralizer (P₀ : Set G)) :
    P₀.subgroupOf N ≤ CFSG.Op_p'p p ↥N := by
  classical
  set W₀ : Subgroup ↥N := CFSG.Op_p'p p ↥N with hW₀
  have hWn : W₀.Normal := hW₀ ▸ inferInstance
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf p ((P.subtype hPN : Subgroup ↥N)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, (P.subtype hPN).isPGroup', (P.subtype hPN).not_dvd_index⟩
  have hIsSylW : CFSG.ABGLocalTools.IsSylowOf p
      ((P.subtype hPN : Subgroup ↥N) ⊓ W₀) W₀ :=
    hTsyl.inf_of_le_normalizer le_top (by
      have h : Subgroup.normalizer (W₀ : Set ↥N) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr hWn
      rw [h])
  obtain ⟨R₁, hR₁⟩ := hIsSylW.exists_sylow_eq_subgroupOf
  have hR₁map : (R₁ : Subgroup W₀).map W₀.subtype = (P.subtype hPN : Subgroup ↥N) ⊓ W₀ := by
    rw [hR₁, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hHH := CFSG.centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable hsolv p R₁
  rw [hR₁map] at hHH
  have hTcent : (P.subtype hPN : Subgroup ↥N) ≤
      Subgroup.centralizer (P₀.subgroupOf N : Set ↥N) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPcent hx) (y : G) hy)
  have hP₀cent : P₀.subgroupOf N ≤
      Subgroup.centralizer ((P.subtype hPN : Subgroup ↥N) ⊓ W₀ : Set ↥N) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxT : x ∈ (P.subtype hPN : Subgroup ↥N) := (Subgroup.mem_inf.mp hx).1
    exact (Subgroup.mem_centralizer_iff.mp (hTcent hxT) y hy).symm
  exact hP₀cent.trans hHH

private theorem le_op_p'p {p : ℕ} [Fact p.Prime] {N P₀ : Subgroup G}
    (hsolv : Group.IsSolvable ↥N) (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N)
    (hP₀N : P₀ ≤ N) (hP₀P : P₀ ≤ (P : Subgroup G))
    (hPcent : (P : Subgroup G) ≤ Subgroup.centralizer (P₀ : Set G)) :
    P₀ ≤ (CFSG.Op_p'p p ↥N).map N.subtype := by
  calc P₀ = (P₀.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hP₀N).symm
    _ ≤ (CFSG.Op_p'p p ↥N).map N.subtype :=
        Subgroup.map_mono (subgroupOf_le_op_p'p hsolv P hPN hP₀N hP₀P hPcent)

private theorem p₀_le_op_p'p_of_weaklyClosed {p : ℕ} [Fact p.Prime] {N P₀ : Subgroup G}
    (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N) (hN : Group.IsSolvable ↥N)
    (hP₀P : P₀ ≤ (P : Subgroup G)) (hP₀ : Nat.card P₀ = p)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀) :
    P₀ ≤ (CFSG.Op_p'p p ↥N).map N.subtype := by
  have hP₀N : P₀ ≤ N := hP₀P.trans hPN
  have hPnorm : (P : Subgroup G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    le_normalizer_of_weaklyClosed P hP₀P hwc
  have hPcent : (P : Subgroup G) ≤ Subgroup.centralizer (P₀ : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq Fact.out
      P.isPGroup' hP₀ hPnorm
  exact le_op_p'p hN P hPN hP₀N hP₀P hPcent

private theorem isPGroup_op_p'p_quotient {p : ℕ} [Fact p.Prime] (N : Subgroup G) :
    IsPGroup p (CFSG.Op_p'p p ↥N ⧸ (CFSG.pPrimeCore p ↥N).subgroupOf (CFSG.Op_p'p p ↥N)) := by
  classical
  have hWn : (CFSG.Op_p'p p ↥N).Normal := inferInstance
  have hK := CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := p) (H := ↥N) hWn
  have hKle : CFSG.pPrimeCore p ↥N ≤ CFSG.Op_p'p p ↥N :=
    CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p
  rw [inf_eq_right.mpr hKle] at hK
  have hcore : CFSG.pPrimeCore p ↥(CFSG.Op_p'p p ↥N) =
      (CFSG.pPrimeCore p ↥N).subgroupOf (CFSG.Op_p'p p ↥N) := by
    have h2 := congrArg (Subgroup.comap (CFSG.Op_p'p p ↥N).subtype) hK
    rwa [Subgroup.comap_map_eq_self_of_injective
      (CFSG.Op_p'p p ↥N).subtype_injective] at h2
  have h := CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p)
    (H := ↥(CFSG.Op_p'p p ↥N)) (CFSG.hasNormalPComplement_Op_p'p (p := p))
  exact h.of_equiv (QuotientGroup.quotientMulEquivOfEq hcore)

private theorem map_subgroupOf_conj {N : Subgroup G} (x : ↥N) (A : Subgroup ↥N) :
    (A.map (MulAut.conj x).toMonoidHom).map N.subtype =
      (A.map N.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  have h : (N.subtype.comp (MulAut.conj x).toMonoidHom)
      = ((MulAut.conj (x : G)).toMonoidHom.comp N.subtype) := by
    ext y
    simp [MulAut.conj_apply]
  rw [h]

private theorem map_subgroupOf_conj_eq {p : ℕ} {N P₀ : Subgroup G} (P : Sylow p G)
    (hPN : (P : Subgroup G) ≤ N) (hP₀N : P₀ ≤ N)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀) :
    ∀ x : ↥N, (P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom ≤
        (P : Subgroup G).subgroupOf N →
      (P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom = P₀.subgroupOf N := by
  intro x hx
  have hle : CFSG.Open.rankThreeConj (x : G)⁻¹ P₀ ≤ (P : Subgroup G) := by
    rw [CFSG.Open.rankThreeConj, inv_inv]
    have h1 := Subgroup.map_mono (f := N.subtype) hx
    have hmap : ((P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom).map N.subtype =
        ((P₀.subgroupOf N).map N.subtype).map (MulAut.conj (x : G)).toMonoidHom :=
      map_subgroupOf_conj (G := G) (N := N) x (P₀.subgroupOf N)
    have h2 : ((P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom).map N.subtype =
        P₀.map (MulAut.conj (x : G)).toMonoidHom := by
      rw [hmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀N]
    have h3 : ((P : Subgroup G).subgroupOf N).map N.subtype = (P : Subgroup G) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN]
    rw [h2, h3] at h1
    exact h1
  have heq : CFSG.Open.rankThreeConj (x : G)⁻¹ P₀ = P₀ := hwc _ hle
  rw [CFSG.Open.rankThreeConj, inv_inv] at heq
  have h2 : ((P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom).map N.subtype =
      (P₀.subgroupOf N).map N.subtype := by
    have hmap : ((P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom).map N.subtype =
        ((P₀.subgroupOf N).map N.subtype).map (MulAut.conj (x : G)).toMonoidHom :=
      map_subgroupOf_conj (G := G) (N := N) x (P₀.subgroupOf N)
    rw [hmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀N]
    exact heq
  have h3 := congrArg (Subgroup.comap N.subtype) h2
  rwa [Subgroup.comap_map_eq_self_of_injective N.subtype_injective,
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at h3

private theorem exists_sylow_inf_op_p'p {p : ℕ} [Fact p.Prime] {N : Subgroup G}
    (T : Sylow p ↥N) :
    ∃ R : Sylow p ↥(CFSG.Op_p'p p ↥N),
      (R : Subgroup ↥(CFSG.Op_p'p p ↥N)).map (CFSG.Op_p'p p ↥N).subtype =
        (T : Subgroup ↥N) ⊓ CFSG.Op_p'p p ↥N := by
  classical
  have hWn : (CFSG.Op_p'p p ↥N).Normal := inferInstance
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf p (T : Subgroup ↥N) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  have hIsSylW : CFSG.ABGLocalTools.IsSylowOf p
      ((T : Subgroup ↥N) ⊓ CFSG.Op_p'p p ↥N) (CFSG.Op_p'p p ↥N) :=
    hTsyl.inf_of_le_normalizer le_top (by
      have h : Subgroup.normalizer ((CFSG.Op_p'p p ↥N) : Set ↥N) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr hWn
      rw [h])
  obtain ⟨R, hR⟩ := hIsSylW.exists_sylow_eq_subgroupOf
  exact ⟨R, by rw [hR, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]⟩

private theorem pPrimeCore_sup_sylow_eq {p : ℕ} [Fact p.Prime] {N : Subgroup G}
    (R : Sylow p ↥(CFSG.Op_p'p p ↥N)) :
    CFSG.pPrimeCore p ↥N ⊔
        (R : Subgroup ↥(CFSG.Op_p'p p ↥N)).map (CFSG.Op_p'p p ↥N).subtype =
      CFSG.Op_p'p p ↥N := by
  classical
  have hKle : CFSG.pPrimeCore p ↥N ≤ CFSG.Op_p'p p ↥N :=
    CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p
  have hquot : IsPGroup p (CFSG.Op_p'p p ↥N ⧸
      (CFSG.pPrimeCore p ↥N).subgroupOf (CFSG.Op_p'p p ↥N)) :=
    isPGroup_op_p'p_quotient (p := p) N
  have h :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient
      p Fact.out ((CFSG.pPrimeCore p ↥N).subgroupOf (CFSG.Op_p'p p ↥N)) inferInstance hquot R
  have himg := congrArg (Subgroup.map (CFSG.Op_p'p p ↥N).subtype) h
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKle,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at himg
  simpa [sup_comm] using himg

private theorem normalizer_inf_op_p'p_le {p : ℕ} [Fact p.Prime] {N P₀ : Subgroup G}
    (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N) (hP₀P : P₀ ≤ (P : Subgroup G))
    (hP₀nW : P₀.subgroupOf N ≤ CFSG.Op_p'p p ↥N)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀) :
    Subgroup.normalizer ((((P.subtype hPN : Subgroup ↥N) ⊓ CFSG.Op_p'p p ↥N : Subgroup ↥N) :
      Set ↥N)) ≤ (N ⊓ Subgroup.normalizer (P₀ : Set G)).subgroupOf N := by
  have hP₀N : P₀ ≤ N := hP₀P.trans hPN
  have hP₀nT : P₀.subgroupOf N ≤ (P.subtype hPN : Subgroup ↥N) := by
    rw [Sylow.coe_subtype]
    exact Subgroup.comap_mono (f := N.subtype) hP₀P
  have hP₀nle : P₀.subgroupOf N ≤ (P.subtype hPN : Subgroup ↥N) ⊓ CFSG.Op_p'p p ↥N :=
    le_inf hP₀nT hP₀nW
  intro x hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨x.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hN := map_subgroupOf_conj_eq P hPN hP₀N hwc x
    ((Subgroup.map_mono hP₀nle).trans (hx.le.trans inf_le_left))
  have h3 := congrArg (Subgroup.map N.subtype) hN
  have h5 : (P₀.subgroupOf N).map N.subtype = P₀ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀N]
  have hmap : ((P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom).map N.subtype =
      ((P₀.subgroupOf N).map N.subtype).map (MulAut.conj (x : G)).toMonoidHom :=
    map_subgroupOf_conj (G := G) (N := N) x (P₀.subgroupOf N)
  have h4 : ((P₀.subgroupOf N).map (MulAut.conj x).toMonoidHom).map N.subtype =
      P₀.map (MulAut.conj (x : G)).toMonoidHom := by
    rw [hmap, h5]
  rw [h4, h5] at h3
  exact h3

private theorem le_sup_inf_normalizer {p : ℕ} [Fact p.Prime] {N P₀ : Subgroup G}
    (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N) (hP₀P : P₀ ≤ (P : Subgroup G))
    (hP₀W : P₀ ≤ (CFSG.Op_p'p p ↥N).map N.subtype)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀) :
    N ≤ CFSG.Open.rankThreePrimeCore p N ⊔ (N ⊓ Subgroup.normalizer (P₀ : Set G)) := by
  classical
  set K₀ : Subgroup ↥N := CFSG.pPrimeCore p ↥N with hK₀
  set W₀ : Subgroup ↥N := CFSG.Op_p'p p ↥N with hW₀
  set T : Sylow p ↥N := P.subtype hPN with hT
  have hWn : W₀.Normal := hW₀ ▸ inferInstance
  have hK₀W : K₀ ≤ W₀ := CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p
  have hP₀nW : P₀.subgroupOf N ≤ W₀ := by
    have h := Subgroup.comap_mono (f := N.subtype) hP₀W
    rwa [Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at h
  obtain ⟨R₁, hR₁map⟩ := exists_sylow_inf_op_p'p (p := p) T
  have hStepS : K₀ ⊔ ((T : Subgroup ↥N) ⊓ W₀) = W₀ := by
    have h := pPrimeCore_sup_sylow_eq (p := p) (N := N) R₁
    rwa [hR₁map] at h
  have hfrat := Sylow.normalizer_sup_eq_top R₁
  rw [hR₁map] at hfrat
  have htop : (⊤ : Subgroup ↥N) ≤
      Subgroup.normalizer (((T : Subgroup ↥N) ⊓ W₀ : Subgroup ↥N) : Set ↥N) ⊔ K₀ := by
    rw [← hfrat]
    exact sup_le le_sup_left (hStepS.symm.le.trans
      (sup_le le_sup_right (le_sup_of_le_left Subgroup.le_normalizer)))
  have hNQ : Subgroup.normalizer (((T : Subgroup ↥N) ⊓ W₀ : Subgroup ↥N) : Set ↥N) ≤
      (N ⊓ Subgroup.normalizer (P₀ : Set G)).subgroupOf N :=
    normalizer_inf_op_p'p_le (p := p) P hPN hP₀P hP₀nW hwc
  have hle : Subgroup.normalizer (((T : Subgroup ↥N) ⊓ W₀ : Subgroup ↥N) : Set ↥N) ⊔ K₀ ≤
      ((N ⊓ Subgroup.normalizer (P₀ : Set G)) ⊔
        CFSG.Open.rankThreePrimeCore p N).subgroupOf N := by
    refine sup_le (hNQ.trans (Subgroup.comap_mono (f := N.subtype) le_sup_left)) ?_
    have h : (CFSG.Open.rankThreePrimeCore p N).subgroupOf N = K₀ := by
      have h1 : CFSG.Open.rankThreePrimeCore p N
          = (CFSG.pPrimeCore p ↥N).map N.subtype :=
        CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
          Fact.out N
      rw [hK₀, h1]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [← h]
    exact Subgroup.comap_mono (f := N.subtype) le_sup_right
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥N) ∈
      Subgroup.normalizer (((T : Subgroup ↥N) ⊓ W₀ : Subgroup ↥N) : Set ↥N) ⊔ K₀ :=
    htop trivial
  have hx' := Subgroup.mem_subgroupOf.mp (hle hmem)
  simpa [sup_comm] using hx'

private theorem not_dvd_card_mulAut_of_isCyclic_card_three_pow {p a : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {R : Subgroup G} (hcyc : IsCyclic ↥R) (hcard : Nat.card R = 3 ^ a) :
    ¬ p ∣ Nat.card (MulAut ↥R) := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [IsCyclic.card_mulAut, hcard, h0, pow_zero, Nat.totient_one]
    exact (Fact.out : p.Prime).not_dvd_one
  · have hAut : Nat.card (MulAut ↥R) = 3 ^ (a - 1) * (3 - 1) := by
      rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime_pow Nat.prime_three hpos]
    rw [hAut]
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h1 | h2
    · have hle : p ≤ 3 :=
        Nat.le_of_dvd (by norm_num) ((Fact.out : p.Prime).dvd_of_dvd_pow h1)
      omega
    · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega

private theorem exists_sylow_three_le_centralizer {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {N P₀ : Subgroup G} (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N)
    (hN : Group.IsSolvable ↥N) (hP₀P : P₀ ≤ (P : Subgroup G)) (hP₀ : Nat.card P₀ = p)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀)
    (hF1 : CFSG.Open.pRank 3 (CFSG.Open.rankThreePrimeCore p N) ≤ 1) :
    ∃ R : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 R (CFSG.Open.rankThreePrimeCore p N) ∧
        P₀ ≤ Subgroup.centralizer (R : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKN, hKnorm, hKcop⟩ := relPPrimeCore_facts (p := p) N
  have hP₀N : P₀ ≤ N := hP₀P.trans hPN
  have hP₀W : P₀ ≤ (CFSG.Op_p'p p ↥N).map N.subtype :=
    p₀_le_op_p'p_of_weaklyClosed P hPN hN hP₀P hP₀ hwc
  have hP₀p : IsPGroup p P₀ :=
    IsPGroup.of_card (by rw [hP₀]; exact (pow_one p).symm)
  have hbot : IsPGroup 3 (⊥ : Subgroup G) :=
    IsPGroup.of_card (by rw [Subgroup.card_bot]; exact (pow_zero 3).symm)
  obtain ⟨R, hRsyl, -, hP₀R⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := p) (r := 3)
      Fact.out Nat.prime_three hP₀p (hP₀N.trans hKnorm)
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hKcop) bot_le hbot
      (by
        have htop : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
          Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)
        rw [htop]
        exact le_top)
  have hRcyc : IsCyclic ↥R :=
    isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hRsyl.isPGroup hRsyl.le hF1
  have hAutR : ¬ p ∣ Nat.card (MulAut ↥R) :=
    not_dvd_card_mulAut_of_isCyclic_card_three_pow (p := p) hp5 hRcyc hRsyl.card_eq
  exact ⟨R, hRsyl, le_centralizer_of_isPGroup_of_not_dvd_card_mulAut Fact.out hP₀p hP₀R hAutR⟩

private theorem not_dvd_three_relIndex_centralizer {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {N P₀ : Subgroup G} (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N)
    (hN : Group.IsSolvable ↥N) (hP₀P : P₀ ≤ (P : Subgroup G)) (hP₀ : Nat.card P₀ = p)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀)
    (hF1 : CFSG.Open.pRank 3 (CFSG.Open.rankThreePrimeCore p N) ≤ 1) :
    ¬ 3 ∣ (CFSG.Open.rankThreePrimeCore p N ⊓
      Subgroup.centralizer (P₀ : Set G)).relIndex (CFSG.Open.rankThreePrimeCore p N) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hRsyl, hP₀centR⟩ := exists_sylow_three_le_centralizer hp5 P hPN hN hP₀P hP₀ hwc hF1
  have hRcent : R ≤ Subgroup.centralizer (P₀ : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hP₀centR hx) r hr).symm
  have hRK : R ≤ CFSG.Open.rankThreePrimeCore p N := hRsyl.le
  have hRC : R ≤ CFSG.Open.rankThreePrimeCore p N ⊓ Subgroup.centralizer (P₀ : Set G) :=
    le_inf hRK hRcent
  have h3 : ¬ 3 ∣ R.relIndex (CFSG.Open.rankThreePrimeCore p N) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
  have hmult := Subgroup.relIndex_mul_relIndex R
    (CFSG.Open.rankThreePrimeCore p N ⊓ Subgroup.centralizer (P₀ : Set G))
    (CFSG.Open.rankThreePrimeCore p N) hRC inf_le_left
  intro h
  apply h3
  rw [← hmult]
  exact dvd_mul_of_dvd_right h _

private theorem relIndex_normalizer_eq {p : ℕ} [Fact p.Prime] {N P₀ : Subgroup G}
    (hNsup : N ≤ CFSG.Open.rankThreePrimeCore p N ⊔
      (N ⊓ Subgroup.normalizer (P₀ : Set G))) :
    (N ⊓ Subgroup.normalizer (P₀ : Set G)).relIndex N =
      (CFSG.Open.rankThreePrimeCore p N ⊓
        Subgroup.normalizer (P₀ : Set G)).relIndex (CFSG.Open.rankThreePrimeCore p N) := by
  classical
  obtain ⟨hKN, hKnorm, -⟩ := relPPrimeCore_facts (p := p) N
  set K : Subgroup G := CFSG.Open.rankThreePrimeCore p N with hK
  set M : Subgroup G := N ⊓ Subgroup.normalizer (P₀ : Set G) with hM
  have hMN : M ≤ N := by rw [hM]; exact inf_le_left
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) := hMN.trans hKnorm
  have hsup : K ⊔ M = N := le_antisymm (sup_le hKN inf_le_left) hNsup
  have hprod : Nat.card ↥(K ⊔ M) * Nat.card ↥(K ⊓ M) = Nat.card K * Nat.card M := by
    have h :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := M) (K := K) hMnormK
    simpa [sup_comm, inf_comm, mul_comm] using h
  have h1 : M.relIndex N * Nat.card M = Nat.card N := by
    have := Subgroup.relIndex_mul_card (H := M) (K := N)
    rwa [inf_eq_left.mpr hMN] at this
  have h2 : (K ⊓ M).relIndex K * Nat.card ↥(K ⊓ M) = Nat.card K := by
    have := Subgroup.relIndex_mul_card (H := K ⊓ M) (K := K)
    rwa [inf_eq_left.mpr (inf_le_left : K ⊓ M ≤ K)] at this
  have h3 : Nat.card N * Nat.card ↥(K ⊓ M) = Nat.card K * Nat.card M := by
    rw [← hsup]
    exact hprod
  have h4 : (M.relIndex N * Nat.card ↥(K ⊓ M)) * Nat.card M = Nat.card K * Nat.card M := by
    rw [← h3, ← h1]
    ring
  have h5 : M.relIndex N * Nat.card ↥(K ⊓ M) = Nat.card K :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
  have hEq : M.relIndex N = (K ⊓ M).relIndex K :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h5]; exact h2.symm)
  have hKM : K ⊓ M = K ⊓ Subgroup.normalizer (P₀ : Set G) := by
    rw [hM, ← inf_assoc, inf_eq_left.mpr hKN]
  rw [hEq, hKM]

theorem not_dvd_three_relIndex_normalizer {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {N P₀ : Subgroup G} (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N)
    (hN : Group.IsSolvable ↥N) (hP₀P : P₀ ≤ (P : Subgroup G)) (hP₀ : Nat.card P₀ = p)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀)
    (hF1 : CFSG.Open.pRank 3 (CFSG.Open.rankThreePrimeCore p N) ≤ 1) :
    ¬ 3 ∣ (N ⊓ Subgroup.normalizer (P₀ : Set G)).relIndex N := by
  classical
  have hcent : ¬ 3 ∣ (CFSG.Open.rankThreePrimeCore p N ⊓
      Subgroup.centralizer (P₀ : Set G)).relIndex (CFSG.Open.rankThreePrimeCore p N) :=
    not_dvd_three_relIndex_centralizer hp5 P hPN hN hP₀P hP₀ hwc hF1
  have hNG : ¬ 3 ∣ (CFSG.Open.rankThreePrimeCore p N ⊓
      Subgroup.normalizer (P₀ : Set G)).relIndex (CFSG.Open.rankThreePrimeCore p N) := by
    intro h
    have hle : CFSG.Open.rankThreePrimeCore p N ⊓ Subgroup.centralizer (P₀ : Set G) ≤
        CFSG.Open.rankThreePrimeCore p N ⊓ Subgroup.normalizer (P₀ : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le_normalizer (P₀ : Set G))
    exact hcent (h.trans
      (Subgroup.relIndex_dvd_of_le_left (CFSG.Open.rankThreePrimeCore p N) hle))
  have hP₀W : P₀ ≤ (CFSG.Op_p'p p ↥N).map N.subtype :=
    p₀_le_op_p'p_of_weaklyClosed P hPN hN hP₀P hP₀ hwc
  rw [relIndex_normalizer_eq (le_sup_inf_normalizer P hPN hP₀P hP₀W hwc)]
  exact hNG

theorem exists_conj_le_normalizer_of_weaklyClosed {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) {N P₀ Q : Subgroup G} (P : Sylow p G)
    (hPN : (P : Subgroup G) ≤ N) (hN : Group.IsSolvable ↥N) (hP₀P : P₀ ≤ (P : Subgroup G))
    (hP₀ : Nat.card P₀ = p)
    (hwc : ∀ g : G, CFSG.Open.rankThreeConj g P₀ ≤ (P : Subgroup G) →
      CFSG.Open.rankThreeConj g P₀ = P₀)
    (hF1 : CFSG.Open.pRank 3 (CFSG.Open.rankThreePrimeCore p N) ≤ 1)
    (hQN : Q ≤ N) (hQ : IsPGroup 3 Q) :
    ∃ g ∈ N, Q.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (P₀ : Set G) := by
  classical
  haveI : Fact p.Prime := ‹Fact p.Prime›
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup G := N ⊓ Subgroup.normalizer (P₀ : Set G) with hM
  have hIdx : ¬ 3 ∣ M.relIndex N := by
    rw [hM]
    exact not_dvd_three_relIndex_normalizer hp5 P hPN hN hP₀P hP₀ hwc hF1
  obtain ⟨R, hRsylM⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 3) M
  have hRM : R ≤ M := hRsylM.le
  have hR3 : IsPGroup 3 R := hRsylM.isPGroup
  have hRdvd : ¬ 3 ∣ R.relIndex M :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsylM).2.2
  have hRsylN : CFSG.ABGLocalTools.IsSylowOf 3 R N := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hRM.trans inf_le_left, hR3, ?_⟩
    have hmult := Subgroup.relIndex_mul_relIndex R M N hRM (inf_le_left : M ≤ N)
    intro h3
    rw [← hmult] at h3
    rcases Nat.prime_three.dvd_mul.mp h3 with h | h
    · exact hRdvd h
    · exact hIdx h
  have hQp : IsPGroup 3 (Q.subgroupOf N) := hQ.comap_subtype
  obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
  have hQ'syl : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup ↥N).map N.subtype) N :=
    ⟨S, rfl⟩
  have hQQ' : Q ≤ (S : Subgroup ↥N).map N.subtype := by
    calc Q = (Q.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hQN).symm
      _ ≤ _ := Subgroup.map_mono hQS
  obtain ⟨k, hk, hconj⟩ :=
    CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hRsylN hQ'syl
  refine ⟨k⁻¹, N.inv_mem hk, ?_⟩
  have hRnorm : R ≤ Subgroup.normalizer (P₀ : Set G) := hRM.trans inf_le_right
  rintro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hz' : k⁻¹ * z * k ∈ R := (hconj z).mp (hQQ' hz)
  simpa [MulAut.conj_apply] using hRnorm hz'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

end
