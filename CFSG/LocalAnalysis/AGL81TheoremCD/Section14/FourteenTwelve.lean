module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThreeCaseTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.RankThree.PartTwo.Sec20.One
import CFSG.Goldschmidt75.Sec45

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def FiveFourteenA11Use : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K T : Subgroup G),
    X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → K ≤ X → (K.subgroupOf X).Normal → K ⊔ T = X →
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 11)) →
    (∀ Y : Subgroup G, Y ≤ X → CFSG.Open.IsSubnormal Y X →
      ¬ CFSG.AGLEmbedding.InClassXBlock Y) →
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧
      X ≤ Subgroup.normalizer (C : Set G)

@[expose] def FiveTwentyFiveS11Use : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X L T R : Subgroup G) (φ : ↥X →* Equiv.Perm (Fin 11))
    (i j : Fin 11),
    X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → (L.subgroupOf X).Normal →
    IsTwoPrimeComponentIn L X → L ⊔ T = X → Function.Surjective φ →
    φ.ker = (pCoreOf 2 X).subgroupOf X → pCoreOf 2 X ≤ R → R ≤ T → i ≠ j →
    ((Subgroup.normalizer (R : Set G) ⊓ X).subgroupOf X).map φ =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) →
    (∀ Y : Subgroup G, Y ≤ X → CFSG.Open.IsSubnormal Y X →
      ¬ CFSG.AGLEmbedding.InClassXBlock Y) →
    ∃ T₀ : Subgroup G, T₀ ≠ ⊥ ∧ T₀ ≤ R ∧ (T₀.subgroupOf R).Characteristic ∧
      X ≤ Subgroup.normalizer (T₀ : Set G)

noncomputable def actPerm {K : Subgroup G} (e : threeStar K ≃* alternatingGroup (Fin 11)) :
    ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 11) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 11)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11 (by norm_num)
        (by norm_num))).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (actStar K))

theorem conjNormal_actPerm {K : Subgroup G} (e : threeStar K ≃* alternatingGroup (Fin 11))
    (n : ↥(Subgroup.normalizer (K : Set G))) :
    MulAut.conjNormal (H := alternatingGroup (Fin 11)) (actPerm e n) =
      MulAut.congr e (actStar K n) := by
  classical
  let hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
    (by norm_num) (by norm_num)
  let f : Equiv.Perm (Fin 11) ≃* MulAut (alternatingGroup (Fin 11)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 11))) hbij
  change MulAut.conjNormal (f.symm (MulAut.congr e (actStar K n))) = _
  exact f.apply_symm_apply _

private theorem conjNormal_coe_eq_conj (q : alternatingGroup (Fin 11)) :
    MulAut.conjNormal (H := alternatingGroup (Fin 11)) (q : Equiv.Perm (Fin 11)) =
      MulAut.conj q := by
  ext z
  rfl

theorem actPerm_of_mem {K : Subgroup G} (e : threeStar K ≃* alternatingGroup (Fin 11))
    (n : ↥(Subgroup.normalizer (K : Set G))) (hn : (n : G) ∈ K) :
    actPerm e n = ((e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨(n : G), hn⟩) :
      alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) := by
  classical
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
    (by norm_num) (by norm_num)
  apply hbij.1
  rw [conjNormal_actPerm]
  let q : threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨(n : G), hn⟩
  have hstar : actStar K n = MulAut.conj q := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) z
    rw [actStar_mk, MulAut.conj_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hcongr : MulAut.congr e (MulAut.conj q) = MulAut.conj (e q) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv, mul_assoc]
  rw [hstar, hcongr]
  exact (conjNormal_coe_eq_conj (e q)).symm

theorem actStar_eq_one_of_actPerm_eq_one {K : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {n : ↥(Subgroup.normalizer (K : Set G))}
    (h : actPerm e n = 1) : actStar K n = 1 := by
  classical
  have hcongr : MulAut.conjNormal (H := alternatingGroup (Fin 11)) (actPerm e n) = 1 := by
    rw [h, map_one]
  rw [conjNormal_actPerm] at hcongr
  have h1 : (MulAut.congr e) (actStar K n) = (MulAut.congr e) 1 := by
    rw [map_one]
    exact hcongr
  exact (MulAut.congr e).injective h1

theorem actStar_eq_one_of_forall_commutator_mem {J : Subgroup G}
    (n : ↥(Subgroup.normalizer (J : Set G)))
    (h : ∀ x ∈ J, ⁅x, (n : G)⁆ ∈ (CFSG.pPrimeCore 3 ↥J).map J.subtype) :
    actStar J n = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hsubeq : O.subgroupOf J = CFSG.pPrimeCore 3 ↥J := by
    change ((CFSG.pPrimeCore 3 ↥J).map J.subtype).comap J.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) z
  rw [actStar_mk, MulAut.one_apply]
  apply QuotientGroup.eq.mpr
  rw [← hsubeq, Subgroup.mem_subgroupOf]
  have hx := h ((x : G)⁻¹) (J.inv_mem x.2)
  have hconv : ⁅((x : G)⁻¹), (n : G)⁆ =
      (x : G)⁻¹ * ((n : G) * (x : G) * (n : G)⁻¹) := by
    rw [commutatorElement_def]
    group
  have hinv : (((n : G) * (x : G) * (n : G)⁻¹))⁻¹ * (x : G) ∈ O := by
    have h1 : ((x : G)⁻¹ * ((n : G) * (x : G) * (n : G)⁻¹))⁻¹ ∈ O :=
      O.inv_mem (hconv ▸ hx)
    simpa using h1
  simpa using hinv

theorem map_actPerm_subgroupOf_eq_twoSet {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11}
    (hI : ((((K ⊓ M).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom) =
        a11TwoSetStab i j) :
    (((K ⊓ M).subgroupOf (Subgroup.normalizer (K : Set G))).map (actPerm e)) =
      (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    have hnKM : (n : G) ∈ K ⊓ M := Subgroup.mem_subgroupOf.mp hn
    have hnK : (n : G) ∈ K := hnKM.1
    rw [actPerm_of_mem e n hnK]
    rw [← hI]
    exact Subgroup.mem_map_of_mem (alternatingGroup (Fin 11)).subtype
      (Subgroup.mem_map_of_mem e.toMonoidHom
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
          (show (⟨(n : G), hnK⟩ : ↥K) ∈ (K ⊓ M).subgroupOf K from
            Subgroup.mem_subgroupOf.mpr hnKM)))
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← hI] at ha
    obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp ha
    obtain ⟨m, hm, hma⟩ := Subgroup.mem_map.mp hz
    have hmKM : (m : G) ∈ K ⊓ M := Subgroup.mem_subgroupOf.mp hm
    have hmK : (m : G) ∈ K := hmKM.1
    let n : ↥(Subgroup.normalizer (K : Set G)) := ⟨(m : G), Subgroup.le_normalizer hmK⟩
    have hn : n ∈ (K ⊓ M).subgroupOf (Subgroup.normalizer (K : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hmKM
    refine Subgroup.mem_map.mpr ⟨n, hn, ?_⟩
    rw [actPerm_of_mem e n hmK, ← hza]
    congr 1
    rw [← hma]
    congr 1

theorem S14Choice.noXBlock_of_le {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hK : KNormalAt M) (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) {X : Subgroup G}
    (hKX : kSub 3 M H ≤ X) (hXH : X ≤ H)
    (h2X : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ kSub 3 M H) :
    ∀ Y : Subgroup G, Y ≤ X → CFSG.Open.IsSubnormal Y X →
      ¬ CFSG.AGLEmbedding.InClassXBlock Y := by
  classical
  intro Y hYX hsub hblock
  let K : Subgroup G := kSub 3 M H
  have hKleH : K ≤ H := kSub_le 3 M H
  have hKH : H ≤ Subgroup.normalizer (K : Set G) := hK 3 E H h.hypCGen
  have hYXK : Y ≤ Subgroup.normalizer (K : Set G) := hYX.trans (hXH.trans hKH)
  have hNnormal : ((K ⊓ Y).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf hYXK Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hquot : IsPGroup 2 (↥Y ⧸ (K ⊓ Y).subgroupOf Y) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((K ⊓ Y).subgroupOf Y) z
    obtain ⟨k, hk⟩ := h2X (y : G) (hYX y.2)
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := (K ⊓ Y).subgroupOf Y) (y ^ 2 ^ k)).mpr
      (Subgroup.mem_subgroupOf.mpr ⟨hk, Y.pow_mem y.2 _⟩)
  have hNtop : (K ⊓ Y).subgroupOf Y = ⊤ := hblock.1.1 _ hquot
  have hYK : Y ≤ K := by
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥Y) ∈ (K ⊓ Y).subgroupOf Y := by
      rw [hNtop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hy').1
  have hsubK : CFSG.Open.IsSubnormal Y K := by
    have h := hsub.inf_of_le hKX
    change CFSG.Open.IsSubnormal (Y ⊓ K) K at h
    rwa [inf_comm, inf_eq_right.mpr hYK] at h
  have hKnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleH).mpr hKH
  have hsubH : CFSG.Open.IsSubnormal Y H :=
    hsubK.trans (CFSG.Open.IsSubnormal.step hKleH hKnormal (CFSG.Open.IsSubnormal.refl H))
  exact hX H Y (h.hypCGen.isMaxTwoLocal_of_mem_H2StarFam h.hypCGen.mem)
    (hYK.trans hKleH) hsubH hblock

theorem S14Choice.exists_char_normal_T {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet)
    (h514 : FiveFourteenA11Use) (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧
      kSub 3 M H ≤ Subgroup.normalizer (C : Set G) := by
  classical
  let K : Subgroup G := kSub 3 M H
  have hKH : K ≤ H := kSub_le 3 M H
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hT_H : CFSG.ABGLocalTools.IsSylowOf 2 T H :=
    h.isSylowOf_two_of_inf h2 hK hU hL hKF hT
  let X : Subgroup G := K ⊔ T
  have hKX : K ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hXH : X ≤ H := sup_le hKH hTH
  have hcharH : CFSG.QuasithinUnique.CharTwo H := h.cstar.charTwo H h.hypCGen.isTwoLocal
  have hcharX : CFSG.QuasithinUnique.CharTwo X :=
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hcharH hXH
      ((h.hypCGen.pCoreOf_two_le_of_isSylowOf hT).trans le_sup_right)
  have hTXsyl : CFSG.ABGLocalTools.IsSylowOf 2 T X := hT_H.of_le hTX hXH
  have hKnormalX : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr
      (hXH.trans (hK 3 E H h.hypCGen))
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := h.J_comp.2.2.1
  have hA11 : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* alternatingGroup (Fin 11)) := by
    simpa [IsA11Star, IsA11Type, threeStar, K] using h2.2
  have hquot : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 11)) :=
    nonempty_mulEquiv_quotient_pCore_two_of_a11 hq hA11
  have h2X : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K := by
    intro x hx
    exact CFSG.Quasithin.E1.exists_pow_mem_of_mem_sup hT.isPGroup
      (hTX.trans (hXH.trans (hK 3 E H h.hypCGen))) (by simpa [X] using hx)
  obtain ⟨C, hCne, hCT, hCchar, hKC⟩ :=
    h514 G X K T hcharX hTXsyl hKX hKnormalX (by rfl) hquot
      (h.noXBlock_of_le hK hX hKX hXH h2X)
  exact ⟨C, hCne, hCT, hCchar, hKX.trans hKC⟩

theorem actPerm_eq_one_or_swap {K M R : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : (((K ⊓ M).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom = a11TwoSetStab i j)
    (hR2 : IsPGroup 2 R) (hRinv : K ⊓ M ≤ Subgroup.normalizer (R : Set G))
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    {n : ↥(Subgroup.normalizer (K : Set G))} (hn : (n : G) ∈ R) :
    actPerm e n = 1 ∨ actPerm e n = Equiv.swap i j := by
  classical
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let ρ : ↥N →* Equiv.Perm (Fin 11) := actPerm e
  let Rsub : Subgroup ↥N := R.subgroupOf N
  let Ksub : Subgroup ↥N := (K ⊓ M).subgroupOf N
  let S : Subgroup (Equiv.Perm (Fin 11)) := Rsub.map ρ
  let A : Subgroup (Equiv.Perm (Fin 11)) := alternatingGroup (Fin 11)
  let D : Subgroup ↥A := S.comap A.subtype
  have hRsub2 : IsPGroup 2 Rsub := hR2.comap_subtype
  have hS2 : IsPGroup 2 S := hRsub2.map ρ
  have hD2 : IsPGroup 2 D := hS2.comap_subtype
  have hKsub_le_normR : Ksub ≤ Subgroup.normalizer (Rsub : Set ↥N) := by
    intro n' hn'
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
      have hnR : (n' : G) ∈ Subgroup.normalizer (R : Set G) :=
        hRinv (Subgroup.mem_subgroupOf.mp hn')
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hnR (r : G)).mp hrR)
    · intro hr
      have hnrR : (n' : G) * (r : G) * (n' : G)⁻¹ ∈ R := Subgroup.mem_subgroupOf.mp hr
      have hnR : (n' : G) ∈ Subgroup.normalizer (R : Set G) :=
        hRinv (Subgroup.mem_subgroupOf.mp hn')
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hnR (r : G)).mpr hnrR)
  have hXle : Ksub.map ρ ≤ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11))) :=
    (Subgroup.map_mono hKsub_le_normR).trans (Subgroup.le_normalizer_map ρ)
  have hXeq : Ksub.map ρ = (a11TwoSetStab i j).map A.subtype := by
    simpa [N, ρ, Ksub, A] using map_actPerm_subgroupOf_eq_twoSet e hI
  have hYle : (a11TwoSetStab i j).map A.subtype ≤
      Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11))) := hXeq ▸ hXle
  have h2set_le_normD : a11TwoSetStab i j ≤ Subgroup.normalizer (D : Set ↥A) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    have hxN : (x : Equiv.Perm (Fin 11)) ∈
        Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11))) :=
      hYle (Subgroup.mem_map_of_mem A.subtype hx)
    simpa using (Subgroup.mem_normalizer_iff.mp hxN (d : Equiv.Perm (Fin 11)))
  have hcomm_le : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤ a11TwoSetStab i j := by
    simpa using Subgroup.commutator_le_sup (a11TwoSetStab i j) (a11TwoSetStab i j)
  have hDnorm : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set ↥A) := hcomm_le.trans h2set_le_normD
  have hDbot : D = ⊥ := a11TwoSetStab_twoSubgroup_eq_bot hij hD2 hDnorm
  have hcomm : ∀ s ∈ S, ∀ x ∈ a11TwoSetStab i j,
      s * (x : Equiv.Perm (Fin 11)) = (x : Equiv.Perm (Fin 11)) * s := by
    intro s hs x hx
    let c : Equiv.Perm (Fin 11) := s * (x : Equiv.Perm (Fin 11)) * s⁻¹ *
      (x : Equiv.Perm (Fin 11))⁻¹
    have hxN : (x : Equiv.Perm (Fin 11)) ∈
        Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11))) :=
      hYle (Subgroup.mem_map_of_mem A.subtype hx)
    have hcS : c ∈ S := by
      have hinner : (x : Equiv.Perm (Fin 11)) * s⁻¹ * (x : Equiv.Perm (Fin 11))⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp hxN s⁻¹).mp (S.inv_mem hs)
      simpa [c, mul_assoc] using S.mul_mem hs hinner
    have hxA : (x : Equiv.Perm (Fin 11)) ∈ A := x.2
    have hAconj : s * (x : Equiv.Perm (Fin 11)) * s⁻¹ ∈ A :=
      (inferInstance : A.Normal).conj_mem (x : Equiv.Perm (Fin 11)) hxA s
    have hcA : c ∈ A := by
      dsimp [c]
      exact A.mul_mem hAconj (A.inv_mem hxA)
    have hc1 : c = 1 := by
      have hmem : (⟨c, hcA⟩ : ↥A) ∈ D := Subgroup.mem_comap.mpr hcS
      rw [hDbot] at hmem
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    calc s * (x : Equiv.Perm (Fin 11)) = c * ((x : Equiv.Perm (Fin 11)) * s) := by
          dsimp [c]
          group
      _ = 1 * ((x : Equiv.Perm (Fin 11)) * s) := by rw [hc1]
      _ = (x : Equiv.Perm (Fin 11)) * s := one_mul _
  have hσS : actPerm e n ∈ S := by
    refine Subgroup.mem_map.mpr ⟨n, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hn
    · rfl
  have hσcentral : ∀ x ∈ ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆,
      (MulAut.conjNormal (H := A) (actPerm e n)) x = x := by
    intro x hx
    have hxH : x ∈ a11TwoSetStab i j := hcomm_le hx
    have hcx := hcomm (actPerm e n) hσS x hxH
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hcx]
    group
  exact eq_one_or_eq_swap_of_forall_conjNormal_eq hij hσcentral

theorem IsMaxInvariantTwoIn.le_of_isPGroup {A R H P : Subgroup G}
    (hR : IsMaxInvariantTwoIn A R H) (hP2 : IsPGroup 2 P) (hPH : P ≤ H)
    (hRP : R ≤ Subgroup.normalizer (P : Set G)) (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ R := by
  classical
  have hPsup2 : IsPGroup 2 ↥(R ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' (p := 2) (H := R) (K := P) hR.2.1 hP2 hRP
  have hAsup : A ≤ Subgroup.normalizer (R ⊔ P : Subgroup G) :=
    (le_inf hR.2.2.1 hAP).trans (Subgroup.inf_normalizer_le_normalizer_sup R P)
  have hsup : R ⊔ P = R :=
    hR.2.2.2 (R ⊔ P) (sup_le hR.1 hPH) hPsup2 hAsup le_sup_left
  exact le_sup_right.trans (le_of_eq hsup)

theorem S14Choice.pCoreOf_two_le_of_isMaxInvariantTwoIn {M H E Q J R : Subgroup G}
    (h : S14Choice G M H E Q J) (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) :
    pCoreOf 2 H ≤ R := by
  classical
  let A : Subgroup G := kSub 3 M H ⊓ M
  have hP2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hPH : pCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 H
  have hRP : R ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hR.1.trans hHP
  have hAP : A ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (inf_le_left.trans (kSub_le 3 M H)).trans hHP
  exact IsMaxInvariantTwoIn.le_of_isPGroup hR hP2 hPH hRP hAP

theorem S14Choice.pCoreOf_two_kSub_eq_caseTwo {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) :
    pCoreOf 2 (kSub 3 M H) = (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := h.J_comp.2.2.1
  have hA11 : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃* alternatingGroup (Fin 11)) := by
    simpa [IsA11Star, IsA11Type, threeStar, K] using h2.2
  have hP : CFSG.pCore 2 ↥K = CFSG.pPrimeCore 3 ↥K :=
    pCore_two_eq_pPrimeCore_three_of_a11 hq hA11
  simpa [K, pCoreOf] using congrArg (Subgroup.map K.subtype) hP

theorem S14Choice.pCoreOf_two_kSub_le {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hK : KNormalAt M) : pCoreOf 2 (kSub 3 M H) ≤ pCoreOf 2 H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  have hKleH : K ≤ H := kSub_le 3 M H
  have hKH : H ≤ Subgroup.normalizer (K : Set G) := hK 3 E H h.hypCGen
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKH.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hPK : pCoreOf 2 K ≤ K := Subgroup.map_subtype_le _
  have hPH : pCoreOf 2 K ≤ H := hPK.trans hKleH
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hnormal : ((pCoreOf 2 K).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hHP
  exact CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hPH hnormal hP2

noncomputable def actPermSup {K R : Subgroup G} (e : threeStar K ≃* alternatingGroup (Fin 11))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : ↥(K ⊔ R) →* Equiv.Perm (Fin 11) :=
  (actPerm e).comp (Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK))

theorem actPermSup_ker_eq {K R : Subgroup G} (e : threeStar K ≃* alternatingGroup (Fin 11))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hO : pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    (actPermSup e hRK).ker = (pCoreOf 2 (K ⊔ R)).subgroupOf (K ⊔ R) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Subgroup G := K ⊔ R
  let φ : ↥X →* Equiv.Perm (Fin 11) := actPermSup e hRK
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
    (by norm_num) (by norm_num)
  have hzero : IsPGroup 2 φ.ker := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    have hxX : ((x : ↥X) : G) ∈ K ⊔ R := (x : ↥X).2
    obtain ⟨a, ha⟩ := CFSG.Quasithin.E1.exists_pow_mem_of_mem_sup hR2 hRK
      (X := K) (N := R) (q := ((x : ↥X) : G)) hxX
    have hφpow : φ ((x : ↥X) ^ 2 ^ a) = 1 := by
      rw [map_pow, show φ (x : ↥X) = 1 from x.2, one_pow]
    have hφ1 : φ (⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ : ↥X) = 1 := by
      rw [show (⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ : ↥X) = (x : ↥X) ^ 2 ^ a
        from Subtype.ext rfl]
      exact hφpow
    have h1 : actPerm e ⟨((x : ↥X) : G) ^ 2 ^ a, Subgroup.le_normalizer ha⟩ = 1 := by
      have hincl : Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK)
          ⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ =
          ⟨((x : ↥X) : G) ^ 2 ^ a, Subgroup.le_normalizer ha⟩ := Subtype.ext rfl
      have h2 : actPerm e (Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK)
          ⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩) = 1 := by
        show φ (⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ : ↥X) = 1
        exact hφ1
      rwa [hincl] at h2
    have h2 : ((e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
        ⟨((x : ↥X) : G) ^ 2 ^ a, ha⟩) :
        alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) = 1 := by
      rw [← actPerm_of_mem e ⟨((x : ↥X) : G) ^ 2 ^ a, Subgroup.le_normalizer ha⟩ ha]
      exact h1
    have h3 : e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
        ⟨((x : ↥X) : G) ^ 2 ^ a, ha⟩) = 1 := Subtype.ext h2
    have h4 : (⟨((x : ↥X) : G) ^ 2 ^ a, ha⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K :=
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K) _).mp
        ((e.map_eq_one_iff).mp h3)
    have h6 : ((x : ↥X) : G) ^ 2 ^ a ∈ pCoreOf 2 K := by
      rw [hO]
      exact Subgroup.mem_map_of_mem K.subtype h4
    have hP2 : IsPGroup 2 ((pCoreOf 2 K).subgroupOf X) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_subtype
    have hxP : (⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ : ↥X) ∈
        (pCoreOf 2 K).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr h6
    obtain ⟨b, hb⟩ := (isPGroup_iff_pow_pow_eq_one.mp hP2)
      (⟨⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩, hxP⟩ :
        ↥((pCoreOf 2 K).subgroupOf X))
    have hb' : (⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ : ↥X) ^ 2 ^ b = 1 :=
      congrArg Subtype.val hb
    have hb2 : ((x : ↥X) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      rw [show (⟨((x : ↥X) : G) ^ 2 ^ a, mem_sup_left ha⟩ : ↥X) = (x : ↥X) ^ 2 ^ a
        from Subtype.ext rfl] at hb'
      exact hb'
    refine ⟨a + b, ?_⟩
    apply Subtype.ext
    show (x : ↥X) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact hb2
  let Kerg : Subgroup G := φ.ker.map X.subtype
  have hKergnorm : (Kerg.subgroupOf X).Normal := by
    have hEq : Kerg.subgroupOf X = φ.ker := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, hzy⟩
        have hzy' : z = y := Subtype.ext hzy
        rwa [hzy'] at hz
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [hEq]
    exact MonoidHom.normal_ker φ
  have hKerg2 : IsPGroup 2 Kerg := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (y : Kerg).2
    obtain ⟨b, hb⟩ := (isPGroup_iff_pow_pow_eq_one.mp hzero) (⟨z, hz⟩ : ↥φ.ker)
    have hb' : z ^ 2 ^ b = 1 := congrArg Subtype.val hb
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change ((y : G) ^ 2 ^ b) = ((1 : ↥Kerg) : G)
    rw [← hzy, ← map_pow, hb', map_one]
    rfl
  have hKergle : Kerg ≤ pCoreOf 2 X :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2
      (Subgroup.map_subtype_le _) hKergnorm hKerg2
  refine le_antisymm (fun x hx => ?_) (fun y hy => ?_)
  · rw [Subgroup.mem_subgroupOf]
    exact hKergle (Subgroup.mem_map_of_mem X.subtype hx)
  · rw [Subgroup.mem_subgroupOf] at hy
    have hPX : pCoreOf 2 X ≤ X := Subgroup.map_subtype_le _
    have hXP : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 X
    have hPXnorm : ((pCoreOf 2 X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr hXP
    have hKXnorm : (K.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hRK)
    have hcomm : ∀ k ∈ K, ⁅k, (y : G)⁆ ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
      intro k hk
      have hkX : k ∈ X := Subgroup.mem_sup_left hk
      have hcommK : ⁅k, (y : G)⁆ ∈ K := by
        have hconj : (y : G) * k⁻¹ * (y : G)⁻¹ ∈ K :=
          Subgroup.mem_subgroupOf.mp
            (hKXnorm.conj_mem ⟨k⁻¹, Subgroup.mem_sup_left (K.inv_mem hk)⟩
              (Subgroup.mem_subgroupOf.mpr (K.inv_mem hk)) y)
        have heq : ⁅k, (y : G)⁆ = k * ((y : G) * k⁻¹ * (y : G)⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [heq]
        exact K.mul_mem hk hconj
      have hcommP : ⁅k, (y : G)⁆ ∈ pCoreOf 2 X := by
        have hconjP : k * (y : G) * k⁻¹ ∈ pCoreOf 2 X :=
          Subgroup.mem_subgroupOf.mp
            (hPXnorm.conj_mem ⟨(y : G), y.2⟩ (Subgroup.mem_subgroupOf.mpr hy)
              ⟨k, hkX⟩)
        have heq : ⁅k, (y : G)⁆ = (k * (y : G) * k⁻¹) * (y : G)⁻¹ := by
          rw [commutatorElement_def]
        rw [heq]
        exact (pCoreOf 2 X).mul_mem hconjP ((pCoreOf 2 X).inv_mem hy)
      have hKPnorm : ((K ⊓ pCoreOf 2 X).subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
          ((le_inf Subgroup.le_normalizer (le_sup_left.trans hXP)).trans
            Subgroup.inf_normalizer_le_normalizer_inf)
      have hPX2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
      have hKP2 : IsPGroup 2 ↥(K ⊓ pCoreOf 2 X) :=
        IsPGroup.to_le (K := pCoreOf 2 X) (H := K ⊓ pCoreOf 2 X) hPX2 inf_le_right
      have hKPle : K ⊓ pCoreOf 2 X ≤ pCoreOf 2 K :=
        CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 inf_le_left
          hKPnorm hKP2
      exact hO ▸ hKPle ⟨hcommK, hcommP⟩
    have hyn : (y : G) ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hKXnorm y.2
    have hstar : actStar K ⟨(y : G), hyn⟩ = 1 :=
      actStar_eq_one_of_forall_commutator_mem ⟨(y : G), hyn⟩ hcomm
    have hperm : actPerm e ⟨(y : G), hyn⟩ = 1 := by
      have hconj : MulAut.conjNormal (H := alternatingGroup (Fin 11))
          (actPerm e ⟨(y : G), hyn⟩) = 1 := by
        rw [conjNormal_actPerm, hstar, map_one]
      exact hbij.1 (by rw [hconj, map_one])
    show actPerm e (Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK) y) = 1
    rw [show Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK) y =
      ⟨(y : G), hyn⟩ from Subtype.ext rfl]
    exact hperm

theorem actPermSup_surjective {K R : Subgroup G} (e : threeStar K ≃* alternatingGroup (Fin 11))
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) {i j : Fin 11} (hij : i ≠ j)
    {r : G} (hr : r ∈ R) (hτ : actPerm e ⟨r, hRK hr⟩ = Equiv.swap i j) :
    Function.Surjective (actPermSup e hRK) := by
  classical
  have hτm : actPermSup e hRK ⟨r, Subgroup.mem_sup_right hr⟩ =
      Equiv.swap i j := by
    have h1 : Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK)
        ⟨r, Subgroup.mem_sup_right hr⟩ = ⟨r, hRK hr⟩ := Subtype.ext rfl
    show actPerm e (Subgroup.inclusion _ ⟨r, Subgroup.mem_sup_right hr⟩) = _
    rw [h1, hτ]
  have hA : ∀ τ : Equiv.Perm (Fin 11), Equiv.Perm.sign τ = 1 →
      τ ∈ (actPermSup e hRK).range := by
    intro τ hτ1
    have hτA : τ ∈ alternatingGroup (Fin 11) := by
      rwa [Equiv.Perm.mem_alternatingGroup]
    obtain ⟨q, hq⟩ := e.surjective ⟨τ, hτA⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) q
    refine ⟨⟨(k : G), Subgroup.mem_sup_left k.2⟩, ?_⟩
    have h1 : Subgroup.inclusion (sup_le Subgroup.le_normalizer hRK)
        ⟨(k : G), Subgroup.mem_sup_left k.2⟩ =
        ⟨(k : G), Subgroup.le_normalizer k.2⟩ := Subtype.ext rfl
    show actPerm e (Subgroup.inclusion _ ⟨(k : G), Subgroup.mem_sup_left k.2⟩) = τ
    rw [h1, actPerm_of_mem e _ k.2]
    exact congrArg (fun z : alternatingGroup (Fin 11) => (z : Equiv.Perm (Fin 11))) hq
  intro σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact hA σ h
  · have hodd : Equiv.Perm.sign (Equiv.swap i j) = -1 := Equiv.Perm.sign_swap hij
    have hσ : Equiv.Perm.sign (σ * (Equiv.swap i j)⁻¹) = 1 := by
      rw [Equiv.Perm.sign_mul, h, map_inv, hodd]
      norm_num
    obtain ⟨u, hu⟩ := hA _ hσ
    refine ⟨u * ⟨r, Subgroup.mem_sup_right hr⟩, ?_⟩
    rw [map_mul, hu, hτm]
    group

theorem map_actPermSup_normalizer_eq {K R : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    {i j : Fin 11} (hij : i ≠ j)
    (hker : (actPermSup e hRK).ker ≤ R.subgroupOf (K ⊔ R))
    (hR1 : ∀ (r : G) (hr : r ∈ R),
      actPerm e ⟨r, hRK hr⟩ = 1 ∨ actPerm e ⟨r, hRK hr⟩ = Equiv.swap i j)
    {r : G} (hr : r ∈ R) (hτ : actPerm e ⟨r, hRK hr⟩ = Equiv.swap i j) :
    ((Subgroup.normalizer (R : Set G) ⊓ (K ⊔ R)).subgroupOf (K ⊔ R)).map (actPermSup e hRK) =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) := by
  classical
  let X : Subgroup G := K ⊔ R
  let φ : ↥X →* Equiv.Perm (Fin 11) := actPermSup e hRK
  let Rsub : Subgroup ↥X := R.subgroupOf X
  have hφsurj : Function.Surjective φ := actPermSup_surjective e hRK hij hr hτ
  have hφval : ∀ (y : ↥X) (hy : (y : G) ∈ R),
      φ y = actPerm e ⟨(y : G), hRK hy⟩ := fun y _ =>
    congrArg (actPerm e) (Subtype.ext rfl)
  have hRhat : Rsub.map φ = Subgroup.zpowers (Equiv.swap i j) := by
    apply le_antisymm
    · rintro z ⟨y, hy, rfl⟩
      rcases hR1 (y : G) (Subgroup.mem_subgroupOf.mp hy) with h1 | h1
      · rw [hφval y (Subgroup.mem_subgroupOf.mp hy), h1]
        exact Subgroup.one_mem _
      · rw [hφval y (Subgroup.mem_subgroupOf.mp hy), h1]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨r, Subgroup.mem_sup_right hr⟩, Subgroup.mem_subgroupOf.mpr hr, ?_⟩
      rw [hφval ⟨r, Subgroup.mem_sup_right hr⟩ hr]
      exact hτ
  have hpre : Subgroup.comap φ (Rsub.map φ) = Rsub := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_comap] at hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      have h1 : φ (z⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, ← hzy, inv_mul_cancel]
      have h2 : z⁻¹ * y ∈ Rsub := hker (MonoidHom.mem_ker.mpr h1)
      have hy' : y = z * (z⁻¹ * y) := by group
      rw [hy']
      exact Rsub.mul_mem hz h2
    · intro y hy
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_map_of_mem φ hy
  have hnormmap : (Subgroup.normalizer (Rsub : Set ↥X)).map φ =
      Subgroup.normalizer (Rsub.map φ : Set (Equiv.Perm (Fin 11))) := by
    have hcomap := Subgroup.comap_normalizer_eq_of_surjective (H := Rsub.map φ) hφsurj
    rw [hpre] at hcomap
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective hφsurj _
  have hsubgroup : (Subgroup.normalizer (R : Set G) ⊓ X).subgroupOf X =
      Subgroup.normalizer (Rsub : Set ↥X) := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.subgroupOf_normalizer_eq (le_sup_right : R ≤ X)
  have hτord : orderOf (Equiv.swap i j) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, Equiv.swap_mul_self]
    · intro h
      have h1 := congrArg (fun f : Equiv.Perm (Fin 11) => f i) h
      rw [Equiv.swap_apply_left] at h1
      exact hij h1.symm
  have hzpow : Subgroup.normalizer (Subgroup.zpowers (Equiv.swap i j) :
      Set (Equiv.Perm (Fin 11))) =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) :=
    CFSG.Goldschmidt75.normalizer_zpowers_eq hτord
  calc ((Subgroup.normalizer (R : Set G) ⊓ X).subgroupOf X).map φ
      = (Subgroup.normalizer (Rsub : Set ↥X)).map φ := by rw [hsubgroup]
    _ = Subgroup.normalizer (Rsub.map φ : Set (Equiv.Perm (Fin 11))) := hnormmap
    _ = Subgroup.normalizer (Subgroup.zpowers (Equiv.swap i j) :
          Set (Equiv.Perm (Fin 11))) := by rw [hRhat]
    _ = Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) := hzpow

theorem S14Choice.kSub_le_normalizer_of_actStar_eq_one {M H E Q R : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H)
    (h1 : ∀ n : ↥(Subgroup.normalizer (kSub 3 M H : Set G)), (n : G) ∈ R →
      actStar (kSub 3 M H) n = 1) :
    kSub 3 M H ≤ Subgroup.normalizer (R : Set G) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hKleH : K ≤ H := kSub_le 3 M H
  have hHO : H ≤ Subgroup.normalizer (K : Set G) := hK 3 E H h.hypCGen
  have hPO : pCoreOf 2 K = O := h.pCoreOf_two_kSub_eq_caseTwo h2
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hO2 : IsPGroup 2 O := hPO ▸ hP2
  have hOK : O ≤ K := by
    rw [← hPO]
    exact Subgroup.map_subtype_le _
  have hOH : O ≤ H := hOK.trans hKleH
  have hPH : pCoreOf 2 K ≤ H := by
    rw [hPO]
    exact hOH
  have hOnormal : (O.subgroupOf H).Normal := by
    rw [← hPO]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr
      (hHO.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hOlePH : O ≤ pCoreOf 2 H :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hOH hOnormal hO2
  have hOR : O ≤ R := hOlePH.trans (h.pCoreOf_two_le_of_isMaxInvariantTwoIn hR)
  have hRleN : R ≤ Subgroup.normalizer (K : Set G) := hR.1.trans hHO
  have hconj : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R := by
    intro k hk r hr
    let n : ↥(Subgroup.normalizer (K : Set G)) := ⟨r, hRleN hr⟩
    have hn : (n : G) ∈ R := hr
    have hcomm : ⁅k, r⁆ ∈ O :=
      commutator_mem_pPrimeCore_of_actStar_eq_one (J := K) n ⟨k, hk⟩ (h1 n hn)
    have hcommR : ⁅k, r⁆ ∈ R := hOR hcomm
    have heq : k * r * k⁻¹ = ⁅k, r⁆ * r := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact R.mul_mem hcommR hr
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · exact hconj k hk r
  · intro hr
    have hkinv : k⁻¹ ∈ K := K.inv_mem hk
    have h := hconj k⁻¹ hkinv (k * r * k⁻¹) hr
    have heq : k⁻¹ * (k * r * k⁻¹) * (k⁻¹)⁻¹ = r := by group
    rwa [heq] at h

theorem S14Choice.exists_char_normal_R {M H E Q R : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet)
    (h525 : FiveTwentyFiveS11Use) (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
      kSub 3 M H ≤ Subgroup.normalizer (C : Set G) := by
  classical
  obtain ⟨e, i, j, hij, hI⟩ := h.exists_twoSet h2 hK hU hL hKF
  let K : Subgroup G := kSub 3 M H
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := hR.1.trans (hK 3 E H h.hypCGen)
  have hR1 : ∀ (r : G) (hr : r ∈ R),
      actPerm e ⟨r, hRK hr⟩ = 1 ∨ actPerm e ⟨r, hRK hr⟩ = Equiv.swap i j :=
    fun r hr => actPerm_eq_one_or_swap e hij hI hR.2.1 hR.2.2.1 hRK hr
  by_cases htriv : ∀ (r : G) (hr : r ∈ R), actPerm e ⟨r, hRK hr⟩ = 1
  · have hstar : ∀ n : ↥(Subgroup.normalizer (kSub 3 M H : Set G)), (n : G) ∈ R →
        actStar (kSub 3 M H) n = 1 := by
      intro n hn
      exact actStar_eq_one_of_actPerm_eq_one e (by simpa using htriv (n : G) hn)
    have hKNR : kSub 3 M H ≤ Subgroup.normalizer (R : Set G) :=
      h.kSub_le_normalizer_of_actStar_eq_one h2 hK hR hstar
    have hO2ne : pCoreOf 2 (kSub 3 M H) ≠ ⊥ := h.pCoreOf_two_kSub_ne_bot_caseTwo hK
    have hO2R : pCoreOf 2 (kSub 3 M H) ≤ R :=
      (h.pCoreOf_two_kSub_le hK).trans (h.pCoreOf_two_le_of_isMaxInvariantTwoIn hR)
    have hRne : R ≠ ⊥ := by
      intro hbot
      exact hO2ne (le_bot_iff.mp (hbot ▸ hO2R))
    have hchar : (R.subgroupOf R).Characteristic := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    exact ⟨R, hRne, le_rfl, hchar, hKNR⟩
  · push Not at htriv
    obtain ⟨r, hr, hne⟩ := htriv
    have hτ : actPerm e ⟨r, hRK hr⟩ = Equiv.swap i j := by
      rcases hR1 r hr with h1 | h1
      · exact absurd h1 hne
      · exact h1
    let X : Subgroup G := K ⊔ R
    let φ : ↥X →* Equiv.Perm (Fin 11) := actPermSup e hRK
    have hKX : K ≤ X := le_sup_left
    have hXR : R ≤ X := le_sup_right
    have hXH : X ≤ H := sup_le (kSub_le 3 M H) hR.1
    have hcharH : CFSG.QuasithinUnique.CharTwo H := h.cstar.charTwo H h.hypCGen.isTwoLocal
    have hOHX : pCoreOf 2 H ≤ X :=
      (h.pCoreOf_two_le_of_isMaxInvariantTwoIn hR).trans hXR
    have hcharX : CFSG.QuasithinUnique.CharTwo X :=
      CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hcharH hXH hOHX
    obtain ⟨T', hT', hRT'⟩ :=
      CFSG.RankThree.PartOne.exists_isSylowOf_ge (p := 2) (K := X) (Q := R) hXR hR.2.1
    have hKnormalX : (K.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr
        (sup_le Subgroup.le_normalizer hRK)
    have hTwoComp : IsTwoPrimeComponentIn K X :=
      ⟨hKX, hKnormalX.isSubnormal, h.J_comp.2.2.1, h.J_comp.2.2.2⟩
    have hsup : K ⊔ T' = X := by
      have h1 : K ⊔ R ≤ K ⊔ T' := sup_le_sup le_rfl hRT'
      exact le_antisymm (sup_le hKX hT'.le) (by simpa [X] using h1)
    have hφsurj : Function.Surjective φ := actPermSup_surjective e hRK hij hr hτ
    have hkerEq : φ.ker = (pCoreOf 2 X).subgroupOf X :=
      actPermSup_ker_eq e hRK hR.2.1 (h.pCoreOf_two_kSub_eq_caseTwo h2)
    have hP2X : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hPX : pCoreOf 2 X ≤ X := Subgroup.map_subtype_le _
    have hXP : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 X
    have hO2Xle : pCoreOf 2 X ≤ R :=
      IsMaxInvariantTwoIn.le_of_isPGroup hR hP2X (hPX.trans hXH) (hXR.trans hXP)
        ((inf_le_left.trans hKX).trans hXP)
    have hker : φ.ker ≤ R.subgroupOf X := by
      rw [hkerEq]
      exact Subgroup.subgroupOf_mono X hO2Xle
    have hnormalizer : ((Subgroup.normalizer (R : Set G) ⊓ X).subgroupOf X).map φ =
        Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) :=
      map_actPermSup_normalizer_eq e hRK hij hker hR1 hr hτ
    have h2X : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K := by
      intro x hx
      exact CFSG.Quasithin.E1.exists_pow_mem_of_mem_sup hR.2.1 hRK (by simpa [X] using hx)
    obtain ⟨T₀, hT₀ne, hT₀R, hT₀char, hXT₀⟩ :=
      h525 G X K T' R φ i j hcharX hT' hKnormalX hTwoComp hsup hφsurj hkerEq
        hO2Xle hRT' hij hnormalizer (h.noXBlock_of_le hK hX hKX hXH h2X)
    exact ⟨T₀, hT₀ne, hT₀R, hT₀char, hKX.trans hXT₀⟩

theorem isMaxInvariantTwoIn_of_normalizer_le {A R H Y : Subgroup G}
    (hR : IsMaxInvariantTwoIn A R H) (hRH : Subgroup.normalizer (R : Set G) ≤ H)
    (hRY : R ≤ Y) : IsMaxInvariantTwoIn A R Y := by
  classical
  refine ⟨hRY, hR.2.1, hR.2.2.1, ?_⟩
  intro S hSY hS2 hAS hRS
  by_contra hSR
  have hlt : R < S := lt_of_le_of_ne hRS (Ne.symm hSR)
  obtain ⟨x, hxS, hxR, hxN⟩ :=
    CFSG.RankThree.PartTwo.Late.exists_mem_normalizer_not_mem_of_lt hS2 hlt
  let U : Subgroup G := S ⊓ Subgroup.normalizer (R : Set G)
  have hU2 : IsPGroup 2 U := hS2.to_le inf_le_left
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    refine (le_inf hAS ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact hR.2.2.1.trans Subgroup.le_normalizer
  have hRleU : R ≤ U := le_inf hRS Subgroup.le_normalizer
  have hUH : U ≤ H := inf_le_right.trans hRH
  have hUeq : U = R := hR.2.2.2 U hUH hU2 hAU hRleU
  have hxU : x ∈ U := ⟨hxS, hxN⟩
  rw [hUeq] at hxU
  exact hxR hxU

theorem S14Choice.isMaxInvariantTwoIn_M {M H E Q R : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H)
    (hRH : Subgroup.normalizer (R : Set G) ≤ H) :
    IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R M := by
  have hEKR : E ≤ Subgroup.normalizer (R : Set G) :=
    (le_inf (h.E_le_kSub h2) h.hypCGen.E_le_M).trans hR.2.2.1
  exact isMaxInvariantTwoIn_of_normalizer_le hR hRH
    (h.hypCGen.invariant_two_le_M hR.2.1 hEKR)

theorem S14Choice.isSylowOf_two_top {M H E Q T : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  obtain ⟨C, hCne, hCT, hCchar, hKC⟩ := h.exists_char_normal_T h2 hK hU hL hKF h514 hX hT
  have hC2 : IsPGroup 2 C := hT.isPGroup.to_le hCT
  have hNCT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h := CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic T
      (C.subgroupOf T)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at h
  have hNCH : Subgroup.normalizer (C : Set G) ≤ H :=
    h.normalizer_le_caseTwo hA h2 hpre hK hL hC2 hCne hKC
  have hT_H : CFSG.ABGLocalTools.IsSylowOf 2 T H :=
    h.isSylowOf_two_of_inf h2 hK hU hL hKF hT
  exact CFSG.RankThree.PartTwo.Sec20.isSylowOf_top_of_normalizer_le hT_H (hNCT.trans hNCH)

theorem S14Choice.normalizer_R_le {M H E Q R : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) :
    Subgroup.normalizer (R : Set G) ≤ H ∧ IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R M := by
  obtain ⟨C, hCne, hCR, hCchar, hKC⟩ := h.exists_char_normal_R h2 hK hU hL hKF h525 hX hR
  have hC2 : IsPGroup 2 C := hR.2.1.to_le hCR
  have hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h := CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic R
      (C.subgroupOf R)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h
  have hNCH : Subgroup.normalizer (C : Set G) ≤ H :=
    h.normalizer_le_caseTwo hA h2 hpre hK hL hC2 hCne hKC
  have hNRH : Subgroup.normalizer (R : Set G) ≤ H := hNRC.trans hNCH
  exact ⟨hNRH, h.isMaxInvariantTwoIn_M h2 hR hNRH⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
