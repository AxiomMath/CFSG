module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypC
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import Certificates.Certificate5122
public import Certificates.Certificate8034
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThree.PartTwo.Sec4 (autIn)

variable {G : Type} [Group G] [Finite G]
variable {M E H A W T : Subgroup G}

private noncomputable def quotientEquivOfSylow {K A : Subgroup G}
    (hA : IsSylowOf 3 A K) :
    ↥A ≃* ↥((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) :=
  (Subgroup.subgroupOfEquivOfLe hA.le).symm.trans <|
    (MonoidHom.ofInjective (f := (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp
        (A.subgroupOf K).subtype) fun x y hxy =>
      Subtype.ext (pPrimeCore_quotient_injOn_of_isSylowOf hA x.2 y.2 hxy)).trans <|
      MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])

private theorem quotientEquivOfSylow_apply {K A : Subgroup G} (hA : IsSylowOf 3 A K)
    (a : ↥A) :
    (quotientEquivOfSylow hA a : ↥K ⧸ CFSG.pPrimeCore 3 ↥K) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨(a : G), hA.le a.2⟩ :=
  rfl

private theorem map_autIn_eq_quotient {K A : Subgroup G} (hA : IsSylowOf 3 A K) :
    (autIn K A).map (MulAut.congr (quotientEquivOfSylow hA)).toMonoidHom =
      autIn (⊤ : Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K))
        ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 ↥(A.subgroupOf K)) := ⟨hA.isPGroup.comap_subtype⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  set N : Subgroup G := Subgroup.normalizer (A : Set G)
  set π : ↥K →* (↥K ⧸ CFSG.pPrimeCore 3 ↥K) :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) with hπ
  set Abar : Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K) := (A.subgroupOf K).map π with hAbar
  have hNorm : Subgroup.normalizer (Abar : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      (Subgroup.normalizer (A.subgroupOf K : Subgroup ↥K)).map π := by
    simpa [Abar, π] using normalizer_map_quotient_eq_map_normalizer 3 (A.subgroupOf K)
      (CFSG.pPrimeCore 3 ↥K) (CFSG.pPrimeCore_normal (p := 3) (G := ↥K))
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  have hcongr : ∀ (n : G) (hnN : n ∈ N) (hnK : n ∈ K)
      (hq : π ⟨n, hnK⟩ ∈ Subgroup.normalizer (Abar : Set _)),
      MulAut.congr (quotientEquivOfSylow hA) (A.normalizerMonoidHom ⟨n, hnN⟩) =
        Abar.normalizerMonoidHom ⟨π ⟨n, hnK⟩, hq⟩ := by
    intro n hnN hnK hq
    ext b
    obtain ⟨a, rfl⟩ := (quotientEquivOfSylow hA).surjective b
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply]
    have hL := quotientEquivOfSylow_apply hA (A.normalizerMonoidHom ⟨n, hnN⟩ a)
    have hR := quotientEquivOfSylow_apply hA a
    rw [hL, Subgroup.normalizerMonoidHom_apply_apply_coe Abar ⟨π ⟨n, hnK⟩, hq⟩
      ((quotientEquivOfSylow hA) a), hR]
    simp only [π, ← map_mul, ← map_inv]
    congr 1
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨n, hnN, hnK, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mp hτ
    have hnK' : (⟨n, hnK⟩ : ↥K) ∈ Subgroup.normalizer (A.subgroupOf K : Subgroup ↥K) := by
      rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer K A hA.le]
      exact Subgroup.mem_subgroupOf.mpr ⟨hnK, hnN⟩
    have hq : π ⟨n, hnK⟩ ∈ Subgroup.normalizer (Abar : Set _) := by
      rw [hNorm]
      exact Subgroup.mem_map_of_mem π hnK'
    exact CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mpr
      ⟨π ⟨n, hnK⟩, hq, Subgroup.mem_top _, (hcongr n hnN hnK hq).symm⟩
  · intro hσ
    obtain ⟨q, hq, -, hqσ⟩ := CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mp hσ
    have hq' : q ∈ (Subgroup.normalizer (A.subgroupOf K : Subgroup ↥K)).map π := by
      rw [← hNorm]; exact hq
    obtain ⟨nK, hnK', hπn⟩ := Subgroup.mem_map.mp hq'
    have hnN : (nK : G) ∈ N := by
      have hmem : nK ∈ Subgroup.normalizer (A.subgroupOf K : Set ↥K) := hnK'
      rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer K A hA.le]
        at hmem
      exact (Subgroup.mem_subgroupOf.mp hmem).2
    have hq'' : π nK ∈ Subgroup.normalizer (Abar : Set _) := hπn ▸ hq
    refine ⟨A.normalizerMonoidHom ⟨(nK : G), hnN⟩,
      CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mpr ⟨(nK : G), hnN, nK.2, rfl⟩, ?_⟩
    change MulAut.congr (quotientEquivOfSylow hA)
      (A.normalizerMonoidHom ⟨(nK : G), hnN⟩) = σ
    have hsub : (⟨π nK, hq''⟩ : ↥(Subgroup.normalizer (Abar : Set _))) = ⟨q, hq⟩ :=
      Subtype.ext hπn
    rw [hcongr (nK : G) hnN nK.2 hq'', hsub]
    exact hqσ

private theorem map_autIn_top_subgroupEquiv {X Y : Type*} [Group X] [Group Y]
    {E : Subgroup X} {F : Subgroup Y} (e : ↥E ≃* ↥F) (φ : X ≃* Y)
    (he : ∀ x : ↥E, ((e x : ↥F) : Y) = φ (x : X)) :
    (autIn (⊤ : Subgroup X) E).map (MulAut.congr e).toMonoidHom =
      autIn (⊤ : Subgroup Y) F := by
  have hEF : E.map φ.toMonoidHom = F := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hthis : ((e ⟨x, hx⟩ : ↥F) : Y) ∈ F := (e ⟨x, hx⟩).2
      rwa [he ⟨x, hx⟩] at hthis
    · intro hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      refine ⟨(x : X), x.2, ?_⟩
      change φ (x : X) = y
      exact (he x).symm.trans (congrArg Subtype.val hx)
  have hcongr : ∀ (x : X) (hx : x ∈ Subgroup.normalizer (E : Set X))
      (hx' : φ x ∈ Subgroup.normalizer (F : Set Y)),
      MulAut.congr e (E.normalizerMonoidHom ⟨x, hx⟩) =
        F.normalizerMonoidHom ⟨φ x, hx'⟩ := by
    intro x hx hx'
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hxE : x * (z : X) * x⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hx (z : X)).mp z.2
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [show (E.normalizerMonoidHom ⟨x, hx⟩ z : ↥E) = ⟨x * (z : X) * x⁻¹, hxE⟩ from rfl]
    rw [he]
    simp [he, map_mul, map_inv]
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨x, hx, -, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mp hτ
    have hx' : φ x ∈ Subgroup.normalizer (F : Set Y) := by
      rw [← hEF, ← Subgroup.map_equiv_normalizer_eq E φ]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
    exact CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mpr
      ⟨φ x, hx', Subgroup.mem_top _, (hcongr x hx hx').symm⟩
  · intro hσ
    obtain ⟨y, hy, -, rfl⟩ := CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mp hσ
    have hy' : y ∈ (Subgroup.normalizer (E : Set X)).map φ.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq E φ, hEF]; exact hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
    exact ⟨E.normalizerMonoidHom ⟨x, hx⟩,
      CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mpr ⟨x, hx, Subgroup.mem_top _, rfl⟩,
      hcongr x hx hy⟩

theorem HypCGen.nonempty_autIn_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    {A : Subgroup G} (hA : IsSylowOf 3 A (kSub 3 M H)) :
    Nonempty (↥(autIn (kSub 3 M H) A) ≃* QuaternionGroup 2) := by
  classical
  obtain ⟨eK⟩ := HypCGen.nonempty_mulEquiv_threeStar hC3
  let eL : threeStar (kSub 3 M H) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    eK.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  let Abar : Subgroup (↥(kSub 3 M H) ⧸ CFSG.pPrimeCore 3 ↥(kSub 3 M H)) :=
    (A.subgroupOf (kSub 3 M H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))
  have hAbar9 : Nat.card Abar = 9 :=
    card_map_pPrimeCore_quotient_of_isSylowOf ⟨eK⟩ hA
  let E' : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 2)) := Abar.map eL.toMonoidHom
  have hE'9 : Nat.card E' = 9 := by
    rw [Subgroup.card_map_of_injective eL.injective, hAbar9]
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨q8⟩ :=
    CFSG.RankThree.PartTwo.KFacts.L34.nonempty_autIn_of_card_eq_nine hk hE'9
  have hEq := map_autIn_eq_quotient (K := kSub 3 M H) (A := A) hA
  let eSub : ↥Abar ≃* ↥E' := by
    change ↥Abar ≃* ↥(Abar.map eL.toMonoidHom)
    exact Subgroup.equivMapOfInjective Abar eL.toMonoidHom eL.injective
  have hE := map_autIn_top_subgroupEquiv (φ := eL) (E := Abar) (F := E') eSub
    (fun x => Subgroup.coe_equivMapOfInjective_apply Abar eL.toMonoidHom eL.injective x)
  have e1 : Nonempty (↥(autIn (kSub 3 M H) A) ≃*
      ↥(autIn (⊤ : Subgroup (↥(kSub 3 M H) ⧸ CFSG.pPrimeCore 3 ↥(kSub 3 M H)))
        Abar)) :=
    ⟨((autIn (kSub 3 M H) A).equivMapOfInjective _
        (MulAut.congr (quotientEquivOfSylow hA)).injective).trans
      (MulEquiv.subgroupCongr hEq)⟩
  have e2 : Nonempty (↥(autIn (⊤ : Subgroup
        (↥(kSub 3 M H) ⧸ CFSG.pPrimeCore 3 ↥(kSub 3 M H))) Abar) ≃*
      ↥(autIn (⊤ : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 2))) E')) :=
    ⟨((autIn (⊤ : Subgroup (↥(kSub 3 M H) ⧸ CFSG.pPrimeCore 3 ↥(kSub 3 M H)))
        Abar).equivMapOfInjective _ (MulAut.congr eSub).injective).trans
      (MulEquiv.subgroupCongr hE)⟩
  obtain ⟨e1⟩ := e1
  obtain ⟨e2⟩ := e2
  exact ⟨e1.trans (e2.trans q8)⟩

private theorem isPGroup_autIn_kSub (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    {A : Subgroup G} (hA : IsSylowOf 3 A (kSub 3 M H)) :
    IsPGroup 2 ↥(autIn (kSub 3 M H) A) := by
  obtain ⟨e⟩ := HypCGen.nonempty_autIn_kSub h hC3 hA
  refine IsPGroup.of_card (n := 3) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

private theorem sup_ker_eq_of_isSylowOf_of_isPGroup {N Q : Type*} [Group N] [Group Q]
    [Finite N] (ψ : N →* Q) {W L : Subgroup N} (hW : IsSylowOf 2 W L)
    (hL : IsPGroup 2 (L.map ψ)) :
    W ⊔ ψ.ker = L ⊔ ψ.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup L := (ψ.comp L.subtype).ker
  have hrange : (ψ.comp L.subtype).range = L.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hD : IsPGroup 2 (L ⧸ D) :=
    hL.of_equiv (((QuotientGroup.quotientKerEquivRange
      (ψ.comp L.subtype)).trans (MulEquiv.subgroupCongr hrange)).symm)
  obtain ⟨Q0, hQ0⟩ := hW.exists_sylow_eq_subgroupOf
  let Qbar : Sylow 2 (L ⧸ D) := Q0.mapSurjective
    (f := QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)
  have hQbar_top : (Qbar : Subgroup (L ⧸ D)) = ⊤ := by
    have htop : IsPGroup 2 (⊤ : Subgroup (L ⧸ D)) :=
      hD.of_equiv Subgroup.topEquiv.symm
    exact (Sylow.is_maximal' Qbar htop le_top).symm
  have hmap_top : (W.subgroupOf L).map (QuotientGroup.mk' D) = ⊤ := by
    rw [← hQ0, ← Sylow.coe_mapSurjective (f := QuotientGroup.mk' D)
      (QuotientGroup.mk'_surjective D), hQbar_top]
  have hsup : W.subgroupOf L ⊔ D = ⊤ := by
    have h := QuotientGroup.comap_map_mk' D (W.subgroupOf L)
    rw [hmap_top, Subgroup.comap_top] at h
    rw [sup_comm]
    exact h.symm
  have hDmap : D.map L.subtype = L ⊓ ψ.ker := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.2, hd⟩
    · rintro ⟨hxL, hxker⟩
      exact ⟨⟨x, hxL⟩, hxker, rfl⟩
  have hsupN : W ⊔ (L ⊓ ψ.ker) = L := by
    have h := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      hDmap, Subgroup.map_subgroupOf_eq_of_le hW.le] at h
    exact h
  have hmain : (W ⊔ (L ⊓ ψ.ker)) ⊔ ψ.ker = L ⊔ ψ.ker := by rw [hsupN]
  have hker : (L ⊓ ψ.ker) ⊔ ψ.ker = ψ.ker := sup_eq_right.mpr inf_le_right
  rw [sup_assoc, hker] at hmain
  exact hmain

theorem autIn_eq_of_isSylowOf_two {X A W : Subgroup G}
    (hW : IsSylowOf 2 W (Subgroup.normalizer (A : Set G) ⊓ X))
    (h2 : IsPGroup 2 ↥(autIn X A)) :
    autIn W A = autIn X A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.normalizer (A : Set G)
  set ψ : ↥N →* MulAut ↥A := A.normalizerMonoidHom
  let L : Subgroup ↥N := (X ⊓ N).subgroupOf N
  let WN : Subgroup ↥N := W.subgroupOf N
  have hWN : W ≤ N := hW.le.trans inf_le_left
  have hW' : IsSylowOf 2 W (X ⊓ N) := by simpa [N, inf_comm] using hW
  have hWN_sylow : IsSylowOf 2 WN L := by
    refine (isSylowOf_map_subtype_iff (p := 2) N).mp ?_
    simpa [WN, L, Subgroup.map_subgroupOf_eq_of_le hWN,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : X ⊓ N ≤ N)] using hW'
  have hLmap : IsPGroup 2 (L.map ψ) := by
    have hEq : L.map ψ = autIn X A := by
      simp [L, ψ, N, autIn]
    rw [hEq]
    exact h2
  have hEq := (Subgroup.map_eq_map_iff (f := ψ)).mpr
    (sup_ker_eq_of_isSylowOf_of_isPGroup ψ hWN_sylow hLmap)
  simpa [autIn, WN, L, ψ, N, inf_eq_left.mpr hWN] using hEq

theorem HypCGen.nonempty_autIn_sylowTwo (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    {A W : Subgroup G} (hA : IsSylowOf 3 A (kSub 3 M H))
    (hW : IsSylowOf 2 W (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H)) :
    Nonempty (↥(autIn W A) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := HypCGen.nonempty_autIn_kSub h hC3 hA
  exact ⟨(MulEquiv.subgroupCongr
    (autIn_eq_of_isSylowOf_two hW (isPGroup_autIn_kSub h hC3 hA))).trans e⟩

theorem HypCGen.exists_sylowTwo_normalizer_inf_kSub_le (h : HypCGen G M 3 E H)
    {A : Subgroup G}
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) :
    ∃ W T : Subgroup G,
      IsSylowOf 2 W (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H) ∧
      IsSylowOf 2 T (H ⊓ M) ∧ W ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := exists_isSylowOf 2
    (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H)
  have hWM : W ≤ M := hW.le.trans hNA
  have hWH : W ≤ H := hW.le.trans (inf_le_right.trans (kSub_le 3 M H))
  obtain ⟨T, hT, hWT⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (K := H ⊓ M) (Q := W)
      (le_inf hWH hWM) hW.isPGroup
  exact ⟨W, T, hW, hT, hWT⟩

theorem HypCGen.l34Config_quaternion (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    {A W T : Subgroup G} (hA : IsSylowOf 3 A (kSub 3 M H))
    (hW : IsSylowOf 2 W (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H)) (hWT : W ≤ T) :
    ∃ Q : Subgroup (MulAut ↥A),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (A : Set G))).map A.normalizerMonoidHom ∧
        Nonempty (↥Q ≃* QuaternionGroup 2) := by
  have hWN : W ≤ Subgroup.normalizer (A : Set G) := hW.le.trans inf_le_left
  have hle : autIn W A ≤
      (T.subgroupOf (Subgroup.normalizer (A : Set G))).map A.normalizerMonoidHom := by
    rw [autIn, inf_eq_left.mpr hWN]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hWT)
  exact ⟨autIn W A, hle, HypCGen.nonempty_autIn_sylowTwo h hC3 hA hW⟩

theorem HypCGen.l34Config_transitive
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    {A W T : Subgroup G} (hA : IsSylowOf 3 A (kSub 3 M H))
    (hW : IsSylowOf 2 W (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H)) (hWT : W ≤ T) :
    ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      ∃ t ∈ T ⊓ Subgroup.normalizer (A : Set G), t * a * t⁻¹ = b := by
  intro a ha ha1 b hb hb1
  obtain ⟨n, hnN, hnconj⟩ :=
    exists_mem_normalizer_inf_conj_eq (HypCGen.nonempty_mulEquiv_threeStar hC3) hA ha ha1 hb hb1
  have hEq := autIn_eq_of_isSylowOf_two (X := kSub 3 M H) (A := A) (W := W) hW
    (isPGroup_autIn_kSub h hC3 hA)
  let σ : MulAut ↥A := A.normalizerMonoidHom ⟨n, hnN.1⟩
  have hσK : σ ∈ autIn (kSub 3 M H) A :=
    CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mpr ⟨n, hnN.1, hnN.2, rfl⟩
  have hσW : σ ∈ autIn W A := hEq ▸ hσK
  obtain ⟨w, hwN, hwW, hwσ⟩ := CFSG.RankThree.PartTwo.Sec4.mem_autIn_iff.mp hσW
  refine ⟨w, ⟨hWT hwW, hwN⟩, ?_⟩
  have hσa : σ ⟨a, ha⟩ = ⟨b, hb⟩ := by
    apply Subtype.ext
    change ((A.normalizerMonoidHom ⟨n, hnN.1⟩ ⟨a, ha⟩ : ↥A) : G) = b
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hnconj
  have h := congrArg (fun τ : MulAut ↥A => ((τ ⟨a, ha⟩ : ↥A) : G)) hwσ
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  rw [show ((σ ⟨a, ha⟩ : ↥A) : G) = b by rw [hσa]] at h
  exact h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
