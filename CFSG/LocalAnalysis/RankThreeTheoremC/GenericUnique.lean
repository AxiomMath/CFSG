module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLinesPlanes
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCentralPoint
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.RankThree.PartOne.KE8F.HyperGen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GorensteinWalter CFSG.ABGLocalTools
  Subgroup
open scoped MatrixGroups

section Psl2Torus

variable {K : Type} [Field K]

theorem psl2QuotientMap_diag2_mul_psl2Root {t : K} (ht : t ≠ 0) (a : K) :
    psl2QuotientMap K (Matrix.SpecialLinearGroup.diag2 t ht) * psl2Root a *
      (psl2QuotientMap K (Matrix.SpecialLinearGroup.diag2 t ht))⁻¹ = psl2Root (t ^ 2 * a) := by
  have hB : Matrix.SpecialLinearGroup.diag2 t ht ∈ sl2Borel K := by
    rw [sl2Borel, sl2_mem_stabilizer_infinity_iff, Matrix.SpecialLinearGroup.diag2_coe']
    simp
  have h := sl2Borel_conj_upperUnipotent hB a
  have h2 : (Matrix.SpecialLinearGroup.diag2 t ht).val 0 0 = t := by
    rw [Matrix.SpecialLinearGroup.diag2_coe']
    simp
  rw [h2] at h
  calc psl2QuotientMap K (Matrix.SpecialLinearGroup.diag2 t ht) * psl2Root a *
        (psl2QuotientMap K (Matrix.SpecialLinearGroup.diag2 t ht))⁻¹
      = psl2QuotientMap K (Matrix.SpecialLinearGroup.diag2 t ht * sl2UpperUnipotent a *
          (Matrix.SpecialLinearGroup.diag2 t ht)⁻¹) := by simp
    _ = psl2Root (t ^ 2 * a) := by rw [h]

theorem psl2Root_injective : Function.Injective (psl2Root : K → PSL2 K) := by
  intro a b hab
  have h := congrArg (fun g : PSL2 K => g • psl2AffinePoint K 0) hab
  simp only [psl2Root_smul_affine, zero_add] at h
  exact psl2AffinePoint_injective h

end Psl2Torus

section GenericData

variable {G : Type} [Group G] [Finite G]

theorem exists_isFieldTorus_of_isGenericPoint (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x) (h5 : 5 ≤ p) {m : ℕ}
    (hm : 2 ≤ m) (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    Nat.card (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
        rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) = p ^ 2 ∧
      IsElemAbelian p (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
        rankThreeLayer (centralizer ({x} : Set G))) ∧
      ∃ h : G, h ∈ M ∧ h ∈ rankThreeLayer (centralizer ({x} : Set G)) ∧
        IsFieldTorus p (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
          rankThreeLayer (centralizer ({x} : Set G))) h := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hxP, hxL, hsyl, hrk⟩ := id hx
  obtain ⟨-, hx1, hxp, -, hxCM⟩ := hxL
  obtain ⟨hm2, -⟩ := eq_two_of_isSylowOf_mulEquiv_psl hsyl (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
    (fun c hc => mem_centralizer_singleton_iff.mp hc) hrk.le hm e
  subst hm2
  obtain ⟨-, hpos⟩ := layer_data_of_isGenericPoint hx hm e
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  set L : Subgroup G := rankThreeLayer (centralizer ({x} : Set G)) with hL
  set U : Subgroup G := ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓ L with hU
  have hUsyl : IsSylowOf p U L :=
    hsyl.inf_of_le_normalizer (rankThreeLayer_le _) (le_normalizer_rankThreeLayer _)
  have hUc : Nat.card U = p ^ 2 := by
    rw [hUsyl.card_eq, factorization_card_of_mulEquiv_psl hK e]
  have hUe : IsElemAbelian p U :=
    ⟨isMulCommutative_of_isPGroup_of_mulEquiv_psl_two hK e inf_le_right hUsyl.isPGroup,
      fun u hu => pow_eq_one_of_mem_isSylowOf_psl hK e hUsyl hu⟩
  refine ⟨hUc, hUe, ?_⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl hK e hUsyl
  obtain ⟨t, ht, hgen⟩ := exists_generator_units (GaloisField p 2)
  rw [hK] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ht
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  set h₀ : L := e'.symm (psl2QuotientMap _ (Matrix.SpecialLinearGroup.diag2 t ht0)) with hh₀
  let ψ : Multiplicative (GaloisField p 2) →* G :=
    L.subtype.comp (e'.symm.toMonoidHom.comp (psl2UpperUnipotentHom (GaloisField p 2)))
  have hψa : ∀ a, ψ (Multiplicative.ofAdd a) = (e'.symm (psl2Root a) : G) := fun a => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : e'.symm (psl2Root a.toAdd) = e'.symm (psl2Root b.toAdd) := Subtype.ext hab
    exact Multiplicative.ext (psl2Root_injective (e'.symm.injective h1))
  have hrange : ψ.range = U := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      refine (he' _).2 ?_
      show e' (e'.symm (psl2Root a.toAdd)) ∈ _
      rw [e'.apply_symm_apply]
      exact psl2Root_mem a.toAdd
    · intro hg
      obtain ⟨b, hb⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 ((he' ⟨g, hUsyl.le hg⟩).1 hg)
      refine ⟨Multiplicative.ofAdd b, ?_⟩
      rw [hψa]
      have hb' : e' ⟨g, hUsyl.le hg⟩ = psl2Root b := hb
      have : e'.symm (psl2Root b) = ⟨g, hUsyl.le hg⟩ := by
        rw [← hb']
        exact e'.symm_apply_apply _
      exact congrArg Subtype.val this
  have hh : ∀ a : GaloisField p 2, (h₀ : G) * ψ (Multiplicative.ofAdd a) * (h₀ : G)⁻¹ =
      ψ (Multiplicative.ofAdd (t ^ 2 * a)) := by
    intro a
    rw [hψa, hψa]
    have := congrArg (fun y : PSL2 (GaloisField p 2) => (e'.symm y : G))
      (psl2QuotientMap_diag2_mul_psl2Root ht0 a)
    simpa [hh₀] using this
  have htorus := IsFieldTorus.of_hom h5 hK ht hgen hψinj hh
  rw [hrange] at htorus
  refine ⟨h₀, ?_, h₀.2, htorus⟩
  have hUp : IsPGroup p U := hUsyl.isPGroup
  have hNU := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hUp
    ((inf_le_left.trans inf_le_left).trans hPM) hpos
  exact hNU htorus.mem_normalizer

end GenericData

section FPF

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isElemAbelian_of_card_eq {p : ℕ} [Fact p.Prime] {S E₁ E₂ : Subgroup G}
    (hS : IsMulCommutative S) (hS3 : CFSG.Open.pRank p S ≤ 3) (h₁S : E₁ ≤ S) (h₂S : E₂ ≤ S)
    (h₁ : IsElemAbelian p E₁) (h₂ : IsElemAbelian p E₂) (hc₁ : Nat.card E₁ = p ^ 3)
    (hc₂ : Nat.card E₂ = p ^ 3) : E₁ = E₂ := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hsup : IsElemAbelian p (E₁ ⊔ E₂) := isElemAbelian_sup_of_commute h₁ h₂ fun a ha b hb =>
    congrArg Subtype.val (hS.is_comm.comm ⟨a, h₁S ha⟩ ⟨b, h₂S hb⟩)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (elementary_isPGroup p _ hsup)
  have hk3 : k ≤ 3 := (le_pRank_of_elemAbelian_card (sup_le h₁S h₂S) hsup hk).trans hS3
  have hle : Nat.card (E₁ ⊔ E₂ : Subgroup G) ≤ p ^ 3 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by omega) hk3
  have e₁ : E₁ = E₁ ⊔ E₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc₁]; exact hle)
  have e₂ : E₂ = E₁ ⊔ E₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hc₂]; exact hle)
  exact e₁.trans e₂.symm

theorem exists_isFPFPoint_of_isGenericPoint (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) {p : ℕ} [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x)
    (h5 : 5 ≤ p) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    ∃ E : Subgroup G, E ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧ IsFPFPoint p E (pCoreOf 2 M) x := by
  obtain ⟨hUc, hUe, h, hhM, hhL, htorus⟩ :=
    exists_isFieldTorus_of_isGenericPoint hS hU0 hp hM hx h5 hm e
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsyl, hrk⟩ := id hx
  obtain ⟨hxL, -⟩ := layer_data_of_isGenericPoint hx hm e
  set L : Subgroup G := rankThreeLayer (centralizer ({x} : Set G)) with hL
  set U : Subgroup G := ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓ L with hU
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hXc : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hxo]
  have hUC : ∀ u ∈ U, u * x = x * u := fun u hu => mem_centralizer_singleton_iff.mp hu.1.2
  have hdisj : Disjoint U (zpowers x) := by
    refine Subgroup.disjoint_def.mpr fun {g} hgU hgX => ?_
    by_contra hg1
    have hzg : zpowers x = zpowers g := eq_zpowers_of_card_eq_prime hXc hgX hg1
    have hxg : x ∈ zpowers g := hzg ▸ mem_zpowers x
    exact hxL (zpowers_le.mpr hgU hxg).2
  have hXe : IsElemAbelian p (zpowers x) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp)
  have hcommUX : ∀ u ∈ U, ∀ ξ ∈ zpowers x, u * ξ = ξ * u := fun u hu ξ hξ => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hξ
    exact ((Commute.zpow_right (show Commute u x from hUC u hu) n).eq)
  refine ⟨U ⊔ zpowers x, sup_le (inf_le_left) ?_, isElemAbelian_sup_of_commute hUe hXe hcommUX,
    ?_, ?_⟩
  · exact zpowers_le.mpr ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U (zpowers x)
      (le_normalizer_of_commute fun ξ hξ u hu => (hcommUX u hu ξ hξ).symm) hdisj, hUc, hXc]
    ring
  · refine ⟨Subgroup.mem_sup_right (mem_zpowers x), hxo, ?_, U, h, le_sup_left, hdisj, htorus,
      mem_centralizer_singleton_iff.mp (rankThreeLayer_le _ hhL),
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hhM⟩
    have hC : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    unfold IsFixedPointFree
    rw [hC]
    exact pCoreOf_two_inf_centralizer_eq_bot hS hD1 hU0 hp hM hx h5 hm e

theorem exists_ne_not_isFixedPointFree (hS : Setting G) {p : ℕ} [hp : Fact p.Prime]
    (hpA : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ∀ B₀ : Subgroup G, B₀ ≤ E → Nat.card B₀ = p ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 2 ∧ B ≠ B₀ ∧
        ¬ IsFixedPointFree (pCoreOf 2 M) B := by
  intro B₀ hB₀E hB₀c
  by_contra! hall
  have hp1 : 1 < p := hp.out.one_lt
  have hodd : p ≠ 2 := sigmaA_odd p hpA
  have : CFSG.IsElementaryAbelian p ↥E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
  have : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hEc]
    exact Nat.one_lt_pow (by norm_num) hp1)
  set T : Subgroup G := pCoreOf 2 M with hT
  have hTnorm : E ≤ normalizer (T : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hTp : ¬ p ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    rw [hn]
    intro h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hp.out h))
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) hTnorm hTp
  have hTle : T ≤ centralizer (B₀ : Set G) := by
    refine hgen.trans (iSup₂_le fun B hB => ?_)
    set B' : Subgroup G := B.map E.subtype with hB'
    have hB'c : Nat.card B' = p ^ 2 := by
      rw [hB', Subgroup.card_map_of_injective E.subtype_injective]
      have h1 := B.card_mul_index
      rw [hB, hEc] at h1
      have : Nat.card B * p = p ^ 2 * p := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    by_cases hBB : B' = B₀
    · rw [← hBB]
      exact inf_le_right
    · have := hall B' (map_subtype_le B) hB'c hBB
      unfold IsFixedPointFree at this
      rw [this]
      exact bot_le
  have hB₀C : B₀ ≤ centralizer (T : Set G) := fun b hb =>
    mem_centralizer_iff.mpr fun t ht => (mem_centralizer_iff.mp (hTle ht) b hb).symm
  have hB₀p : IsPGroup p B₀ := (elementary_isPGroup p E hE).to_le hB₀E
  have hbot : B₀ = ⊥ := charTwo_odd_pGroup_centralizing_core_eq_bot hS.charTwo M hM.1.1 p hp.out
    hodd B₀ hB₀p (hB₀E.trans hEM) hB₀C
  rw [hbot, Subgroup.card_bot] at hB₀c
  have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
  omega

end FPF

section Unique

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_inf_centralizer_eq (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x y : G}
    (hx : IsGenericPoint p P M x) (hy : IsGenericPoint p P M y)
    (hSxy : (P : Subgroup G) ⊓ centralizer ({y} : Set G) =
      (P : Subgroup G) ⊓ centralizer ({x} : Set G)) : zpowers y = zpowers x := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨h5, hfx, mx, hmx, ⟨ex⟩⟩ := hL p hp P M hM hfail hIH x hx
  obtain ⟨-, hfy, my, hmy, ⟨ey⟩⟩ := hL p hp P M hM hfail hIH y hy
  obtain ⟨Ex, hExS, hExe, hExc, hFx⟩ :=
    exists_isFPFPoint_of_isGenericPoint hS hD1 hU0 hp hM hx h5 hmx ex
  obtain ⟨Ey, hEyS, hEye, hEyc, hFy⟩ :=
    exists_isFPFPoint_of_isGenericPoint hS hD1 hU0 hp hM hy h5 hmy ey
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsylx, hrkx⟩ := id hx
  have hSab : IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    isMulCommutative_of_isSylowOf_mulEquiv_psl h5 hsylx (rankThreeLayer_le _)
      (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
      (fun c hc => mem_centralizer_singleton_iff.mp hc) hrkx.le hmx ex
  have hEE : Ex = Ey :=
    eq_of_isElemAbelian_of_card_eq hSab hrkx.le hExS (hSxy ▸ hEyS) hExe hEye hExc hEyc
  subst hEE
  have hEM : Ex ≤ M := hExS.trans (inf_le_left.trans hPM)
  exact zpowers_eq_of_isFPFPoint hExe hExc (exists_ne_not_isFixedPointFree hS hp hM hEM hExe hExc)
    hFx hFy

theorem le_centralizer_of_zpowers_eq_of_inf_eq {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) {x : G} (hx : IsGenericPoint p P M x)
    (hU : ∀ y : G, IsGenericPoint p P M y →
      (P : Subgroup G) ⊓ centralizer ({y} : Set G) = (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
        zpowers y = zpowers x) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  by_contra hne
  have hprime : p.Prime := Fact.out
  obtain ⟨-, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := id hx
  set S : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hS
  have hlt : S < (P : Subgroup G) :=
    lt_of_le_of_ne inf_le_left fun h => hne (h ▸ inf_le_right)
  obtain ⟨n, ⟨hnP, hnN⟩, hnS⟩ := IsConcreteLE.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hprime P S P.isPGroup' hlt)
  have hy := hx.conj_of_mem_normalizer hPM hnP hnN
  have hSmap : S.map (MulAut.conj n).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  have hPmap : (P : Subgroup G).map (MulAut.conj n).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hnP)
  have hSy : (P : Subgroup G) ⊓ centralizer ({MulAut.conj n x} : Set G) = S := by
    calc (P : Subgroup G) ⊓ centralizer ({MulAut.conj n x} : Set G)
        = (P : Subgroup G).map (MulAut.conj n).toMonoidHom ⊓
            (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom := by
          rw [centralizer_singleton_conj, hPmap]
      _ = S.map (MulAut.conj n).toMonoidHom :=
          (Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective).symm
      _ = S := hSmap
  have hmem : n * x * n⁻¹ ∈ zpowers x := by
    have := hU _ hy hSy ▸ mem_zpowers (MulAut.conj n x)
    simpa [MulAut.conj_apply] using this
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
  have hk' : n ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hcomm := conj_eq_self_of_conj_mem_zpowers hx1 hxp hk' hmem
  exact hnS ⟨hnP, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcomm)⟩

theorem zpowers_eq_of_isGenericPoint (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hL : GL83GenericLayer G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x : G}
    (hx : IsGenericPoint p P M x) : ∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have key : ∀ y : G, IsGenericPoint p P M y →
      (P : Subgroup G) ⊓ centralizer ({y} : Set G) = (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
        zpowers y = zpowers x := fun y hy h =>
    zpowers_eq_of_inf_centralizer_eq hS hD1 hU0 hL hp hM hfail hIH hx hy h
  have hPx := le_centralizer_of_zpowers_eq_of_inf_eq hPM hx key
  obtain ⟨h5, hfx, mx, hmx, ⟨ex⟩⟩ := hL p hp P M hM hfail hIH x hx
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsylx, hrkx⟩ := id hx
  have hSab : IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    isMulCommutative_of_isSylowOf_mulEquiv_psl h5 hsylx (rankThreeLayer_le _)
      (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
      (fun c hc => mem_centralizer_singleton_iff.mp hc) hrkx.le hmx ex
  rw [inf_of_le_left hPx] at hSab
  intro y hy
  obtain ⟨hyP, -⟩ := id hy
  have hPy : (P : Subgroup G) ≤ centralizer ({y} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hSab.is_comm.comm ⟨g, hg⟩ ⟨y, hyP⟩))
  exact key y ‹_› (by rw [inf_of_le_left hPy, inf_of_le_left hPx])

end Unique

end CFSG.LocalAnalysis.RankThreeTheoremC
