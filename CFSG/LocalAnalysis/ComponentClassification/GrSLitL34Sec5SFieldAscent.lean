module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldGluing
public import CFSG.LocalAnalysis.ComponentClassification.GSTopExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFieldMirrorReach

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LargeExtraspecial.S5 (exists_isSylowTwoIn_ge)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isElemTwo_of_isElemAbelian {A : Subgroup G} (hA : Open.IsElemAbelian 2 A) :
    IsElemTwo A :=
  isElemTwo_of_sq fun a ha => by rw [← pow_two]; exact hA.2 a ha

omit [Finite G] in
theorem exists_map_eq_projUnitriangular_of_isSylowTwoIn {F : Type} [Field F] [Finite F]
    [CharP F 2] {J R : Subgroup G} (ρ : ↥J →* projectiveSL 3 F) (hρ : Function.Surjective ρ)
    (hR : LargeExtraspecial.S5.IsSylowTwoIn R J) :
    ∃ ρ' : ↥J →* projectiveSL 3 F, Function.Surjective ρ' ∧ ρ'.ker = ρ.ker ∧
      (R.subgroupOf J).map ρ' = projUnitriangular 3 F := by
  have hR' : LargeExtraspecial.S5.IsSylowTwoIn (R.subgroupOf J) ⊤ :=
    ⟨le_top, hR.isPGroup.of_equiv (subgroupOfEquivOfLe hR.le).symm, by
      rw [relIndex_top_right]
      exact hR.not_dvd⟩
  have hS := hR'.map ρ
  rw [map_top_of_surjective ρ hρ] at hS
  obtain ⟨S, hSU⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU' : LargeExtraspecial.S5.IsSylowTwoIn (projUnitriangular 3 F) ⊤ :=
    ⟨le_top, hSU ▸ S.isPGroup', by
      rw [relIndex_top_right, ← hSU]
      exact S.not_dvd_index⟩
  obtain ⟨c, -, hc⟩ := hS.exists_conj hU'
  refine ⟨(MulAut.conj c).toMonoidHom.comp ρ, (MulAut.conj c).surjective.comp hρ, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · ext y
    rw [hc y]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, by simp [mul_assoc]⟩
    · rintro ⟨r, hr, hry⟩
      exact ⟨r, hr, by simp [hry, mul_assoc]⟩

theorem wGroup_eq_of_isSylowTwoIn_of_surjective (hB : GWTwoBalanced G)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 16 ≤ Nat.card F) {J R : Subgroup G}
    (ρ : ↥J →* projectiveSL 3 F) (hρ : Function.Surjective ρ) (hU : Odd (Nat.card ρ.ker))
    (hR : LargeExtraspecial.S5.IsSylowTwoIn R J) :
    IsElemTwo (R ⊓ centralizer (R : Set G)) ∧
      Nat.card ↥(R ⊓ centralizer (R : Set G)) = Nat.card F ∧
      ∀ A : Subgroup G, A ≤ J → IsElemTwo A → 8 ≤ Nat.card A →
        wGroup A = wGroup (R ⊓ centralizer (R : Set G)) := by
  obtain ⟨ρ', hρ', hker, hRU⟩ := exists_map_eq_projUnitriangular_of_isSylowTwoIn ρ hρ hR
  have hU' : Odd (Nat.card ρ'.ker) := by rw [hker]; exact hU
  obtain ⟨hZe, hZc⟩ := isElemTwo_inf_centralizer_of_map_eq hU' hR.le hR.isPGroup hRU
  have hJN := le_normalizer_wGroup_of_map_eq hB hρ' hU' hF hR.le hR.isPGroup hRU
  refine ⟨hZe, hZc, fun A hAJ hA hA8 => ?_⟩
  have hRG : GrSLit.IsSylowTwoIn R J := ⟨hR.le, hR.toSylow, hR.coe_toSylow⟩
  obtain ⟨c, hcJ, hc⟩ := hRG.exists_conj_le hAJ hA.isPGroup
  have hAR : A.map (MulAut.conj c).toMonoidHom ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hA8' : 8 ≤ Nat.card (A.map (MulAut.conj c).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj c).injective]
    exact hA8
  have hW := wGroup_eq_of_commute hB ((hA.map_conj c).isAbelianTwoOfRank hA8')
    (hZe.isAbelianTwoOfRank (by omega)) fun x hx y hy => mem_centralizer_iff.mp hy.2 x (hAR hx)
  rw [wGroup_map_conj] at hW
  exact map_injective (MulAut.conj c).injective
    (hW.trans (mem_normalizer_iff_map_conj_eq.mp (hJN hcJ)).symm)

theorem exists_surjective_of_lieModel_pPrimeCore {J : Subgroup G} {m : ℕ}
    (hJ : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ρ : ↥J →* projectiveSL 3 F),
      Nat.card F = 2 ^ m ∧ Function.Surjective ρ ∧ Odd (Nat.card ρ.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hJ
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  set ρ : ↥J →* projectiveSL 3 F := ψ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J))
    with hρ
  have hker : ρ.ker = pPrimeCore 2 J := by
    ext x
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨F, inferInstance, inferInstance, inferInstance, ρ, hF,
    ψ.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [hker]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem wGroup_eq_of_isSylowTwoIn_of_lieModel (hB : GWTwoBalanced G) {J R : Subgroup G} {m : ℕ}
    (hm : 4 ≤ m) (hJ : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 m)
    (hR : LargeExtraspecial.S5.IsSylowTwoIn R J) :
    IsElemTwo (R ⊓ centralizer (R : Set G)) ∧ 16 ≤ Nat.card ↥(R ⊓ centralizer (R : Set G)) ∧
      ∀ A : Subgroup G, A ≤ J → IsElemTwo A → 8 ≤ Nat.card A →
        wGroup A = wGroup (R ⊓ centralizer (R : Set G)) := by
  obtain ⟨F, _, _, _, ρ, hF, hρ, hU⟩ := exists_surjective_of_lieModel_pPrimeCore hJ
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨hZe, hZc, hW⟩ := wGroup_eq_of_isSylowTwoIn_of_surjective hB hF16 ρ hρ hU hR
  exact ⟨hZe, hZc ▸ hF16, hW⟩

theorem field_wGroup_eq_of_internal
    {G : Type} [Group G] [Finite G] (hB : GWTwoBalanced G)
    {J A B : Subgroup G} {m : ℕ} (hm : 4 ≤ m)
    (hJ : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 m)
    (hAJ : A ≤ J) (hBJ : B ≤ J)
    (hA : Open.IsElemAbelian 2 A) (hA8 : 8 ≤ Nat.card A)
    (hB' : Open.IsElemAbelian 2 B) (hB8 : 8 ≤ Nat.card B) :
    GrSLit.wGroup A = GrSLit.wGroup B := by
  obtain ⟨R, hR, -⟩ := exists_isSylowTwoIn_ge (bot_le : ⊥ ≤ J) IsPGroup.of_bot
  obtain ⟨-, -, hW⟩ := wGroup_eq_of_isSylowTwoIn_of_lieModel hB hm hJ hR
  rw [hW A hAJ (isElemTwo_of_isElemAbelian hA) hA8, hW B hBJ (isElemTwo_of_isElemAbelian hB') hB8]

theorem exists_mul_of_isSylowTwoIn_sup {Q R S : Subgroup G} (hRQ : R ≤ normalizer (Q : Set G))
    (hQR : Q ≤ normalizer (R : Set G)) (hS : LargeExtraspecial.S5.IsSylowTwoIn S (Q ⊔ R))
    {x : G} (hx : x ∈ S) : ∃ y ∈ S ⊓ R, y⁻¹ * x ∈ S ⊓ Q := by
  have : (Q.subgroupOf (Q ⊔ R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hRQ)
  have hRn : (R.subgroupOf (Q ⊔ R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hQR le_normalizer)
  have hT : LargeExtraspecial.S5.IsSylowTwoIn (S ⊓ R) R :=
    hS.inf_of_isSubnormal (ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_sup_right hRn)
  have hT' : LargeExtraspecial.S5.IsSylowTwoIn ((S ⊓ R).subgroupOf (Q ⊔ R))
      (R.subgroupOf (Q ⊔ R)) :=
    ⟨fun z hz => mem_subgroupOf.mpr (mem_subgroupOf.mp hz).2,
      hT.isPGroup.of_equiv (subgroupOfEquivOfLe (inf_le_right.trans le_sup_right)).symm,
      by rw [relIndex_subgroupOf le_sup_right]; exact hT.not_dvd⟩
  have hsup : Q.subgroupOf (Q ⊔ R) ⊔ R.subgroupOf (Q ⊔ R) = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have htop : (R.subgroupOf (Q ⊔ R)).map (QuotientGroup.mk' (Q.subgroupOf (Q ⊔ R))) = ⊤ := by
    rw [← map_top_of_surjective _ (QuotientGroup.mk'_surjective (Q.subgroupOf (Q ⊔ R))), ← hsup,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hmap := hT'.map (QuotientGroup.mk' (Q.subgroupOf (Q ⊔ R)))
  rw [htop] at hmap
  have heq := hmap.eq_of_le (map_mono fun z hz => mem_subgroupOf.mpr (mem_subgroupOf.mp hz).1)
    le_top ((hS.isPGroup.of_equiv (subgroupOfEquivOfLe hS.le).symm).map _)
  have hxS : (⟨x, hS.le hx⟩ : ↥(Q ⊔ R)) ∈ S.subgroupOf (Q ⊔ R) := mem_subgroupOf.mpr hx
  obtain ⟨y, hy, hyx⟩ := heq ▸ mem_map_of_mem (QuotientGroup.mk' (Q.subgroupOf (Q ⊔ R))) hxS
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have hy' := mem_subgroupOf.mp hy
  exact ⟨y, hy', mem_inf.mpr ⟨mul_mem (inv_mem hy'.1) hx, by simpa using mem_subgroupOf.mp hyx⟩⟩

theorem commute_of_mem_coreActionKernel {Q S : Subgroup G} (hS : IsPGroup 2 S) {j g : G}
    (hj : j ∈ Q) (hg : g ∈ coreActionKernel Q) (hjg : j⁻¹ * g⁻¹ * j * g ∈ S) :
    j * g = g * j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime (Nat.card S) (Nat.card ((pPrimeCore 2 Q).map Q.subtype)) := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn, card_map_of_injective Q.subtype_injective]
    exact Nat.Coprime.pow_left n pPrimeCore_coprime_card
  have h1 : j⁻¹ * g⁻¹ * j * g ∈ S ⊓ (pPrimeCore 2 Q).map Q.subtype :=
    mem_inf.mpr ⟨hjg, (mem_coreActionKernel.mp hg).2 j hj⟩
  rw [inf_eq_bot_of_coprime hcop, mem_bot] at h1
  calc j * g = g * j * (j⁻¹ * g⁻¹ * j * g) := by group
    _ = g * j := by rw [h1, mul_one]

theorem commute_of_mem_center_inf_of_isSylowTwoIn_sup {Q R S : Subgroup G}
    (hRQ : R ≤ coreActionKernel Q) (hQR : Q ≤ normalizer (R : Set G))
    (hS : LargeExtraspecial.S5.IsSylowTwoIn S (Q ⊔ R)) {x z : G} (hx : x ∈ S)
    (hz : z ∈ S ⊓ Q ⊓ centralizer ((S ⊓ Q : Subgroup G) : Set G)) : x * z = z * x := by
  obtain ⟨y, hy, hq⟩ := exists_mul_of_isSylowTwoIn_sup
    (fun g hg => (mem_coreActionKernel.mp (hRQ hg)).1) hQR hS hx
  have hzq : y⁻¹ * x * z = z * (y⁻¹ * x) := mem_centralizer_iff.mp hz.2 _ hq
  have hzy : z * y = y * z := commute_of_mem_coreActionKernel hS.isPGroup hz.1.2 (hRQ hy.2)
    (mul_mem (mul_mem (mul_mem (inv_mem hz.1.1) (inv_mem hy.1)) hz.1.1) hy.1)
  calc x * z = y * (y⁻¹ * x * z) := by group
    _ = y * (z * (y⁻¹ * x)) := by rw [hzq]
    _ = y * z * (y⁻¹ * x) := by group
    _ = z * y * (y⁻¹ * x) := by rw [← hzy]
    _ = z * x := by group

theorem field_wGroup_eq_of_swapped_component
    {G : Type} [Group G] [Finite G] (hB : GWTwoBalanced G)
    {a : G} {H Q A B : Subgroup G} {m : ℕ}
    (haH : a ∈ normalizer (H : Set G))
    (hQ : FooteLit.IsTwoComponentIn Q H)
    (hmove : conjugate Q a ≠ Q)
    (hm : 4 ≤ m)
    (htype : Blueprint.LieModel (Q ⧸ pPrimeCore 2 Q) .PSL 3 2 m)
    (hAL : A ≤ Q ⊔ conjugate Q a) (hBQ : B ≤ Q)
    (hA : Open.IsElemAbelian 2 A) (hA8 : 8 ≤ Nat.card A)
    (hB' : Open.IsElemAbelian 2 B) (hB8 : 8 ≤ Nat.card B) :
    GrSLit.wGroup A = GrSLit.wGroup B := by
  have hQa : FooteLit.IsTwoComponentIn (conjugate Q a) H := by
    have h := Sol76.isTwoComponentIn_map (MulAut.conj a⁻¹) hQ
    have hH : H.map (MulAut.conj a⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem haH)
    rw [hH] at h
    exact h
  have h1 := GSThmB.B5a.le_coreActionKernel_of_ne hQ.1 hQa.1 hQ.2 hQa.2 (Ne.symm hmove)
  have h2 := GSThmB.B5a.le_coreActionKernel_of_ne hQa.1 hQ.1 hQa.2 hQ.2 hmove
  have hAe := isElemTwo_of_isElemAbelian hA
  obtain ⟨S, hS, hAS⟩ := exists_isSylowTwoIn_ge hAL hAe.isPGroup
  have hS1 : LargeExtraspecial.S5.IsSylowTwoIn (S ⊓ Q) Q :=
    hS.inf_of_isSubnormal (ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_sup_left
      ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le le_normalizer fun x hx => (mem_coreActionKernel.mp (h1 hx)).1)))
  obtain ⟨hZe, hZ16, hW⟩ := wGroup_eq_of_isSylowTwoIn_of_lieModel hB hm htype hS1
  have hc : ∀ x ∈ A, ∀ z ∈ S ⊓ Q ⊓ centralizer ((S ⊓ Q : Subgroup G) : Set G),
      x * z = z * x := fun x hx z hz => commute_of_mem_center_inf_of_isSylowTwoIn_sup h1
    (fun g hg => (mem_coreActionKernel.mp (h2 hg)).1) hS (hAS hx) hz
  rw [wGroup_eq_of_commute hB (hAe.isAbelianTwoOfRank hA8) (hZe.isAbelianTwoOfRank (by omega)) hc,
    ← hW B hBQ (isElemTwo_of_isElemAbelian hB') hB8]

theorem field_wGroup_eq_of_gsWeakCorr (hS : SchreierFor Blueprint.Catalog)
    {G : Type} [Group G] [Finite G] (hB : GWTwoBalanced G)
    (hKP : Assembly.KProper Blueprint.Catalog G)
    {a b : G} {J K A B : Subgroup G} {m n : ℕ}
    (hcorr : GSWeakCorr a J b K) (hbZ : b ∉ center G)
    (hm : 4 ≤ m) (hJ : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 m)
    (hn : 4 ≤ n) (hK : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 3 2 n)
    (hAJ : A ≤ J) (hA : Open.IsElemAbelian 2 A) (hA8 : 8 ≤ Nat.card A)
    (hBK : B ≤ K) (hB' : Open.IsElemAbelian 2 B) (hB8 : 8 ≤ Nat.card B) :
    GrSLit.wGroup A = GrSLit.wGroup B := by
  obtain ⟨hDN, -, ⟨φ⟩⟩ := gsFixedLayer_isPComponent_of_gsWeakCorr hS hKP hcorr hbZ
  obtain ⟨R, hR, -⟩ := exists_isSylowTwoIn_ge (bot_le : ⊥ ≤ UnbalancedGS.gsFixedLayer J b)
    IsPGroup.of_bot
  obtain ⟨hZe, hZ16, -⟩ := wGroup_eq_of_isSylowTwoIn_of_lieModel hB hm
    (LieType.CurtisTits.lieModel_of_mulEquiv φ.symm hJ) hR
  have hZD : R ⊓ centralizer (R : Set G) ≤ UnbalancedGS.gsFixedLayer J b := inf_le_left.trans hR.le
  have hDJ : UnbalancedGS.gsFixedLayer J b ≤ J :=
    (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left
  rw [field_wGroup_eq_of_internal hB hm hJ hAJ (hZD.trans hDJ) hA hA8 hZe.isElemAbelian
    (by omega)]
  by_cases hKa : conjugate K a = K
  · rw [hKa, sup_idem] at hDN
    exact field_wGroup_eq_of_internal hB hn hK (hZD.trans (hDN.trans inf_le_left)) hBK
      hZe.isElemAbelian (by omega) hB' hB8
  · exact field_wGroup_eq_of_swapped_component hB
      (le_normalizer (mem_centralizer_singleton_iff.mpr hcorr.2.2.1))
      ⟨hcorr.2.2.2.2.2.1, hcorr.2.2.2.2.2.2.1⟩ hKa hn hK (hZD.trans (hDN.trans inf_le_left)) hBK
      hZe.isElemAbelian (by omega) hB' hB8

omit [Finite G] in
theorem lieModel_fusionZStar_of_lieModel_pPrimeCore {J : Subgroup G} {m : ℕ}
    (hJ : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 m) :
    Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 m := by
  obtain ⟨F, _, _, -, ⟨ψ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hJ
  have hZ : center (J ⧸ pPrimeCore 2 J) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : ψ x ∈ center (projectiveSL 3 F) := mem_center_iff.mpr fun y => by
      obtain ⟨w, rfl⟩ := ψ.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx w]
    rw [GH74.KGroups.L3Eps.center_projectiveSL_three_eq_bot, mem_bot] at h1
    exact mem_bot.mpr (ψ.map_eq_one_iff.mp h1)
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar ↥J
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eS) hJ

theorem field_wGroup_eq_of_mirrorStep
    {G : Type} [Group G] [Finite G] (hB : GWTwoBalanced G)
    {Y X A B : Subgroup G} {m n : ℕ} (hstep : FooteLit.MirrorStep Y X)
    (hm : 4 ≤ m) (hY : Blueprint.LieModel (Y ⧸ pPrimeCore 2 Y) .PSL 3 2 m)
    (hn : 4 ≤ n) (hX : Blueprint.LieModel (X ⧸ pPrimeCore 2 X) .PSL 3 2 n)
    (hAY : A ≤ Y) (hA : Open.IsElemAbelian 2 A) (hA8 : 8 ≤ Nat.card A)
    (hBX : B ≤ X) (hB' : Open.IsElemAbelian 2 B) (hB8 : 8 ≤ Nat.card B) :
    GrSLit.wGroup A = GrSLit.wGroup B := by
  obtain ⟨z, s, D, -, hs, hzs, hYz, hYs, hXs, hD, hDY, hDX⟩ := hstep
  obtain ⟨eDY⟩ := Foote5.SolMax.diagonal_fusionZStar_equiv hs hzs hYz hYs hD hDY
  obtain ⟨E, hED, hE, hE8⟩ := exists_isElemTwo_of_three_le_pRank
    (three_le_pRank_of_lieModel_fusionZStar (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv eDY.symm
        (lieModel_fusionZStar_of_lieModel_pPrimeCore hY)))
  rw [← field_wGroup_eq_of_swapped_component hB
    (le_normalizer (mem_centralizer_singleton_iff.mpr hzs.symm)) hYz hYs hm hY (hED.trans hDY)
    hAY hE.isElemAbelian hE8 hA hA8]
  by_cases hXz : conjugate X z = X
  · rw [hXz, sup_idem] at hDX
    exact field_wGroup_eq_of_internal hB hn hX (hED.trans hDX) hBX hE.isElemAbelian hE8 hB' hB8
  · exact field_wGroup_eq_of_swapped_component hB
      (le_normalizer (mem_centralizer_singleton_iff.mpr hzs)) hXs hXz hn hX (hED.trans hDX) hBX
      hE.isElemAbelian hE8 hB' hB8

theorem lieModel_pPrimeCore_of_isTwoComponentIn (hmult : Quasithin.SchurMult2L3) {a : G}
    {Y : Subgroup G} (hY : FooteLit.IsTwoComponentIn Y (centralizer ({a} : Set G))) {m : ℕ}
    (hm : 3 ≤ m) (hL : Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 3 2 m) :
    Blueprint.LieModel (Y ⧸ pPrimeCore 2 Y) .PSL 3 2 m := by
  have : Group.IsPerfect Y := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hY.2
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hY.1).toMonoidHom)
      (subgroupOfEquivOfLe hY.1).surjective
  have hZO := (fusionZStar_eq_fusionOddCore_of_schurMult2L3 hmult (X := Y) hm hL).trans
    (UnbalancingLocal.fusionOddCore_eq_pPrimeCore Y)
  exact LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO) hL

theorem exists_isElemTwo_of_lieModel_pPrimeCore {J : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    (hJ : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 m) :
    ∃ A : Subgroup G, A ≤ J ∧ IsElemTwo A ∧ 8 ≤ Nat.card A := by
  obtain ⟨F, _, _, _, ρ, hF, hρ, hU⟩ := exists_surjective_of_lieModel_pPrimeCore hJ
  obtain ⟨R, hR, -⟩ := exists_isSylowTwoIn_ge (bot_le : ⊥ ≤ J) IsPGroup.of_bot
  obtain ⟨ρ', -, hker, hRU⟩ := exists_map_eq_projUnitriangular_of_isSylowTwoIn ρ hρ hR
  obtain ⟨hZe, hZc⟩ := isElemTwo_inf_centralizer_of_map_eq (by rw [hker]; exact hU) hR.le
    hR.isPGroup hRU
  refine ⟨_, inf_le_left.trans hR.le, hZe, ?_⟩
  rw [hZc, hF]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem exists_lieModel_pPrimeCore_of_gsMirrorReach (hS : SchreierFor Blueprint.Catalog)
    (hcat : L3TwoPowProperFixedCatalog) (hmult : Quasithin.SchurMult2L3) (hG : L34BaseSetting G)
    {t : G} {P Y : Subgroup G} (ht : orderOf t = 2)
    (hP : FooteLit.IsTwoComponentIn P (centralizer ({t} : Set G))) {m : ℕ} (hm : 4 ≤ m)
    (hev : Even m) (htype : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m)
    (hPY : FooteLit.GSMirrorReach P Y) :
    ∃ k : ℕ, 4 ≤ k ∧ Blueprint.LieModel (Y ⧸ pPrimeCore 2 Y) .PSL 3 2 k := by
  obtain ⟨hsimple, hna, hKP, -⟩ := id hG
  have := hsimple
  obtain ⟨k, hk, -, hYL⟩ := lieModel_of_gsMirrorReach hS hna hKP hcat hm hev htype hPY
  obtain ⟨c, -, hYc⟩ := Foote5.SolMax.isTwoComponentAt_of_gsMirrorReach ⟨t, ht, hP⟩ hPY
  exact ⟨k, hk, lieModel_pPrimeCore_of_isTwoComponentIn hmult hYc (by omega) hYL⟩

omit [Finite G] in
theorem forall_wGroup_eq_bot_iff_of_eq {Y X : Subgroup G}
    (hY : ∃ A : Subgroup G, A ≤ Y ∧ IsElemTwo A ∧ 8 ≤ Nat.card A)
    (hX : ∃ B : Subgroup G, B ≤ X ∧ IsElemTwo B ∧ 8 ≤ Nat.card B)
    (h : ∀ A B : Subgroup G, A ≤ Y → Open.IsElemAbelian 2 A → 8 ≤ Nat.card A → B ≤ X →
      Open.IsElemAbelian 2 B → 8 ≤ Nat.card B → wGroup A = wGroup B) :
    (∀ A : Subgroup G, A ≤ Y → Open.IsElemAbelian 2 A → 8 ≤ Nat.card A → wGroup A = ⊥) ↔
      (∀ B : Subgroup G, B ≤ X → Open.IsElemAbelian 2 B → 8 ≤ Nat.card B → wGroup B = ⊥) := by
  obtain ⟨A₀, hA₀Y, hA₀, hA₀8⟩ := hY
  obtain ⟨B₀, hB₀X, hB₀, hB₀8⟩ := hX
  refine ⟨fun hYv B hBX hB hB8 => ?_, fun hXv A hAY hA hA8 => ?_⟩
  · rw [← h A₀ B hA₀Y hA₀.isElemAbelian hA₀8 hBX hB hB8]
    exact hYv A₀ hA₀Y hA₀.isElemAbelian hA₀8
  · rw [h A B₀ hAY hA hA8 hB₀X hB₀.isElemAbelian hB₀8]
    exact hXv B₀ hB₀X hB₀.isElemAbelian hB₀8

omit [Finite G] in
theorem forall_wGroup_eq_bot_iff_conjugate (Y : Subgroup G) (g : G) :
    (∀ A : Subgroup G, A ≤ Y → Open.IsElemAbelian 2 A → 8 ≤ Nat.card A → wGroup A = ⊥) ↔
      (∀ B : Subgroup G, B ≤ conjugate Y g → Open.IsElemAbelian 2 B → 8 ≤ Nat.card B →
        wGroup B = ⊥) := by
  have key : ∀ (Y : Subgroup G) (h : G), (∀ A : Subgroup G, A ≤ Y → Open.IsElemAbelian 2 A →
      8 ≤ Nat.card A → wGroup A = ⊥) → ∀ B : Subgroup G, B ≤ Y.map (MulAut.conj h).toMonoidHom →
      Open.IsElemAbelian 2 B → 8 ≤ Nat.card B → wGroup B = ⊥ := by
    intro Y h hY B hBY hB hB8
    have hBY' : B.map (MulAut.conj h⁻¹).toMonoidHom ≤ Y := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hBY hx
      simpa [mul_assoc] using hy
    have h0 := hY _ hBY' ((isElemTwo_of_isElemAbelian hB).map_conj h⁻¹).isElemAbelian
      (by rw [card_map_of_injective (MulAut.conj h⁻¹).injective]; exact hB8)
    rw [wGroup_map_conj] at h0
    exact map_injective (MulAut.conj h⁻¹).injective (h0.trans (Subgroup.map_bot _).symm)
  refine ⟨key Y g⁻¹, fun hX A hAY hA hA8 => key _ g hX A (fun x hx => ?_) hA hA8⟩
  exact ⟨g⁻¹ * x * g, ⟨x, hAY hx, by simp⟩, by simp [mul_assoc]⟩

theorem field_internal_vanishing_iff_of_gsMirrorReach
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3)
    {G : Type} [Group G] [Finite G]
    (hG : L34BaseSetting G) {t : G} {P Q : Subgroup G}
    (ht : orderOf t = 2)
    (hP : FooteLit.IsTwoComponentIn P (centralizer ({t} : Set G)))
    {m : ℕ} (hm : 4 ≤ m) (hev : Even m)
    (htype : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m)
    (hreach : FooteLit.GSMirrorReach P Q) :
    (∀ A : Subgroup G, A ≤ P → Open.IsElemAbelian 2 A →
      8 ≤ Nat.card A → GrSLit.wGroup A = ⊥) ↔
    (∀ B : Subgroup G, B ≤ Q → Open.IsElemAbelian 2 B →
      8 ≤ Nat.card B → GrSLit.wGroup B = ⊥) := by
  obtain ⟨hsimple, hna, hKP, -, -, hloc, -, -⟩ := id hG
  have := hsimple
  have hB : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hloc
  have hvert := fun Y (hPY : FooteLit.GSMirrorReach P Y) =>
    exists_lieModel_pPrimeCore_of_gsMirrorReach hS hcat hmult hG ht hP hm hev htype hPY
  have hE8 := fun Y (hPY : FooteLit.GSMirrorReach P Y) =>
    have ⟨_, hk, hYk⟩ := hvert Y hPY
    exists_isElemTwo_of_lieModel_pPrimeCore (by omega) hYk
  induction hreach with
  | refl => exact Iff.rfl
  | @tail Y X hPY hst ih =>
    refine ih.trans ?_
    have hPX := hPY.tail hst
    obtain ⟨k, hk, hYk⟩ := hvert Y hPY
    obtain ⟨l, hl, hXl⟩ := hvert X hPX
    rcases hst with ⟨c, d, hW⟩ | hMir | ⟨g, rfl⟩
    · exact forall_wGroup_eq_bot_iff_of_eq (hE8 Y hPY) (hE8 X hPX)
        fun A B hAY hA hA8 hBX hB' hB8 => field_wGroup_eq_of_gsWeakCorr hS hB hKP hW
          (GSLit.not_mem_center_of_orderOf_eq_two hna hW.2.1) hk hYk hl hXl hAY hA hA8 hBX hB' hB8
    · exact forall_wGroup_eq_bot_iff_of_eq (hE8 Y hPY) (hE8 X hPX)
        fun A B hAY hA hA8 hBX hB' hB8 =>
          field_wGroup_eq_of_mirrorStep hB hMir hk hYk hl hXl hAY hA hA8 hBX hB' hB8
    · exact forall_wGroup_eq_bot_iff_conjugate Y g

end CFSG.ComponentClassification.GrSLit.L34Sec5S
