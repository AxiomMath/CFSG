module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorHost
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldKernel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMember
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.Goldschmidt.Steps.G37Basic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped commutatorElement

theorem false_of_field_host_central_normal (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) (hGold : GoldschmidtStronglyClosedInput)
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W)
    (hM : normalizer (W : Set G) = M) {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L)
    (hLn : L.Normal) (hZ : center ↥L = ⊥)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L) {n : ℕ} (hn : 4 ≤ n)
    (hLL : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 n) : False := by
  classical
  have hset' := hset
  obtain ⟨hbase, ht2, hPt, hPp, hPn, _⟩ := hset'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : centralizer ({t} : Set G) ≤ M :=
    ((normal_subgroupOf_iff_le_normalizer hPt).mp hPn).trans (hM ▸ hPW)
  have htM : t ∈ M := hCM (mem_centralizer_singleton_iff.mpr rfl)
  have hPM : P ≤ M := hPt.trans hCM
  obtain ⟨S, htS, hSW, ⟨A0, hA0S, hSA0, hA0ea, hA032⟩, hfus0⟩ :=
    exists_sylow_fusion_of_field hcat hmult hset hWodd hW1 hPW hWE
  have hSM : (S : Subgroup G) ≤ M := hM ▸ hSW
  rw [hM] at hfus0
  have hfus := hfus0
  let X := ↥M ⧸ pPrimeCore 2 ↥M
  let π : ↥M →* X := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = pPrimeCore 2 ↥M := QuotientGroup.ker_mk' _
  haveI : L.Normal := hLn
  let K : Subgroup X := Subgroup.centralizer (L : Set X)
  have hKn : K.Normal := Subgroup.normal_centralizer
  have hX0n : (L.comap π).Normal := hLn.comap π
  have hKcomapN : (K.comap π).Normal := hKn.comap π
  let SM : Subgroup ↥M := (S : Subgroup G).subgroupOf M
  let U : Subgroup ↥M := SM ⊓ L.comap π
  let Bm : Subgroup ↥M := SM ⊓ K.comap π
  let Am : Subgroup ↥M := ⁅U, U⁆
  let A : Subgroup G := Am.map M.subtype
  let B : Subgroup G := Bm.map M.subtype
  have hSM2 : IsPGroup 2 SM := by
    change IsPGroup 2 ((S : Subgroup G).comap M.subtype)
    exact S.isPGroup'.comap_subtype
  have hU_SM : U ≤ SM := inf_le_left
  have hBm_SM : Bm ≤ SM := inf_le_left
  have hAU : Am ≤ U := by
    change ⁅U, U⁆ ≤ U
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hAm_SM : Am ≤ SM := hAU.trans hU_SM
  have hNodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥M) :=
    Nat.prime_two.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hSbot : (S : Subgroup G) ⊓ (pPrimeCore 2 ↥M).map M.subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxN⟩ := mem_inf.mp hx
    obtain ⟨n, hnN, rfl⟩ := Subgroup.mem_map.mp hxN
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := (S.isPGroup' : IsPGroup 2 ↥S).exists_orderOf_eq_pow
      ⟨M.subtype n, hxS⟩
    have hk' : orderOf (M.subtype n) = 2 ^ k := by
      rwa [Subgroup.orderOf_mk] at hk
    have hnk : orderOf n = 2 ^ k := by
      rwa [orderOf_injective M.subtype M.subtype_injective n] at hk'
    have hodd : ¬ 2 ∣ orderOf n := fun h =>
      hNodd (h.trans ((pPrimeCore 2 ↥M).orderOf_dvd_natCard hnN))
    have hk0 : k = 0 := by
      cases k with
      | zero => rfl
      | succ j =>
        exfalso
        exact hodd (by rw [hnk]; exact dvd_pow_self 2 (Nat.succ_ne_zero j))
    have hn1 : n = 1 := orderOf_eq_one_iff.mp (by rw [hnk, hk0, pow_zero])
    rw [hn1, map_one]
  let V : Subgroup X := U.map π
  have hVleL : V ≤ L := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hu).2
  let SMs : Sylow 2 ↥M := S.subtype hSM
  have hSMs_coe : (SMs : Subgroup ↥M) = SM := rfl
  let VX : Sylow 2 X := SMs.mapSurjective (f := π) hπsurj
  have hVXcoe : (VX : Subgroup X) = SM.map π := by
    rw [Sylow.coe_mapSurjective (f := π) hπsurj SMs, hSMs_coe]
  let VL : Sylow 2 ↥L := CFSG.QuasiDihedralFusion.sylowInfNormal VX L
  have hVLcoe : (VL : Subgroup ↥L) = (VX : Subgroup X).subgroupOf L :=
    CFSG.QuasiDihedralFusion.sylowInfNormal_coe VX L
  have hVeq : V = SM.map π ⊓ L := by
    apply le_antisymm
    · exact le_inf (Subgroup.map_mono hU_SM) hVleL
    · intro y hy
      obtain ⟨hySM, hyL⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨u, huSM, rfl⟩ := Subgroup.mem_map.mp hySM
      exact Subgroup.mem_map.mpr
        ⟨u, Subgroup.mem_inf.mpr ⟨huSM, Subgroup.mem_comap.mpr hyL⟩, rfl⟩
  have hVLmap : ((VL : Subgroup ↥L).map L.subtype) = V := by
    rw [hVLcoe, Subgroup.subgroupOf_map_subtype, hVXcoe]
    exact hVeq.symm
  have hVsub : V.subgroupOf L = (VL : Subgroup ↥L) := by
    rw [← hVLmap]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hPSL : Open.StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 2 n :=
    hLL.statedClassicalModel (by decide)
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨eF⟩⟩ := hPSL
  letI : Field F := hFfield
  letI : Finite F := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  have hFchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rwa [← Nat.card_eq_fintype_card])
  letI : CharP F 2 := hFchar
  let eL : ↥L ≃* projectiveSL 3 F :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eF).trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  let ef : (Fin 1 → projectiveSL 3 F) ≃* projectiveSL 3 F :=
    MulEquiv.funUnique (Fin 1) (projectiveSL 3 F)
  let VLS : Sylow 2 (projectiveSL 3 F) := VL.mapSurjective (f := eL.toMonoidHom) eL.surjective
  let V1 : Sylow 2 (Fin 1 → projectiveSL 3 F) :=
    VLS.mapSurjective (f := ef.symm.toMonoidHom) ef.symm.surjective
  let V1s : Subgroup (Fin 1 → projectiveSL 3 F) := V1
  have hVLScoe : (VLS : Subgroup (projectiveSL 3 F)) =
      (VL : Subgroup ↥L).map eL.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eL.toMonoidHom) eL.surjective VL
  have hV1coe : V1s = (VLS : Subgroup (projectiveSL 3 F)).map ef.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := ef.symm.toMonoidHom) ef.symm.surjective VLS
  let φ : ↥V →* (Fin 1 → projectiveSL 3 F) :=
    ef.symm.toMonoidHom.comp (eL.toMonoidHom.comp (Subgroup.inclusion hVleL))
  have hφinj : Function.Injective φ :=
    ef.symm.injective.comp (eL.injective.comp (Subgroup.inclusion_injective hVleL))
  have hincl_range : (Subgroup.inclusion hVleL).range = V.subgroupOf L := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr v.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext rfl⟩
  have hφrange : φ.range = V1s := by
    rw [MonoidHom.range_eq_map]
    change (⊤ : Subgroup ↥V).map
      (ef.symm.toMonoidHom.comp (eL.toMonoidHom.comp (Subgroup.inclusion hVleL))) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, Subgroup.map_top, hincl_range, hVsub,
      ← hVLScoe, ← hV1coe]
  let Hv : Subgroup ↥V := ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆
  have hHvmap : Hv.map V.subtype = ⁅V, V⁆ := by
    change (⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆).map V.subtype = ⁅V, V⁆
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hφHv : Hv.map φ = ⁅V1s, V1s⁆ := by
    change (⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆).map φ = _
    rw [Subgroup.map_commutator, Subgroup.map_top, hφrange]
  have hHvelem : IsElemTwo Hv := by
    have h1 : IsElemTwo ⁅V1s, V1s⁆ :=
      (isElemTwo_commutator_sylow_pi V1).1
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hx' : φ x ∈ ⁅V1s, V1s⁆ := by
        rw [← hφHv]; exact Subgroup.mem_map_of_mem φ hx
      have hy' : φ y ∈ ⁅V1s, V1s⁆ := by
        rw [← hφHv]; exact Subgroup.mem_map_of_mem φ hy
      apply hφinj
      rw [map_mul, map_mul]
      exact h1.1 _ hx' _ hy'
    · have hx' : φ x ∈ ⁅V1s, V1s⁆ := by
        rw [← hφHv]; exact Subgroup.mem_map_of_mem φ hx
      apply hφinj
      rw [map_mul, h1.2 _ hx', map_one]
  have hVVelem : IsElemTwo ⁅V, V⁆ := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hx' : x ∈ Hv.map V.subtype := by rw [hHvmap]; exact hx
      have hy' : y ∈ Hv.map V.subtype := by rw [hHvmap]; exact hy
      obtain ⟨x', hx'', rfl⟩ := Subgroup.mem_map.mp hx'
      obtain ⟨y', hy'', rfl⟩ := Subgroup.mem_map.mp hy'
      simpa using congrArg V.subtype (hHvelem.1 x' hx'' y' hy'')
    · have hx' : x ∈ Hv.map V.subtype := by rw [hHvmap]; exact hx
      obtain ⟨x', hx'', rfl⟩ := Subgroup.mem_map.mp hx'
      simpa using congrArg V.subtype (hHvelem.2 x' hx'')
  have hAmap : Am.map π = ⁅V, V⁆ := by
    change (⁅U, U⁆).map π = ⁅V, V⁆
    rw [Subgroup.map_commutator]
  have hUN : U ⊓ pPrimeCore 2 ↥M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzU : z ∈ U := (mem_inf.mp hz).1
    have hzN : z ∈ pPrimeCore 2 ↥M := (mem_inf.mp hz).2
    rw [Subgroup.mem_bot]
    apply M.subtype_injective
    have hzSM : z ∈ SM := hU_SM hzU
    have hzS : M.subtype z ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.mp hzSM
    have hzNL : M.subtype z ∈ (pPrimeCore 2 ↥M).map M.subtype :=
      Subgroup.mem_map_of_mem M.subtype hzN
    have hzbot : M.subtype z ∈ (⊥ : Subgroup G) := by
      rw [← hSbot]
      exact mem_inf.mpr ⟨hzS, hzNL⟩
    simpa using hzbot
  have hπinjU : Function.Injective (π.subgroupMap U) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap, hπker]
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hzN : (z : ↥M) ∈ pPrimeCore 2 ↥M := Subgroup.mem_subgroupOf.mp hz
    have hzbot : (z : ↥M) ∈ (⊥ : Subgroup ↥M) := by
      rw [← hUN]
      exact mem_inf.mpr ⟨z.2, hzN⟩
    exact Subgroup.mem_bot.mp hzbot
  have hAmelem : IsElemTwo Am := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hxU : x ∈ U := hAU hx
      have hyU : y ∈ U := hAU hy
      have hπx : π x ∈ ⁅V, V⁆ := by
        rw [← hAmap]; exact Subgroup.mem_map_of_mem π hx
      have hπy : π y ∈ ⁅V, V⁆ := by
        rw [← hAmap]; exact Subgroup.mem_map_of_mem π hy
      have h1 : π.subgroupMap U ⟨x, hxU⟩ * π.subgroupMap U ⟨y, hyU⟩ =
          π.subgroupMap U ⟨y, hyU⟩ * π.subgroupMap U ⟨x, hxU⟩ := by
        apply Subtype.ext
        show π x * π y = π y * π x
        exact hVVelem.1 _ hπx _ hπy
      have h2 : π.subgroupMap U (⟨x, hxU⟩ * ⟨y, hyU⟩) =
          π.subgroupMap U (⟨y, hyU⟩ * ⟨x, hxU⟩) := by
        simpa only [map_mul] using h1
      exact congrArg Subtype.val (hπinjU h2)
    · have hxU : x ∈ U := hAU hx
      have hπx : π x ∈ ⁅V, V⁆ := by
        rw [← hAmap]; exact Subgroup.mem_map_of_mem π hx
      have h1 : π.subgroupMap U ⟨x, hxU⟩ * π.subgroupMap U ⟨x, hxU⟩ = 1 := by
        apply Subtype.ext
        show π x * π x = 1
        exact hVVelem.2 _ hπx
      have h2 : π.subgroupMap U (⟨x, hxU⟩ * ⟨x, hxU⟩) =
          π.subgroupMap U (1 : ↥U) := by
        simpa only [map_mul, map_one] using h1
      exact congrArg Subtype.val (hπinjU h2)
  have hAelem : IsElemTwo A := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨xm, hxm, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨ym, hym, rfl⟩ := Subgroup.mem_map.mp hy
      simpa using congrArg M.subtype (hAmelem.1 xm hxm ym hym)
    · obtain ⟨xm, hxm, rfl⟩ := Subgroup.mem_map.mp hx
      simpa using congrArg M.subtype (hAmelem.2 xm hxm)
  have hA16 : 16 ≤ Nat.card A := by
    have hcardV1 : Nat.card ↥⁅V1s, V1s⁆ =
        Nat.card F := by
      simpa using (isElemTwo_commutator_sylow_pi V1).2
    have hcardHv : Nat.card ↥⁅V, V⁆ = Nat.card ↥Hv := by
      rw [← hHvmap, Subgroup.card_map_of_injective V.subtype_injective]
    have hcardVV : Nat.card ↥⁅V1s, V1s⁆ ≤
        Nat.card ↥⁅V, V⁆ := by
      have h1 := Nat.card_le_card_of_surjective (φ.subgroupMap Hv)
        (φ.subgroupMap_surjective Hv)
      rw [hφHv] at h1
      rwa [← hcardHv] at h1
    have hcardAm : Nat.card ↥⁅V, V⁆ ≤ Nat.card ↥Am := by
      have h1 := Nat.card_le_card_of_surjective (π.subgroupMap Am)
        (π.subgroupMap_surjective Am)
      rwa [hAmap] at h1
    have hcardA : Nat.card A = Nat.card ↥Am := by
      change Nat.card ↥(Am.map M.subtype) = Nat.card ↥Am
      exact Subgroup.card_map_of_injective M.subtype_injective
    have hF16 : 16 ≤ Nat.card F := by
      rw [hFcard]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 16 ≤ Nat.card F := hF16
      _ = Nat.card ↥⁅V1s, V1s⁆ := hcardV1.symm
      _ ≤ Nat.card ↥⁅V, V⁆ := hcardVV
      _ ≤ Nat.card ↥Am := hcardAm
      _ = Nat.card A := hcardA.symm
  have hBS : B ≤ (S : Subgroup G) := by
    change Bm.map M.subtype ≤ (S : Subgroup G)
    intro x hx
    obtain ⟨xm, hxm, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hBm_SM hxm)
  have hAS : A ≤ (S : Subgroup G) := by
    change Am.map M.subtype ≤ (S : Subgroup G)
    intro x hx
    obtain ⟨xm, hxm, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hAm_SM hxm)
  have hAmBm : Am ⊓ Bm = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzAm : z ∈ Am := (mem_inf.mp hz).1
    have hzBm : z ∈ Bm := (mem_inf.mp hz).2
    have hzU : z ∈ U := hAU hzAm
    have hπzL : π z ∈ L := Subgroup.mem_comap.mp (mem_inf.mp hzU).2
    have hπzK : π z ∈ K := Subgroup.mem_comap.mp (mem_inf.mp hzBm).2
    have hLK : (L ⊓ K : Subgroup X) = ⊥ := by
      change L ⊓ Subgroup.centralizer (L : Set X) = ⊥
      rw [CFSG.GroupTheory.inf_centralizer_eq_map_center L, hZ, Subgroup.map_bot]
    have hπzbot : π z ∈ (⊥ : Subgroup X) := by
      rw [← hLK]
      exact mem_inf.mpr ⟨hπzL, hπzK⟩
    have hπ1 : π z = 1 := Subgroup.mem_bot.mp hπzbot
    have h1 : (⟨z, hzU⟩ : ↥U) = 1 := by
      apply hπinjU
      apply Subtype.ext
      simpa using hπ1
    exact congrArg Subtype.val h1
  have hAB : A ⊓ B = ⊥ := by
    change Am.map M.subtype ⊓ Bm.map M.subtype = ⊥
    rw [← Subgroup.map_inf Am Bm M.subtype M.subtype_injective, hAmBm, Subgroup.map_bot]
  have hBmA : Bm ≤ Subgroup.centralizer (Am : Set ↥M) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hbSM : b ∈ SM := hBm_SM hb
    have haU : a ∈ U := hAU ha
    have hcommπ : π ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      have haL : π a ∈ L := Subgroup.mem_comap.mp (mem_inf.mp haU).2
      have hbK : π b ∈ K := Subgroup.mem_comap.mp (mem_inf.mp hb).2
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hbK) (π a) haL)
    have hmemU : ⁅a, b⁆ ∈ U := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hU_SM haU) hbSM) (inv_mem (hU_SM haU)))
          (inv_mem hbSM)
      · rw [Subgroup.mem_comap, hcommπ]
        exact one_mem L
    have h1 : (⟨⁅a, b⁆, hmemU⟩ : ↥U) = 1 := by
      apply hπinjU
      apply Subtype.ext
      simpa using hcommπ
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h1)
  have hcomm : B ≤ Subgroup.centralizer (A : Set G) := by
    change Bm.map M.subtype ≤ Subgroup.centralizer (Am.map M.subtype : Set G)
    intro b hb
    obtain ⟨bm, hbm, rfl⟩ := Subgroup.mem_map.mp hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨am, ham, rfl⟩ := Subgroup.mem_map.mp ha
    simpa using congrArg M.subtype
      (Subgroup.mem_centralizer_iff.mp (hBmA hbm) am ham)
  have hUn : SM ≤ Subgroup.normalizer (U : Set ↥M) := by
    intro sm hsm
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact mem_inf.mpr ⟨mul_mem (mul_mem hsm (mem_inf.mp hu).1) (inv_mem hsm),
        hX0n.conj_mem u (mem_inf.mp hu).2 sm⟩
    · intro hu
      have h1 : u = sm⁻¹ * (sm * u * sm⁻¹) * sm := by group
      rw [h1]
      exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hsm) (mem_inf.mp hu).1) hsm,
        hX0n.conj_mem' (sm * u * sm⁻¹) (mem_inf.mp hu).2 sm⟩
  have hAmn : SM ≤ Subgroup.normalizer (Am : Set ↥M) := by
    intro sm hsm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (⁅U, U⁆).map (MulAut.conj sm) = ⁅U, U⁆
    rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUn hsm)]
  have hAn : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hsm : (⟨s, hSM hs⟩ : ↥M) ∈ SM := hs
    have hcomp : (MulAut.conj s).toMonoidHom.comp M.subtype =
        M.subtype.comp (MulAut.conj (⟨s, hSM hs⟩ : ↥M)).toMonoidHom := by
      ext l
      simp [MulAut.conj_apply, mul_assoc]
    change (Am.map M.subtype).map (MulAut.conj s).toMonoidHom = Am.map M.subtype
    calc (Am.map M.subtype).map (MulAut.conj s).toMonoidHom =
        Am.map ((MulAut.conj s).toMonoidHom.comp M.subtype) :=
          Subgroup.map_map Am (MulAut.conj s).toMonoidHom M.subtype
      _ = Am.map (M.subtype.comp (MulAut.conj (⟨s, hSM hs⟩ : ↥M)).toMonoidHom) := by
          rw [hcomp]
      _ = (Am.map (MulAut.conj (⟨s, hSM hs⟩ : ↥M)).toMonoidHom).map M.subtype :=
          (Subgroup.map_map Am M.subtype
            (MulAut.conj (⟨s, hSM hs⟩ : ↥M)).toMonoidHom).symm
      _ = Am.map M.subtype := by
          have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAmn hsm)
          simpa using congrArg (Subgroup.map M.subtype) h
  have htmK : π ⟨t, htM⟩ ∈ K := by
    change π ⟨t, htM⟩ ∈ Subgroup.centralizer (L : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hPL] at ha
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hPt (Subgroup.mem_subgroupOf.mp hp))
  have htmBm : (⟨t, htM⟩ : ↥M) ∈ Bm := by
    refine mem_inf.mpr ⟨?_, Subgroup.mem_comap.mpr htmK⟩
    exact Subgroup.mem_subgroupOf.mpr htS
  have htB : t ∈ B := by
    change t ∈ Bm.map M.subtype
    exact Subgroup.mem_map.mpr ⟨⟨t, htM⟩, htmBm, rfl⟩
  have hBne : B ≠ ⊥ := by
    intro hbot
    have ht1 : t = 1 := by
      have hmem : t ∈ (⊥ : Subgroup G) := hbot ▸ htB
      simpa using hmem
    rw [ht1, orderOf_one] at ht2
    norm_num at ht2
  have hA0 : IsElemTwo A0 := isElemTwo_of_sq fun a ha => by
    rw [← pow_two]
    exact hA0ea.2 a ha
  have hBinv : ∀ b ∈ B, orderOf b = 2 → ∀ g : G,
      g⁻¹ * b * g ∈ (S : Subgroup G) → g⁻¹ * b * g ∈ B := by
    intro b hb hb2 g hg
    have hbS : b ∈ (S : Subgroup G) := hBS hb
    have hbM : b ∈ M := hSM hbS
    have hbsq : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
    have hrb : 3 ≤ pRank 2 ↥((S : Subgroup G) ⊓ centralizer ({b} : Set G)) :=
      three_le_pRank_of_sq_centralizes hA0S hA0 hA032 (hSA0 hbS)
        (fun e _ => by rw [hbsq, one_mul, mul_one])
    have hysq : (g⁻¹ * b * g) * (g⁻¹ * b * g) = 1 := by
      calc (g⁻¹ * b * g) * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
        _ = 1 := by rw [hbsq]; group
    have hry : 3 ≤ pRank 2
        ↥((S : Subgroup G) ⊓ centralizer ({g⁻¹ * b * g} : Set G)) :=
      three_le_pRank_of_sq_centralizes hA0S hA0 hA032 (hSA0 hg)
        (fun e _ => by rw [hysq, one_mul, mul_one])
    obtain ⟨m, hmM, hm⟩ := hfus b hbS g hg hrb hry
    have hbmBm : (⟨b, hbM⟩ : ↥M) ∈ Bm := by
      have hmem : b ∈ Bm.map M.subtype := hb
      obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hmem
      have hz_eq : z = ⟨b, hbM⟩ := M.subtype_injective (by simpa using hzeq)
      rwa [hz_eq] at hz
    have hymK : (⟨g⁻¹ * b * g, hSM hg⟩ : ↥M) ∈ K.comap π := by
      have hconj : (⟨g⁻¹ * b * g, hSM hg⟩ : ↥M) =
          (⟨m, hmM⟩ : ↥M)⁻¹ * ⟨b, hbM⟩ * ⟨m, hmM⟩ := by
        apply Subtype.ext
        simpa using hm
      rw [hconj]
      exact hKcomapN.conj_mem' ⟨b, hbM⟩ (mem_inf.mp hbmBm).2 ⟨m, hmM⟩
    have hymBm : (⟨g⁻¹ * b * g, hSM hg⟩ : ↥M) ∈ Bm :=
      mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hg, hymK⟩
    change g⁻¹ * b * g ∈ Bm.map M.subtype
    exact Subgroup.mem_map.mpr ⟨_, hymBm, rfl⟩
  have hBM : ∀ m ∈ M, ∀ b ∈ B, m⁻¹ * b * m ∈ (S : Subgroup G) →
      m⁻¹ * b * m ∈ B := by
    intro m hmM b hb hconj
    change b ∈ Bm.map M.subtype at hb
    obtain ⟨bm, hbm, rfl⟩ := Subgroup.mem_map.mp hb
    have hyM : (⟨m⁻¹ * M.subtype bm * m, hSM hconj⟩ : ↥M) =
        (⟨m, hmM⟩ : ↥M)⁻¹ * bm * ⟨m, hmM⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    have hyK : (⟨m⁻¹ * M.subtype bm * m, hSM hconj⟩ : ↥M) ∈ K.comap π := by
      rw [hyM]
      exact hKcomapN.conj_mem' bm (mem_inf.mp hbm).2 ⟨m, hmM⟩
    have hyBm : (⟨m⁻¹ * M.subtype bm * m, hSM hconj⟩ : ↥M) ∈ Bm :=
      mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hconj, hyK⟩
    change m⁻¹ * M.subtype bm * m ∈ Bm.map M.subtype
    exact Subgroup.mem_map.mpr ⟨_, hyBm, rfl⟩
  have hstrong : CFSG.IsStronglyClosedIn (S : Subgroup G) (B : Set G) :=
    stronglyClosed_kernel_of_rank_four S.isPGroup' hSM hAS hBS hAn hAelem.isElemAbelian hA16
      hAB hcomm hBinv hBM hfus
  have hsc : ∀ a ∈ B, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ B :=
    hstrong.2
  obtain ⟨hsF, hnF, -⟩ := GrS5.fstar_facts hbase
  have hGoldB : Group.IsSolvable ↥(Subgroup.centralizer (B : Set G)) :=
    hGold G hsF hnF S B hBS hBne hsc
  let X0 : Subgroup ↥M := L.comap π
  have hX0def : X0 = L.comap π := rfl
  have hX0normal : X0.Normal := by rw [hX0def]; exact hX0n
  have hNX0 : pPrimeCore 2 ↥M ≤ X0 := by
    rw [hX0def]
    intro n hn
    rw [Subgroup.mem_comap]
    have hπn : π n = 1 := by
      show (QuotientGroup.mk' (pPrimeCore 2 ↥M)) n = 1
      exact (QuotientGroup.eq_one_iff n).mpr hn
    rw [hπn]
    exact one_mem L
  have hRX0 : Bm ≤ Subgroup.normalizer (X0 : Set ↥M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hX0normal]
    exact le_top
  have hRN : Bm ≤ Subgroup.normalizer (pPrimeCore 2 ↥M : Set ↥M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (pPrimeCore 2 ↥M).Normal)]
    exact le_top
  have hR2 : IsPGroup 2 Bm := hSM2.to_le hBm_SM
  have hX0map : X0.map π = L := by
    rw [hX0def]
    exact Subgroup.map_comap_eq_self_of_surjective hπsurj L
  have hNmap : (pPrimeCore 2 ↥M).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπker]
  have hcommCover : ⁅X0, Bm⁆ ≤ pPrimeCore 2 ↥M := by
    rw [← hπker, ← Subgroup.map_eq_bot_iff]
    rw [Subgroup.map_commutator, hX0map]
    have hLKBot : ⁅L, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp hk x hx).symm
    have hBK : Bm.map π ≤ K := by
      intro y hy
      obtain ⟨bm, hbm, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_comap.mp (mem_inf.mp hbm).2
    exact le_bot_iff.mp (hLKBot ▸ Subgroup.commutator_mono_right hBK)
  have hcover := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    hNX0 hRX0 hRN hR2 hNodd hcommCover
  have hS0map : (X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)).map π = L := by
    have h := congrArg (Subgroup.map π) hcover
    rw [Subgroup.map_sup, hX0map, hNmap, sup_bot_eq] at h
    exact h
  have hS0C : (X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)).map M.subtype ≤
      Subgroup.centralizer (B : Set G) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    change b ∈ Bm.map M.subtype at hb
    obtain ⟨bm, hbm, rfl⟩ := Subgroup.mem_map.mp hb
    have hzR : z ∈ Subgroup.centralizer (Bm : Set ↥M) := (mem_inf.mp hz).2
    simpa using congrArg M.subtype
      (Subgroup.mem_centralizer_iff.mp hzR bm hbm)
  have hsolvImage : Group.IsSolvable
      ↥((X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)).map M.subtype) := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer (B : Set G)) := hGoldB
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hS0C)
  have hsolvS0 : Group.IsSolvable ↥(X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)) := by
    haveI : Group.IsSolvable
        ↥((X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)).map M.subtype) := hsolvImage
    let f : ↥(X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)) →*
        ↥((X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)).map M.subtype) :=
      M.subtype.subgroupMap _
    have hf : Function.Injective f :=
      M.subtype.subgroupMap_injective _ M.subtype_injective
    exact Group.isSolvable_of_isSolvable_injective hf
  have hsolvMap : Group.IsSolvable
      ↥((X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)).map π) := by
    haveI : Group.IsSolvable ↥(X0 ⊓ Subgroup.centralizer (Bm : Set ↥M)) := hsolvS0
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  have hsolvL : Group.IsSolvable ↥L := by
    rw [hS0map] at hsolvMap
    exact hsolvMap
  have hntL : Nontrivial ↥L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    have h' : a = b := Subsingleton.elim a b
    exact hab (by rw [h'])
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : Nontrivial ↥L := hntL
  exact Group.IsPerfect.not_isSolvable ↥L hsolvL

theorem false_of_field_host_central_moved (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] {t : G} {P M : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hmax : FooteLit.GSMirrorMaximal P)
    (hCM : centralizer ({t} : Set G) ≤ M) {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hL : IsComponent L) (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L)
    (hLn : ¬ L.Normal) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfield : L34FieldNormalSetting G t P := hset
  have hbase0 : L34BaseSetting G := hset.1
  obtain ⟨hbase, ht, hPt, hPp, hPn, mexp, hmexp, hme, hPLie⟩ := hset
  obtain ⟨hsimple, hnab, hKP, -, -, -, -, -⟩ := hbase
  let π : ↥M →* (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let O : Subgroup ↥M := pPrimeCore 2 ↥M
  have htM : t ∈ M := hCM (mem_centralizer_singleton_iff.mpr rfl)
  have hPM : P ≤ M := hPt.trans hCM
  obtain ⟨K₀, hK₀p, hK₀map⟩ :=
    GH74.GLS.C3.Layer1.Thm1.exists_pComponent_of_quotient_component hL
  let K : Subgroup G := K₀.map M.subtype
  have hKsub : K.subgroupOf M = K₀ := CFSG.subgroupOf_map_subtype_eq K₀
  have hKM : K ≤ M := Subgroup.map_subtype_le K₀
  have hK : FooteLit.IsTwoComponentIn K M := ⟨hKM, by rw [hKsub]; exact hK₀p⟩
  have hKmap : (K.subgroupOf M).map π = L := by
    rw [hKsub]
    simpa only [π] using hK₀map
  have hPle : P.subgroupOf M ≤ O ⊔ K₀ := by
    intro x hx
    have hxL : π x ∈ L := by
      have h1 : π x ∈ (P.subgroupOf M).map π := Subgroup.mem_map_of_mem π hx
      have h2 : (P.subgroupOf M).map π = L := by simpa only [π] using hPL
      rwa [h2] at h1
    have hxK : π x ∈ K₀.map π := by
      rw [hK₀map]
      exact hxL
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hxK
    have hker : π (k⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hkπ]
      group
    have hxO : k⁻¹ * x ∈ O := by
      have h1 : k⁻¹ * x ∈ (QuotientGroup.mk' O).ker := MonoidHom.mem_ker.mpr hker
      rwa [QuotientGroup.ker_mk'] at h1
    have hxeq : x = k * (k⁻¹ * x) := by group
    rw [hxeq]
    simpa only [sup_comm] using Subgroup.mul_mem_sup hk hxO
  have hPcomm : ⁅P, P⁆ = P := TBLit.commutator_self_of_isPComponent hPt hPp
  have hPperf : Group.IsPerfect ↥(P.subgroupOf M) := by
    have hPperfG : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPcomm
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPM).symm.surjective
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa only [O] using pPrimeCore_coprime_card (p := 2) (G := ↥M)
  have hOsolv : Group.IsSolvable ↥O :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp hOcop)
  have hPleK₀ : P.subgroupOf M ≤ K₀ :=
    CFSG.Goldschmidt.G37.le_of_perfect_of_le_sup hPperf
      (by simpa only [sup_comm] using hPle) (pPrimeCore_le_normalizer hK₀p) hOsolv
  have hPK : P ≤ K := by
    have h1 := Subgroup.map_mono (f := M.subtype) hPleK₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hPM] at h1
  let tM : ↥M := ⟨t, htM⟩
  let u : ↥M ⧸ pPrimeCore 2 ↥M := π tM
  have hcentL : ∀ x ∈ L, u * x = x * u := by
    intro x hx
    have hx' : (x : ↥M ⧸ pPrimeCore 2 ↥M) ∈ (P.subgroupOf M).map π := by
      have h2 : (P.subgroupOf M).map π = L := by simpa only [π] using hPL
      rwa [h2]
    obtain ⟨pM, hpM, hpπ⟩ := Subgroup.mem_map.mp hx'
    have hpP : (pM : G) ∈ P := Subgroup.mem_subgroupOf.mp hpM
    have hcomm : (pM : ↥M) * tM = tM * pM := by
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hPt hpP)
    calc u * x = π tM * π pM := by rw [← hpπ]
      _ = π (tM * pM) := (map_mul π tM pM).symm
      _ = π (pM * tM) := by rw [hcomm]
      _ = π pM * π tM := map_mul π pM tM
      _ = x * u := by rw [hpπ]
  have huL : conjugate L u = L := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      change (MulAut.conj u⁻¹) x ∈ L
      rw [show (MulAut.conj u⁻¹) x = x by
        rw [MulAut.conj_apply]
        have h := hcentL x hx
        calc u⁻¹ * x * (u⁻¹)⁻¹ = u⁻¹ * (x * u) := by group
          _ = u⁻¹ * (u * x) := by rw [h]
          _ = x := by group]
      exact hx
    · intro y hy
      refine ⟨y, hy, ?_⟩
      change (MulAut.conj u⁻¹) y = y
      rw [MulAut.conj_apply]
      have h := hcentL y hy
      calc u⁻¹ * y * (u⁻¹)⁻¹ = u⁻¹ * (y * u) := by group
        _ = u⁻¹ * (u * y) := by rw [h]
        _ = y := by group
  have hKt : FooteLit.IsTwoComponentIn (conjugate K t) M := by
    have hh : t⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer (inv_mem htM)
    simpa [CFSG.conjugate] using Sol76.isTwoComponentIn_map_conj hK hh
  have hKtmap : ((conjugate K t).subgroupOf M).map π = L := by
    have hsub : (conjugate K t).subgroupOf M = conjugate (K.subgroupOf M) tM := by
      simpa [CFSG.conjugate] using
        (CFSG.GroupTheory.conjugate_subgroupOf (B := K) (U := M) tM).symm
    calc ((conjugate K t).subgroupOf M).map π =
          (conjugate (K.subgroupOf M) tM).map π := by rw [hsub]
      _ = conjugate ((K.subgroupOf M).map π) (π tM) :=
        UnbalancedLayer.map_conjugate π (K.subgroupOf M) tM
      _ = conjugate L u := by rw [hKmap]
      _ = L := huL
  have hKeqK : K.subgroupOf M = (conjugate K t).subgroupOf M :=
    pComponent_eq_of_map_eq hK.2 hKt.2 (by rw [hKmap, hKtmap])
  have hKeq : K = conjugate K t := by
    have h := Subgroup.subgroupOf_inj.mp hKeqK
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hKt.1] at h
  have htNK : t ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have h1 := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hKeq.symm
    rw [CFSG.conjugate, Subgroup.map_map, hcomp, Subgroup.map_id] at h1
    exact h1.symm
  have htQ : t ∈ UnbalancedLayer.coreActionKernel K := by
    refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨htNK, ?_⟩
    intro j hj
    have hjM : j ∈ M := hK.1 hj
    have htinvNK : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem htNK
    have hcK : j⁻¹ * t⁻¹ * j * t ∈ K := by
      have h1 : t⁻¹ * j * t ∈ K := by
        simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp htinvNK j).mp hj
      have h2 : j⁻¹ * (t⁻¹ * j * t) ∈ K := K.mul_mem (K.inv_mem hj) h1
      simpa [mul_assoc] using h2
    have hcOM : j⁻¹ * t⁻¹ * j * t ∈ FooteLit.oddCoreIn M := by
      let jM : ↥M := ⟨j, hjM⟩
      let cM : ↥M := jM⁻¹ * tM⁻¹ * jM * tM
      have hπj : π jM ∈ L := by
        have hmem : jM ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr hj
        have h1 : π jM ∈ (K.subgroupOf M).map π := Subgroup.mem_map_of_mem π hmem
        rwa [hKmap] at h1
      have hcπ : π cM = 1 := by
        have hcomm : u * π jM = π jM * u := hcentL (π jM) hπj
        have hcomm' : u⁻¹ * π jM = π jM * u⁻¹ :=
          (show Commute u (π jM) from hcomm).inv_left
        have h1 : (π jM)⁻¹ * u⁻¹ * (π jM) * u = 1 := by
          calc (π jM)⁻¹ * u⁻¹ * (π jM) * u =
                (π jM)⁻¹ * (u⁻¹ * (π jM)) * u := by group
            _ = (π jM)⁻¹ * ((π jM) * u⁻¹) * u := by rw [hcomm']
            _ = 1 := by group
        simpa only [cM, map_mul, map_inv, u] using h1
      have hcO : cM ∈ O := by
        have h1 : cM ∈ (QuotientGroup.mk' O).ker := MonoidHom.mem_ker.mpr hcπ
        rwa [QuotientGroup.ker_mk'] at h1
      have hcM : (cM : G) = j⁻¹ * t⁻¹ * j * t := by simp [cM, jM, tM]
      rw [← hcM]
      exact Subgroup.mem_map.mpr ⟨cM, hcO, rfl⟩
    change j⁻¹ * t⁻¹ * j * t ∈ FooteLit.oddCoreIn K
    rw [← Sol76.inf_oddCoreIn_eq hK]
    exact Subgroup.mem_inf.mpr ⟨hcK, hcOM⟩
  have hπcop : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    simpa only [O] using pPrimeCore_coprime_card (p := 2) (G := ↥M)
  have hπodd : ¬ 2 ∣ Nat.card π.ker := Nat.prime_two.coprime_iff_not_dvd.mp hπcop
  have hPLstar : Nonempty (P ⧸ Open.fusionZStar P ≃* L ⧸ Open.fusionZStar L) := by
    have hPL' : (P.subgroupOf M).map π = L := by simpa only [π] using hPL
    obtain ⟨e0⟩ :=
      GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π hπodd (P.subgroupOf M)
    rw [hPL'] at e0
    exact ⟨(Sol78.fusionZStarQuotCongr (Subgroup.subgroupOfEquivOfLe hPM)).symm.trans e0⟩
  have hKLstar : Nonempty (K ⧸ Open.fusionZStar K ≃* L ⧸ Open.fusionZStar L) := by
    obtain ⟨e0⟩ :=
      GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π hπodd (K.subgroupOf M)
    rw [hKmap] at e0
    exact ⟨(Sol78.fusionZStarQuotCongr
      (Subgroup.subgroupOfEquivOfLe hK.1)).symm.trans e0⟩
  have htype : Nonempty (P ⧸ Open.fusionZStar P ≃* K ⧸ Open.fusionZStar K) := by
    obtain ⟨eP⟩ := hPLstar
    obtain ⟨eK⟩ := hKLstar
    exact ⟨eP.trans eK.symm⟩
  set H : Subgroup G := K ⊓ centralizer ({t} : Set G) with hH
  have hHC : H ≤ centralizer ({t} : Set G) := hH.symm ▸ inf_le_right
  have hHM : H ≤ M := hH.symm ▸ (inf_le_left.trans hK.1)
  have hPH : P ≤ H := hH.symm ▸ le_inf hPK hPt
  have hPpcH : IsPComponent 2 (P.subgroupOf H) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hPH hHC hPp
  let g : ↥H →* (↥M ⧸ pPrimeCore 2 ↥M) := π.comp (Subgroup.inclusion hHM)
  let f : ↥H →* ↥L := g.codRestrict L fun x => by
    have hxH : (x : G) ∈ K ⊓ centralizer ({t} : Set G) := by
      rw [← hH]
      exact x.2
    have hxK' : ((Subgroup.inclusion hHM x : ↥M) : G) ∈ K := by
      simpa using (mem_inf.mp hxH).1
    have hxK : (Subgroup.inclusion hHM x : ↥M) ∈ K.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hxK'
    have h1 : g x ∈ (K.subgroupOf M).map π := by
      simpa only [g, MonoidHom.comp_apply] using Subgroup.mem_map_of_mem π hxK
    rwa [hKmap] at h1
  have hgcop : Nat.Coprime 2 (Nat.card g.ker) := by
    let ι : g.ker →* π.ker :=
      { toFun := fun x => ⟨Subgroup.inclusion hHM (x : ↥H),
          MonoidHom.mem_ker.mpr (by
            have hx : g (x : ↥H) = 1 := MonoidHom.mem_ker.mp x.2
            simpa only [g, MonoidHom.comp_apply] using hx)⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
    have hinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext
      exact Subtype.ext (congrArg (fun z : π.ker => ((z : ↥M) : G)) hab)
    exact hπcop.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hinj)
  have hker : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [MonoidHom.ker_codRestrict]
    exact hgcop
  have hcover : Function.Surjective (f.domRestrict (P.subgroupOf H)) := by
    intro l
    have hPL' : (P.subgroupOf M).map π = L := by simpa only [π] using hPL
    have hl : (l : ↥M ⧸ pPrimeCore 2 ↥M) ∈ (P.subgroupOf M).map π := by
      rw [hPL']
      exact l.2
    obtain ⟨pM, hpM, hpπ⟩ := Subgroup.mem_map.mp hl
    have hpG : (pM : G) ∈ P := Subgroup.mem_subgroupOf.mp hpM
    have hpH : (pM : G) ∈ H := by
      rw [hH]
      exact mem_inf.mpr ⟨hPK hpG, hPt hpG⟩
    refine ⟨⟨⟨pM, hpH⟩, Subgroup.mem_subgroupOf.mpr hpG⟩, ?_⟩
    apply Subtype.ext
    exact hpπ
  have hlayer : CFSG.pLayer ↥H 2 = P.subgroupOf H :=
    UnbalancedGS.OrbitFixedComponent.pLayer_eq_of_cover f hker (P.subgroupOf H) hPpcH hcover
  have hfix : UnbalancedGS.gsFixedLayer K t = P := by
    rw [UnbalancedGS.gsFixedLayer, ← hH, hlayer]
    exact Subgroup.map_subgroupOf_eq_of_le hPH
  have hKmem := solomon_member_of_same_field_host hfield hmax hK htQ hfix htype
  have hKstar : K ∈ FooteLit.solomonKStar G := hKmem.2.2
  have hPrank : 3 ≤ CFSG.pRank 2 ↥P :=
    (mem_solomonKStar_of_field_mirror hbase0 ht ⟨hPt, hPp⟩ hmexp hPLie hmax).2
  have hrank : 3 ≤ CFSG.pRank 2 ↥K := hPrank.trans (Sol78.pRank_le_of_le hPK)
  have hxne : ∃ x : ↥M ⧸ pPrimeCore 2 ↥M, conjugate L x ≠ L := by
    by_contra h
    push Not at h
    exact hLn (Subgroup.normal_iff_map_conj_eq.mpr fun g => by
      have h1 : conjugate L g⁻¹ = L := h g⁻¹
      simpa [CFSG.conjugate] using h1)
  obtain ⟨x, hxne⟩ := hxne
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) x
  let K' : Subgroup G := conjugate K (m : G)
  have hK' : FooteLit.IsTwoComponentIn K' M := by
    simpa [K', CFSG.conjugate] using
      (Sol76.isTwoComponentIn_map_conj hK (Subgroup.le_normalizer (inv_mem m.2)))
  have hK'sub : K'.subgroupOf M = conjugate (K.subgroupOf M) m := by
    simpa [K', CFSG.conjugate] using
      (CFSG.GroupTheory.conjugate_subgroupOf (B := K) (U := M) m).symm
  have himg : (K'.subgroupOf M).map π = conjugate L x := by
    calc (K'.subgroupOf M).map π = (conjugate (K.subgroupOf M) m).map π := by
          rw [hK'sub]
      _ = conjugate ((K.subgroupOf M).map π) (π m) :=
        UnbalancedLayer.map_conjugate π (K.subgroupOf M) m
      _ = conjugate L x := by rw [hKmap, hm]
  have hne : K' ≠ K := by
    intro hEq
    have h1 : (K'.subgroupOf M).map π = L := by rw [hEq, hKmap]
    rw [himg] at h1
    exact hxne h1
  have hc1 : ⁅K, K'⁆ ≤ FooteLit.oddCoreIn K :=
    TBLit.commutator_le_oddCoreIn_of_ne hK.1 hK'.1 hK.2 hK'.2 (Ne.symm hne)
  have hc2 : ⁅K, K'⁆ ≤ FooteLit.oddCoreIn K' := by
    rw [Subgroup.commutator_comm]
    exact TBLit.commutator_le_oddCoreIn_of_ne hK'.1 hK.1 hK'.2 hK.2 hne
  have hc : ⁅K, conjugate K (m : G)⁆ ≤
      FooteLit.oddCoreIn K ⊓ FooteLit.oddCoreIn (conjugate K (m : G)) :=
    le_inf hc1 hc2
  have hconj := Sol76.sup_conjugate_le_solomonKStarOf_top
    (fun N hN => absurd hN (h13 G hsimple hnab hKP N)) hK hKstar hrank (m : G) hc
  obtain ⟨hsF, hnF, -⟩ := GrS5.fstar_facts hbase0
  rw [Sol76.solomonKStarOf_top_eq_bot_of_fStar hsF hnF] at hconj
  have hKne : K ≠ ⊥ := by
    intro h
    exact Sol78.ne_bot_of_isPComponent' hK.2 (by rw [h]; exact bot_subgroupOf M)
  exact hKne (le_bot_iff.mp (le_sup_left.trans hconj))

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
