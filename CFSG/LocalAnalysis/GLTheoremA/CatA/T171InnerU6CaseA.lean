module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs
import CFSG.GroupTheory.SuzukiTwoGroupsKernel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.TwoReflections
import CFSG.GroupTheory.SteinbergCBFTSCN
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.GroupTheory
open scoped commutatorElement

theorem stepCaseACard_holds : StepCaseACard := by
  intro hE9 hE27 Ω _ _ B x L hsetup D K hstd hcat hsimple hKcard hBle E hEea hECK hENL
    hECx hEcard T hTNL hTCx hT2 hBT hTBne
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg : S171.Cfg Ω 3 B x L := hsetup.cfg
  obtain ⟨hDleB, hDab, hDcard, hxD, hKdef, hKcomp, hDB⟩ := hstd
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hK_le_inf : K ≤ L ⊓ Subgroup.centralizer (D : Set Ω) := hKcomp.1
  have hK_le_L : K ≤ L := hK_le_inf.trans inf_le_left
  have hK_le_CD : K ≤ Subgroup.centralizer (D : Set Ω) := hK_le_inf.trans inf_le_right
  have hK_le_Cx : K ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hK_le_CD hk) x hxD).symm
  have hKqC : CFSG.IsQuasisimple ↥K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1).mpr hKq
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ :=
    CFSG.ClassicalInvolution.Balance.LocalBalance.exists_noncomm_of_isQuasisimple hKqC
  have hnonab : ∃ u v : ↥K, u * v ≠ v * u :=
    ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩, fun h =>
      hab₀ (congrArg (fun t : ↥K => (t : Ω)) h)⟩
  have hcenterK : Subgroup.center ↥K = ⊥ :=
    CFSG.Quasithin.SteinbergCF.center_eq_bot_of_simple hnonab
  have hx_cL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).mpr (Subgroup.mem_zpowers x)
  obtain ⟨z, hz2, hz1, A9, hA9ea, hA9card, hA9z⟩ := hE9 (Y := ↥K) hcat
  let A9' : Subgroup Ω := A9.map K.subtype
  have hA9'ea : IsElemAbelian 3 A9' := hA9ea.map K.subtype
  have hA9'card : Nat.card A9' = 9 := by
    dsimp [A9']
    rw [Subgroup.card_map_of_injective K.subtype_injective, hA9card]
  have hA9'_le_K : A9' ≤ K := by
    dsimp [A9']
    exact Subgroup.map_subtype_le A9
  have hA9'_le_L : A9' ≤ L := hA9'_le_K.trans hK_le_L
  have hA9'_le_Cx : A9' ≤ Subgroup.centralizer ({x} : Set Ω) :=
    hA9'_le_K.trans hK_le_Cx
  have hz2Ω : (z : Ω) ^ 2 = 1 := by
    simpa using congrArg (fun t : ↥K => (t : Ω)) hz2
  have hz1Ω : (z : Ω) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext h)
  have hEcentz : E ≤ Subgroup.centralizer ({(z : Ω)} : Set Ω) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hECK he) (z : Ω) z.2).symm
  have hA9'centz : A9' ≤ Subgroup.centralizer ({(z : Ω)} : Set Ω) := by
    intro y hy
    obtain ⟨ak, hak, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun t : ↥K => (t : Ω)) (hA9z ak hak)
  have hF9cent : E ⊔ A9' ≤ Subgroup.centralizer ({(z : Ω)} : Set Ω) :=
    sup_le hEcentz hA9'centz
  have hcommEA9 : ∀ a ∈ E, ∀ b ∈ A9', a * b = b * a := by
    intro a ha b hb
    obtain ⟨bk, hbk, rfl⟩ := hb
    exact (Subgroup.mem_centralizer_iff.mp (hECK ha) (bk : Ω) bk.2).symm
  have hF9ea : IsElemAbelian 3 (E ⊔ A9') := hEea.sup_of_commute hA9'ea hcommEA9
  have hF9inf : E ⊓ A9' = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    have hhE : h ∈ E := hh.1
    have hhA : h ∈ A9' := hh.2
    have hhK : h ∈ K := hA9'_le_K hhA
    have hcenter : (⟨h, hhK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hECK hhE) (y : Ω) y.2)
    have hh1 : (⟨h, hhK⟩ : ↥K) = 1 := by
      simpa [hcenterK] using hcenter
    have hh_eq : h = 1 := congrArg (fun t : ↥K => (t : Ω)) hh1
    simpa using hh_eq
  have hF9card : Nat.card ↥(E ⊔ A9') = Nat.card E * 9 := by
    have h := (card_sup_mul_card_inf_of_commute E A9' hcommEA9).1
    rw [hF9inf, Subgroup.card_bot, mul_one, hA9'card] at h
    exact h
  have hF9card_ge : 243 ≤ Nat.card ↥(E ⊔ A9') := by
    rw [hF9card]
    nlinarith
  have hzP : IsPGroup 2 (Subgroup.zpowers (z : Ω)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz2Ω
  have hzNe : Subgroup.zpowers (z : Ω) ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1Ω
  have hF9normz : E ⊔ A9' ≤
      Subgroup.normalizer (Subgroup.zpowers (z : Ω) : Set Ω) := by
    intro f hf
    apply CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq
    have hfz : f * (z : Ω) = (z : Ω) * f :=
      Subgroup.mem_centralizer_singleton_iff.mp (hF9cent hf)
    calc f * (z : Ω) * f⁻¹ = (z : Ω) * f * f⁻¹ := by rw [hfz]
      _ = (z : Ω) := by group
  have hBge : 243 ≤ Nat.card B :=
    hF9card_ge.trans (hsetup.maxG (E ⊔ A9') (Subgroup.zpowers (z : Ω))
      hF9ea hzP hzNe hF9normz)
  have hcardB : Nat.card B = 243 := le_antisymm hBle hBge
  refine ⟨hcardB, ?_⟩
  intro hle
  let Y0 : Subgroup Ω :=
    Subgroup.centralizer (L : Set Ω) ⊓ Subgroup.centralizer ({x} : Set Ω)
  have hTB_le_T : ⁅T, B⁆ ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.mp hBT
  have hTB_le_Y0 : ⁅T, B⁆ ≤ Y0 := le_inf hle (hTB_le_T.trans hTCx)
  have hTB2 : IsPGroup 2 ↥⁅T, B⁆ := hT2.to_le hTB_le_T
  have h2dvdTB : 2 ∣ Nat.card ↥⁅T, B⁆ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTB2
    have hnpos : 0 < n := by
      by_contra h
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
      rw [hn0, pow_zero] at hn
      have hlt : 1 < Nat.card ↥⁅T, B⁆ :=
        (Subgroup.one_lt_card_iff_ne_bot ⁅T, B⁆).mpr hTBne
      omega
    rw [hn]
    exact dvd_pow_self 2 hnpos.ne'
  have hcyc : ∀ P : Sylow 3 ↥Y0, IsCyclic P := by
    intro P
    let Pmap : Subgroup Ω := (P : Subgroup ↥Y0).map Y0.subtype
    have hPmap_le : Pmap ≤ Subgroup.centralizer (L : Set Ω) := by
      intro y hy
      obtain ⟨y0, hy0, rfl⟩ := hy
      exact y0.2.1
    have hPmap_p : IsPGroup 3 Pmap := P.isPGroup'.map Y0.subtype
    have hPmap_cyc : IsCyclic Pmap := hcfg.cyc Pmap hPmap_le hPmap_p
    let f : ↥(P : Subgroup ↥Y0) →* ↥Pmap :=
      { toFun := fun y => ⟨Y0.subtype y, ⟨y, y.2, rfl⟩⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun a b => Subtype.ext rfl }
    exact isCyclic_of_injective f fun a b hab =>
      Subtype.ext (Y0.subtype_injective (congrArg (fun t : ↥Pmap => (t : Ω)) hab))
  have hcen : ∀ y : ↥Y0, orderOf y = 3 → y ∈ Subgroup.center ↥Y0 := by
    intro y hyord
    have hyΩord : orderOf (y : Ω) = 3 := by
      rwa [Subgroup.orderOf_coe]
    have hy3 : (y : Ω) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hyΩord])
    have hxY0 : x ∈ Y0 :=
      ⟨hx_cL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let xY0 : ↥Y0 := ⟨x, hxY0⟩
    have hxY0ord : orderOf xY0 = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
    let H : Subgroup Ω := Subgroup.zpowers x ⊔ Subgroup.zpowers (y : Ω)
    have hxH : x ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have hyH : (y : Ω) ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers (y : Ω))
    have hH_le_C : H ≤ Subgroup.centralizer (L : Set Ω) :=
      sup_le (Subgroup.zpowers_le.mpr hx_cL) (Subgroup.zpowers_le.mpr y.2.1)
    have hH3 : IsPGroup 3 H := by
      refine IsPGroup.to_sup_of_normal_left' ?_ ?_ ?_
      · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_dvd_iff_pow_eq_one.mpr (hcfg.elem.2 x hcfg.mem)
      · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_dvd_iff_pow_eq_one.mpr hy3
      · apply Subgroup.zpowers_le.mpr
        apply CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq
        have hyx : (y : Ω) * x = x * (y : Ω) :=
          Subgroup.mem_centralizer_singleton_iff.mp y.2.2
        calc (y : Ω) * x * (y : Ω)⁻¹ = x * (y : Ω) * (y : Ω)⁻¹ := by rw [hyx]
          _ = x := by group
    have hHcyc : IsCyclic H := hcfg.cyc H hH_le_C hH3
    let xH : H := ⟨x, hxH⟩
    let yH : H := ⟨(y : Ω), hyH⟩
    have hxHord : orderOf xH = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
    have hyHord : orderOf yH = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hyΩord
    haveI : IsCyclic H := hHcyc
    have hyH_mem : yH ∈ Subgroup.zpowers xH :=
      CFSG.GroupTheory.SuzukiTwoGroup.mem_zpowers_of_orderOf_eq (by rw [hyHord, hxHord])
    have hyΩ_mem : (y : Ω) ∈ Subgroup.zpowers x := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyH_mem
      exact Subgroup.mem_zpowers_iff.mpr
        ⟨k, by simpa using congrArg (fun t : H => (t : Ω)) hk⟩
    have hy_memY0 : y ∈ Subgroup.zpowers xY0 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyΩ_mem
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_memY0
    have hzx : z * xY0 = xY0 * z :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp z.2.2)
    calc z * y = z * xY0 ^ k := by rw [hk]
      _ = xY0 ^ k * z := (show Commute z xY0 from hzx).zpow_right k |>.eq
      _ = y * z := by rw [hk]
  have hcomp := CFSG.LocalAnalysis.RankThreeTheoremC.hasNormalPComplement_of_cyclic_sylow_central
    (Y := ↥Y0) (p := 3) hcyc hcen
  obtain ⟨N0, hN0⟩ :=
    (CFSG.GroupTheory.hasNormalPComplement_iff_exists (G := ↥Y0) 3).mp hcomp
  haveI : N0.Normal := hN0.1
  obtain ⟨k0, hk0⟩ := hN0.2.2
  have hN0quot : IsPGroup 3 (↥Y0 ⧸ N0) :=
    IsPGroup.of_card (n := k0) (by rw [← Subgroup.index_eq_card]; exact hk0)
  let A : Subgroup ↥Y0 := ⁅T, B⁆.subgroupOf Y0
  have hA2 : IsPGroup 2 A := hTB2.comap_subtype
  have hAimg2 : IsPGroup 2 (A.map (QuotientGroup.mk' N0)) := hA2.map _
  have hAimg3 : IsPGroup 3 (A.map (QuotientGroup.mk' N0)) :=
    hN0quot.to_subgroup _
  have hAimg_bot : A.map (QuotientGroup.mk' N0) = ⊥ :=
    disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hAimg2 hAimg3)
  have hA_le_N0 : A ≤ N0 := by
    have h := (Subgroup.map_eq_bot_iff (H := A) (f := QuotientGroup.mk' N0)).mp hAimg_bot
    simpa [QuotientGroup.ker_mk'] using h
  let NΩ : Subgroup Ω := N0.map Y0.subtype
  have hTB_le_NΩ : ⁅T, B⁆ ≤ NΩ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTB_le_Y0]
    exact Subgroup.map_mono hA_le_N0
  have h2dvdNΩ : 2 ∣ Nat.card NΩ :=
    h2dvdTB.trans (Subgroup.card_dvd_of_le hTB_le_NΩ)
  obtain ⟨A27, hA27ea, hA27card⟩ := hE27 (Y := ↥K) hcat
  let A27' : Subgroup Ω := A27.map K.subtype
  have hA27'ea : IsElemAbelian 3 A27' := hA27ea.map K.subtype
  have hA27'card : Nat.card A27' = 27 := by
    dsimp [A27']
    rw [Subgroup.card_map_of_injective K.subtype_injective, hA27card]
  have hA27'_le_K : A27' ≤ K := by
    dsimp [A27']
    exact Subgroup.map_subtype_le A27
  have hA27'_le_L : A27' ≤ L := hA27'_le_K.trans hK_le_L
  have hA27'_le_Cx : A27' ≤ Subgroup.centralizer ({x} : Set Ω) :=
    hA27'_le_K.trans hK_le_Cx
  have hcommEA27 : ∀ a ∈ E, ∀ b ∈ A27', a * b = b * a := by
    intro a ha b hb
    obtain ⟨bk, hbk, rfl⟩ := hb
    exact (Subgroup.mem_centralizer_iff.mp (hECK ha) (bk : Ω) bk.2).symm
  have hF27ea : IsElemAbelian 3 (E ⊔ A27') := hEea.sup_of_commute hA27'ea hcommEA27
  have hF27inf : E ⊓ A27' = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    have hhE : h ∈ E := hh.1
    have hhA : h ∈ A27' := hh.2
    have hhK : h ∈ K := hA27'_le_K hhA
    have hcenter : (⟨h, hhK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hECK hhE) (y : Ω) y.2)
    have hh1 : (⟨h, hhK⟩ : ↥K) = 1 := by
      simpa [hcenterK] using hcenter
    have hh_eq : h = 1 := congrArg (fun t : ↥K => (t : Ω)) hh1
    simpa using hh_eq
  have hF27card : Nat.card ↥(E ⊔ A27') = Nat.card E * 27 := by
    have h := (card_sup_mul_card_inf_of_commute E A27' hcommEA27).1
    rw [hF27inf, Subgroup.card_bot, mul_one, hA27'card] at h
    exact h
  have hF27card_ge : 729 ≤ Nat.card ↥(E ⊔ A27') := by
    rw [hF27card]
    nlinarith
  have hF27_3 : IsPGroup 3 ↥(E ⊔ A27') := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro f
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hF27ea.2 f f.2
  have hF27_NL : E ⊔ A27' ≤ Subgroup.normalizer (L : Set Ω) :=
    sup_le hENL (hA27'_le_L.trans Subgroup.le_normalizer)
  have hF27_Cx : E ⊔ A27' ≤ Subgroup.centralizer ({x} : Set Ω) :=
    sup_le hECx hA27'_le_Cx
  have hF27_NCL : E ⊔ A27' ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Ω)) :=
    hF27_NL.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer L)
  have hF27_NCx : E ⊔ A27' ≤
      Subgroup.normalizer (Subgroup.centralizer ({x} : Set Ω)) := by
    have hNzp : E ⊔ A27' ≤
        Subgroup.normalizer (Subgroup.zpowers x : Set Ω) := by
      intro f hf
      apply CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq
      have hfx : f * x = x * f :=
        Subgroup.mem_centralizer_singleton_iff.mp (hF27_Cx hf)
      calc f * x * f⁻¹ = x * f * f⁻¹ := by rw [hfx]
        _ = x := by group
    have h := CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer
      (A := Subgroup.zpowers x) hNzp
    rwa [CFSG.centralizer_zpowers_eq_centralizer_singleton x] at h
  have hF27_NY0 : E ⊔ A27' ≤ Subgroup.normalizer (Y0 : Set Ω) := by
    intro f hf
    exact CFSG.ABGLocalTools.mem_normalizer_inf (hF27_NCL hf) (hF27_NCx hf)
  have hN0char : N0.Characteristic :=
    CFSG.GroupTheory.FrobeniusNormalComplement.IsNormalPComplement.characteristic hN0
  haveI : N0.Characteristic := hN0char
  have hF27_NΩ : E ⊔ A27' ≤ Subgroup.normalizer (NΩ : Set Ω) := by
    intro f hf
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := Y0) (C := N0) (hF27_NY0 hf)
  let : Subgroup.Normalizes (E ⊔ A27') NΩ := ⟨hF27_NΩ⟩
  letI : MulDistribMulAction ↥(E ⊔ A27') NΩ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (E ⊔ A27') NΩ hF27_NΩ
  haveI : Fact (IsPGroup 3 ↥(E ⊔ A27')) := ⟨hF27_3⟩
  have hcopNΩ : Nat.Coprime 3 (Nat.card NΩ) := by
    have hcardNΩ : Nat.card NΩ = Nat.card N0 := by
      dsimp [NΩ]
      exact Subgroup.card_map_of_injective Y0.subtype_injective
    rw [hcardNΩ]
    exact hN0.2.1.symm
  obtain ⟨P, hPinv⟩ :=
    CFSG.exists_invariant_sylow_of_pgroup_operator_coprime
      (G := NΩ) (A := ↥(E ⊔ A27')) (r := 3) (p := 2) hcopNΩ
  let U : Subgroup Ω := (P : Subgroup NΩ).map NΩ.subtype
  have hU2 : IsPGroup 2 U := P.isPGroup'.map NΩ.subtype
  have hPne : (P : Subgroup NΩ) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h2dvdNΩ
  have hUne : U ≠ ⊥ := by
    intro hUbot
    apply hPne
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup NΩ)
      NΩ.subtype_injective).mp hUbot
  have hF27_NU : E ⊔ A27' ≤ Subgroup.normalizer (U : Set Ω) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(⟨f, hf⟩ : ↥(E ⊔ A27')) • y, (hPinv.invariant ⟨f, hf⟩ y).mp hy, ?_⟩
      simpa using Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        (↥(E ⊔ A27')) NΩ (⟨f, hf⟩ : ↥(E ⊔ A27')) y
    · rintro ⟨y, hy, hyu⟩
      refine ⟨(⟨f, hf⟩ : ↥(E ⊔ A27'))⁻¹ • y, (hPinv.invariant ⟨f, hf⟩⁻¹ y).mp hy, ?_⟩
      calc
        (((⟨f, hf⟩ : ↥(E ⊔ A27'))⁻¹ • y : NΩ) : Ω)
            = f⁻¹ * (y : Ω) * (f⁻¹)⁻¹ := by
              simpa using Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
                (↥(E ⊔ A27')) NΩ (⟨f, hf⟩ : ↥(E ⊔ A27'))⁻¹ y
        _ = f⁻¹ * (f * u * f⁻¹) * f := by
              change f⁻¹ * (NΩ.subtype y) * (f⁻¹)⁻¹ = f⁻¹ * (f * u * f⁻¹) * f
              rw [hyu]
              group
        _ = u := by group
  have hF27_le_B : Nat.card ↥(E ⊔ A27') ≤ Nat.card B :=
    hsetup.maxG (E ⊔ A27') U hF27ea hU2 hUne hF27_NU
  have : 729 ≤ Nat.card B := hF27card_ge.trans hF27_le_B
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
