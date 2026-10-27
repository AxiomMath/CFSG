module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorPump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldGluing
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACentral
public import CFSG.Holt.General.DLineTools
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Ord

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem false_of_field_host_spare
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h13 : Sol76T13.SolomonThm13Simple) (hmult : Quasithin.SchurMult2L3)
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hmax : FooteLit.GSMirrorMaximal P)
    (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W)
    (hM : normalizer (W : Set G) = M) (htM : t ∈ M) {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hL : IsComponent L) (hZ : center ↥L = ⊥) {m n : ℕ} (hm : 4 ≤ m)
    (hPm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m) (hmn : m ≤ n)
    (hLn : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 n)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
      L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom)
    (hcase : (L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom = L ∧
        n = 2 * m) ∨
      L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hspare : ∃ g : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj g).toMonoidHom ≠ L ∧
      L.map (MulAut.conj g).toMonoidHom ≠
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨hbase, ht2, hPC, hPp, hPn, m0, hm0, hme0, hPL0⟩ := hset'
  have hCM : centralizer ({t} : Set G) ≤ M := by
    rw [← hM]
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mp hPn).trans hPW
  have hPM : P ≤ M := hPC.trans hCM
  set X := ↥M ⧸ pPrimeCore 2 ↥M with hXdef
  set π : ↥M →* X := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπdef
  set tM : ↥M := ⟨t, htM⟩ with htMdef
  set tbar : X := π tM with htbardef
  have htM2 : tM * tM = 1 := by
    rw [htMdef]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      have h := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at h)
  have htbar2 : tbar * tbar = 1 := by
    rw [htbardef, ← map_mul, htM2, map_one]
  have htbari : tbar⁻¹ = tbar := inv_eq_of_mul_eq_one_right htbar2
  obtain ⟨g, hgL, hgLt⟩ := hspare
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLgdef
  set Lt := L.map (MulAut.conj tbar).toMonoidHom with hLtdef
  set Lgt := Lg.map (MulAut.conj tbar).toMonoidHom with hLgtdef
  have hLt_comp : IsComponent Lt :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tbar) hL
  have hLg_comp : IsComponent Lg :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  have hLgt_comp : IsComponent Lgt :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tbar) hLg_comp
  have hLg_ne_L : Lg ≠ L := hgL
  have hLg_ne_Lt : Lg ≠ Lt := hgLt
  have hLgt_map : Lgt.map (MulAut.conj tbar).toMonoidHom = Lg := by
    rw [hLgtdef]
    have h := CFSG.GroupTheory.map_conj_map_conj_inv tbar Lg
    rwa [htbari] at h
  have hLt_map : Lt.map (MulAut.conj tbar).toMonoidHom = L := by
    rw [hLtdef]
    have h := CFSG.GroupTheory.map_conj_map_conj_inv tbar L
    rwa [htbari] at h
  have hLgt_ne_L : Lgt ≠ L := by
    intro h
    apply hLg_ne_Lt
    have h1 : Lgt.map (MulAut.conj tbar).toMonoidHom =
        L.map (MulAut.conj tbar).toMonoidHom := by rw [h]
    rwa [hLgt_map] at h1
  have hLgt_ne_Lt : Lgt ≠ Lt := by
    intro h
    apply hLg_ne_L
    have h1 : Lgt.map (MulAut.conj tbar).toMonoidHom =
        Lt.map (MulAut.conj tbar).toMonoidHom := by rw [h]
    rwa [hLgt_map, hLt_map] at h1
  have hcommLgL : ⁅Lg, L⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hLg_comp hL with h | h
    · exact absurd h hLg_ne_L
    · exact h
  have hcommLgLt : ⁅Lg, Lt⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hLg_comp hLt_comp with h | h
    · exact absurd h hLg_ne_Lt
    · exact h
  have hcommLgtL : ⁅Lgt, L⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hLgt_comp hL with h | h
    · exact absurd h hLgt_ne_L
    · exact h
  have hcommLgtLt : ⁅Lgt, Lt⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hLgt_comp hLt_comp with h | h
    · exact absurd h hLgt_ne_Lt
    · exact h
  set R := Lg ⊔ Lgt with hRdef
  have hRcL : R ≤ centralizer (L : Set X) :=
    sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLgL)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLgtL)
  have hRcLt : R ≤ centralizer (Lt : Set X) :=
    sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLgLt)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLgtLt)
  have hRcent : R ≤ centralizer ((L ⊔ Lt : Subgroup X) : Set X) :=
    CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hRcL hRcLt
  have hRconj : R.map (MulAut.conj tbar).toMonoidHom = R := by
    rw [hRdef, Subgroup.map_sup]
    rw [show Lg.map (MulAut.conj tbar).toMonoidHom = Lgt from rfl, hLgt_map]
    exact sup_comm _ _
  have htbarN : tbar ∈ normalizer (R : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hRconj
  have hLmodel : Blueprint.LieModel ↥L .PSL 3 2 n :=
    Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hLn
  have hn1 : 1 ≤ n := by omega
  have hL2 : 2 ∣ Nat.card ↥L := by
    have hdvd : 2 ^ (3 * n) ∣ Nat.card ↥L :=
      pow_dvd_card_of_lieModel_psl_three hn1 hLmodel
    exact (show 2 ∣ 2 ^ (3 * n) from by
      simpa using Nat.pow_dvd_pow 2 (show 1 ≤ 3 * n by omega)).trans hdvd
  have hLg2 : 2 ∣ Nat.card ↥Lg := by
    rw [show Nat.card ↥Lg = Nat.card ↥L from
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hL2
  have hR2 : 2 ∣ Nat.card ↥R :=
    hLg2.trans (Subgroup.card_dvd_of_le (le_sup_left : Lg ≤ R))
  set H : Subgroup X := R ⊔ zpowers tbar with hHdef
  have hRH : R ≤ H := le_sup_left
  have htbarH : tbar ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers tbar)
  set tb : H := ⟨tbar, htbarH⟩ with htbdef
  have htb_ord_dvd : orderOf tb ∣ 2 := by
    have h : orderOf tbar ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact htbar2)
    rwa [htbdef, Subgroup.orderOf_mk]
  have hpgroup : IsPGroup 2 (Subgroup.zpowers tb) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_two).mp htb_ord_dvd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨Q, hQle⟩ := hpgroup.exists_le_sylow
  have hRHnorm : (R.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRH]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le]
    exact htbarN
  have hRH_even : 2 ∣ Nat.card ↥(R.subgroupOf H) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  have hRN : (Q : Subgroup H) ≤ normalizer (R.subgroupOf H : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hRHnorm]
    exact le_top
  have hOddIdx : ¬ 2 ∣ ((R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf
      (R.subgroupOf H)).index := by
    have hrel : (R.subgroupOf H ⊓ (Q : Subgroup H)).relIndex (R.subgroupOf H) =
        ((R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (R.subgroupOf H)).index := rfl
    rw [← hrel]
    have hsecond :=
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hRN).1
    rw [inf_comm] at hsecond
    rw [← hsecond]
    have hoddQ : ¬ 2 ∣ (Q : Subgroup H).relIndex (⊤ : Subgroup H) := by
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index' Subgroup.index_ne_zero_of_finite
    have hdiv : (Q : Subgroup H).relIndex ((Q : Subgroup H) ⊔ R.subgroupOf H) ∣
        (Q : Subgroup H).relIndex (⊤ : Subgroup H) := by
      rw [← Subgroup.relIndex_mul_relIndex (H := (Q : Subgroup H))
        (K := (Q : Subgroup H) ⊔ R.subgroupOf H) (L := ⊤) le_sup_left le_top]
      exact dvd_mul_right _ _
    exact fun h => hoddQ (h.trans hdiv)
  have hInf_even : 2 ∣ Nat.card ↥(R.subgroupOf H ⊓ (Q : Subgroup H)) := by
    have hcard : Nat.card ↥(R.subgroupOf H) =
        Nat.card ↥((R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (R.subgroupOf H)) *
          ((R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (R.subgroupOf H)).index :=
      (Subgroup.card_mul_index _).symm
    rw [hcard] at hRH_even
    rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp hRH_even with h | h
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    · exact absurd h hOddIdx
  have hNne : R.subgroupOf H ⊓ (Q : Subgroup H) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hInf_even
    exact absurd hInf_even (by simp)
  have hsubeq : (R.subgroupOf H).subgroupOf (Q : Subgroup H) =
      (R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (Q : Subgroup H) := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hNn : ((R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf
      (Q : Subgroup H)).Normal := by
    rw [← hsubeq]
    exact hRHnorm.subgroupOf (Q : Subgroup H)
  have hNqne : (R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (Q : Subgroup H) ≠ ⊥ := by
    intro hbot
    apply hNne
    have h1 : ((R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf
        (Q : Subgroup H)).map (Q : Subgroup H).subtype = ⊥ := by
      rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
  let Nq : Subgroup ↥(Q : Subgroup H) :=
    (R.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (Q : Subgroup H)
  have hNqnormal : Nq.Normal := hNn
  have hNqne : Nq ≠ ⊥ := hNqne
  let zsub : Subgroup ↥(Q : Subgroup H) := Nq ⊓ Subgroup.center ↥(Q : Subgroup H)
  have hzsub2 : IsPGroup 2 ↥zsub := Q.isPGroup'.to_subgroup zsub
  have hzsubne : zsub ≠ ⊥ := by
    letI : Nq.Normal := hNqnormal
    exact CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      Q.isPGroup' Nq hNqne
  letI : Nontrivial ↥zsub := (Subgroup.nontrivial_iff_ne_bot zsub).mpr hzsubne
  obtain ⟨z, -, hzord⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.exists_mem_center_orderOf_eq_two hzsub2
  have hzN : z.1 ∈ Nq := (Subgroup.mem_inf.mp z.2).1
  have hzC : z.1 ∈ Subgroup.center ↥(Q : Subgroup H) := (Subgroup.mem_inf.mp z.2).2
  have hzR : (((z.1 : ↥(Q : Subgroup H)) : H) : X) ∈ R := by
    have h1 : ((z.1 : ↥(Q : Subgroup H)) : H) ∈ R.subgroupOf H :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hzN)).1
    exact Subgroup.mem_subgroupOf.mp h1
  set zX : X := (((z.1 : ↥(Q : Subgroup H)) : H) : X) with hzXdef
  have hzXord : orderOf zX = 2 := by
    rw [hzXdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hzord
  have hz_comm : tbar * zX = zX * tbar := by
    have hcomm : (⟨tb, hQle (Subgroup.mem_zpowers tb)⟩ : ↥(Q : Subgroup H)) * z.1 =
        z.1 * (⟨tb, hQle (Subgroup.mem_zpowers tb)⟩ : ↥(Q : Subgroup H)) :=
      Subgroup.mem_center_iff.mp hzC (⟨tb, hQle (Subgroup.mem_zpowers tb)⟩ :
        ↥(Q : Subgroup H))
    have hcomm' := congrArg (fun y : ↥(Q : Subgroup H) => (((y : H) : X))) hcomm
    simpa [zX, tb, htbdef, tbar] using hcomm'
  have hkerOdd : Odd (Nat.card π.ker) := by
    have hker : π.ker = pPrimeCore 2 ↥M := QuotientGroup.ker_mk' _
    rw [hker]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  obtain ⟨vM, hvMord, htvM, hπvM⟩ :=
    exists_involution_lift_centralizing π (QuotientGroup.mk'_surjective _) hkerOdd
      (by rw [htMdef, Subgroup.orderOf_mk]; exact ht2) hzXord (hcomm := hz_comm)
  have hvG : orderOf (vM : G) = 2 := by
    rw [Subgroup.orderOf_coe, hvMord]
  have htvG : t * (vM : G) = (vM : G) * t := by
    have h := congrArg (fun y : ↥M => (y : G)) htvM
    simpa [tM] using h
  have hv_cent : ∀ y ∈ L ⊔ Lt, π vM * y = y * π vM := by
    intro y hy
    rw [hπvM]
    exact (Subgroup.mem_centralizer_iff.mp (hRcent hzR) y hy).symm
  let OM : Subgroup G := (pPrimeCore 2 ↥M).map M.subtype
  have hOMsub : (OM.subgroupOf M).Normal := by
    rw [show OM.subgroupOf M = pPrimeCore 2 ↥M by
      ext x
      simp [OM, Subgroup.mem_subgroupOf, Subgroup.mem_map]]
    exact pPrimeCore_normal
  have hOMleM : OM ≤ M := Subgroup.map_subtype_le _
  have hMnormOM : M ≤ normalizer (OM : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOMleM).mp hOMsub
  have hPnormOM : P ≤ normalizer (OM : Set G) := hPM.trans hMnormOM
  let K : Subgroup G := OM ⊓ P
  have hPK : P ≤ normalizer (K : Set G) :=
    (le_inf hPnormOM Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKN : (K.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hPK
  have hcopK : Nat.Coprime 2 (Nat.card K) := by
    have hKdvd : Nat.card K ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective (K := pPrimeCore 2 ↥M) (f := M.subtype)
        M.subtype_injective]
      exact Subgroup.card_dvd_of_le (inf_le_left : K ≤ OM)
    exact CFSG.pPrimeCore_coprime_card.coprime_dvd_right hKdvd
  have hK_le_odd : K ≤ oddIn P := by
    letI : (K.subgroupOf P).Normal := hKN
    have h := CFSG.subgroupOf_le_pPrimeCore_map (p := 2) (K := K) (H := P) inf_le_right hcopK
    simpa [oddIn] using h
  have hvC : (vM : G) ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htvG.symm
  have hvN : (vM : G) ∈ normalizer (P : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mp hPn) hvC
  have hvP : ∀ p ∈ P, p⁻¹ * (vM : G)⁻¹ * p * (vM : G) ∈ oddIn P := by
    intro p hp
    have hpM : p ∈ M := hPM hp
    have hkP : p⁻¹ * (vM : G)⁻¹ * p * (vM : G) ∈ P := by
      have hvNinv : (vM : G)⁻¹ ∈ normalizer (P : Set G) := inv_mem hvN
      have hvpv : (vM : G)⁻¹ * p * (vM : G) ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp hvNinv p).mp hp
      have h1 : p⁻¹ ∈ P := P.inv_mem hp
      simpa [mul_assoc] using P.mul_mem h1 hvpv
    have hkM : p⁻¹ * (vM : G)⁻¹ * p * (vM : G) ∈ M := by
      have h1 : p⁻¹ * (vM : G)⁻¹ ∈ M := M.mul_mem (M.inv_mem hpM) (M.inv_mem vM.2)
      have h2 : p * (vM : G) ∈ M := M.mul_mem hpM vM.2
      simpa [mul_assoc] using M.mul_mem h1 h2
    set pM : ↥M := ⟨p, hpM⟩ with hpMdef
    have hπp : π pM ∈ L ⊔ Lt :=
      hPL (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hp))
    have hkey : π (⟨p⁻¹ * (vM : G)⁻¹ * p * (vM : G), hkM⟩ : ↥M) = 1 := by
      have h1 : (⟨p⁻¹ * (vM : G)⁻¹ * p * (vM : G), hkM⟩ : ↥M) =
          pM⁻¹ * vM⁻¹ * pM * vM := by
        apply Subtype.ext
        simp [pM]
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hcomm := hv_cent (π pM) hπp
      rw [hπvM] at hcomm
      calc (π pM)⁻¹ * (π vM)⁻¹ * π pM * π vM
          = ((π vM) * π pM)⁻¹ * (π pM * π vM) := by group
        _ = 1 := by rw [hπvM, hcomm, inv_mul_cancel]
    have hkcore : (⟨p⁻¹ * (vM : G)⁻¹ * p * (vM : G), hkM⟩ : ↥M) ∈
        pPrimeCore 2 ↥M := by
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)]
      exact MonoidHom.mem_ker.mpr hkey
    have hkOM : p⁻¹ * (vM : G)⁻¹ * p * (vM : G) ∈ OM :=
      Subgroup.mem_map_of_mem M.subtype hkcore
    exact hK_le_odd (Subgroup.mem_inf.mpr ⟨hkOM, hkP⟩)
  have hvK : (vM : G) ∈ coreActionKernel P := mem_coreActionKernel.mpr ⟨hvN, hvP⟩
  have hW' : ∀ A : Subgroup G, A ≤ P → Open.IsElemAbelian 2 A → 8 ≤ Nat.card A →
      GrSLit.wGroup A = W := fun A hAP hA h8 => hWE A (hAP.trans hPC) hA h8
  have hglue : L34FieldSignalizerGluing := l34FieldSignalizerGluing_of_inputs hmult
  obtain ⟨Q, hsetQ, hQmirror, hPQiso, hcorr, hDQ, hQN, hDsup⟩ :=
    exists_field_mirror_pump_in_normalizer hS h13 hmult hglue hset hmax hvG htvG hvK hW'
  obtain ⟨hQbase, hQord, hQvC, hQpc, hQn, mq, hmq, hmeq, hQmodelq⟩ := hsetQ
  have hQM : Q ≤ M := by
    rw [hM] at hQN
    exact hQN
  let D : Subgroup G := UnbalancedGS.gsFixedLayer P (vM : G)
  have hD_le_P : D ≤ P := hDsup ▸ le_sup_left
  have hD_le_M : D ≤ M := hD_le_P.trans hPM
  have hD_perf : ⁅D, D⁆ = D := by
    change ⁅UnbalancedGS.gsFixedLayer P (vM : G),
      UnbalancedGS.gsFixedLayer P (vM : G)⁆ = UnbalancedGS.gsFixedLayer P (vM : G)
    rw [UnbalancedGS.gsFixedLayer, ← Subgroup.map_commutator,
      CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect]
  have hoddInP_odd : Odd (Nat.card (oddIn P)) := by
    have hcard : Nat.card (oddIn P) = Nat.card (pPrimeCore 2 ↥P) :=
      Subgroup.card_map_of_injective (K := pPrimeCore 2 ↥P) (f := P.subtype)
        P.subtype_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hP2 : 2 ∣ Nat.card P := by
    have hquot : 2 ∣ Nat.card (P ⧸ Open.fusionZStar P) := by
      have hdvd : 2 ^ (3 * m) ∣ Nat.card (P ⧸ Open.fusionZStar P) :=
        pow_dvd_card_of_lieModel_psl_three (n := m) (by omega) hPm
      exact (show 2 ∣ 2 ^ (3 * m) from by
        simpa using Nat.pow_dvd_pow 2 (show 1 ≤ 3 * m by omega)).trans hdvd
    exact hquot.trans (Subgroup.card_quotient_dvd_card (s := Open.fusionZStar P))
  have hOMinfP_le_odd : OM ⊓ P ≤ oddIn P := hK_le_odd
  let Dbar : Subgroup X := (D.subgroupOf M).map π
  have hDbar_ne : Dbar ≠ ⊥ := by
    intro hbot
    change (D.subgroupOf M).map π = ⊥ at hbot
    have hDleOM : D ≤ OM := by
      have hle : D.subgroupOf M ≤ pPrimeCore 2 ↥M := by
        have h := (Subgroup.map_eq_bot_iff (D.subgroupOf M)).mp hbot
        rwa [QuotientGroup.ker_mk'] at h
      intro x hx
      let xM : ↥M := ⟨x, hD_le_M hx⟩
      have hxsub : xM ∈ D.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_map_of_mem M.subtype (hle hxsub)
    have hDle_odd : D ≤ oddIn P :=
      (le_inf hDleOM hD_le_P).trans hK_le_odd
    have hPle_odd : P ≤ oddIn P := by
      have h1 : D ⊔ oddIn P ≤ oddIn P := sup_le hDle_odd le_rfl
      rwa [hDsup] at h1
    have hP_eq : P = oddIn P := le_antisymm hPle_odd (Subgroup.map_subtype_le _)
    have hoddP : Odd (Nat.card P) := by
      rw [hP_eq]
      exact hoddInP_odd
    exact (Nat.not_even_iff_odd.mpr hoddP) (even_iff_two_dvd.mpr hP2)
  have hDsub_perf : Group.IsPerfect ↥(D.subgroupOf M) := by
    letI : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hD_perf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hD_le_M).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hD_le_M).symm.surjective
  have hDbar_perf : ⁅Dbar, Dbar⁆ = Dbar := by
    letI : Group.IsPerfect ↥(D.subgroupOf M) := hDsub_perf
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.map (H := D.subgroupOf M) π)
  have hcontra : ⁅Dbar, Dbar⁆ = ⊥ → False := fun h => hDbar_ne (hDbar_perf.symm.trans h)
  set Cv : Subgroup ↥M := centralizer ({vM} : Set ↥M) with hCvdef
  set A : Subgroup X := centralizer ({π vM} : Set X) with hAdef
  have hE : IsPGroup 2 (Subgroup.zpowers vM) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hvMord, pow_one]
  have hker : ¬ 2 ∣ Nat.card (π.domRestrict (⊤ : Subgroup ↥M)).ker := by
    have hcard : Nat.card (π.domRestrict (⊤ : Subgroup ↥M)).ker =
        Nat.card (pPrimeCore 2 ↥M) := by
      have hk : (π.domRestrict (⊤ : Subgroup ↥M)).ker =
          (pPrimeCore 2 ↥M).subgroupOf (⊤ : Subgroup ↥M) := by
        rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
      rw [hk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    rw [hcard, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
  have hmap := CFSG.ComponentClassification.GSThmB.OddQuot.map_inf_centralizer π hE
    (by rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top]; exact le_top) hker
  have hAeq : Cv.map π = A := by
    have h1 : Cv = ⊤ ⊓ centralizer ((Subgroup.zpowers vM : Subgroup ↥M) : Set ↥M) := by
      rw [hCvdef, top_inf_eq, CFSG.GroupTheory.centralizer_zpowers_eq]
    rw [hAdef]
    rw [h1, hmap, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M))]
    rw [top_inf_eq, MonoidHom.map_zpowers, CFSG.GroupTheory.centralizer_zpowers_eq]
  let Qbar : Subgroup X := (Q.subgroupOf M).map π
  have hQbarA : Qbar ≤ A := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hAdef, Subgroup.mem_centralizer_singleton_iff]
    have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have hqv : (q : G) * (vM : G) = (vM : G) * (q : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQvC hqQ)
    have hqvM : q * vM = vM * q := by
      apply Subtype.ext
      simpa using hqv
    rw [← map_mul, ← map_mul, hqvM]
  have hQC : Q.subgroupOf M ≤ Cv := by
    intro x hx
    rw [hCvdef, Subgroup.mem_centralizer_singleton_iff]
    have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have hxv : (x : G) * (vM : G) = (vM : G) * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQvC hxQ)
    apply Subtype.ext
    simpa using hxv
  have hQN_G : centralizer ({(vM : G)} : Set G) ≤ normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQvC).mp hQn
  have hQnC : ((Q.subgroupOf M).subgroupOf Cv).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQC]
    intro c hc
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem (fun x hx => ?_)
    have hcG : (c : G) ∈ centralizer ({(vM : G)} : Set G) := by
      have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg (fun z : ↥M => (z : G)) hc'
    have hcN : (c : G) ∈ normalizer (Q : Set G) := hQN_G hcG
    have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have hconj : (c : G) * (x : G) * (c : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hcN (x : G)).mp hxQ
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hconj)
  have hQbarN : (Qbar.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQbarA]
    intro y hy
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem (fun q hq => ?_)
    rw [← hAeq] at hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    refine ⟨c * x * c⁻¹, ?_, ?_⟩
    · have hxC : x ∈ Cv := hQC hx
      have hxsub : (⟨x, hxC⟩ : ↥Cv) ∈ (Q.subgroupOf M).subgroupOf Cv := hx
      have hconj := hQnC.conj_mem ⟨x, hxC⟩ hxsub ⟨c, hc⟩
      have := Subgroup.mem_subgroupOf.mp hconj
      simpa using this
    · simp only [map_mul, map_inv]
  have hLA : L ≤ A := by
    intro l hl
    rw [hAdef, Subgroup.mem_centralizer_singleton_iff]
    exact (hv_cent l (Subgroup.mem_sup_left hl)).symm
  have hLtA : Lt ≤ A := by
    intro l hl
    rw [hAdef, Subgroup.mem_centralizer_singleton_iff]
    exact (hv_cent l (Subgroup.mem_sup_right hl)).symm
  have hLAcomp : IsComponent (L.subgroupOf A) := CFSG.LocalCores.component_overgroup hL hLA
  have hLtAcomp : IsComponent (Lt.subgroupOf A) :=
    CFSG.LocalCores.component_overgroup hLt_comp hLtA
  have hLQbar := CFSG.Holt.General.le_or_commutator_eq_bot_of_isComponent_of_normal
    (G := X) (Y := A) (W := A) (C := L) (M := Qbar)
    le_rfl (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
    hLA hLAcomp hQbarA hQbarN
  have hLtQbar := CFSG.Holt.General.le_or_commutator_eq_bot_of_isComponent_of_normal
    (G := X) (Y := A) (W := A) (C := Lt) (M := Qbar)
    le_rfl (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
    hLtA hLtAcomp hQbarA hQbarN
  have hDbarQbar : Dbar ≤ Qbar := Subgroup.map_mono (Subgroup.subgroupOf_mono M hDQ)
  have hDbarPbar : Dbar ≤ (P.subgroupOf M).map π :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M hD_le_P)
  have hDbarSup : Dbar ≤ L ⊔ Lt := hDbarPbar.trans hPL
  have htbar_cent_Dbar : ∀ y ∈ Dbar, tbar * y = y * tbar := by
    rintro _ ⟨d, hd, rfl⟩
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hdt : (d : G) * t = t * (d : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPC (hD_le_P hdD))
    have hdtM : d * tM = tM * d := by
      apply Subtype.ext
      simpa [tM] using hdt
    rw [← map_mul, ← map_mul, hdtM]
  have hQbar_dvd_Q : Nat.card ↥Qbar ∣ Nat.card ↥Q := by
    have h1 : Nat.card ↥Qbar ∣ Nat.card ↥(Q.subgroupOf M) := Subgroup.card_map_dvd _ π
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv] at h1
  obtain ⟨ePQ⟩ := hPQiso
  have hQmodel : Blueprint.LieModel (↥Q ⧸ Open.fusionZStar ↥Q) .PSL 3 2 m :=
    Blueprint.LieModel.of_mulEquiv ePQ hPm
  have hQperfect : Group.IsPerfect ↥Q := by
    have h := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hQpc
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hQvC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQvC).surjective
  letI : Group.IsPerfect ↥Q := hQperfect
  have hQZ : Open.fusionZStar ↥Q = Open.fusionOddCore ↥Q :=
    fusionZStar_eq_fusionOddCore_of_schurMult2L3 hmult (X := ↥Q) (by omega) hQmodel
  have hQoddZ : Odd (Nat.card (Open.fusionZStar ↥Q)) := by
    rw [hQZ, CFSG.ComponentClassification.UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hQcard : Nat.card ↥Q = Nat.card (↥Q ⧸ Open.fusionZStar ↥Q) *
      Nat.card (Open.fusionZStar ↥Q) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Open.fusionZStar ↥Q)
  have hQpadic : padicValNat 2 (Nat.card ↥Q) = 3 * m := by
    rw [hQcard, padicValNat.mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
    rw [padicValNat_card_of_lieModel_psl_three (n := m) (by omega) hQmodel,
      padicValNat.eq_zero_of_not_dvd hQoddZ.not_two_dvd_nat]
    omega
  have hQ2not : ¬ 2 ^ (3 * m + 1) ∣ Nat.card ↥Q := by
    intro h
    have hle : 3 * m + 1 ≤ padicValNat 2 (Nat.card ↥Q) :=
      (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥Q)
        (Nat.card_pos.ne')).mp h
    omega
  have hL2n : 2 ^ (3 * n) ∣ Nat.card ↥L :=
    pow_dvd_card_of_lieModel_psl_three hn1 hLmodel
  have hLtcard : Nat.card ↥Lt = Nat.card ↥L := by
    rw [hLtdef]
    exact Subgroup.card_map_of_injective (MulAut.conj tbar).injective
  have hZLt : center ↥Lt = ⊥ := by
    have e : ↥L ≃* ↥Lt := MulEquiv.subgroupMap (MulAut.conj tbar) L
    have hcard : Nat.card ↥(center ↥L) = Nat.card ↥(center ↥Lt) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    refine (Subgroup.card_eq_one (H := center ↥Lt)).mp ?_
    rw [← hcard, hZ]
    simp
  rcases hLQbar with hLleQ | hLcommQ
  · rcases hcase with ⟨hLt_eq, hn_eq⟩ | hLt_ne
    ·
      have hdvdL : Nat.card ↥L ∣ Nat.card ↥Q :=
        (Subgroup.card_dvd_of_le hLleQ).trans hQbar_dvd_Q
      have hdvdQn : 2 ^ (3 * n) ∣ Nat.card ↥Q := hL2n.trans hdvdL
      have hle : 3 * m + 1 ≤ 3 * n := by omega
      exact hQ2not ((Nat.pow_dvd_pow 2 hle).trans hdvdQn)
    ·
      have hcommLtL : ⁅Lt, L⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hLt_comp hL with h | h
        · exact absurd h hLt_ne
        · exact h
      have hLtCentL : Lt ≤ centralizer (L : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLtL
      have hLtNormL : Lt ≤ normalizer (L : Set X) :=
        hLtCentL.trans (Subgroup.centralizer_le_normalizer (L : Set X))
      have hcommLLt : ∀ a ∈ L, ∀ b ∈ Lt, a * b = b * a := by
        intro a ha b hb
        exact Subgroup.mem_centralizer_iff.mp (hLtCentL hb) a ha
      have hinf : L ⊓ Lt = ⊥ := by
        rw [eq_bot_iff]
        intro n hn
        obtain ⟨hnL, hnLt⟩ := Subgroup.mem_inf.mp hn
        have hcent : (⟨n, hnL⟩ : ↥L) ∈ Subgroup.center ↥L := by
          rw [Subgroup.mem_center_iff]
          intro l
          apply Subtype.ext
          exact hcommLLt l.val l.2 n hnLt
        have h1 : (⟨n, hnL⟩ : ↥L) = 1 := by
          have hc := hZ ▸ hcent
          exact Subgroup.mem_bot.mp hc
        simpa using Subtype.ext_iff.mp h1
      rcases hLtQbar with hLtleQ | hLtcommQ
      ·
        have hdisj : Disjoint L Lt := disjoint_iff.mpr hinf
        have hcard_sup : Nat.card ↥(L ⊔ Lt) = Nat.card ↥L * Nat.card ↥Lt :=
          CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
            L Lt hLtNormL hdisj
        have hsup_le : L ⊔ Lt ≤ Qbar := sup_le hLleQ hLtleQ
        have hdvd : Nat.card ↥(L ⊔ Lt) ∣ Nat.card ↥Q :=
          (Subgroup.card_dvd_of_le hsup_le).trans hQbar_dvd_Q
        have hbig : 2 ^ (3 * n) * 2 ^ (3 * n) ∣ Nat.card ↥Q := by
          rw [hcard_sup, hLtcard] at hdvd
          exact (mul_dvd_mul hL2n hL2n).trans hdvd
        have hbig' : 2 ^ (6 * n) ∣ Nat.card ↥Q := by
          have hpow : 2 ^ (3 * n) * 2 ^ (3 * n) = 2 ^ (6 * n) := by
            rw [← pow_add]
            congr 1
            ring
          rwa [hpow] at hbig
        have hle : 3 * m + 1 ≤ 6 * n := by omega
        exact hQ2not ((Nat.pow_dvd_pow 2 hle).trans hbig')
      ·
        have hLtCentQ : Qbar ≤ centralizer (Lt : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hLtcommQ)
        have hDbarL : Dbar ≤ L := by
          intro y hy
          have hcentLt : y ∈ centralizer (Lt : Set X) := hLtCentQ (hDbarQbar hy)
          obtain ⟨a, ha, b, hb, hab⟩ :=
            (CFSG.mem_sup_of_commute (fun a ha b hb => hcommLLt a ha b hb)).mp
              (hDbarSup hy)
          have ha_cent : a ∈ centralizer (Lt : Set X) := by
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            exact (Subgroup.mem_centralizer_iff.mp (hLtCentL hz) a ha).symm
          have hbeq : b = a⁻¹ * y := by
            rw [← hab]
            group
          have hb_cent : b ∈ centralizer (Lt : Set X) := by
            have h1 : a⁻¹ * y ∈ centralizer (Lt : Set X) :=
              Subgroup.mul_mem _ (Subgroup.inv_mem _ ha_cent) hcentLt
            rwa [← hbeq] at h1
          have hb_center : (⟨b, hb⟩ : ↥Lt) ∈ Subgroup.center ↥Lt := by
            rw [Subgroup.mem_center_iff]
            intro l
            apply Subtype.ext
            exact Subgroup.mem_centralizer_iff.mp hb_cent l.val l.2
          have hb1 : b = 1 := by
            have hc := hZLt ▸ hb_center
            exact congrArg Subtype.val (Subgroup.mem_bot.mp hc)
          have hyeq : y = a := by rw [← hab, hb1, mul_one]
          simpa [hyeq] using ha
        have hDbarLt : Dbar ≤ Lt := by
          intro y hy
          have hyL := hDbarL hy
          have htcent : tbar * y = y * tbar := htbar_cent_Dbar y hy
          have hconj : tbar * y * tbar⁻¹ ∈ Lt := by
            rw [hLtdef]
            exact Subgroup.mem_map_of_mem _ (by simpa [mul_assoc] using hyL)
          have hyconj : tbar * y * tbar⁻¹ = y := by
            rw [htcent, mul_assoc, mul_inv_cancel, mul_one]
          rwa [hyconj] at hconj
        have hbot : Dbar ≤ ⊥ := by
          intro y hy
          have hmem : y ∈ L ⊓ Lt :=
            Subgroup.mem_inf.mpr ⟨hDbarL hy, hDbarLt hy⟩
          rwa [hinf] at hmem
        exact hDbar_ne (le_bot_iff.mp hbot)
  · rcases hcase with ⟨hLt_eq, hn_eq⟩ | hLt_ne
    ·
      have hLtcommQ : ⁅Lt, Qbar⁆ = ⊥ := by rw [hLt_eq]; exact hLcommQ
      have hQbarCentL : Qbar ≤ centralizer (L : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hLcommQ)
      have hQbarCentLt : Qbar ≤ centralizer (Lt : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hLtcommQ)
      have hDbar_cent : Dbar ≤ centralizer ((L ⊔ Lt : Subgroup X) : Set X) :=
        CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
          (hDbarQbar.trans hQbarCentL) (hDbarQbar.trans hQbarCentLt)
      have hDbar_abelian : ⁅Dbar, Dbar⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (hDbar_cent.trans (Subgroup.centralizer_le hDbarSup))
      exact hcontra hDbar_abelian
    ·
      have hcommLtL : ⁅Lt, L⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hLt_comp hL with h | h
        · exact absurd h hLt_ne
        · exact h
      have hLtCentL : Lt ≤ centralizer (L : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLtL
      have hcommLLt : ∀ a ∈ L, ∀ b ∈ Lt, a * b = b * a := by
        intro a ha b hb
        exact Subgroup.mem_centralizer_iff.mp (hLtCentL hb) a ha
      have hinf : L ⊓ Lt = ⊥ := by
        rw [eq_bot_iff]
        intro n hn
        obtain ⟨hnL, hnLt⟩ := Subgroup.mem_inf.mp hn
        have hcent : (⟨n, hnL⟩ : ↥L) ∈ Subgroup.center ↥L := by
          rw [Subgroup.mem_center_iff]
          intro l
          apply Subtype.ext
          exact hcommLLt l.val l.2 n hnLt
        have h1 : (⟨n, hnL⟩ : ↥L) = 1 := by
          have hc := hZ ▸ hcent
          exact Subgroup.mem_bot.mp hc
        simpa using Subtype.ext_iff.mp h1
      rcases hLtQbar with hLtleQ | hLtcommQ
      ·
        have hQbarCentL : Qbar ≤ centralizer (L : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hLcommQ)
        have hDbarLt : Dbar ≤ Lt := by
          intro y hy
          have hcentL : y ∈ centralizer (L : Set X) := hQbarCentL (hDbarQbar hy)
          obtain ⟨a, ha, b, hb, hab⟩ :=
            (CFSG.mem_sup_of_commute (fun a ha b hb => hcommLLt a ha b hb)).mp
              (hDbarSup hy)
          have hb_cent : b ∈ centralizer (L : Set X) := hLtCentL hb
          have haeq : a = y * b⁻¹ := by
            rw [← hab]
            group
          have ha_cent : a ∈ centralizer (L : Set X) := by
            have h1 : y * b⁻¹ ∈ centralizer (L : Set X) :=
              Subgroup.mul_mem _ hcentL (Subgroup.inv_mem _ hb_cent)
            rwa [← haeq] at h1
          have ha_center : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := by
            rw [Subgroup.mem_center_iff]
            intro l
            apply Subtype.ext
            exact Subgroup.mem_centralizer_iff.mp ha_cent l.val l.2
          have ha1 : a = 1 := by
            have hc := hZ ▸ ha_center
            exact congrArg Subtype.val (Subgroup.mem_bot.mp hc)
          have hyeq : y = b := by rw [← hab, ha1, one_mul]
          simpa [hyeq] using hb
        have hDbarL : Dbar ≤ L := by
          intro y hy
          have htcent : tbar * y = y * tbar := htbar_cent_Dbar y hy
          have hconj : tbar * y * tbar⁻¹ ∈ L := by
            rw [← hLt_map]
            exact Subgroup.mem_map_of_mem _ (by simpa [mul_assoc] using hDbarLt hy)
          have hyconj : tbar * y * tbar⁻¹ = y := by
            rw [htcent, mul_assoc, mul_inv_cancel, mul_one]
          rwa [hyconj] at hconj
        have hbot : Dbar ≤ ⊥ := by
          intro y hy
          have hmem : y ∈ L ⊓ Lt :=
            Subgroup.mem_inf.mpr ⟨hDbarL hy, hDbarLt hy⟩
          rwa [hinf] at hmem
        exact hDbar_ne (le_bot_iff.mp hbot)
      ·
        have hQbarCentL : Qbar ≤ centralizer (L : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hLcommQ)
        have hQbarCentLt : Qbar ≤ centralizer (Lt : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hLtcommQ)
        have hDbar_cent : Dbar ≤ centralizer ((L ⊔ Lt : Subgroup X) : Set X) :=
          CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
            (hDbarQbar.trans hQbarCentL) (hDbarQbar.trans hQbarCentLt)
        have hDbar_abelian : ⁅Dbar, Dbar⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (hDbar_cent.trans (Subgroup.centralizer_le hDbarSup))
        exact hcontra hDbar_abelian

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
