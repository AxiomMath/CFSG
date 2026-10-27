module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Config
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Components
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGTrans

public section

namespace CFSG.SectionRank.QTK.Insp443.Hyp

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique
  CFSG.Quasithin.C2Nine CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB K : Subgroup G}

theorem kConf (h : Hyp G T M L B Tp VB K) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) :
    KConf ↥K ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K)
      (VB.subgroupOf K) (M.subgroupOf K) := by
  classical
  let LB : Subgroup G := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))
  let TB : Subgroup G := Tp ⊓ Subgroup.normalizer (B : Set G)
  let L' : Subgroup ↥K := LB.subgroupOf K
  let V' : Subgroup ↥K := VB.subgroupOf K
  let MK : Subgroup ↥K := M.subgroupOf K
  have hElemAb : IsElemAbelian 2 V' :=
    (show IsElemAbelian 2 VB from ⟨VB_comm h, VB_sq h⟩).subgroupOf K
  have hVne : V' ≠ ⊥ := by
    intro hbot
    apply h.setting.hyp.VB_ne_bot
    have h' := congrArg (Subgroup.map K.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le h.VB_le, Subgroup.map_bot] at h'
    exact h'
  have hperf : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, show L' = LB.subgroupOf K from rfl,
      Subgroup.map_subgroupOf_eq_of_le h.LB_le]
    exact LB_perfect h
  have hLeNorm : L' ≤ Subgroup.normalizer (V' : Set ↥K) := by
    have h1 : L' ≤ (Subgroup.normalizer (VB : Set G)).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        (LB_le_normalizer_VB h (Subgroup.mem_subgroupOf.mp hx))
    rw [Subgroup.subgroupOf_normalizer_eq h.VB_le] at h1
    exact h1
  have hVlePc : V' ≤ pCoreOf 2 L' := by
    have hNH : V' ≤ L' := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (VB_le_LB h (Subgroup.mem_subgroupOf.mp hx))
    exact le_pCoreOf 2 hNH (Subgroup.normal_subgroupOf_of_le_normalizer hLeNorm) hElemAb.isPGroup
  have hPcMap : (pCoreOf 2 L').map K.subtype = pCoreOf 2 LB := by
    rw [← CFSG.Quasithin.H13.F431.AG.pCoreOf_map_injective K.subtype K.subtype_injective
      (LB.subgroupOf K), Subgroup.map_subgroupOf_eq_of_le h.LB_le]
  have hPc_le : pCoreOf 2 L' ≤ Subgroup.centralizer (V' : Set ↥K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hxG : (x : G) ∈ pCoreOf 2 LB := by
      have h := Subgroup.mem_map_of_mem K.subtype hx
      rwa [hPcMap] at h
    have hyG : (y : G) ∈ VB := Subgroup.mem_subgroupOf.mp hy
    exact Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer h hxG) (y : G) hyG
  have heqcomm : V' = ⁅V', L'⁆ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, show V' = VB.subgroupOf K from rfl,
      show L' = LB.subgroupOf K from rfl, Subgroup.map_subgroupOf_eq_of_le h.VB_le,
      Subgroup.map_subgroupOf_eq_of_le h.LB_le]
    exact VB_eq_commutator h
  have hleMK : L' ≤ MK := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((LB_le_inf h).trans inf_le_left (Subgroup.mem_subgroupOf.mp hx))
  have hMK_le : MK ≤ Subgroup.normalizer (L' : Set ↥K) := by
    have h1 : MK ≤ (Subgroup.normalizer (LB : Set G)).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        (MB_le_normalizer_LB h.setting h37 h38 h39
          ⟨Subgroup.mem_subgroupOf.mp hx, h.K_le x.2⟩)
    rw [Subgroup.subgroupOf_normalizer_eq h.LB_le] at h1
    exact h1
  have hMK_ne_top : MK ≠ ⊤ := by
    intro htop
    exact h.not_le (Subgroup.subgroupOf_eq_top.mp htop)
  have hσ_apply : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) (q : ↥K),
      ((K.normalizerMonoidHom ⟨x, hx⟩) q : G) = x * (q : G) * x⁻¹ := by
    intro x hx q
    simpa using Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hx⟩ q
  have hcomp_conj : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      K.subtype.comp (K.normalizerMonoidHom ⟨x, hx⟩).toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp K.subtype := by
    intro x hx
    ext q
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hσ_apply x hx q
  have hmap_σ : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) (A : Subgroup ↥K),
      (A.map (K.normalizerMonoidHom ⟨x, hx⟩).toMonoidHom).map K.subtype =
        (A.map K.subtype).map (MulAut.conj x).toMonoidHom := by
    intro x hx A
    rw [Subgroup.map_map, hcomp_conj x hx, ← Subgroup.map_map]
  have hσ_fix_iff : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) (A : Subgroup ↥K),
      A.map (K.normalizerMonoidHom ⟨x, hx⟩).toMonoidHom = A ↔
        (A.map K.subtype).map (MulAut.conj x).toMonoidHom = A.map K.subtype := by
    intro x hx A
    constructor
    · intro hfix
      rw [← hmap_σ x hx A, hfix]
    · intro hfix
      apply Subgroup.map_injective K.subtype_injective
      rw [hmap_σ x hx A, hfix]
  have hsub_conj : ∀ y : ↥K, (MulAut.conj (y : G)).toMonoidHom.comp K.subtype =
      K.subtype.comp (MulAut.conj y).toMonoidHom := by
    intro y
    ext q
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hmap_conj : ∀ (y : ↥K) (A : Subgroup ↥K),
      (A.map (MulAut.conj y).toMonoidHom).map K.subtype =
        (A.map K.subtype).map (MulAut.conj (y : G)).toMonoidHom := by
    intro y A
    rw [Subgroup.map_map, ← hsub_conj y, ← Subgroup.map_map]
  refine
    { quasisimple := h.quasisimple
      odd_card_center := odd_card_center h
      ne_bot := hVne
      elemAbelian := hElemAb
      perfect := hperf
      le_normalizer := hLeNorm
      le_pCoreOf := hVlePc
      pCoreOf_le := hPc_le
      eq_commutator := heqcomm
      le_MK := hleMK
      MK_le_normalizer := hMK_le
      MK_ne_top := hMK_ne_top
      normalizer_le := ?_
      card_eq := ?_
      card_le := ?_ }
  · intro Q hQ hQ2 hQinv
    let P : Subgroup G := Q.map K.subtype
    have hPne : P ≠ ⊥ := by
      intro hbot
      exact hQ ((Subgroup.map_eq_bot_iff_of_injective Q K.subtype_injective).mp hbot)
    have hP2 : IsPGroup 2 P := hQ2.map K.subtype
    have step : ∀ (x : G), x ∈ Subgroup.normalizer (K : Set G) →
        x ∈ Subgroup.normalizer (VB : Set G) → x ∈ Subgroup.normalizer (LB : Set G) →
        x ∈ M → x ∈ Subgroup.normalizer (P : Set G) := by
      intro x hxK hxV hxL hxM
      have hσV : V'.map (K.normalizerMonoidHom ⟨x, hxK⟩).toMonoidHom = V' := by
        rw [hσ_fix_iff x hxK V', show V' = VB.subgroupOf K from rfl,
          Subgroup.map_subgroupOf_eq_of_le h.VB_le]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxV
      have hσL : L'.map (K.normalizerMonoidHom ⟨x, hxK⟩).toMonoidHom = L' := by
        rw [hσ_fix_iff x hxK L', show L' = LB.subgroupOf K from rfl,
          Subgroup.map_subgroupOf_eq_of_le h.LB_le]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxL
      have hσMK : MK.map (K.normalizerMonoidHom ⟨x, hxK⟩).toMonoidHom = MK := by
        rw [hσ_fix_iff x hxK MK, show MK = M.subgroupOf K from rfl,
          Subgroup.subgroupOf_map_subtype,
          Subgroup.map_inf M K (MulAut.conj x).toMonoidHom (MulAut.conj x).injective,
          show Subgroup.map (MulAut.conj x).toMonoidHom M = M from
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxM),
          show Subgroup.map (MulAut.conj x).toMonoidHom K = K from
            Subgroup.mem_normalizer_iff_map_conj_eq.mp hxK]
      have hQmap : Q.map (K.normalizerMonoidHom ⟨x, hxK⟩).toMonoidHom = Q :=
        hQinv (K.normalizerMonoidHom ⟨x, hxK⟩) hσV hσL hσMK
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h := congrArg (Subgroup.map K.subtype) hQmap
      rw [hmap_σ x hxK Q] at h
      exact h
    have hLB_N : LB ≤ Subgroup.normalizer (P : Set G) := by
      intro x hx
      exact step x (Subgroup.le_normalizer (h.LB_le hx)) (LB_le_normalizer_VB h hx)
        (Subgroup.le_normalizer hx) ((LB_le_inf h).trans inf_le_left hx)
    have hTB_N : TB ≤ Subgroup.normalizer (P : Set G) := by
      intro x hx
      obtain ⟨hxTp, hxB⟩ := Subgroup.mem_inf.mp hx
      have hxM : x ∈ M :=
        ((le_sup_right : TB ≤ LB ⊔ TB).trans h.setting.sup_le_normalizer) hx |>.1
      have hxK : x ∈ Subgroup.normalizer (K : Set G) := h.normalizer_le hxB
      have hxV : x ∈ Subgroup.normalizer (VB : Set G) :=
        (le_sup_right.trans h.setting.hyp.VB_normalized) (h.setting.hyp.Tp_le hxTp)
      have hxL : x ∈ Subgroup.normalizer (LB : Set G) :=
        MB_le_normalizer_LB h.setting h37 h38 h39 ⟨hxM, hxB⟩
      exact step x hxK hxV hxL hxM
    have hle : LB ⊔ TB ≤ Subgroup.normalizer (P : Set G) := sup_le hLB_N hTB_N
    have hNM : Subgroup.normalizer (P : Set G) ≤ M :=
      isUniqueM_normalizer_le h.unique hPne hP2
        (by simpa only [TB] using hle)
    intro y hy
    have hyP : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
      have hqmap : Q.map (MulAut.conj y).toMonoidHom = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h := congrArg (Subgroup.map K.subtype) hqmap
      rw [hmap_conj y Q] at h
      exact h
    exact Subgroup.mem_subgroupOf.mpr (hNM hyP)
  · intro X Y hXn hYn hXq hYq
    have hN421 : CFSG.Quasithin.conjClosure L T ≤ Subgroup.normalizer (L : Set G) :=
      conjClosure_le_normalizer_of_hyp421 h.setting.hyp421 h37 h39
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := h.setting.hyp.quasisimple
    let eL' : ↥L' ≃* ↥LB := Subgroup.subgroupOfEquivOfLe h.LB_le
    let e1 : (↥L' ⧸ CFSG.pCore 2 ↥L') ≃* (↥LB ⧸ CFSG.pCore 2 ↥LB) :=
      QuotientGroup.congr (CFSG.pCore 2 ↥L') (CFSG.pCore 2 ↥LB) eL'
        (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL')
    obtain ⟨e2⟩ := E443.nonempty_quotEquiv (E443.LB_le L T B)
      (lemma_4_4_5_orbit h.setting.hyp.toHyp4_4_1TwoOrbit) (E443.pCoreOf_LB_le h.setting)
    let e : (↥L' ⧸ CFSG.pCore 2 ↥L') ≃*
        (↥(CFSG.Quasithin.conjClosure L T) ⧸
          CFSG.pCore 2 ↥(CFSG.Quasithin.conjClosure L T)) := e1.trans e2
    have hXcard : Nat.card X = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have hqX : CFSG.IsQuasisimple ↥(X.map e.toMonoidHom) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective) hXq
      have hnX : (X.map e.toMonoidHom).Normal :=
        Subgroup.Normal.map hXn e.toMonoidHom e.surjective
      have h := card_eq_of_isQuasisimple_of_normal hN421 hq (X.map e.toMonoidHom) hnX hqX
      rwa [Subgroup.card_map_of_injective e.injective] at h
    have hYcard : Nat.card Y = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have hqY : CFSG.IsQuasisimple ↥(Y.map e.toMonoidHom) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective) hYq
      have hnY : (Y.map e.toMonoidHom).Normal :=
        Subgroup.Normal.map hYn e.toMonoidHom e.surjective
      have h := card_eq_of_isQuasisimple_of_normal hN421 hq (Y.map e.toMonoidHom) hnY hqY
      rwa [Subgroup.card_map_of_injective e.injective] at h
    rw [hXcard, hYcard]
  · intro Q hQ hQ2 p hp hp2 E hE hEab
    have hfactp : Fact (Nat.Prime p) := ⟨hp⟩
    let P : Subgroup G := Q.map K.subtype
    have hPne : P ≠ ⊥ := by
      intro hbot
      exact hQ ((Subgroup.map_eq_bot_iff_of_injective Q K.subtype_injective).mp hbot)
    have hP2 : IsPGroup 2 P := hQ2.map K.subtype
    let E' : Subgroup G := E.map K.subtype
    have hE'le : E' ≤ Subgroup.normalizer (P : Set G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyN : y ∈ Subgroup.normalizer (Q : Set ↥K) := hE hy
      have hqmap : Q.map (MulAut.conj y).toMonoidHom = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h := congrArg (Subgroup.map K.subtype) hqmap
      rw [hmap_conj y Q] at h
      exact h
    have hE'ab : IsElemAbelian p E' := hEab.map K.subtype
    have hcardE : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective K.subtype_injective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE'ab.isPGroup
    have hkE : Nat.card E = p ^ k := by
      rw [← hcardE]
      exact hk
    have hk2 : k ≤ 2 := by
      have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (P : Set G)) :=
        le_pRank_of_isElemAbelian hp.one_lt hE'le hE'ab hk
      have h2 : CFSG.Open.pRank p (Subgroup.normalizer (P : Set G)) ≤ 2 :=
        pRank_le_two_of_isTwoLocal h.setting.hyp.qtke hp hp2 ⟨P, hPne, hP2, rfl⟩
      exact h1.trans h2
    calc Nat.card E = p ^ k := hkE
      _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hk2

end CFSG.SectionRank.QTK.Insp443.Hyp
