module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O97Defs
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsL34
import CFSG.Quasithin.Vol2.Ch11SKFIto
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open

private def tau1 : alternatingGroup (Fin 11) :=
  ⟨Equiv.swap (0 : Fin 11) 1 * Equiv.swap (2 : Fin 11) 9, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

private def tau2 : alternatingGroup (Fin 11) :=
  ⟨Equiv.swap (0 : Fin 11) 2 * Equiv.swap (1 : Fin 11) 9, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

private theorem tau1_sq : tau1 * tau1 = 1 := by decide

private theorem tau2_sq : tau2 * tau2 = 1 := by decide

private theorem tau_commute : tau1 * tau2 = tau2 * tau1 := by decide

private theorem tau1_ne_one : tau1 ≠ 1 := by decide

private theorem tau2_ne_one : tau2 ≠ 1 := by decide

private theorem tau1_ne_tau2 : tau1 ≠ tau2 := by decide

private def kleinV : Subgroup (alternatingGroup (Fin 11)) :=
  CFSG.LocalAnalysis.ComponentInitial.kleinFourOf tau1_sq tau2_sq tau_commute

private theorem mem_kleinV {a : alternatingGroup (Fin 11)} :
    a ∈ kleinV ↔ a = 1 ∨ a = tau1 ∨ a = tau2 ∨ a = tau1 * tau2 :=
  CFSG.LocalAnalysis.ComponentInitial.mem_kleinFourOf tau1_sq tau2_sq tau_commute

private theorem card_kleinV : Nat.card kleinV = 4 :=
  CFSG.LocalAnalysis.ComponentInitial.card_kleinFourOf tau1_sq tau2_sq tau_commute
    tau1_ne_one tau2_ne_one tau1_ne_tau2

private theorem kleinV_ne_bot : kleinV ≠ ⊥ := by
  intro h
  have hcard := card_kleinV
  rw [h, Subgroup.card_bot] at hcard
  norm_num at hcard

private theorem isPGroup_kleinV : IsPGroup 2 kleinV :=
  IsPGroup.of_card (n := 2) (by rw [card_kleinV]; norm_num)

private def sigma0 : alternatingGroup (Fin 11) :=
  CFSG.SectionRank.cyc (by norm_num : 9 ≤ 11) 0

private def sigma1 : alternatingGroup (Fin 11) :=
  CFSG.SectionRank.cyc (by norm_num : 9 ≤ 11) 1

private def sigma2 : alternatingGroup (Fin 11) :=
  CFSG.SectionRank.cyc (by norm_num : 9 ≤ 11) 2

private def e27Param (v : Fin 3 → ZMod 3) : alternatingGroup (Fin 11) :=
  sigma0 ^ (v 0).val * sigma1 ^ (v 1).val * sigma2 ^ (v 2).val

private theorem e27Param_add :
    ∀ v w : Fin 3 → ZMod 3, e27Param (v + w) = e27Param v * e27Param w := by
  decide +kernel

private theorem e27Param_zero : e27Param 0 = 1 := by
  decide +kernel

private theorem e27Param_eq_one :
    ∀ v : Fin 3 → ZMod 3, e27Param v = 1 → v = 0 := by
  decide +kernel

private def e27Hom : Multiplicative (Fin 3 → ZMod 3) →* alternatingGroup (Fin 11) where
  toFun v := e27Param (Multiplicative.toAdd v)
  map_one' := e27Param_zero
  map_mul' v w := e27Param_add (Multiplicative.toAdd v) (Multiplicative.toAdd w)

private theorem e27Hom_injective : Function.Injective e27Hom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  have h : e27Param (Multiplicative.toAdd v) = 1 := by
    simpa [e27Hom] using congrArg Subtype.val hv
  exact Subgroup.mem_bot.2 (Multiplicative.toAdd.injective (e27Param_eq_one _ h))

private def e27T : Subgroup (alternatingGroup (Fin 11)) := e27Hom.range

private theorem isElemAbelian_e27T : CFSG.Open.IsElemAbelian 3 e27T := by
  have hpow : ∀ x : Multiplicative (Fin 3 → ZMod 3), x ^ 3 = 1 := by decide
  have hE : CFSG.Open.IsElemAbelian 3
      (⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 3))) :=
    ⟨⟨⟨fun a b => mul_comm a b⟩⟩, fun x _ => hpow x⟩
  have h := CFSG.SectionRank.isElemAbelian_map hE e27Hom
  rw [e27T, MonoidHom.range_eq_map]
  exact h

private theorem card_e27T : Nat.card e27T = 27 := by
  have h := (Nat.card_congr (MonoidHom.ofInjective e27Hom_injective).toEquiv).symm
  change Nat.card e27Hom.range = 27
  rw [h]
  simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]

private theorem mem_normalizer_kleinV_of_conj {c : alternatingGroup (Fin 11)}
    (h1 : MulAut.conj c tau1 ∈ kleinV) (h2 : MulAut.conj c tau2 ∈ kleinV) :
    c ∈ Subgroup.normalizer (kleinV : Set (alternatingGroup (Fin 11))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    change (MulAut.conj c) a ∈ kleinV
    rw [mem_kleinV] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · simpa using kleinV.one_mem
    · simpa only [MulAut.conj_apply] using h1
    · simpa only [MulAut.conj_apply] using h2
    · rw [map_mul]
      exact Subgroup.mul_mem _ (by simpa only [MulAut.conj_apply] using h1)
        (by simpa only [MulAut.conj_apply] using h2)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]

private theorem sigma0_mem_normalizer :
    sigma0 ∈ Subgroup.normalizer (kleinV : Set (alternatingGroup (Fin 11))) := by
  refine mem_normalizer_kleinV_of_conj ?_ ?_
  · rw [mem_kleinV]
    exact Or.inr (Or.inr (Or.inl (by decide : MulAut.conj sigma0 tau1 = tau2)))
  · rw [mem_kleinV]
    exact Or.inr (Or.inr (Or.inr (by decide : MulAut.conj sigma0 tau2 = tau1 * tau2)))

private theorem sigma1_mem_normalizer :
    sigma1 ∈ Subgroup.normalizer (kleinV : Set (alternatingGroup (Fin 11))) := by
  refine mem_normalizer_kleinV_of_conj ?_ ?_
  · rw [mem_kleinV]
    exact Or.inr (Or.inl (by decide : MulAut.conj sigma1 tau1 = tau1))
  · rw [mem_kleinV]
    exact Or.inr (Or.inr (Or.inl (by decide : MulAut.conj sigma1 tau2 = tau2)))

private theorem sigma2_mem_normalizer :
    sigma2 ∈ Subgroup.normalizer (kleinV : Set (alternatingGroup (Fin 11))) := by
  refine mem_normalizer_kleinV_of_conj ?_ ?_
  · rw [mem_kleinV]
    exact Or.inr (Or.inl (by decide : MulAut.conj sigma2 tau1 = tau1))
  · rw [mem_kleinV]
    exact Or.inr (Or.inr (Or.inl (by decide : MulAut.conj sigma2 tau2 = tau2)))

private theorem e27T_le_normalizer :
    e27T ≤ Subgroup.normalizer (kleinV : Set (alternatingGroup (Fin 11))) := by
  rintro t ⟨v, rfl⟩
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ sigma0_mem_normalizer _)
      (Subgroup.pow_mem _ sigma1_mem_normalizer _))
    (Subgroup.pow_mem _ sigma2_mem_normalizer _)

theorem a11_exists_klein_e27 : ∃ V T : Subgroup (alternatingGroup (Fin 11)), V ≠ ⊥ ∧
    IsPGroup 2 V ∧ CFSG.Open.IsElemAbelian 3 T ∧ Nat.card T = 27 ∧
    T ≤ Subgroup.normalizer (V : Set (alternatingGroup (Fin 11))) :=
  ⟨kleinV, e27T, kleinV_ne_bot, isPGroup_kleinV, isElemAbelian_e27T, card_e27T,
    e27T_le_normalizer⟩

private theorem O98Red.shape_not_isA11_z_not_mem {X : Type} [Group X] [Finite X]
    {E Y S : Subgroup X} {z : X} (h : O98Red X E Y S z) {L : Subgroup X}
    (hAK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type
      ↥(L.subgroupOf (Subgroup.normalizer (L : Set X)))) : z ∉ L := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hA11L : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type ↥L :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLX') hAK
  have hZL : Subgroup.center ↥L = ⊥ := by
    obtain ⟨eL⟩ := hA11L
    have hc := Subgroup.map_center_eq eL
    rw [alternatingGroup.center_eq_bot (α := Fin 11) (by norm_num)] at hc
    exact Subgroup.map_injective eL.injective (hc.trans (Subgroup.map_bot _).symm)
  intro hz
  have hzcent : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp h.center_z (y : X))
  rw [hZL, Subgroup.mem_bot] at hzcent
  have hz1 : z = 1 := congrArg Subtype.val hzcent
  have hord := h.order_z
  rw [hz1, orderOf_one] at hord
  norm_num at hord

private theorem O98Red.shape_not_isA11_map {X : Type} [Group X] [Finite X]
    {z : X} {L : Subgroup X}
    (hAK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type
      ↥(L.subgroupOf (Subgroup.normalizer (L : Set X)))) (hzL : z ∉ L) :
    ∃ VX TX : Subgroup X, VX ≠ ⊥ ∧ IsPGroup 2 VX ∧ IsElemAbelian 3 TX ∧
      Nat.card TX = 27 ∧ TX ≤ Subgroup.normalizer (VX : Set X) ∧
      TX ≤ L ∧ z ∉ TX := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  let K : Subgroup X' := L.subgroupOf X'
  obtain ⟨eK⟩ := hAK
  let f : alternatingGroup (Fin 11) →* X :=
    X'.subtype.comp (K.subtype.comp eK.symm.toMonoidHom)
  have hf : Function.Injective f :=
    X'.subtype_injective.comp (K.subtype_injective.comp eK.symm.injective)
  obtain ⟨V, T, hVne, hV2, hTelem, hTcard, hTN⟩ := a11_exists_klein_e27
  let VX : Subgroup X := V.map f
  let TX : Subgroup X := T.map f
  have hVXne : VX ≠ ⊥ := by
    intro hbot
    apply hVne
    have hbot' : Subgroup.map f V = ⊥ := hbot
    exact Subgroup.map_injective hf (by rw [hbot', Subgroup.map_bot])
  have hVX2 : IsPGroup 2 VX := IsPGroup.map hV2 f
  have hTXelem : IsElemAbelian 3 TX := CFSG.SectionRank.isElemAbelian_map hTelem f
  have hTXcard : Nat.card TX = 27 := by
    change Nat.card ↥(Subgroup.map f T) = 27
    rw [Subgroup.card_map_of_injective hf, hTcard]
  have hTXnorm : TX ≤ Subgroup.normalizer (VX : Set X) :=
    (Subgroup.map_mono hTN).trans (Subgroup.le_normalizer_map f)
  have hTXle : TX ≤ L := by
    rintro _ ⟨t, -, rfl⟩
    exact (eK.symm t).2
  exact ⟨VX, TX, hVXne, hVX2, hTXelem, hTXcard, hTXnorm, hTXle,
    fun hz => hzL (hTXle hz)⟩

private theorem O98Red.shape_not_isA11_rank {X : Type} [Group X] [Finite X]
    {E Y S : Subgroup X} {z : X} (h : O98Red X E Y S z) {VX TX : Subgroup X}
    (hVXne : VX ≠ ⊥) (hVX2 : IsPGroup 2 VX) (hTXelem : IsElemAbelian 3 TX)
    (hTXcard : Nat.card TX = 27) (hTXnorm : TX ≤ Subgroup.normalizer (VX : Set X))
    (hzTX : z ∉ TX) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE81elem, hE81card⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := 3) hTXelem h.order_z
      (fun e _ => Subgroup.mem_center_iff.mp h.center_z e) hzTX
  have hE81norm : TX ⊔ Subgroup.zpowers z ≤
      Subgroup.normalizer (VX : Set X) := by
    refine sup_le hTXnorm ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.center_le_normalizer (VX : Set X) h.center_z
  have hE81card81 : Nat.card ↥(TX ⊔ Subgroup.zpowers z) = 3 ^ 4 := by
    rw [hE81card, hTXcard]
    norm_num
  have h4 : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (VX : Set X)) := by
    refine CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hE81norm hE81elem ?_
    rw [hE81card81]
  have h3 : CFSG.Open.pRank 3 (Subgroup.normalizer (VX : Set X)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Subgroup.normalizer (VX : Set X)),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(Subgroup.normalizer (VX : Set X))]
    exact h.rank23 VX hVXne hVX2
  omega

private theorem O98Red.shape_not_isA11 {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (h : O98Red X E Y S z) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hAK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type
      ↥(L.subgroupOf (Subgroup.normalizer (L : Set X)))) : False := by
  have hzL := O98Red.shape_not_isA11_z_not_mem h hAK
  obtain ⟨VX, TX, hVXne, hVX2, hTXelem, hTXcard, hTXnorm, -, hzTX⟩ :=
    O98Red.shape_not_isA11_map hAK hzL
  exact O98Red.shape_not_isA11_rank h hVXne hVX2 hTXelem hTXcard hTXnorm hzTX

theorem O97Red.pPrimeCore_subgroupOf_normalizer_eq_bot {X : Type} [Group X] [Finite X]
    {E Y S : Subgroup X} (h : O97Red X E Y S) {L : Subgroup X}
    (hL : CFSG.IsComponent L) :
    CFSG.pPrimeCore 3 ↥(L.subgroupOf (Subgroup.normalizer (L : Set X))) = ⊥ := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hcoreL : CFSG.pPrimeCore 3 ↥L = ⊥ := by
    have hsub : ((CFSG.pPrimeCore 3 ↥L).map L.subtype).IsSubnormal := by
      refine Subgroup.IsSubnormal.step _ L (Subgroup.map_subtype_le _) hL.2 ?_
      have h1 : (Subgroup.map L.subtype (CFSG.pPrimeCore 3 ↥L)).subgroupOf L =
          CFSG.pPrimeCore 3 ↥L := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rw [h1]
      exact CFSG.pPrimeCore_normal
    have hcop : Nat.Coprime 3
        (Nat.card ↥((CFSG.pPrimeCore 3 ↥L).map L.subtype)) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hsub hcop
    have hbot : (CFSG.pPrimeCore 3 ↥L).map L.subtype = ⊥ := by
      rw [h.core] at hle
      exact le_bot_iff.mp hle
    have hrec := Subgroup.comap_map_eq_self_of_injective L.subtype_injective
      (CFSG.pPrimeCore 3 ↥L)
    rw [hbot] at hrec
    simpa using hrec.symm
  let K : Subgroup X' := L.subgroupOf X'
  change CFSG.pPrimeCore 3 ↥K = ⊥
  let e : ↥K ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX'
  have hmap := CFSG.pPrimeCore_map_iso 3 e
  rw [hcoreL] at hmap
  exact Subgroup.map_injective e.injective (hmap.trans (Subgroup.map_bot _).symm)

theorem O97Red.Y_le_normalizer_S {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    (h : O97Red X E Y S) : Y ≤ Subgroup.normalizer (S : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h.normal_S y hy s, fun hs => ?_⟩
  have := h.normal_S y⁻¹ (Y.inv_mem hy) (y * s * y⁻¹) hs
  rwa [show y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s by group] at this

theorem O97Red.rankThreeGamma_subgroupOf_le {X : Type} [Group X] [Finite X]
    {E Y S : Subgroup X} (h : O97Red X E Y S) (X' : Subgroup X) :
    CFSG.Open.rankThreeGamma 1 3 (E.subgroupOf X') ≤ Y.subgroupOf X' := by
  let E' : Subgroup X' := E.subgroupOf X'
  change CFSG.Open.GLBCore 3 1 E' ≤ Y.subgroupOf X'
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q hQE' hQrank
  let Q0 : Subgroup X := Q.map X'.subtype
  have hQ0E : Q0 ≤ E := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQE' hq
  have hQ0rank : 1 ≤ CFSG.Open.pRank 3 Q0 :=
    hQrank.trans (CFSG.SectionRank.pRank_le_map (by norm_num) X'.subtype
      X'.subtype_injective Q)
  have hNQ0 : Subgroup.normalizer (Q0 : Set X) ≤ Y :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQ0E hQ0rank).trans
      h.gamma_le
  have hmapN : (Subgroup.normalizer (Q : Set X')).map X'.subtype ≤
      Subgroup.normalizer (Q0 : Set X) :=
    Subgroup.le_normalizer_map (f := X'.subtype) (H := Q)
  intro n hn
  exact hNQ0 (hmapN (Subgroup.apply_coe_mem_map X'.subtype _ ⟨n, hn⟩))

theorem O97Red.rank23_subgroup {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    (h : O97Red X E Y S) (X' : Subgroup X) :
    ∀ T' : Subgroup X', T' ≠ ⊥ → IsPGroup 2 T' →
      CFSG.pRank 3 ↥(Subgroup.normalizer (T' : Set X')) ≤ 3 := by
  have hrank23open : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank 3 (Subgroup.normalizer (T : Set X)) ≤ 3 := by
    intro T hTne hT2
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Subgroup.normalizer (T : Set X)),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(Subgroup.normalizer (T : Set X))]
    exact h.rank23 T hTne hT2
  intro T' hT'ne hT'2
  let T : Subgroup X := T'.map X'.subtype
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hT'ne
    have hbot' : Subgroup.map X'.subtype T' = ⊥ := hbot
    have h := Subgroup.comap_map_eq_self_of_injective X'.subtype_injective T'
    rw [hbot'] at h
    simpa using h.symm
  have hT2 : IsPGroup 2 T := IsPGroup.map hT'2 X'.subtype
  have hNle : (Subgroup.normalizer (T' : Set X')).map X'.subtype ≤
      Subgroup.normalizer (T : Set X) :=
    Subgroup.le_normalizer_map (f := X'.subtype) (H := T')
  have h := (CFSG.SectionRank.pRank_le_map (by norm_num) X'.subtype X'.subtype_injective
    (Subgroup.normalizer (T' : Set X'))).trans
    ((CFSG.SectionRank.pRank_mono (by norm_num) hNle).trans (hrank23open T hTne hT2))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3
    ↥(Subgroup.normalizer (T' : Set X')),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (Subgroup.normalizer (T' : Set X'))]
  exact h

private theorem O98Red.shape_S_not_centralizing {X : Type} [Group X] {S L : Subgroup X}
    (hSL : ¬ S ≤ Subgroup.centralizer (L : Set X))
    (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    ¬ S.subgroupOf (Subgroup.normalizer (L : Set X)) ≤
      Subgroup.centralizer ((L.subgroupOf (Subgroup.normalizer (L : Set X))) :
        Set (Subgroup.normalizer (L : Set X))) := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hSX' : S ≤ X' := hSN
  change ¬ S.subgroupOf X' ≤
    Subgroup.centralizer ((L.subgroupOf X' : Subgroup X') : Set X')
  intro hSC
  apply hSL
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hs' : (⟨s, hSX' hs⟩ : X') ∈ S.subgroupOf X' := hs
  have hcent := Subgroup.mem_centralizer_iff.mp (hSC hs')
    (⟨l, hLX' hl⟩ : X') hl
  exact congrArg Subtype.val hcent

private theorem O97Red.shape_Y_subgroupOf_le_normalizer {X : Type} [Group X] [Finite X]
    {E Y S : Subgroup X} (h : O97Red X E Y S) {L : Subgroup X}
    (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    Y.subgroupOf (Subgroup.normalizer (L : Set X)) ≤
      Subgroup.normalizer
        ((S.subgroupOf (Subgroup.normalizer (L : Set X))) :
          Set (Subgroup.normalizer (L : Set X))) := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hSX' : S ≤ X' := hSN
  let S' : Subgroup X' := S.subgroupOf X'
  change Y.subgroupOf X' ≤ Subgroup.normalizer (S' : Set X')
  rw [← Subgroup.subgroupOf_normalizer_eq hSX']
  intro y hy
  exact h.Y_le_normalizer_S hy

theorem O97Red.pRank_rankThreeGamma_subgroupOf_le {X : Type} [Group X] [Finite X]
    {E Y S : Subgroup X} (h : O97Red X E Y S) (X' : Subgroup X) :
    CFSG.pRank 3 ↥(CFSG.Open.rankThreeGamma 1 3 (E.subgroupOf X')) ≤ 3 := by
  let E' : Subgroup X' := E.subgroupOf X'
  change CFSG.pRank 3 ↥(CFSG.Open.rankThreeGamma 1 3 E') ≤ 3
  have hΓle : CFSG.Open.rankThreeGamma 1 3 E' ≤ Y.subgroupOf X' :=
    h.rankThreeGamma_subgroupOf_le X'
  have hΓrank : CFSG.Open.pRank 3 (CFSG.Open.rankThreeGamma 1 3 E') ≤ 3 := by
    have hYrankY : CFSG.Open.pRank 3 Y ≤ 3 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥Y]
      exact h.rank_Y
    have hYrank : CFSG.Open.pRank 3 (Y.subgroupOf X') ≤ 3 := by
      have h1 := CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 3) X'.subtype
        X'.subtype_injective (Y.subgroupOf X')
      rw [Subgroup.subgroupOf_map_subtype] at h1
      exact h1.trans ((CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_left).trans
        hYrankY)
    exact (CFSG.SectionRank.pRank_mono (by norm_num) hΓle).trans hYrank
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3
      ↥(CFSG.Open.rankThreeGamma 1 3 E'),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (CFSG.Open.rankThreeGamma 1 3 E')]
  exact hΓrank

theorem O97Red.shape_k37 {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    (hK37 : KFactThreeSevenTwoThree) (h : O97Red X E Y S) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hSL : ¬ S ≤ Subgroup.centralizer (L : Set X))
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    (CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type
        ↥(L.subgroupOf (Subgroup.normalizer (L : Set X))) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card
        ↥((L.subgroupOf (Subgroup.normalizer (L : Set X))) ⊓
          Subgroup.normalizer
            ((S.subgroupOf (Subgroup.normalizer (L : Set X))) :
              Set (Subgroup.normalizer (L : Set X)))) → r = 2 ∨ r = 3) ∨
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type
        ↥(L.subgroupOf (Subgroup.normalizer (L : Set X))) := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hEX' : E ≤ X' := hEN
  have hSX' : S ≤ X' := hSN
  let K : Subgroup X' := L.subgroupOf X'
  let E' : Subgroup X' := E.subgroupOf X'
  let S' : Subgroup X' := S.subgroupOf X'
  change (CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥K ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(K ⊓ Subgroup.normalizer (S' : Set X')) →
        r = 2 ∨ r = 3) ∨
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type ↥K
  have hΓle : CFSG.Open.rankThreeGamma 1 3 E' ≤ Y.subgroupOf X' :=
    h.rankThreeGamma_subgroupOf_le X'
  have hΓN : CFSG.Open.rankThreeGamma 1 3 E' ≤
      Subgroup.normalizer (S' : Set X') :=
    hΓle.trans (O97Red.shape_Y_subgroupOf_le_normalizer h hSN)
  have hΓrank_group := h.pRank_rankThreeGamma_subgroupOf_le X'
  have hnotΓ : ¬ K ≤ CFSG.Open.rankThreeGamma 1 3 E' := by
    intro hKΓ
    have hKY : K ≤ Y.subgroupOf X' := hKΓ.trans hΓle
    have hLY' : L ≤ Y := by
      intro l hl
      exact hKY (show (⟨l, hLX' hl⟩ : X') ∈ K from hl)
    exact hLY hLY'
  exact hK37 (X := X') (K := K) (E := E') (S := S')
    (h.catalog.subgroup X') Subgroup.normal_in_normalizer
    (CFSG.LocalCores.component_overgroup hL hLX').1
    (h.pPrimeCore_subgroupOf_normalizer_eq_bot hL)
    (CFSG.Open.IsElemAbelian.subgroupOf h.elem_E X') (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX').toEquiv, h.card_E])
    (h.rank23_subgroup X') hΓrank_group hnotΓ
    (IsPGroup.of_equiv h.two_S (Subgroup.subgroupOfEquivOfLe hSX').symm)
    hΓN (O98Red.shape_S_not_centralizing hSL hSN)

theorem O98Red.Y_le_normalizer_S {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    {z : X} (h : O98Red X E Y S z) : Y ≤ Subgroup.normalizer (S : Set X) :=
  h.toO97Red.Y_le_normalizer_S

private theorem O98Red.shape_k37 {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (hK37 : KFactThreeSevenTwoThree) (h : O98Red X E Y S z) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hSL : ¬ S ≤ Subgroup.centralizer (L : Set X))
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    (CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type
        ↥(L.subgroupOf (Subgroup.normalizer (L : Set X))) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card
        ↥((L.subgroupOf (Subgroup.normalizer (L : Set X))) ⊓
          Subgroup.normalizer
            ((S.subgroupOf (Subgroup.normalizer (L : Set X))) :
              Set (Subgroup.normalizer (L : Set X)))) → r = 2 ∨ r = 3) ∨
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type
        ↥(L.subgroupOf (Subgroup.normalizer (L : Set X))) :=
  O97Red.shape_k37 hK37 h.toO97Red hL hLY hSL hEN hSN

private theorem O98Red.shape_prime {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    {z : X} (h : O98Red X E Y S z) {L : Subgroup X}
    (hSN : S ≤ Subgroup.normalizer (L : Set X))
    (hprimeK : ∀ r : ℕ, r.Prime → r ∣ Nat.card
      ↥((L.subgroupOf (Subgroup.normalizer (L : Set X))) ⊓
        Subgroup.normalizer
          ((S.subgroupOf (Subgroup.normalizer (L : Set X))) :
            Set (Subgroup.normalizer (L : Set X)))) → r = 2 ∨ r = 3) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(L ⊓ Y) → r = 2 ∨ r = 3 := by
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hSX' : S ≤ X' := hSN
  let K : Subgroup X' := L.subgroupOf X'
  let S' : Subgroup X' := S.subgroupOf X'
  intro r hr hdvd
  apply hprimeK r hr
  have hle : L ⊓ Y ≤ L ⊓ Subgroup.normalizer (S : Set X) :=
    inf_le_inf_left L h.Y_le_normalizer_S
  have hdvd1 : r ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (S : Set X)) :=
    hdvd.trans (Subgroup.card_dvd_of_le hle)
  have hsub : K ⊓ Subgroup.normalizer (S' : Set X') =
      (L ⊓ Subgroup.normalizer (S : Set X)).subgroupOf X' := by
    rw [← Subgroup.subgroupOf_normalizer_eq hSX']
    ext x
    change ((x : X) ∈ L ∧ (x : X) ∈ Subgroup.normalizer (S : Set X)) ↔
      (x : X) ∈ L ⊓ Subgroup.normalizer (S : Set X)
    rw [Subgroup.mem_inf]
  have hcardeq : Nat.card ↥(L ⊓ Subgroup.normalizer (S : Set X)) =
      Nat.card ↥(K ⊓ Subgroup.normalizer (S' : Set X')) := by
    rw [hsub]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_trans inf_le_left hLX')).toEquiv).symm
  rwa [hcardeq] at hdvd1

theorem O98Red.shape {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (hK37 : KFactThreeSevenTwoThree) (h : O98Red X E Y S z) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hSL : ¬ S ≤ Subgroup.centralizer (L : Set X))
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hSN : S ≤ Subgroup.normalizer (L : Set X)) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥L ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(L ⊓ Y) → r = 2 ∨ r = 3 := by
  rcases O98Red.shape_k37 hK37 h hL hLY hSL hEN hSN with ⟨h34K, hprimeK⟩ | hA11K
  · refine ⟨CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))) h34K, ?_⟩
    exact O98Red.shape_prime h hSN hprimeK
  · exact (O98Red.shape_not_isA11 h hL hA11K).elim

private def conjSub {X : Type*} [Group X] (g : X) (L : Subgroup X) : Subgroup X :=
  L.map (MulAut.conj g).toMonoidHom

private theorem isComponent_conjSub {X : Type*} [Group X] {L : Subgroup X}
    (hL : CFSG.IsComponent L) (g : X) : CFSG.IsComponent (conjSub g L) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL

private theorem conjSub_one {X : Type*} [Group X] (L : Subgroup X) :
    conjSub 1 L = L := by
  unfold conjSub
  ext x
  simp

private theorem conjSub_mul {X : Type*} [Group X] (a b : X) (L : Subgroup X) :
    conjSub (a * b) L = (conjSub b L).map (MulAut.conj a).toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem mem_normalizer_of_pow_seven {X : Type*} [Group X] {L : Subgroup X} {y : X}
    (hy : orderOf y = 7) {d : ℕ} (hd0 : 0 < d) (hd7 : d < 7)
    (hd : y ^ d ∈ Subgroup.normalizer (L : Set X)) :
    y ∈ Subgroup.normalizer (L : Set X) := by
  have hnot : ¬ 7 ∣ d := by
    intro h
    have := Nat.le_of_dvd hd0 h
    omega
  have hcop7 : Nat.Coprime 7 d :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr hnot
  have hcop : Nat.Coprime d 7 := Nat.coprime_comm.mp hcop7
  have hmem : y ∈ Subgroup.zpowers (y ^ d) := by
    rw [mem_zpowers_pow_iff, hy]
    exact hcop
  exact (Subgroup.zpowers_le.mpr hd) hmem

private theorem conjSub_pow_eq_of_eq {X : Type*} [Group X] {L : Subgroup X} {y : X}
    {i j : ℕ} (hij : i < j) (heq : conjSub (y ^ i) L = conjSub (y ^ j) L) :
    conjSub (y ^ (j - i)) L = L := by
  have h := congrArg (fun H => H.map (MulAut.conj (y ^ i)⁻¹).toMonoidHom) heq
  rw [← conjSub_mul (y ^ i)⁻¹ (y ^ i) L, inv_mul_cancel, conjSub_one,
    ← conjSub_mul (y ^ i)⁻¹ (y ^ j) L] at h
  have hpow : (y ^ i)⁻¹ * y ^ j = y ^ (j - i) := by
    have h1 : y ^ (j - i) * y ^ i = y ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hij)]
    rw [← h1]
    group
  rw [hpow] at h
  exact h.symm

private theorem eq_conjSub_imp_mem_normalizer {X : Type*} [Group X] {L : Subgroup X} {y : X}
    (hy : orderOf y = 7) {d : ℕ} (hd0 : 0 < d) (hd7 : d < 7)
    (heq : conjSub (y ^ d) L = L) : y ∈ Subgroup.normalizer (L : Set X) := by
  apply mem_normalizer_of_pow_seven hy hd0 hd7
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

private theorem conjSub_pow_ne {X : Type*} [Group X] {L : Subgroup X} {y : X}
    (hy : orderOf y = 7) (hyN : y ∉ Subgroup.normalizer (L : Set X)) :
    ∀ {i j : ℕ}, 1 ≤ i → i < j → j ≤ 4 → conjSub (y ^ i) L ≠ conjSub (y ^ j) L := by
  intro i j hi hij hj heq
  have hd0 : 0 < j - i := Nat.sub_pos_of_lt hij
  have hd7 : j - i < 7 := by omega
  have heq' := conjSub_pow_eq_of_eq (L := L) (y := y) hij heq
  exact hyN (eq_conjSub_imp_mem_normalizer hy hd0 hd7 heq')

private theorem conjSub_pow_ne_self {X : Type*} [Group X] {L : Subgroup X} {y : X}
    (hy : orderOf y = 7) (hyN : y ∉ Subgroup.normalizer (L : Set X))
    {i : ℕ} (hi0 : 0 < i) (hi4 : i ≤ 4) : conjSub (y ^ i) L ≠ L := by
  intro heq
  exact hyN (eq_conjSub_imp_mem_normalizer hy hi0 (by omega) heq)

private theorem commute_of_distinct_components {X : Type*} [Group X] [Finite X]
    {L M : Subgroup X}
    (hL : CFSG.IsComponent L) (hM : CFSG.IsComponent M) (hne : L ≠ M) {a b : X}
    (ha : a ∈ L) (hb : b ∈ M) : a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hL hM with h | h
  · exact (hne h).elim
  · have hc : L ≤ Subgroup.centralizer (M : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (hc ha) b hb).symm

private theorem two_and_three_dvd_card_of_isL34Type {L : Type*} [Group L] [Finite L]
    (hL34 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type L) :
    2 ∣ Nat.card L ∧ 3 ∣ Nat.card L := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hL34
  have hcard : Nat.card (L ⧸ Subgroup.center L) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactCardL34_holds d hd
  constructor
  · refine (show 2 ∣ 20160 by norm_num).trans ?_
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card (Subgroup.center L)
  · refine (show 3 ∣ 20160 by norm_num).trans ?_
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card (Subgroup.center L)

private theorem exists_orderOf_two_of_isL34Type {L : Type*} [Group L] [Finite L]
    (hL34 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type L) :
    ∃ t : L, orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 (two_and_three_dvd_card_of_isL34Type hL34).1

private theorem exists_order_three_noncentral {X : Type*} [Group X] [Finite X]
    {C : Subgroup X} (hC : CFSG.IsComponent C) (h3 : 3 ∣ Nat.card ↥C) :
    ∃ a : C, a ^ 3 = 1 ∧ a ∉ Subgroup.center C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥C := hC.1.1
  exact CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center
    (by norm_num : (3 : ℕ) ≠ 2) h3

private theorem extend_elemAbelian_of_component {X : Type*} [Group X] [Finite X]
    {C : Subgroup X} (hC : CFSG.IsComponent C) {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcent : E ≤ Subgroup.centralizer (C : Set X)) {a : X} (ha_mem : a ∈ C)
    (ha3 : a ^ 3 = 1) (ha_noncent : (⟨a, ha_mem⟩ : C) ∉ Subgroup.center C) :
    CFSG.Open.IsElemAbelian 3 (E ⊔ Subgroup.zpowers a) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers a) = Nat.card E * 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha_ne : a ≠ 1 := by
    intro h
    apply ha_noncent
    have h1 : (⟨a, ha_mem⟩ : C) = 1 := Subtype.ext h
    rw [h1]
    exact Subgroup.one_mem _
  have ha_ord : orderOf a = 3 := orderOf_eq_prime ha3 ha_ne
  have haE : a ∉ E := by
    intro haE
    apply ha_noncent
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEcent haE) (g : C) g.2)
  have hcommE : ∀ e ∈ E, Commute e a := by
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEcent he) a ha_mem).symm
  exact CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE ha_ord hcommE haE

private theorem zpowers_le_centralizer_of_mem_component {X : Type*} [Group X] [Finite X]
    {C D : Subgroup X} (hC : CFSG.IsComponent C) (hD : CFSG.IsComponent D)
    (hne : C ≠ D) {a : X} (ha : a ∈ C) :
    Subgroup.zpowers a ≤ Subgroup.centralizer (D : Set X) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro d hd
  exact (commute_of_distinct_components hC hD hne ha hd).symm

private theorem seven_elemAbelian_two {X : Type} [Group X] [Finite X]
    {C : ℕ → Subgroup X} (hComp1 : CFSG.IsComponent (C 1))
    (hComp2 : CFSG.IsComponent (C 2)) (hComp3 : CFSG.IsComponent (C 3))
    (hComp4 : CFSG.IsComponent (C 4))
    (h31 : 3 ∣ Nat.card (C 1)) (h32 : 3 ∣ Nat.card (C 2))
    (hne12 : C 1 ≠ C 2) (hne13 : C 1 ≠ C 3) (hne14 : C 1 ≠ C 4)
    (hne23 : C 2 ≠ C 3) (hne24 : C 2 ≠ C 4)
    {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hneL1 : C 1 ≠ L) (hneL2 : C 2 ≠ L) {tX : X} (htmem : tX ∈ L) :
    ∃ E2 : Subgroup X, IsElemAbelian 3 E2 ∧ Nat.card E2 = 9 ∧
      E2 ≤ Subgroup.centralizer (C 3 : Set X) ∧
      E2 ≤ Subgroup.centralizer (C 4 : Set X) ∧
      E2 ≤ Subgroup.centralizer ({tX} : Set X) := by
  obtain ⟨a1, ha1_3, ha1_nc⟩ := exists_order_three_noncentral hComp1 h31
  obtain ⟨a2, ha2_3, ha2_nc⟩ := exists_order_three_noncentral hComp2 h32
  have hpow1 : (a1 : X) ^ 3 = 1 := by simpa using congrArg Subtype.val ha1_3
  have hpow2 : (a2 : X) ^ 3 = 1 := by simpa using congrArg Subtype.val ha2_3
  have hnc1 : (⟨(a1 : X), a1.2⟩ : C 1) ∉ Subgroup.center (C 1) := by simpa using ha1_nc
  have hnc2 : (⟨(a2 : X), a2.2⟩ : C 2) ∉ Subgroup.center (C 2) := by simpa using ha2_nc
  have hE0 : IsElemAbelian 3 (⊥ : Subgroup X) := CFSG.SectionRank.isElemAbelian_bot 3
  obtain ⟨hE1elem, hE1card⟩ := extend_elemAbelian_of_component hComp1 hE0
    (bot_le : (⊥ : Subgroup X) ≤ Subgroup.centralizer (C 1 : Set X)) a1.2 hpow1 hnc1
  let E1 : Subgroup X := ⊥ ⊔ Subgroup.zpowers (a1 : X)
  have hE1cent2 : E1 ≤ Subgroup.centralizer (C 2 : Set X) :=
    sup_le bot_le (zpowers_le_centralizer_of_mem_component hComp1 hComp2 hne12 a1.2)
  have hE1cent3 : E1 ≤ Subgroup.centralizer (C 3 : Set X) :=
    sup_le bot_le (zpowers_le_centralizer_of_mem_component hComp1 hComp3 hne13 a1.2)
  have hE1cent4 : E1 ≤ Subgroup.centralizer (C 4 : Set X) :=
    sup_le bot_le (zpowers_le_centralizer_of_mem_component hComp1 hComp4 hne14 a1.2)
  have hE1card3 : Nat.card E1 = 3 := by
    rw [show Nat.card E1 = Nat.card ↥(⊥ ⊔ Subgroup.zpowers (a1 : X)) from rfl, hE1card]
    simp
  obtain ⟨hE2elem, hE2card⟩ := extend_elemAbelian_of_component hComp2 hE1elem
    hE1cent2 a2.2 hpow2 hnc2
  let E2 : Subgroup X := E1 ⊔ Subgroup.zpowers (a2 : X)
  have hE2cent3 : E2 ≤ Subgroup.centralizer (C 3 : Set X) :=
    sup_le hE1cent3 (zpowers_le_centralizer_of_mem_component hComp2 hComp3 hne23 a2.2)
  have hE2cent4 : E2 ≤ Subgroup.centralizer (C 4 : Set X) :=
    sup_le hE1cent4 (zpowers_le_centralizer_of_mem_component hComp2 hComp4 hne24 a2.2)
  have hE2card3 : Nat.card E2 = 9 := by
    rw [show Nat.card E2 = Nat.card ↥(E1 ⊔ Subgroup.zpowers (a2 : X)) from rfl,
      hE2card, hE1card3]
  have hE1centT : E1 ≤ Subgroup.centralizer ({tX} : Set X) :=
    sup_le bot_le ((zpowers_le_centralizer_of_mem_component hComp1 hL hneL1 a1.2).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htmem)))
  have hE2centT : E2 ≤ Subgroup.centralizer ({tX} : Set X) :=
    sup_le hE1centT ((zpowers_le_centralizer_of_mem_component hComp2 hL hneL2 a2.2).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htmem)))
  exact ⟨E2, hE2elem, hE2card3, hE2cent3, hE2cent4, hE2centT⟩

private theorem seven_elemAbelian_four {X : Type} [Group X] [Finite X]
    {C : ℕ → Subgroup X} (hComp3 : CFSG.IsComponent (C 3))
    (hComp4 : CFSG.IsComponent (C 4))
    (h33 : 3 ∣ Nat.card (C 3)) (h34 : 3 ∣ Nat.card (C 4)) (hne34 : C 3 ≠ C 4)
    {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hneL3 : C 3 ≠ L) (hneL4 : C 4 ≠ L) {tX : X} (htmem : tX ∈ L)
    {E2 : Subgroup X} (hE2elem : IsElemAbelian 3 E2) (hE2card : Nat.card E2 = 9)
    (hE2cent3 : E2 ≤ Subgroup.centralizer (C 3 : Set X))
    (hE2cent4 : E2 ≤ Subgroup.centralizer (C 4 : Set X))
    (hE2centT : E2 ≤ Subgroup.centralizer ({tX} : Set X)) :
    ∃ E4 : Subgroup X, IsElemAbelian 3 E4 ∧ Nat.card E4 = 3 ^ 4 ∧
      E4 ≤ Subgroup.centralizer ({tX} : Set X) := by
  obtain ⟨a3, ha3_3, ha3_nc⟩ := exists_order_three_noncentral hComp3 h33
  obtain ⟨a4, ha4_3, ha4_nc⟩ := exists_order_three_noncentral hComp4 h34
  have hpow3 : (a3 : X) ^ 3 = 1 := by simpa using congrArg Subtype.val ha3_3
  have hpow4 : (a4 : X) ^ 3 = 1 := by simpa using congrArg Subtype.val ha4_3
  have hnc3 : (⟨(a3 : X), a3.2⟩ : C 3) ∉ Subgroup.center (C 3) := by simpa using ha3_nc
  have hnc4 : (⟨(a4 : X), a4.2⟩ : C 4) ∉ Subgroup.center (C 4) := by simpa using ha4_nc
  obtain ⟨hE3elem, hE3card⟩ := extend_elemAbelian_of_component hComp3 hE2elem
    hE2cent3 a3.2 hpow3 hnc3
  let E3 : Subgroup X := E2 ⊔ Subgroup.zpowers (a3 : X)
  have hE3cent4 : E3 ≤ Subgroup.centralizer (C 4 : Set X) :=
    sup_le hE2cent4 (zpowers_le_centralizer_of_mem_component hComp3 hComp4 hne34 a3.2)
  have hE3card3 : Nat.card E3 = 27 := by
    rw [show Nat.card E3 = Nat.card ↥(E2 ⊔ Subgroup.zpowers (a3 : X)) from rfl,
      hE3card, hE2card]
  obtain ⟨hE4elem, hE4card⟩ := extend_elemAbelian_of_component hComp4 hE3elem
    hE3cent4 a4.2 hpow4 hnc4
  let E4 : Subgroup X := E3 ⊔ Subgroup.zpowers (a4 : X)
  have hE4card3 : Nat.card E4 = 3 ^ 4 := by
    rw [show Nat.card E4 = Nat.card ↥(E3 ⊔ Subgroup.zpowers (a4 : X)) from rfl,
      hE4card, hE3card3]
    norm_num
  have hE3centT : E3 ≤ Subgroup.centralizer ({tX} : Set X) :=
    sup_le hE2centT ((zpowers_le_centralizer_of_mem_component hComp3 hL hneL3 a3.2).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htmem)))
  have hE4centT : E4 ≤ Subgroup.centralizer ({tX} : Set X) :=
    sup_le hE3centT ((zpowers_le_centralizer_of_mem_component hComp4 hL hneL4 a4.2).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htmem)))
  exact ⟨E4, hE4elem, hE4card3, hE4centT⟩

private theorem seven_elemAbelian {X : Type} [Group X] [Finite X]
    {C : ℕ → Subgroup X} (hCcomp : ∀ i, CFSG.IsComponent (C i))
    (hC3 : ∀ i, 3 ∣ Nat.card (C i))
    (hne12 : C 1 ≠ C 2) (hne13 : C 1 ≠ C 3) (hne14 : C 1 ≠ C 4)
    (hne23 : C 2 ≠ C 3) (hne24 : C 2 ≠ C 4) (hne34 : C 3 ≠ C 4)
    {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hneL1 : C 1 ≠ L) (hneL2 : C 2 ≠ L) (hneL3 : C 3 ≠ L) (hneL4 : C 4 ≠ L)
    {tX : X} (htX_ord : orderOf tX = 2) (htmem : tX ∈ L) :
    4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Subgroup.zpowers tX : Set X)) := by
  obtain ⟨E2, hE2elem, hE2card, hE2cent3, hE2cent4, hE2centT⟩ :=
    seven_elemAbelian_two (hCcomp 1) (hCcomp 2) (hCcomp 3) (hCcomp 4)
      (hC3 1) (hC3 2) hne12 hne13 hne14 hne23 hne24 hL hneL1 hneL2 htmem
  obtain ⟨E4, hE4elem, hE4card, hE4centT⟩ :=
    seven_elemAbelian_four (hCcomp 3) (hCcomp 4) (hC3 3) (hC3 4) hne34
      hL hneL3 hneL4 htmem
      hE2elem hE2card hE2cent3 hE2cent4 hE2centT
  have hE4centZ : E4 ≤ Subgroup.centralizer (Subgroup.zpowers tX : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hE4centT
  refine CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) ?_ hE4elem ?_
  · exact hE4centZ.trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers tX : Set X))
  · exact hE4card

private theorem seven_aux {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (h : O98Red X E Y S z) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hL34 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥L) {y : X}
    (hy : y ^ 7 = 1) : y ∈ Subgroup.normalizer (L : Set X) := by
  by_contra hyN
  have hy_ne : y ≠ 1 := by
    intro h1
    exact hyN (by rw [h1]; exact Subgroup.one_mem _)
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hy_ord : orderOf y = 7 := orderOf_eq_prime hy hy_ne
  let C : ℕ → Subgroup X := fun i => conjSub (y ^ i) L
  have hCcomp : ∀ i, CFSG.IsComponent (C i) := fun i => isComponent_conjSub hL _
  have hCcard : ∀ i, Nat.card (C i) = Nat.card ↥L := by
    intro i
    exact Subgroup.card_map_of_injective (MulAut.conj (y ^ i)).injective
  have hC3 : ∀ i, 3 ∣ Nat.card (C i) := by
    intro i
    rw [hCcard i]
    exact (two_and_three_dvd_card_of_isL34Type hL34).2
  have hne12 : C 1 ≠ C 2 := conjSub_pow_ne hy_ord hyN (by norm_num) (by norm_num) (by norm_num)
  have hne13 : C 1 ≠ C 3 := conjSub_pow_ne hy_ord hyN (by norm_num) (by norm_num) (by norm_num)
  have hne14 : C 1 ≠ C 4 := conjSub_pow_ne hy_ord hyN (by norm_num) (by norm_num) (by norm_num)
  have hne23 : C 2 ≠ C 3 := conjSub_pow_ne hy_ord hyN (by norm_num) (by norm_num) (by norm_num)
  have hne24 : C 2 ≠ C 4 := conjSub_pow_ne hy_ord hyN (by norm_num) (by norm_num) (by norm_num)
  have hne34 : C 3 ≠ C 4 := conjSub_pow_ne hy_ord hyN (by norm_num) (by norm_num) (by norm_num)
  have hneL1 : C 1 ≠ L := conjSub_pow_ne_self hy_ord hyN (by norm_num) (by norm_num)
  have hneL2 : C 2 ≠ L := conjSub_pow_ne_self hy_ord hyN (by norm_num) (by norm_num)
  have hneL3 : C 3 ≠ L := conjSub_pow_ne_self hy_ord hyN (by norm_num) (by norm_num)
  have hneL4 : C 4 ≠ L := conjSub_pow_ne_self hy_ord hyN (by norm_num) (by norm_num)
  obtain ⟨t, ht_ord⟩ := exists_orderOf_two_of_isL34Type hL34
  let tX : X := (t : L)
  have htX_ord : orderOf tX = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht_ord
  have h4 := seven_elemAbelian hCcomp hC3 hne12 hne13 hne14 hne23 hne24 hne34 hL
    hneL1 hneL2 hneL3 hneL4 htX_ord t.2
  have htX_ne : tX ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htX_ord
    norm_num at htX_ord
  have hTne : Subgroup.zpowers tX ≠ ⊥ := by
    intro hbot
    exact htX_ne ((Subgroup.zpowers_eq_bot).mp hbot)
  have hT2 : IsPGroup 2 (Subgroup.zpowers tX) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, htX_ord]
    norm_num
  have h3 : CFSG.Open.pRank 3
      (Subgroup.normalizer (Subgroup.zpowers tX : Set X)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
        (Subgroup.normalizer (Subgroup.zpowers tX : Set X)),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 3
        ↥(Subgroup.normalizer (Subgroup.zpowers tX : Set X))]
    exact h.rank23 (Subgroup.zpowers tX) hTne hT2
  omega

theorem O98Red.seven {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (h : O98Red X E Y S z) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hL34 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥L) :
    ∀ y : X, y ^ 7 = 1 → y ∈ Subgroup.normalizer (L : Set X) :=
  fun y hy => seven_aux h hL hL34 hy

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
