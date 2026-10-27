module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddData
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlSuzUnique
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlBasic
import CFSG.GroupTheory.CentralizerMapMulEquiv
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.GroupTheory.PerfectLeSupCenter
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Classes
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {t : G}

private theorem center_centerQuotient_eq_bot (hS : L34SuzOddSetting A t) :
    Subgroup.center (↥A ⧸ Subgroup.center ↥A) = ⊥ := by
  have : Group.IsPerfect ↥A := isPerfect_of_l34SuzOddSetting hS
  exact Group.IsPerfect.center_quotient_center_eq_bot (G := ↥A)



private theorem eq_or_eq_one_of_commute_of_involution_of_sylow_card_two
    {H : Type*} [Group H] [Finite H] (hsylow : ∀ S : Sylow 2 H, Nat.card S = 2)
    {a b : H} (ha : a * a = 1) (hb : b * b = 1) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    a = 1 ∨ a = b := by
  classical
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  · right
    have horda : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha1
    have hordb : orderOf b = 2 := orderOf_eq_prime (by rwa [pow_two]) hb1
    have hcarda : Nat.card ↥(Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, horda]
    have hcardb : Nat.card ↥(Subgroup.zpowers b) = 2 := by rw [Nat.card_zpowers, hordb]
    have hpa : IsPGroup 2 (Subgroup.zpowers a) :=
      IsPGroup.of_card (p := 2) (n := 1) (by rw [hcarda]; norm_num)
    have hpb : IsPGroup 2 (Subgroup.zpowers b) :=
      IsPGroup.of_card (p := 2) (n := 1) (by rw [hcardb]; norm_num)
    have hacent : a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((show Commute a b from hab).zpow_right j).eq.symm
    have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set H) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hacent)
    have hjoinpg : IsPGroup 2 (Subgroup.zpowers b ⊔ Subgroup.zpowers a : Subgroup H) :=
      IsPGroup.to_sup_of_normal_left' hpb hpa hnorm
    obtain ⟨S2, hle⟩ := hjoinpg.exists_le_sylow
    have hS2card : Nat.card S2 = 2 := hsylow S2
    have hjoincard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers a : Subgroup H) ≤ 2 :=
      (Subgroup.card_le_of_le hle).trans (le_of_eq hS2card)
    have hsup_eq : Subgroup.zpowers a = Subgroup.zpowers b ⊔ Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
      rw [hcarda]
      exact hjoincard
    have hbmem : b ∈ Subgroup.zpowers a := by
      rw [hsup_eq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    rw [CFSG.ClassicalInvolution.QuaternionStructure.mem_zpowers_iff_of_orderOf_eq_two horda]
      at hbmem
    rcases hbmem with h1 | h1
    · exact absurd h1 hb1
    · exact h1.symm

private theorem eq_one_or_eq_t_of_involution_centralizer
    (hS : L34SuzOddSetting A t) {c : G}
    (hcC : c ∈ centralizer (A : Set G)) (hc2 : c * c = 1)
    (htc : t * c = c * t) : c = 1 ∨ c = t := by
  let CG : Subgroup G := centralizer (A : Set G)
  let C : ↥CG := ⟨c, hcC⟩
  let T : ↥CG := ⟨t, hS.t_mem⟩
  have hC2 : C * C = 1 := Subtype.ext (by simpa [C] using hc2)
  have hT2 : T * T = 1 := by
    apply Subtype.ext
    rw [← pow_two, ← hS.orderOf_t]
    exact pow_orderOf_eq_one t
  have hCT : C * T = T * C := Subtype.ext (by simpa [C, T] using htc.symm)
  have hT1 : T ≠ 1 := by
    intro h
    have h1 : t = 1 := congrArg Subtype.val h
    have h2 := hS.orderOf_t
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  rcases eq_or_eq_one_of_commute_of_involution_of_sylow_card_two hS.card_sylow hC2 hT2 hT1 hCT
    with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

private theorem sq_eq_one_of_conj_eq_of_center_eq_bot {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) {α : MulAut S} (hα2 : α * α = 1) {s : S}
    (hs : MulAut.conj s = α) : s * s = 1 := by
  have hconj : MulAut.conj (s * s) = 1 := by rw [map_mul, hs, hα2]
  have hmem : s * s ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := congrArg (fun φ : MulAut S => φ y) hconj
    rw [MulAut.conj_apply, MulAut.one_apply] at hy
    have hyz : (s * s) * y = y * (s * s) := by
      calc (s * s) * y = ((s * s) * y * (s * s)⁻¹) * (s * s) := by group
        _ = y * (s * s) := by rw [hy]
    exact hyz.symm
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem map_mulAut_conj_pow_apply {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (u w : X) (k : ℕ) :
    f (((MulAut.conj u) ^ k) w) = ((MulAut.conj (f u)) ^ k) (f w) := by
  rw [← map_pow MulAut.conj u k, ← map_pow MulAut.conj (f u) k, ← map_pow f u k,
    MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem centerQuotientHom_conj_pow_card {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card (Subgroup.center A))) (φx : MulAut A) (hφx2 : φx * φx = 1)
    (u : A) (s : A ⧸ Subgroup.center A)
    (hu : (QuotientGroup.mk' (Subgroup.center A)) u = s)
    (hs : MulAut.conj s =
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom A φx) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom A
        (MulAut.conj (u ^ Nat.card (Subgroup.center A))) =
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom A φx := by
  classical
  let qA : A →* A ⧸ Subgroup.center A := QuotientGroup.mk' (Subgroup.center A)
  let α := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom A φx
  have hα2 : α * α = 1 := by rw [show α = _ from rfl, ← map_mul, hφx2, map_one]
  have hαk : α ^ Nat.card (Subgroup.center A) = α := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_add, pow_mul, show α ^ 2 = 1 by rw [pow_two, hα2], one_pow, one_mul,
      pow_one]
  ext y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center A) y
  change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
      (MulAut.conj (u ^ Nat.card (Subgroup.center A))) (qA w) =
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient φx (qA w)
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  have hconjs : (MulAut.conj s) ^ Nat.card (Subgroup.center A) = α := by
    rw [hs, hαk]
  calc qA (MulAut.conj (u ^ Nat.card (Subgroup.center A)) w)
      = qA (((MulAut.conj u) ^ Nat.card (Subgroup.center A)) w) := by
        rw [map_pow MulAut.conj u]
    _ = ((MulAut.conj (qA u)) ^ Nat.card (Subgroup.center A)) (qA w) :=
        map_mulAut_conj_pow_apply qA u w _
    _ = ((MulAut.conj s) ^ Nat.card (Subgroup.center A)) (qA w) := by rw [hu]
    _ = α (qA w) := by rw [hconjs]
    _ = qA (φx w) := rfl

private theorem exists_involution_lift_centerQuotient
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2)
    (hxA : x ∈ normalizer (A : Set G))
    (hInner : ∃ s : ↥A ⧸ center ↥A,
      MulAut.conj s = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)) :
    ∃ a : ↥A, a * a = 1 ∧
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A (MulAut.conj a) =
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) := by
  classical
  let S := ↥A ⧸ center ↥A
  let qA : ↥A →* S := QuotientGroup.mk' (center ↥A)
  let φx : MulAut ↥A := Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩
  let α : MulAut S :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A φx
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← hx]
    exact pow_orderOf_eq_one x
  have hφx2 : φx * φx = 1 := by
    rw [← map_mul]
    have h1 : (⟨x, hxA⟩ : normalizer (A : Set G)) * ⟨x, hxA⟩ = 1 := by
      ext
      simpa [pow_two] using hx2
    rw [h1, map_one]
  have hα2 : α * α = 1 := by rw [← map_mul, hφx2, map_one]
  obtain ⟨s, hs⟩ := hInner
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center ↥A) s
  have hs2 : s * s = 1 :=
    sq_eq_one_of_conj_eq_of_center_eq_bot (center_centerQuotient_eq_bot hS) hα2 hs
  have hu2 : u * u ∈ center ↥A := by
    rw [← QuotientGroup.eq_one_iff]
    change qA (u * u) = 1
    rw [map_mul, hu, hs2]
  have hpow : (u * u) ^ Nat.card (center ↥A) = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥A)) (x := ⟨u * u, hu2⟩)
    exact congrArg Subtype.val this
  refine ⟨u ^ Nat.card (center ↥A), ?_, ?_⟩
  · calc u ^ Nat.card (center ↥A) * u ^ Nat.card (center ↥A)
        = (u * u) ^ Nat.card (center ↥A) := ((Commute.refl u).mul_pow _).symm
      _ = 1 := hpow
  · exact centerQuotientHom_conj_pow_card hS.odd_card_center φx hφx2 u s hu hs

private theorem isComponent_centralizer_t_of_l34SuzOddSetting (hS : L34SuzOddSetting A t) :
    IsComponent (A.subgroupOf (centralizer ({t} : Set G))) := by
  let C : Subgroup G := centralizer ({t} : Set G)
  have hAC : A ≤ C := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp hS.t_mem y hy).symm
  have hAnorm : (A.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAC]
    intro g hg
    exact CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
      hS.standard.standardComponentIsStandard hS.t_mem hS.orderOf_t
      (Subgroup.mem_centralizer_singleton_iff.mp hg)
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hAC).symm hS.standard.1, hAnorm.isSubnormal⟩

omit [Finite G] in
private theorem commute_of_commutator_subgroupOf_eq_bot {C A P : Subgroup G} (hAC : A ≤ C)
    (hPA : P ≤ A) (hcomm : ⁅P.subgroupOf C, A.subgroupOf C⁆ = ⊥) :
    ∀ y ∈ A, ∀ p ∈ P, y * p = p * y := by
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro y hy p hp
  have h1 : (⟨y, hAC hy⟩ : ↥C) * ⟨p, hAC (hPA hp)⟩ =
      ⟨p, hAC (hPA hp)⟩ * ⟨y, hAC hy⟩ :=
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_subgroupOf.mpr hp))
      _ (Subgroup.mem_subgroupOf.mpr hy)
  exact congrArg Subtype.val h1

omit [Finite G] in
private theorem le_map_center_of_commutes {A P : Subgroup G} (hPA : P ≤ A)
    (hcomm : ∀ y ∈ A, ∀ p ∈ P, y * p = p * y) :
    P ≤ (Subgroup.center ↥A).map A.subtype := by
  intro p hp
  refine ⟨⟨p, hPA hp⟩, ?_, rfl⟩
  change (⟨p, hPA hp⟩ : ↥A) ∈ Subgroup.center ↥A
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact hcomm y y.2 p hp

omit [Finite G] in
private theorem isMulCommutative_of_le_map_center {P A : Subgroup G}
    (hPZ : P ≤ (Subgroup.center ↥A).map A.subtype) : IsMulCommutative ↥P := by
  refine ⟨⟨fun p q => Subtype.ext ?_⟩⟩
  obtain ⟨zp, hzp, hzpeq⟩ := hPZ p.2
  obtain ⟨zq, hzq, hzqeq⟩ := hPZ q.2
  have h1 : zp * zq = zq * zp := (Subgroup.mem_center_iff.mp hzp zq).symm
  have hpq : (p : G) * (q : G) = (zp : G) * (zq : G) := by
    rw [← hzpeq, ← hzqeq]
    rfl
  have hqp : (zq : G) * (zp : G) = (q : G) * (p : G) := by
    rw [← hzqeq, ← hzpeq]
    rfl
  calc (p : G) * (q : G) = (zp : G) * (zq : G) := hpq
    _ = (zq : G) * (zp : G) := by simpa using congrArg Subtype.val h1
    _ = (q : G) * (p : G) := hqp

omit [Finite G] in
private theorem false_of_isQuasisimple_of_le_map_center {P A : Subgroup G}
    (hPq : IsQuasisimple ↥P) (hPZ : P ≤ (Subgroup.center ↥A).map A.subtype) : False := by
  have hcommP : IsMulCommutative ↥P := isMulCommutative_of_le_map_center hPZ
  have hntP : Nontrivial ↥P := CFSG.LocalCores.isQuasisimple_nontrivial hPq
  exact @not_subsingleton ↥P hntP
    (@Group.IsPerfect.subsingleton_of_isMulCommutative ↥P _ hPq.1 hcommP)

private theorem ne_one_of_isComponent
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2) (hxt : x * t = t * x)
    {P : Subgroup G} (hPA : P ≤ A) (hPx : P ≤ centralizer ({x} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPL : IsL34Type (↥P ⧸ center ↥P)) {a c : G} (hcC : c ∈ centralizer (A : Set G))
    (hc : c = 1 ∨ c = t) (hxac : x = a * c) : a ≠ 1 := by
  intro ha1
  have hxt' : x = t := by
    rcases hc with rfl | rfl
    · rw [ha1, one_mul] at hxac
      exfalso
      have hxne : x ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hx
        norm_num at hx
      exact hxne hxac
    · rw [ha1, one_mul] at hxac
      exact hxac
  let C : Subgroup G := centralizer ({t} : Set G)
  have hPt : P ≤ C := by
    change P ≤ centralizer ({t} : Set G)
    rw [← hxt']
    exact hPx
  have hcompC : IsComponent (P.subgroupOf C) := by
    change IsComponent (P.subgroupOf (centralizer ({t} : Set G)))
    rw [← hxt']
    exact hcomp
  have hAC : A ≤ C := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp hS.t_mem y hy).symm
  have hAcomp : IsComponent (A.subgroupOf C) :=
    isComponent_centralizer_t_of_l34SuzOddSetting hS
  rcases CFSG.LocalCores.distinct_components_commute hcompC hAcomp with hEq | hcomm
  ·
    have hPA' : P = A := by
      have h := congrArg (Subgroup.map C.subtype) hEq
      rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPt,
        Subgroup.subgroupOf_map_subtype, inf_of_le_left hAC] at h
    have hPcard : Nat.card (↥P ⧸ center ↥P) = 20160 :=
      CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hPL
    obtain ⟨eS⟩ := hS.suz
    have hAcard : Nat.card (↥A ⧸ center ↥A) = 448345497600 := by
      rw [Nat.card_congr eS.toEquiv]
      exact CFSG.Sporadic.Suz.card_Suz
    rw [hPA', hAcard] at hPcard
    norm_num at hPcard
  ·
    have hPq : IsQuasisimple ↥P :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPt) hcompC.1
    exact false_of_isQuasisimple_of_le_map_center hPq
      (le_map_center_of_commutes hPA
        (commute_of_commutator_subgroupOf_eq_bot hAC hPA hcomm))

private theorem centralizes_of_normalizerMonoidHom_eq_one
    (hS : L34SuzOddSetting A t) {c : G} (hcN : c ∈ normalizer (A : Set G))
    (hquot : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
      (Subgroup.normalizerMonoidHom (H := A) ⟨c, hcN⟩) = 1) :
    c ∈ centralizer (A : Set G) := by
  have hφc : Subgroup.normalizerMonoidHom (H := A) ⟨c, hcN⟩ = 1 :=
    @CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp ↥A _
      (isPerfect_of_l34SuzOddSetting hS) (Subgroup.normalizerMonoidHom (H := A) ⟨c, hcN⟩) (by
        change CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨c, hcN⟩) = 1
        exact hquot)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := congrArg (fun φ : MulAut ↥A => (φ ⟨y, hy⟩ : ↥A)) hφc
  have h1 := congrArg Subtype.val h
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  simp only [MulAut.one_apply, Subgroup.coe_mk] at h1
  calc y * c = (c * y * c⁻¹) * c := by rw [h1]
    _ = c * y := by group

omit [Finite G] in
private theorem sq_eq_one_of_eq_mul_of_involution {x a c : G} (haA : a ∈ A)
    (hcC : c ∈ centralizer (A : Set G)) (ha2 : a * a = 1) (hx2 : x * x = 1)
    (hxac : x = a * c) : c * c = 1 := by
  have hcomm_ac : c * a * c⁻¹ = a := by
    have h := Subgroup.mem_centralizer_iff.mp hcC a haA
    calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [h]
      _ = a := by group
  have hsq : x * x = (a * a) * (c * c) := by
    calc x * x = (a * c) * (a * c) := by rw [hxac]
      _ = a * (c * a * c⁻¹) * (c * c) := by group
      _ = (a * a) * (c * c) := by rw [hcomm_ac]
  calc c * c = (a * a)⁻¹ * (x * x) := by rw [hsq]; group
    _ = 1 := by simp [ha2, hx2]

private theorem commute_t_of_eq_mul (hS : L34SuzOddSetting A t) {x a c : G}
    (hxt : x * t = t * x) (haA : a ∈ A) (hxac : x = a * c) : t * c = c * t := by
  have hta : a * t = t * a := Subgroup.mem_centralizer_iff.mp hS.t_mem a haA
  have hta_inv : t * a⁻¹ = a⁻¹ * t := by
    calc t * a⁻¹ = a⁻¹ * (a * t) * a⁻¹ := by group
      _ = a⁻¹ * (t * a) * a⁻¹ := by rw [hta]
      _ = a⁻¹ * t := by group
  calc t * c = t * (a⁻¹ * x) := by simp only [hxac]; group
    _ = (t * a⁻¹) * x := by group
    _ = (a⁻¹ * t) * x := by rw [hta_inv]
    _ = a⁻¹ * (t * x) := by group
    _ = a⁻¹ * (x * t) := by rw [hxt]
    _ = (a⁻¹ * x) * t := by group
    _ = c * t := by simp only [hxac]; group

private theorem exists_involution_mul_centralizer
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2) (hxt : x * t = t * x)
    (hxA : x ∈ normalizer (A : Set G))
    (hInner : ∃ s : ↥A ⧸ center ↥A,
      MulAut.conj s = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)) :
    ∃ a c : G, a ∈ A ∧ a * a = 1 ∧ c ∈ centralizer (A : Set G) ∧ c * c = 1 ∧
      x = a * c ∧ (c = 1 ∨ c = t) := by
  classical
  obtain ⟨aA, ha2A, haction⟩ := exists_involution_lift_centerQuotient hS hx hxA hInner
  let a : G := (aA : G)
  let nx : normalizer (A : Set G) := ⟨x, hxA⟩
  let na : normalizer (A : Set G) := ⟨a, Subgroup.le_normalizer aA.2⟩
  let c : G := a⁻¹ * x
  have hcN : c ∈ normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).mul_mem
      ((Subgroup.normalizer (A : Set G)).inv_mem (Subgroup.le_normalizer aA.2)) hxA
  let nc : normalizer (A : Set G) := ⟨c, hcN⟩
  have hnc : nc = na⁻¹ * nx := by
    ext
    simp [nc, na, nx, c, a]
  have hφna : Subgroup.normalizerMonoidHom (H := A) na = MulAut.conj aA := by
    ext y
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [MulAut.conj_apply, na, a]
  have hcenter : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
      (Subgroup.normalizerMonoidHom (H := A) nc) =
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) na))⁻¹ *
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) nx) := by
    rw [hnc, map_mul (Subgroup.normalizerMonoidHom (H := A)),
      map_inv (Subgroup.normalizerMonoidHom (H := A)),
      map_mul (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A),
      map_inv (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A)]
  have hφc : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
      (Subgroup.normalizerMonoidHom (H := A) nc) = 1 := by
    rw [hcenter, hφna, haction]
    exact inv_mul_cancel _
  have hcC : c ∈ centralizer (A : Set G) :=
    centralizes_of_normalizerMonoidHom_eq_one hS hcN hφc
  have ha2 : a * a = 1 := congrArg Subtype.val ha2A
  have hxac : x = a * c := by simp [c]
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← hx]
    exact pow_orderOf_eq_one x
  have hc2 : c * c = 1 := sq_eq_one_of_eq_mul_of_involution aA.2 hcC ha2 hx2 hxac
  have hct : t * c = c * t := commute_t_of_eq_mul hS hxt aA.2 hxac
  exact ⟨a, c, aA.2, ha2, hcC, hc2, hxac,
    eq_one_or_eq_t_of_involution_centralizer hS hcC hc2 hct⟩


private theorem card_centralizer_suzM_eq_inf (x : ↥suzM) :
    Nat.card (Subgroup.centralizer ({x} : Set ↥suzM)) =
      Nat.card ↥(suzM ⊓ Subgroup.centralizer
        ({(x : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782)))) := by
  let Z : Subgroup (Equiv.Perm (Fin 1782)) :=
    suzM ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782)))
  have h : Z.subgroupOf suzM = Subgroup.centralizer ({x} : Set ↥suzM) := by
    ext m
    simp [Z, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rw [show suzM ⊓ Subgroup.centralizer
      ({(x : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) = Z from rfl, ← h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Z ≤ suzM from inf_le_left)).toEquiv

private theorem card_centralizer_suzM_suzInv
    (i : ℕ) (hi : i < 4) (hmem : suzInv i ∈ suzM) :
    Nat.card (Subgroup.centralizer ({⟨suzInv i, hmem⟩} : Set ↥suzM)) =
      invInnerOrders.getD i 0 := by
  rw [card_centralizer_suzM_eq_inf]
  exact CFSG.ComponentClassification.AS81.card_suzM_inf_centralizer hi

private theorem exists_conj_base_of_card_centralizer
    {S : Type*} [Group S] (e : S ≃* ↥suzM) (h0 : suzInv 0 ∈ suzM) {y : S}
    (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyC : Nat.card (Subgroup.centralizer ({y} : Set S)) = 161280) :
    ∃ s : S, s * y * s⁻¹ = e.symm ⟨suzInv 0, h0⟩ := by
  classical
  obtain ⟨horder, -, -, -, -, h0mem, h1mem, -, -, -, -⟩ :=
    CFSG.Sporadic.SuzOddCore.CTUC_Suz_four_exact_involution_centralizers
  have h0mem' : suzInv 0 ∈ suzM := h0mem
  have h1mem' : suzInv 1 ∈ suzM := h1mem
  have hey2 : orderOf (e y) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      simpa using congrArg e hy2
    · intro h
      exact hy1 (e.injective (by simpa using h))
  have hey2' : orderOf ((e y : ↥suzM) : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hey2
  rcases CFSG.ComponentClassification.AS81.suzM_conj_cases (e y).2 hey2' with
    ⟨m, hm, hconj⟩ | ⟨m, hm, hconj⟩
  ·
    refine ⟨(e.symm ⟨m, hm⟩)⁻¹, ?_⟩
    apply e.injective
    have hconjM : e y = ⟨m, hm⟩ * ⟨suzInv 0, h0mem'⟩ * ⟨m, hm⟩⁻¹ := by
      apply Subtype.ext
      simpa using hconj
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hconjM]
    group
  ·
    exfalso
    have hey_eq : e y = ⟨m, hm⟩ * ⟨suzInv 1, h1mem'⟩ * ⟨m, hm⟩⁻¹ := by
      apply Subtype.ext
      simpa using hconj
    have hcardM : Nat.card (Subgroup.centralizer ({e y} : Set ↥suzM)) =
        Nat.card (Subgroup.centralizer
          ({⟨suzInv 1, h1mem'⟩} : Set ↥suzM)) := by
      rw [hey_eq, ← CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton (⟨m, hm⟩ : ↥suzM)
          (⟨suzInv 1, h1mem'⟩ : ↥suzM),
        Subgroup.card_map_of_injective (MulAut.conj (⟨m, hm⟩ : ↥suzM)).injective]
    rw [card_centralizer_suzM_suzInv 1 (by norm_num) h1mem'] at hcardM
    have h3317 : invInnerOrders.getD 1 0 = 3317760 := by simp [invInnerOrders]
    rw [h3317] at hcardM
    have hcardS : Nat.card (Subgroup.centralizer ({y} : Set S)) =
        Nat.card (Subgroup.centralizer ({e y} : Set ↥suzM)) :=
      CFSG.GroupTheory.card_centralizer_singleton_mulEquiv e y
    rw [hyC, hcardM] at hcardS
    norm_num at hcardS

private theorem card_eq_161280_of_dvd_seven
    {S : Type*} [Group S] (e : S ≃* ↥suzM) {y : S}
    (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({y} : Set S))) :
    Nat.card (Subgroup.centralizer ({y} : Set S)) = 161280 := by
  classical
  obtain ⟨-, -, -, -, -, h0mem, h1mem, -, -, -, -⟩ :=
    CFSG.Sporadic.SuzOddCore.CTUC_Suz_four_exact_involution_centralizers
  have hey2 : orderOf (e y) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      simpa using congrArg e hy2
    · intro h
      exact hy1 (e.injective (by simpa using h))
  have hey2' : orderOf ((e y : ↥suzM) : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hey2
  rcases CFSG.ComponentClassification.AS81.suzM_conj_cases (e y).2 hey2' with
    ⟨m, hm, hconj⟩ | ⟨m, hm, hconj⟩
  · have hey_eq : e y = ⟨m, hm⟩ * ⟨suzInv 0, h0mem⟩ * ⟨m, hm⟩⁻¹ := by
      apply Subtype.ext
      simpa using hconj
    have hcardM : Nat.card (Subgroup.centralizer ({e y} : Set ↥suzM)) =
        Nat.card (Subgroup.centralizer ({⟨suzInv 0, h0mem⟩} : Set ↥suzM)) := by
      rw [hey_eq, ← CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton (⟨m, hm⟩ : ↥suzM)
          (⟨suzInv 0, h0mem⟩ : ↥suzM),
        Subgroup.card_map_of_injective (MulAut.conj (⟨m, hm⟩ : ↥suzM)).injective]
    rw [card_centralizer_suzM_suzInv 0 (by norm_num) h0mem] at hcardM
    have h161 : invInnerOrders.getD 0 0 = 161280 := by simp [invInnerOrders]
    rw [h161] at hcardM
    rw [CFSG.GroupTheory.card_centralizer_singleton_mulEquiv e y, hcardM]
  · exfalso
    have hey_eq : e y = ⟨m, hm⟩ * ⟨suzInv 1, h1mem⟩ * ⟨m, hm⟩⁻¹ := by
      apply Subtype.ext
      simpa using hconj
    have hcardM : Nat.card (Subgroup.centralizer ({e y} : Set ↥suzM)) =
        Nat.card (Subgroup.centralizer ({⟨suzInv 1, h1mem⟩} : Set ↥suzM)) := by
      rw [hey_eq, ← CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton (⟨m, hm⟩ : ↥suzM)
          (⟨suzInv 1, h1mem⟩ : ↥suzM),
        Subgroup.card_map_of_injective (MulAut.conj (⟨m, hm⟩ : ↥suzM)).injective]
    rw [card_centralizer_suzM_suzInv 1 (by norm_num) h1mem] at hcardM
    have h3317 : invInnerOrders.getD 1 0 = 3317760 := by simp [invInnerOrders]
    rw [h3317] at hcardM
    have hcardS : Nat.card (Subgroup.centralizer ({y} : Set S)) =
        Nat.card (Subgroup.centralizer ({e y} : Set ↥suzM)) :=
      CFSG.GroupTheory.card_centralizer_singleton_mulEquiv e y
    rw [hcardM] at hcardS
    rw [hcardS] at h7
    norm_num at h7





omit [Finite G] in
private theorem odd_card_center_map_center
    {P : Subgroup G} (hPA : P ≤ A) (hPq : IsQuasisimple ↥P)
    (hPodd : Odd (Nat.card (center ↥P))) :
    Odd (Nat.card (Subgroup.center ↥((P.subgroupOf A).map
      (QuotientGroup.mk' (center ↥A))))) := by
  classical
  let P_A : Subgroup ↥A := P.subgroupOf A
  let Pbar : Subgroup (↥A ⧸ center ↥A) := P_A.map (QuotientGroup.mk' (center ↥A))
  have hP_A_q : IsQuasisimple ↥P_A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPA).symm hPq
  let f : ↥P_A →* ↥Pbar :=
    ((QuotientGroup.mk' (center ↥A)).comp P_A.subtype).codRestrict Pbar fun a =>
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (center ↥A)) a.2
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfker : f.ker ≤ Subgroup.center ↥P_A := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hz1 : (QuotientGroup.mk' (center ↥A) (z : ↥P_A) : ↥A ⧸ center ↥A) = 1 := by
      have := MonoidHom.mem_ker.mp hz
      exact congrArg Subtype.val this
    have hzZ : ((z : ↥P_A) : ↥A) ∈ center ↥A := (QuotientGroup.eq_one_iff _).mp hz1
    exact Subgroup.mem_center_iff.mp hzZ ((w : ↥P_A) : ↥A)
  have hcenter_quot :=
    CFSG.LocalCores.quasisimple_central_quotient hP_A_q f.ker hfker
  have hcenter : Subgroup.center ↥Pbar = (Subgroup.center ↥P_A).map f := by
    let e := QuotientGroup.quotientKerEquivOfSurjective f hfsurj
    have hmap := Subgroup.map_center_eq e
    rw [← hmap, hcenter_quot.2.2, Subgroup.map_map]
    congr 1
  have hdvd : Nat.card (Subgroup.center ↥Pbar) ∣ Nat.card (Subgroup.center ↥P) := by
    rw [hcenter]
    refine (Subgroup.card_map_dvd (Subgroup.center ↥P_A) f).trans ?_
    exact Nat.card_congr (Subgroup.centerCongr
      (Subgroup.subgroupOfEquivOfLe hPA)).toEquiv ▸ Nat.dvd_refl _
  exact hPodd.of_dvd_nat hdvd

omit [Finite G] in
private theorem card_centerQuotient_map_center
    {P : Subgroup G} (hPA : P ≤ A) (hPq : IsQuasisimple ↥P)
    (hPL : IsL34Type (↥P ⧸ center ↥P)) :
    Nat.card (((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) ⧸
      Subgroup.center ((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))) = 20160 := by
  classical
  let P_A : Subgroup ↥A := P.subgroupOf A
  let Pbar : Subgroup (↥A ⧸ center ↥A) := P_A.map (QuotientGroup.mk' (center ↥A))
  have hP_A_q : IsQuasisimple ↥P_A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPA).symm hPq
  let f : ↥P_A →* ↥Pbar :=
    ((QuotientGroup.mk' (center ↥A)).comp P_A.subtype).codRestrict Pbar fun a =>
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (center ↥A)) a.2
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfker : f.ker ≤ Subgroup.center ↥P_A := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hz1 : (QuotientGroup.mk' (center ↥A) (z : ↥P_A) : ↥A ⧸ center ↥A) = 1 := by
      have := MonoidHom.mem_ker.mp hz
      exact congrArg Subtype.val this
    have hzZ : ((z : ↥P_A) : ↥A) ∈ center ↥A := (QuotientGroup.eq_one_iff _).mp hz1
    exact Subgroup.mem_center_iff.mp hzZ ((w : ↥P_A) : ↥A)
  have e1 : (↥P_A ⧸ Subgroup.center ↥P_A) ≃* (↥Pbar ⧸ Subgroup.center ↥Pbar) :=
    @CFSG.ComponentClassification.PerfectCentralQuotient.equivalence ↥P_A ↥Pbar _ _
      hP_A_q.1 f hfsurj hfker
  let e2 : ↥P_A ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPA
  have e3 : (↥P_A ⧸ Subgroup.center ↥P_A) ≃* (↥P ⧸ Subgroup.center ↥P) :=
    QuotientGroup.congr (Subgroup.center ↥P_A) (Subgroup.center ↥P) e2
      (Subgroup.map_center_eq e2)
  have hPcard : Nat.card (↥P ⧸ Subgroup.center ↥P) = 20160 :=
    CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hPL
  rw [← Nat.card_congr e1.toEquiv, Nat.card_congr e3.toEquiv, hPcard]

omit [Finite G] in
private theorem l34SuzOddData_conj {V K : Subgroup G} {y h : G}
    (hD : L34SuzOddData A V K y) (hh : h ∈ A) :
    L34SuzOddData A (V.map (MulAut.conj h).toMonoidHom)
      (K.map (MulAut.conj h).toMonoidHom) (h * y * h⁻¹) := by
  classical
  let φ : MulAut G := MulAut.conj h
  let V' : Subgroup G := V.map φ.toMonoidHom
  let K' : Subgroup G := K.map φ.toMonoidHom
  have hAφ : A.map φ.toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
  have hV'le : V' ≤ A := by
    calc V' = (V.map φ.toMonoidHom) := rfl
      _ ≤ A.map φ.toMonoidHom := Subgroup.map_mono hD.le_A
      _ = A := hAφ
  let φA : MulAut ↥A := Subgroup.normalizerMonoidHom (H := A) ⟨h, Subgroup.le_normalizer hh⟩
  have hφA : ∀ k : ↥A, (φA k : G) = h * (k : G) * h⁻¹ := by
    intro k
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hqconj : ∀ k : ↥A,
      (QuotientGroup.mk' (center ↥A)) (φA k) =
        (MulAut.conj ((QuotientGroup.mk' (center ↥A)) ⟨h, hh⟩))
          ((QuotientGroup.mk' (center ↥A)) k) := by
    intro k
    have h1 : (QuotientGroup.mk' (center ↥A)) (φA k) =
        (QuotientGroup.mk' (center ↥A)) (⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹) := by
      congr 1
    rfl
  have hyV : V.map (MulAut.conj y).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hD.y_normalizes
  have hV'set : (V' : Set G) = φ.toMonoidHom '' (V : Set G) := by
    ext z
    simp [V']
  have hcent : A ⊓ Subgroup.centralizer (V' : Set G) =
      (A ⊓ Subgroup.centralizer (V : Set G)).map φ.toMonoidHom := by
    rw [hV'set, ← CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv φ (V : Set G),
      Subgroup.map_inf_eq A (Subgroup.centralizer (V : Set G)) φ.toMonoidHom φ.injective,
      hAφ]
  refine {
    le_A := hV'le
    card_V := by
      change Nat.card V' = 4
      rw [show V' = V.map φ.toMonoidHom from rfl,
        Subgroup.card_map_of_injective φ.injective, hD.card_V]
    mul_self := ?_
    card_centralizer := ?_
    K_eq := ?_
    perfect := ?_
    l34 := ?_
    card_image := ?_
    y_mem := A.mul_mem (A.mul_mem hh hD.y_mem) (A.inv_mem hh)
    y_centralizes := ?_
    odd_orderOf_y := ?_
    y_normalizes := ?_
    y_moves := ?_ }
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_mul, hD.mul_self w hw, map_one]
  · intro v hv hv1
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have hw1 : w ≠ 1 := by
      intro h1
      exact hv1 (by rw [h1, map_one])
    have hclass : (((⟨(MulEquiv.toMonoidHom (MulAut.conj h)) w,
          hV'le (Subgroup.mem_map_of_mem φ.toMonoidHom hw)⟩ : ↥A)) : ↥A ⧸ center ↥A) =
        (((φA ⟨w, hD.le_A hw⟩ : ↥A)) : ↥A ⧸ center ↥A) := by
      congr 1
    rw [hclass]
    change Nat.card (Subgroup.centralizer
      ({(QuotientGroup.mk' (center ↥A)) (φA ⟨w, hD.le_A hw⟩)} :
        Set (↥A ⧸ center ↥A))) = 161280
    rw [hqconj, MulAut.conj_apply, ← CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton
        ((QuotientGroup.mk' (center ↥A)) ⟨h, hh⟩)
        ((QuotientGroup.mk' (center ↥A)) ⟨w, hD.le_A hw⟩),
      Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hD.card_centralizer w hw hw1
  · change K.map φ.toMonoidHom = ⁅A ⊓ Subgroup.centralizer (V' : Set G),
      A ⊓ Subgroup.centralizer (V' : Set G)⁆
    rw [hD.K_eq, hcent, ← Subgroup.map_commutator]
  · rw [show K.map (MulAut.conj h).toMonoidHom = K' from rfl, ← Subgroup.map_commutator,
      hD.perfect]
  · let eK : ↥K' ≃* ↥K := (Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective).symm
    have eQ : (↥K' ⧸ center ↥K') ≃* (↥K ⧸ center ↥K) :=
      QuotientGroup.congr (Subgroup.center ↥K') (Subgroup.center ↥K) eK
        (Subgroup.map_center_eq eK)
    exact hD.l34.of_mulEquiv eQ.symm
  · have hKsub : K'.subgroupOf A = (K.subgroupOf A).map φA.toMonoidHom := by
      ext x
      constructor
      · intro hx
        change x.1 ∈ K' at hx
        obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr ⟨⟨k, le_A_of_l34SuzOddData hD hk⟩, hk, ?_⟩
        apply Subtype.ext
        change (φA ⟨k, le_A_of_l34SuzOddData hD hk⟩ : G) = x.1
        rw [hφA ⟨k, le_A_of_l34SuzOddData hD hk⟩]
        simpa [φ, MulAut.conj_apply] using hkx
      · rintro ⟨k, hk, hfl⟩
        have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
        have hflG : (φA k : G) = x.1 := congrArg Subtype.val hfl
        change x.1 ∈ K'
        rw [← hflG, hφA k]
        exact Subgroup.mem_map_of_mem φ.toMonoidHom hkK
    have himg : (K'.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) =
        ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).map
          (MulAut.conj ((QuotientGroup.mk' (center ↥A)) ⟨h, hh⟩)).toMonoidHom := by
      rw [hKsub, Subgroup.map_map, Subgroup.map_map]
      have hcomp : ((QuotientGroup.mk' (center ↥A)).comp φA.toMonoidHom) =
          ((MulAut.conj ((QuotientGroup.mk' (center ↥A)) ⟨h, hh⟩)).toMonoidHom.comp
            (QuotientGroup.mk' (center ↥A))) := by
        ext k
        exact hqconj k
      rw [hcomp]
    rw [show K.map (MulAut.conj h).toMonoidHom = K' from rfl, himg,
      Subgroup.card_map_of_injective (MulAut.conj _).injective, hD.card_image]
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm := Subgroup.mem_centralizer_iff.mp hD.y_centralizes k hk
    change (h * k * h⁻¹) * (h * y * h⁻¹) = (h * y * h⁻¹) * (h * k * h⁻¹)
    rw [show (h * k * h⁻¹) * (h * y * h⁻¹) = h * (k * y) * h⁻¹ from by group,
      show (h * y * h⁻¹) * (h * k * h⁻¹) = h * (y * k) * h⁻¹ from by group, hcomm]
  · have hord : orderOf (h * y * h⁻¹) = orderOf y :=
      (SemiconjBy.orderOf_eq h (by unfold SemiconjBy; group)).symm
    rw [hord]
    exact hD.odd_orderOf_y
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change V'.map (MulAut.conj (h * y * h⁻¹)).toMonoidHom = V'
    rw [show V' = V.map φ.toMonoidHom from rfl, Subgroup.map_map]
    have hcomp : ((MulAut.conj (h * y * h⁻¹)).toMonoidHom.comp φ.toMonoidHom) =
        (φ.toMonoidHom.comp (MulAut.conj y).toMonoidHom) := by
      ext z
      simp [φ, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map, hyV]
  · intro v hv hv1
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have hw1 : w ≠ 1 := by
      intro h1
      exact hv1 (by rw [h1, map_one])
    intro hconj
    apply hD.y_moves w hw hw1
    have hconj' : h * (y * w * y⁻¹) * h⁻¹ = h * w * h⁻¹ := by
      simpa [φ, MulAut.conj_apply, mul_assoc] using hconj
    have h2 : (y * w * y⁻¹) * h⁻¹ = w * h⁻¹ :=
      mul_left_cancel (show h * ((y * w * y⁻¹) * h⁻¹) = h * (w * h⁻¹) by
        simpa [mul_assoc] using hconj')
    exact mul_right_cancel h2

omit [Finite G] in
private theorem sq_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

omit [Finite G] in
private theorem sq_eq_one_normalizerMonoidHom {x : G} (hx : orderOf x = 2)
    (hxA : x ∈ normalizer (A : Set G)) :
    (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) *
      (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) = 1 := by
  rw [← map_mul]
  have h1 : (⟨x, hxA⟩ : normalizer (A : Set G)) * ⟨x, hxA⟩ = 1 := by
    ext
    simpa [pow_two] using sq_eq_one_of_orderOf_eq_two hx
  rw [h1, map_one]

private def centerQuotient_fixSubHom {x : G} (hxA : x ∈ normalizer (A : Set G)) :
    ↥(A ⊓ centralizer ({x} : Set G)) →*
      ↥(CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩))) :=
  { toFun := fun y =>
      ⟨(QuotientGroup.mk' (center ↥A)) ⟨y.1, y.2.1⟩, by
        rw [CFSG.Sporadic.Schreier.mem_fixSub]
        rw [show (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
              (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩))
            ((QuotientGroup.mk' (center ↥A)) ⟨y.1, y.2.1⟩) =
            (QuotientGroup.mk' (center ↥A))
              ((Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) ⟨y.1, y.2.1⟩) from
          CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
            (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) ⟨y.1, y.2.1⟩]
        congr 1
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
        rw [← hcomm]
        group⟩,
    map_one' := by
      apply Subtype.ext
      exact map_one (QuotientGroup.mk' (center ↥A)),
    map_mul' := by
      intro a b
      apply Subtype.ext
      exact map_mul (QuotientGroup.mk' (center ↥A)) ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ }

omit [Finite G] in
private theorem map_centerQuotient_le_fixSub {x : G} (hxA : x ∈ normalizer (A : Set G))
    {P : Subgroup G} (hPx : P ≤ centralizer ({x} : Set G)) :
    (P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ≤
      CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)) := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
  rw [CFSG.Sporadic.Schreier.mem_fixSub]
  let φx : MulAut ↥A := Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩
  let α : MulAut (↥A ⧸ center ↥A) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A φx
  change α ((QuotientGroup.mk' (center ↥A)) p) = (QuotientGroup.mk' (center ↥A)) p
  rw [show α ((QuotientGroup.mk' (center ↥A)) p) =
      (QuotientGroup.mk' (center ↥A)) (φx p) from
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk φx p]
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
    (hPx (Subgroup.mem_subgroupOf.mp hp))
  rw [← hcomm]
  group

omit [Finite G] in
private theorem map_centerQuotient_le_centralizer {a : G} (haA : a ∈ A)
    {P : Subgroup G} (hPa : P ≤ centralizer ({a} : Set G)) :
    (P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ≤
      Subgroup.centralizer ({(QuotientGroup.mk' (center ↥A)) ⟨a, haA⟩} :
        Set (↥A ⧸ center ↥A)) := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (hPa (Subgroup.mem_subgroupOf.mp hp))

omit [Finite G] in
private theorem map_centerQuotient_le_centralizer_of_l34SuzOddData
    {V K : Subgroup G} {y : G} (hD : L34SuzOddData A V K y) {a : G} (haV : a ∈ V) :
    (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ≤
      Subgroup.centralizer ({(QuotientGroup.mk' (center ↥A)) ⟨a, hD.le_A haV⟩} :
        Set (↥A ⧸ center ↥A)) := by
  intro z hz
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← map_mul, ← map_mul]
  congr 1
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hKa : (k : G) ∈ centralizer ({a} : Set G) :=
    le_centralizer_of_l34SuzOddData hD haV hkK
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp hKa

omit [Finite G] in
private theorem isQuasisimple_fixSub_of_isComponent
    {x : G} (hxA : x ∈ normalizer (A : Set G)) {P : Subgroup G} (hPA : P ≤ A)
    (hPx : P ≤ centralizer ({x} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPbar_le : (P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ≤
      CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩))) :
    IsQuasisimple ↥(((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).subgroupOf
      (CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)))) := by
  let P_A : Subgroup ↥A := P.subgroupOf A
  let qA : ↥A →* (↥A ⧸ center ↥A) := QuotientGroup.mk' (center ↥A)
  let Pbar : Subgroup (↥A ⧸ center ↥A) := P_A.map qA
  have hP_A_q : IsQuasisimple ↥P_A := by
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hPx).trans
        (Subgroup.subgroupOfEquivOfLe hPA).symm) hcomp.1
  have hPbar_q : IsQuasisimple ↥Pbar := by
    let f : ↥P_A →* ↥Pbar :=
      (qA.comp P_A.subtype).codRestrict Pbar fun a =>
        Subgroup.mem_map_of_mem qA a.2
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hfker : f.ker ≤ Subgroup.center ↥P_A := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hz1 : (qA (z : ↥P_A) : (↥A ⧸ center ↥A)) = 1 := by
        have := MonoidHom.mem_ker.mp hz
        exact congrArg Subtype.val this
      have hzZ : ((z : ↥P_A) : ↥A) ∈ center ↥A :=
        (QuotientGroup.eq_one_iff _).mp hz1
      exact Subgroup.mem_center_iff.mp hzZ ((w : ↥P_A) : ↥A)
    exact CFSG.LocalCores.isQuasisimple_of_surjective hP_A_q f hfsurj hfker
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hPbar_le).symm hPbar_q

omit [Finite G] in
private theorem map_centerQuotient_subgroupOf_eq
    {x : G} (hxA : x ∈ normalizer (A : Set G)) {P : Subgroup G} (hPA : P ≤ A)
    (hPx : P ≤ centralizer ({x} : Set G)) :
    (P.subgroupOf (A ⊓ centralizer ({x} : Set G))).map (centerQuotient_fixSubHom hxA) =
      (((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).subgroupOf
        (CFSG.Sporadic.Schreier.fixSub
          (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
            (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)))) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' (center ↥A)) hp)
  · intro hy
    have hy' : (y : ↥A ⧸ center ↥A) ∈ (P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) :=
      Subgroup.mem_subgroupOf.mp hy
    obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy'
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    refine ⟨⟨(p : G), ⟨hPA hpP, hPx hpP⟩⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hpP
    · apply Subtype.ext
      change (QuotientGroup.mk' (center ↥A)) ⟨(p : G), _⟩ = (y : ↥A ⧸ center ↥A)
      exact hpy

private theorem exists_fixed_mem_coset_centerQuotient
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2)
    (hxA : x ∈ normalizer (A : Set G)) (y : ↥A)
    (hz : (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩))
      ((QuotientGroup.mk' (center ↥A)) y) = (QuotientGroup.mk' (center ↥A)) y) :
    ∃ n ∈ center ↥A,
      (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) (y * n) = y * n ∧
      ((y * n : ↥A) : G) ∈ A ⊓ centralizer ({x} : Set G) := by
  let φx : MulAut ↥A := Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩
  have hfix : (QuotientGroup.mk' (center ↥A)) (φx y) =
      (QuotientGroup.mk' (center ↥A)) y := by
    rw [show (QuotientGroup.mk' (center ↥A)) (φx y) =
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A φx)
          ((QuotientGroup.mk' (center ↥A)) y) from
      (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk φx y).symm]
    exact hz
  have hg : y⁻¹ * φx y ∈ center ↥A := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (center ↥A)) (y⁻¹ * φx y) = 1
    rw [map_mul, map_inv, hfix, inv_mul_cancel]
  have hN : ∀ n ∈ center ↥A, φx n ∈ center ↥A := by
    intro n hn
    have hmap : (center ↥A).map φx.toMonoidHom = center ↥A :=
      Subgroup.map_center_eq φx
    rw [← hmap]
    exact Subgroup.mem_map_of_mem φx.toMonoidHom hn
  have hφx2 : φx * φx = 1 := sq_eq_one_normalizerMonoidHom hx hxA
  have hcop : Nat.Coprime (orderOf φx) (Nat.card (center ↥A)) := by
    have hdvd : orderOf φx ∣ 2 := orderOf_dvd_of_pow_eq_one hφx2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · rw [h]; exact Nat.coprime_one_left _
    · rw [h]; exact Nat.coprime_two_left.mpr hS.odd_card_center
  obtain ⟨n, hn, hfixn⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime_mulAut (center ↥A) φx hN hg hcop
  have hnC : ((y * n : ↥A) : G) ∈ A ⊓ centralizer ({x} : Set G) := by
    refine ⟨A.mul_mem y.2 n.2, ?_⟩
    change ((y * n : ↥A) : G) ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hv := congrArg Subtype.val hfixn
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hv
    have hv' : x * (↑(y * n) : G) = (↑(y * n) : G) * x := by
      calc x * (↑(y * n) : G) = (x * ↑(y * n) * x⁻¹) * x := by group
        _ = (↑(y * n) : G) * x := by rw [hv]
    exact hv'.symm
  exact ⟨n, hn, hfixn, hnC⟩

private theorem surjective_centerQuotient_fixSubHom
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2)
    (hxA : x ∈ normalizer (A : Set G)) :
    Function.Surjective (centerQuotient_fixSubHom hxA) := by
  intro z
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center ↥A) (z : ↥A ⧸ center ↥A)
  have hzy : (QuotientGroup.mk' (center ↥A)) y = (z : ↥A ⧸ center ↥A) := hy
  let φx : MulAut ↥A := Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩
  let α : MulAut (↥A ⧸ center ↥A) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A φx
  have hz : (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A φx)
      ((QuotientGroup.mk' (center ↥A)) y) = (QuotientGroup.mk' (center ↥A)) y := by
    change α ((QuotientGroup.mk' (center ↥A)) y) = (QuotientGroup.mk' (center ↥A)) y
    rw [hzy]
    exact z.2
  obtain ⟨n, hn, -, hnC⟩ := exists_fixed_mem_coset_centerQuotient hS hx hxA y hz
  refine ⟨⟨((y * n : ↥A) : G), hnC⟩, ?_⟩
  apply Subtype.ext
  change (QuotientGroup.mk' (center ↥A)) (y * n) = (z : ↥A ⧸ center ↥A)
  rw [map_mul]
  have hn1 : (QuotientGroup.mk' (center ↥A)) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [hn1, mul_one, hzy]

omit [Finite G] in
private theorem card_centerQuotient_fixSub
    {x : G} (hxA : x ∈ normalizer (A : Set G)) {P : Subgroup G} (hPA : P ≤ A)
    (hPx : P ≤ centralizer ({x} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPL : IsL34Type (↥P ⧸ center ↥P))
    (hPbar_le : (P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ≤
      CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)))
    {B : Subgroup (CFSG.Sporadic.Schreier.fixSub
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)))}
    (hB : B = ((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).subgroupOf
      (CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)))) :
    Nat.card (B ⧸ center B) = 20160 := by
  rw [hB]
  have hPq : IsQuasisimple ↥P :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPx) hcomp.1
  have hPbar_card : Nat.card (((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) ⧸
      Subgroup.center ((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))) = 20160 :=
    card_centerQuotient_map_center hPA hPq hPL
  let B' : Subgroup (CFSG.Sporadic.Schreier.fixSub
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩))) :=
    ((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).subgroupOf
      (CFSG.Sporadic.Schreier.fixSub
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
          (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩)))
  change Nat.card (B' ⧸ center B') = 20160
  let e4 : ↥B' ≃* ↥((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) :=
    Subgroup.subgroupOfEquivOfLe hPbar_le
  have e5 : (↥B' ⧸ center ↥B') ≃*
      (↥((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) ⧸
        center ↥((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))) :=
    QuotientGroup.congr (Subgroup.center ↥B')
      (Subgroup.center ↥((P.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))) e4
      (Subgroup.map_center_eq e4)
  rw [Nat.card_congr e5.toEquiv, hPbar_card]

private theorem isInner_centerQuotient
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2)
    (hxA : x ∈ normalizer (A : Set G)) {P : Subgroup G} (hPA : P ≤ A)
    (hPx : P ≤ centralizer ({x} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPL : IsL34Type (↥P ⧸ center ↥P)) :
    ∃ s : ↥A ⧸ center ↥A,
      MulAut.conj s = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A
        (Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩) := by
  classical
  let S := ↥A ⧸ center ↥A
  let qA : ↥A →* S := QuotientGroup.mk' (center ↥A)
  let φx : MulAut ↥A := Subgroup.normalizerMonoidHom (H := A) ⟨x, hxA⟩
  let α : MulAut S := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥A φx
  have hα2 : α * α = 1 := by
    rw [← map_mul, sq_eq_one_normalizerMonoidHom hx hxA, map_one]
  by_contra hout
  have hPbar_le : (P.subgroupOf A).map qA ≤ CFSG.Sporadic.Schreier.fixSub α :=
    map_centerQuotient_le_fixSub hxA hPx
  let B : Subgroup (CFSG.Sporadic.Schreier.fixSub α) :=
    ((P.subgroupOf A).map qA).subgroupOf (CFSG.Sporadic.Schreier.fixSub α)
  have hBcomp : IsComponent B := by
    refine ⟨?_, ?_⟩
    · exact isQuasisimple_fixSub_of_isComponent hxA hPA hPx hcomp hPbar_le
    · let C : Subgroup G := A ⊓ centralizer ({x} : Set G)
      have hPsub : (P.subgroupOf C).IsSubnormal :=
        CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (B := P) (L := C)
          (K := centralizer ({x} : Set G)) inf_le_right hcomp.2
      have himg : (P.subgroupOf C).map (centerQuotient_fixSubHom hxA) = B :=
        map_centerQuotient_subgroupOf_eq hxA hPA hPx
      rw [← himg]
      exact hPsub.map (surjective_centerQuotient_fixSubHom hS hx hxA)
  have hBcard : Nat.card (B ⧸ center B) = 20160 :=
    card_centerQuotient_fixSub hxA hPA hPx hcomp hPL hPbar_le rfl
  have houtcard :=
    CFSG.ComponentClassification.SolMax.suzOuterComponentsInput_holds (G := S) hS.suz α hα2
      hout B hBcomp
  rcases houtcard with h | h
  · rw [hBcard] at h
    norm_num at h
  · rw [hBcard] at h
    norm_num at h

private theorem eq_of_l34SuzOddData_of_isComponent
    (hS : L34SuzOddSetting A t) {V K : Subgroup G} {y a : G} (hD : L34SuzOddData A V K y)
    {P : Subgroup G} (hPA : P ≤ A) (haV : a ∈ V) (ha1 : a ≠ 1)
    (hPa : P ≤ centralizer ({a} : Set G)) (hPq : IsQuasisimple ↥P)
    (hPodd : Odd (Nat.card (center ↥P))) (hPL : IsL34Type (↥P ⧸ center ↥P)) :
    P = K := by
  classical
  let S := ↥A ⧸ center ↥A
  let qA : ↥A →* S := QuotientGroup.mk' (center ↥A)
  let aA : ↥A := ⟨a, hD.le_A haV⟩
  let abar : S := qA aA
  have ha2 : a * a = 1 := hD.mul_self a haV
  have habar2 : abar * abar = 1 := by
    dsimp [abar, aA]
    rw [← map_mul, ← map_one qA]
    congr 1
    exact Subtype.ext ha2
  have hCcard : Nat.card (Subgroup.centralizer ({abar} : Set S)) = 161280 := by
    simpa [abar, aA, qA, S] using hD.card_centralizer a haV ha1
  let P_A : Subgroup ↥A := P.subgroupOf A
  let Pbar : Subgroup S := P_A.map qA
  let K_A : Subgroup ↥A := K.subgroupOf A
  let Kbar : Subgroup S := K_A.map qA
  have hP_A_q : IsQuasisimple ↥P_A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPA).symm hPq
  have hP_A_perf : ⁅P_A, P_A⁆ = P_A := Subgroup.isPerfect_iff.mp hP_A_q.1
  have hPbar_perf : ⁅Pbar, Pbar⁆ = Pbar := by
    rw [show Pbar = P_A.map qA from rfl, ← Subgroup.map_commutator, hP_A_perf]
  have hK_A_perf : ⁅K_A, K_A⁆ = K_A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (le_A_of_l34SuzOddData hD), hD.perfect]
  have hKbar_perf : ⁅Kbar, Kbar⁆ = Kbar := by
    rw [show Kbar = K_A.map qA from rfl, ← Subgroup.map_commutator, hK_A_perf]
  have hPbar_le : Pbar ≤ Subgroup.centralizer ({abar} : Set S) := by
    simpa [Pbar, abar, aA, qA, S] using
      map_centerQuotient_le_centralizer (hD.le_A haV) hPa
  have hKbar_le : Kbar ≤ Subgroup.centralizer ({abar} : Set S) := by
    simpa [Kbar, abar, aA, qA, S] using
      map_centerQuotient_le_centralizer_of_l34SuzOddData hD haV
  have hquot : Nat.card (Pbar ⧸ Subgroup.center Pbar) = 20160 :=
    card_centerQuotient_map_center hPA hPq hPL
  have hZodd : Odd (Nat.card (Subgroup.center Pbar)) :=
    odd_card_center_map_center hPA hPq hPodd
  have hcardPbar : Nat.card Pbar = 20160 * Nat.card (Subgroup.center Pbar) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Pbar), hquot]
  have hPbar_dvd : Nat.card Pbar ∣ 161280 := by
    rw [← hCcard]
    let C : Subgroup S := Subgroup.centralizer ({abar} : Set S)
    have hcard : Nat.card ↥(Pbar.subgroupOf C) = Nat.card Pbar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Pbar ≤ C from hPbar_le)).toEquiv
    exact hcard ▸ Subgroup.card_subgroup_dvd_card (Pbar.subgroupOf C)
  have hZ1 : Nat.card (Subgroup.center Pbar) = 1 := by
    have hZ_dvd_8 : Nat.card (Subgroup.center Pbar) ∣ 8 := by
      apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 20160)
      have h := hPbar_dvd
      rw [hcardPbar, show 161280 = 20160 * 8 by norm_num] at h
      exact h
    have hZle : Nat.card (Subgroup.center Pbar) ≤ 8 := Nat.le_of_dvd (by norm_num) hZ_dvd_8
    obtain ⟨m, hm⟩ := hZodd
    have hmle : m ≤ 3 := by omega
    interval_cases m
    · omega
    · norm_num [hm] at hZ_dvd_8
    · norm_num [hm] at hZ_dvd_8
    · norm_num [hm] at hZ_dvd_8
  have hPbar_card : Nat.card Pbar = 20160 := by
    rw [hcardPbar, hZ1, mul_one]
  have hEqBar : Pbar = Kbar :=
    eq_of_perfect_of_card_eq_of_isSporadic_suz hS.suz habar2 hCcard hPbar_le hKbar_le
      hPbar_perf hKbar_perf hPbar_card hD.card_image
  have hPK : P_A = K_A := by
    have hle1 : P_A ≤ K_A ⊔ Subgroup.center ↥A := by
      intro p hp
      have hmem : qA p ∈ Kbar := by
        rw [← hEqBar]
        exact Subgroup.mem_map_of_mem qA hp
      obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp hmem
      rw [Subgroup.mem_sup_of_normal_right]
      refine ⟨k, hk, k⁻¹ * p, ?_, by group⟩
      rw [← QuotientGroup.eq_one_iff]
      change qA (k⁻¹ * p) = 1
      rw [map_mul, map_inv, hkp, inv_mul_cancel]
    have hle2 : K_A ≤ P_A ⊔ Subgroup.center ↥A := by
      intro k hk
      have hmem : qA k ∈ Pbar := by
        rw [hEqBar]
        exact Subgroup.mem_map_of_mem qA hk
      obtain ⟨p, hp, hkp⟩ := Subgroup.mem_map.mp hmem
      rw [Subgroup.mem_sup_of_normal_right]
      refine ⟨p, hp, p⁻¹ * k, ?_, by group⟩
      rw [← QuotientGroup.eq_one_iff]
      change qA (p⁻¹ * k) = 1
      rw [map_mul, map_inv, hkp, inv_mul_cancel]
    have h1 : P_A ≤ K_A := CFSG.le_of_perfect_of_le_sup_center hK_A_perf hP_A_perf hle1
    have h2 : K_A ≤ P_A := CFSG.le_of_perfect_of_le_sup_center hP_A_perf hK_A_perf hle2
    exact le_antisymm h1 h2
  have hPKG : P = K := by
    have hmap : P_A.map A.subtype = K_A.map A.subtype :=
      congrArg (fun H : Subgroup ↥A => H.map A.subtype) hPK
    rwa [Subgroup.map_subgroupOf_eq_of_le hPA,
      Subgroup.map_subgroupOf_eq_of_le (le_A_of_l34SuzOddData hD)] at hmap
  exact hPKG

theorem exists_l34SuzOddData_of_isComponent_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2) (hxt : x * t = t * x)
    (hxA : x ∈ normalizer (A : Set G)) {P : Subgroup G} (hPA : P ≤ A)
    (hPx : P ≤ centralizer ({x} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPodd : Odd (Nat.card (center ↥P))) (hPL : IsL34Type (↥P ⧸ center ↥P)) :
    ∃ (V : Subgroup G) (y u : G), L34SuzOddData A V P y ∧ u ∈ V ∧ u ≠ 1 ∧
      (x = u ∨ x = t * u) := by
  classical
  obtain ⟨V₀, K₀, y₀, hD₀⟩ := exists_l34SuzOddData hS.suz hS.odd_card_center
  obtain ⟨s, hs⟩ := isInner_centerQuotient hS hx hxA hPA hPx hcomp hPL
  obtain ⟨a, c, haA, ha2, hcC, hc2, hxac, hc⟩ :=
    exists_involution_mul_centralizer hS hx hxt hxA ⟨s, hs⟩
  have ha1 : a ≠ 1 := ne_one_of_isComponent hS hx hxt hPA hPx hcomp hPL hcC hc hxac
  have hPa : P ≤ centralizer ({a} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hax : a = x * c⁻¹ := by rw [hxac]; group
    have hxcomm : p * x = x * p :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPx hp)
    have hccomm : p * c = c * p :=
      Subgroup.mem_centralizer_iff.mp hcC p (hPA hp)
    have hcinv : p * c⁻¹ = c⁻¹ * p :=
      ((show Commute p c from hccomm).inv_right).eq
    calc p * a = p * (x * c⁻¹) := by rw [hax]
      _ = x * p * c⁻¹ := by
          rw [show p * (x * c⁻¹) = (p * x) * c⁻¹ by group, hxcomm]
      _ = x * (p * c⁻¹) := by group
      _ = x * (c⁻¹ * p) := by rw [hcinv]
      _ = (x * c⁻¹) * p := by group
      _ = a * p := by rw [hax]
  let S := ↥A ⧸ center ↥A
  let qA : ↥A →* S := QuotientGroup.mk' (center ↥A)
  let aA : ↥A := ⟨a, haA⟩
  let abar : S := qA aA
  have ha2A : aA * aA = 1 := Subtype.ext ha2
  have habar2 : abar * abar = 1 := by
    dsimp [abar, aA]
    rw [← map_mul, ← map_one qA]
    congr 1
  have habar1 : abar ≠ 1 := by
    intro h
    apply ha1
    exact congrArg Subtype.val
      (CFSG.EvenSporadicStandard.Induction.Closing.eq_one_of_sq_eq_one_of_odd_center
        hS.odd_card_center ((QuotientGroup.eq_one_iff aA).mp h) ha2A)
  let Pbar : Subgroup S := (P.subgroupOf A).map qA
  have hPbar_le : Pbar ≤ Subgroup.centralizer ({abar} : Set S) := by
    simpa [Pbar, abar, aA, qA, S] using
      map_centerQuotient_le_centralizer haA hPa
  have hPq : IsQuasisimple ↥P :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPx) hcomp.1
  have hquot : Nat.card (Pbar ⧸ Subgroup.center Pbar) = 20160 :=
    card_centerQuotient_map_center hPA hPq hPL
  have h7quot : 7 ∣ Nat.card (Pbar ⧸ Subgroup.center Pbar) := by
    rw [hquot]
    norm_num
  have h7bar : 7 ∣ Nat.card Pbar :=
    h7quot.trans (Subgroup.card_quotient_dvd_card (Subgroup.center Pbar))
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer ({abar} : Set S)) := by
    let C : Subgroup S := Subgroup.centralizer ({abar} : Set S)
    have hcard : Nat.card ↥(Pbar.subgroupOf C) = Nat.card Pbar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Pbar ≤ C from hPbar_le)).toEquiv
    have h7sub : 7 ∣ Nat.card ↥(Pbar.subgroupOf C) := by
      rwa [hcard]
    exact h7sub.trans (Subgroup.card_subgroup_dvd_card (Pbar.subgroupOf C))
  obtain ⟨eS⟩ := hS.suz
  let e : S ≃* ↥suzM := eS.trans suzEquivM
  obtain ⟨-, -, -, -, -, h0mem, -, -, -, -, -⟩ :=
    CFSG.Sporadic.SuzOddCore.CTUC_Suz_four_exact_involution_centralizers
  have hCcard : Nat.card (Subgroup.centralizer ({abar} : Set S)) = 161280 :=
    card_eq_161280_of_dvd_seven e habar2 habar1 h7
  obtain ⟨s₁, hs₁⟩ := exists_conj_base_of_card_centralizer e h0mem habar2 habar1 hCcard
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    have hc := hD₀.card_V
    rw [hbot, Subgroup.card_bot] at hc
    norm_num at hc
  have hntV : Nontrivial ↥V₀ := (Subgroup.nontrivial_iff_ne_bot V₀).mpr hV0ne
  obtain ⟨v, hv, hv1⟩ := @Subgroup.exists_ne_one_of_nontrivial _ _ V₀ hntV
  let vA : ↥A := ⟨v, hD₀.le_A hv⟩
  let vbar : S := qA vA
  have hv2 : v * v = 1 := hD₀.mul_self v hv
  have hv2A : vA * vA = 1 := Subtype.ext hv2
  have hvbar2 : vbar * vbar = 1 := by
    dsimp [vbar, vA]
    rw [← map_mul, ← map_one qA]
    congr 1
  have hvbar1 : vbar ≠ 1 := by
    intro h
    apply hv1
    have := (QuotientGroup.eq_one_iff vA).mp h
    exact congrArg Subtype.val
      (CFSG.EvenSporadicStandard.Induction.Closing.eq_one_of_sq_eq_one_of_odd_center
        hS.odd_card_center this hv2A)
  have hvC : Nat.card (Subgroup.centralizer ({vbar} : Set S)) = 161280 := by
    simpa [vbar, vA, qA, S] using hD₀.card_centralizer v hv hv1
  obtain ⟨s₂, hs₂⟩ := exists_conj_base_of_card_centralizer e h0mem hvbar2 hvbar1 hvC
  have hs : (s₂⁻¹ * s₁) * abar * (s₂⁻¹ * s₁)⁻¹ = vbar := by
    calc (s₂⁻¹ * s₁) * abar * (s₂⁻¹ * s₁)⁻¹
        = s₂⁻¹ * (s₁ * abar * s₁⁻¹) * s₂ := by group
      _ = s₂⁻¹ * e.symm ⟨suzInv 0, h0mem⟩ * s₂ := by rw [hs₁]
      _ = vbar := by
          rw [← hs₂]
          group
  obtain ⟨hA, hqA⟩ := QuotientGroup.mk'_surjective (center ↥A) (s₂⁻¹ * s₁)
  have hhA : (hA : G) ∈ A := hA.2
  have hconj : (hA : G) * a * (hA : G)⁻¹ = v := by
    have hq : qA ⟨(hA : G) * a * (hA : G)⁻¹,
        A.mul_mem (A.mul_mem hhA haA) (A.inv_mem hhA)⟩ = qA vA := by
      change qA (⟨(hA : G), hhA⟩ * ⟨a, haA⟩ * ⟨(hA : G), hhA⟩⁻¹) = qA vA
      rw [map_mul, map_mul, map_inv]
      change qA ⟨(hA : G), hhA⟩ * qA ⟨a, haA⟩ * (qA ⟨(hA : G), hhA⟩)⁻¹ = qA vA
      rw [hqA]
      exact hs
    have hsq : ((⟨(hA : G) * a * (hA : G)⁻¹,
        A.mul_mem (A.mul_mem hhA haA) (A.inv_mem hhA)⟩ : ↥A) *
        ⟨(hA : G) * a * (hA : G)⁻¹,
          A.mul_mem (A.mul_mem hhA haA) (A.inv_mem hhA)⟩) = 1 := by
      apply Subtype.ext
      change ((hA : G) * a * (hA : G)⁻¹) * ((hA : G) * a * (hA : G)⁻¹) = 1
      calc ((hA : G) * a * (hA : G)⁻¹) * ((hA : G) * a * (hA : G)⁻¹)
          = (hA : G) * (a * a) * (hA : G)⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have hEq := CFSG.EvenSporadicStandard.Induction.Closing.eq_of_mk_eq_of_sq
      hS.odd_card_center hsq hv2A hq
    exact congrArg Subtype.val hEq
  let h' : G := (hA : G)⁻¹
  have hh' : h' ∈ A := A.inv_mem hhA
  have haV : a ∈ V₀.map (MulAut.conj h').toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨v, hv, ?_⟩
    change h' * v * h'⁻¹ = a
    rw [show h' = (hA : G)⁻¹ from rfl]
    rw [← hconj]
    group
  have hD' : L34SuzOddData A (V₀.map (MulAut.conj h').toMonoidHom)
      (K₀.map (MulAut.conj h').toMonoidHom) (h' * y₀ * h'⁻¹) :=
    l34SuzOddData_conj hD₀ hh'
  have hPK := eq_of_l34SuzOddData_of_isComponent hS hD' hPA haV ha1 hPa hPq hPodd hPL
  refine ⟨V₀.map (MulAut.conj h').toMonoidHom, h' * y₀ * h'⁻¹, a, hPK.symm ▸ hD', haV, ha1, ?_⟩
  rcases hc with rfl | rfl
  · left
    simpa using hxac
  · right
    rw [hxac]
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem a haA

end CFSG.ComponentClassification.GrSLit.L34Sec5S
