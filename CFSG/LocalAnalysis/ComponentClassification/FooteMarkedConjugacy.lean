module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
public import CFSG.LocalAnalysis.ComponentClassification.Sol76ChoiceConj
public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.CatalogueBPrimeJoin

variable {G : Type*} [Group G]

theorem conjugate_zpowers (x g : G) :
    CFSG.conjugate (zpowers x) g = zpowers (g⁻¹ * x * g) := by
  rw [CFSG.conjugate, MonoidHom.map_zpowers]
  simp

theorem conjugate_sup (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g :=
  Subgroup.map_sup _ _ _

@[simp] theorem conjugate_one_eq (K : Subgroup G) : CFSG.conjugate K 1 = K := by
  ext x
  simp [CFSG.conjugate]

theorem centralizer_conjugate (U : Subgroup G) (g : G) :
    CFSG.conjugate (centralizer (U : Set G)) g =
      centralizer ((CFSG.conjugate U g : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx
    rw [UnbalancedLayer.mem_conjugate_iff] at hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g * y * g⁻¹ ∈ U :=
      (UnbalancedLayer.mem_conjugate_iff (K := U) (g := g) (x := y)).mp hy
    have h := hx (g * y * g⁻¹) hy'
    calc
      y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = x * y := by group
  · intro hx
    rw [UnbalancedLayer.mem_conjugate_iff]
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ CFSG.conjugate U g :=
      (UnbalancedLayer.mem_conjugate_iff (K := U) (g := g) (x := g⁻¹ * y * g)).mpr
        (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group])
    have h := hx (g⁻¹ * y * g) hy'
    calc
      y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = (g * x * g⁻¹) * y := by group

theorem centralizer_singleton_conjugate (a g : G) :
    CFSG.conjugate (centralizer ({a} : Set G)) g =
      centralizer ({g⁻¹ * a * g} : Set G) := by
  rw [← UnbalancedLayer.centralizer_zpowers_eq a,
    ← UnbalancedLayer.centralizer_zpowers_eq (g⁻¹ * a * g),
    centralizer_conjugate, conjugate_zpowers]

theorem perfectResidualOf_conjugate (M : Subgroup G) (g : G) :
    CFSG.conjugate ((CFSG.perfectResidual ↥M).map M.subtype) g =
      (CFSG.perfectResidual ↥(CFSG.conjugate M g)).map (CFSG.conjugate M g).subtype := by
  let C : Subgroup G := M
  let C' : Subgroup G := CFSG.conjugate M g
  let e : ↥C ≃* ↥C' := MulEquiv.subgroupMap (MulAut.conj g⁻¹) C
  have hC' : C' = C.map (MulAut.conj g⁻¹).toMonoidHom := rfl
  have hperf : (CFSG.perfectResidual C).map e.toMonoidHom = CFSG.perfectResidual C' := by
    unfold CFSG.perfectResidual
    rw [Subgroup.map_iInf e.toMonoidHom e.injective]
    simp_rw [map_derivedSeries_eq (f := e.toMonoidHom) e.surjective]
  change ((CFSG.perfectResidual C).map C.subtype).map
      (MulAut.conj g⁻¹).toMonoidHom = (CFSG.perfectResidual C').map C'.subtype
  rw [Subgroup.map_map]
  have hcomp : C'.subtype.comp e.toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp C.subtype := by
    ext x
    rfl
  rw [← hcomp, ← Subgroup.map_map, hperf]

theorem fixedShadow_conjugate (M U : Subgroup G) (g : G) :
    CFSG.conjugate (fixedShadow M U) g =
      fixedShadow (CFSG.conjugate M g) (CFSG.conjugate U g) := by
  have hC : CFSG.conjugate (M ⊓ centralizer (U : Set G)) g =
      CFSG.conjugate M g ⊓ centralizer (CFSG.conjugate U g : Set G) := by
    change (M ⊓ centralizer (U : Set G)).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective]
    change CFSG.conjugate M g ⊓ CFSG.conjugate (centralizer (U : Set G)) g = _
    rw [centralizer_conjugate]
  unfold fixedShadow
  rw [perfectResidualOf_conjugate, hC]

theorem fixedShadowAt_conjugate (M : Subgroup G) (a g : G) :
    CFSG.conjugate (fixedShadowAt M a) g =
      fixedShadowAt (CFSG.conjugate M g) (g⁻¹ * a * g) := by
  rw [← fixedShadow_zpowers M a, ← fixedShadow_zpowers (CFSG.conjugate M g) (g⁻¹ * a * g),
    fixedShadow_conjugate, conjugate_zpowers]

theorem oddCoreIn_conjugate (M : Subgroup G) (g : G) :
    CFSG.conjugate (FooteLit.oddCoreIn M) g = FooteLit.oddCoreIn (CFSG.conjugate M g) := by
  unfold FooteLit.oddCoreIn
  let e : ↥M ≃* ↥(CFSG.conjugate M g) := MulEquiv.subgroupMap (MulAut.conj g⁻¹) M
  have hcore : (pPrimeCore 2 M).map e.toMonoidHom = pPrimeCore 2 (CFSG.conjugate M g) :=
    CFSG.pPrimeCore_map_iso 2 e
  rw [CFSG.conjugate, Subgroup.map_map]
  have hcomp : (CFSG.conjugate M g).subtype.comp e.toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp M.subtype := by
    ext x
    rfl
  rw [← hcomp, ← Subgroup.map_map, hcore]

theorem oddCoreOfCentralizer_conjugate (a g : G) :
    CFSG.conjugate (oddCoreOfCentralizer a) g =
      oddCoreOfCentralizer (g⁻¹ * a * g) := by
  change CFSG.conjugate (FooteLit.oddCoreIn (centralizer ({a} : Set G))) g =
    FooteLit.oddCoreIn (centralizer ({g⁻¹ * a * g} : Set G))
  rw [oddCoreIn_conjugate, centralizer_singleton_conjugate]

theorem mem_coreActionKernel_conjugate {M : Subgroup G} {a : G}
    (ha : a ∈ coreActionKernel M) (g : G) :
    g⁻¹ * a * g ∈ coreActionKernel (CFSG.conjugate M g) := by
  rw [UnbalancedLayer.mem_coreActionKernel] at ha ⊢
  refine ⟨?_, ?_⟩
  · have hconj : CFSG.conjugate (CFSG.conjugate M g) (g⁻¹ * a * g) =
        CFSG.conjugate M g := by
      rw [UnbalancedLayer.conjugate_conjugate]
      rw [show g * (g⁻¹ * a * g) = a * g by group]
      rw [← UnbalancedLayer.conjugate_conjugate]
      rw [UnbalancedLayer.conjugate_eq_of_mem_normalizer ha.1]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hiff := UnbalancedLayer.mem_conjugate_iff (K := CFSG.conjugate M g)
      (g := g⁻¹ * a * g) (x := y)
    rwa [hconj] at hiff
  · intro y hy
    have hy' : g * y * g⁻¹ ∈ M :=
      (UnbalancedLayer.mem_conjugate_iff (K := M) (g := g) (x := y)).mp hy
    have hcomm := ha.2 (g * y * g⁻¹) hy'
    have hmem : g⁻¹ * ((g * y * g⁻¹)⁻¹ * a⁻¹ * (g * y * g⁻¹) * a) * g ∈
        CFSG.conjugate (FooteLit.oddCoreIn M) g := by
      rw [UnbalancedLayer.mem_conjugate_iff]
      rw [show g * (g⁻¹ * ((g * y * g⁻¹)⁻¹ * a⁻¹ * (g * y * g⁻¹) * a) * g) * g⁻¹ =
          (g * y * g⁻¹)⁻¹ * a⁻¹ * (g * y * g⁻¹) * a by group]
      exact hcomm
    rw [oddCoreIn_conjugate] at hmem
    rw [show g⁻¹ * ((g * y * g⁻¹)⁻¹ * a⁻¹ * (g * y * g⁻¹) * a) * g =
        y⁻¹ * (g⁻¹ * a * g)⁻¹ * y * (g⁻¹ * a * g) by group] at hmem
    simpa only [FooteLit.oddCoreIn] using hmem

theorem quotient_pPrimeCore_conjugate (M : Subgroup G) (g : G) :
    Nonempty (M ⧸ pPrimeCore 2 M ≃*
      (CFSG.conjugate M g) ⧸ pPrimeCore 2 (CFSG.conjugate M g)) := by
  let e : ↥M ≃* ↥(CFSG.conjugate M g) := MulEquiv.subgroupMap (MulAut.conj g⁻¹) M
  exact ⟨QuotientGroup.congr (pPrimeCore 2 M) (pPrimeCore 2 (CFSG.conjugate M g)) e
    (CFSG.pPrimeCore_map_iso 2 e)⟩

theorem Marked.conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) {M : Subgroup G} (hM : Marked S T M) (g : G) :
    Marked S T (CFSG.conjugate M g) := by
  obtain ⟨hperf, hquot, a, ha2, haKer, Sa, hSaS, heq⟩ := hM
  refine ⟨?_, ?_, g⁻¹ * a * g, ?_, ?_, CFSG.conjugate Sa g, ?_, ?_⟩
  · change Group.IsPerfect (M.map (MulAut.conj g⁻¹).toMonoidHom)
    have : Group.IsPerfect M := hperf
    exact Group.IsPerfect.map (H := M) (f := (MulAut.conj g⁻¹).toMonoidHom)
  · obtain ⟨e⟩ := hquot
    exact ⟨(quotient_pPrimeCore_conjugate M g).some.symm.trans e⟩
  · have h : orderOf ((MulAut.conj g⁻¹) a) = 2 := by
      rw [MulEquiv.orderOf_eq, ha2]
    simpa [MulAut.conj_apply] using h
  · exact mem_coreActionKernel_conjugate haKer g
  · exact hFam.2.2.1 Sa hSaS g
  · have hsup := congrArg (fun H : Subgroup G => CFSG.conjugate H g) heq
    rw [conjugate_sup, conjugate_sup] at hsup
    simpa only [fixedShadowAt_conjugate, oddCoreOfCentralizer_conjugate] using hsup

theorem conjugate_le_of_mem {M H : Subgroup G} (hMH : M ≤ H) {g : G} (hg : g ∈ H) :
    CFSG.conjugate M g ≤ H := by
  intro x hx
  rw [UnbalancedLayer.mem_conjugate_iff] at hx
  have h := H.mul_mem (H.mul_mem (H.inv_mem hg) (hMH hx)) hg
  simpa [mul_assoc] using h

theorem isPComponent_conjugate_subgroupOf {M H : Subgroup G} {g : G} (hg : g ∈ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) :
    IsPComponent 2 ((CFSG.conjugate M g).subgroupOf H) := by
  have h := UnbalancedLayer.isPComponent_conjugate hM (⟨g, hg⟩ : H)
  rwa [UnbalancedLayer.conjugate_subgroupOf_eq] at h

theorem markedComponents_conjugate_iff {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (X : Subgroup G) (x : X) (K : Subgroup G) :
    K ∈ markedComponents S T X ↔ CFSG.conjugate K (x : G) ∈ markedComponents S T X := by
  have hforward : ∀ (y : X) (K : Subgroup G), K ∈ markedComponents S T X →
      CFSG.conjugate K (y : G) ∈ markedComponents S T X := by
    rintro y K ⟨hKX, hMK⟩
    exact ⟨⟨conjugate_le_of_mem hKX.1 y.2,
      isPComponent_conjugate_subgroupOf y.2 hKX.2⟩,
      Marked.conjugate hFam hMK (y : G)⟩
  constructor
  · exact hforward x K
  · intro hK
    have h := hforward x⁻¹ (CFSG.conjugate K (x : G)) hK
    rw [show ((x⁻¹ : X) : G) = (x : G)⁻¹ from rfl,
      UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, conjugate_one_eq] at h
    exact h

theorem markedLayer_conjugate {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (X : Subgroup G) (x : X) :
    CFSG.conjugate (markedLayer S T X) (x : G) = markedLayer S T X := by
  let L := markedLayer S T X
  have hmap_le : ∀ y : X, L.map (MulAut.conj (y : G)⁻¹).toMonoidHom ≤ L := by
    intro y
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro K hK
    exact (Subgroup.map_le_iff_le_comap).mp
      (le_sSup ((markedComponents_conjugate_iff hFam X y K).mp hK))
  have hle : CFSG.conjugate L (x : G) ≤ L := hmap_le x
  have hle_inv : L.map (MulAut.conj (x : G)).toMonoidHom ≤ L := by
    simpa using hmap_le x⁻¹
  have hcomp : (MulAut.conj (x : G)⁻¹).toMonoidHom.comp
      (MulAut.conj (x : G)).toMonoidHom = MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hge : L ≤ CFSG.conjugate L (x : G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj (x : G)⁻¹).toMonoidHom) hle_inv
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    exact h
  exact le_antisymm hle hge

theorem markedLayer_le_normalizer {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (markedLayer S T X : Set G) := by
  intro x hx
  have hfix : CFSG.conjugate (markedLayer S T X) (x : G) = markedLayer S T X :=
    markedLayer_conjugate hFam X ⟨x, hx⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hiff := UnbalancedLayer.mem_conjugate_iff (K := markedLayer S T X) (g := x) (x := y)
  rwa [hfix] at hiff

theorem markedLayer_subgroupOf_normal {S : Set (Subgroup G)} {T : Type*} [Group T]
    (hFam : IsomorphicFamily S T) (X : Subgroup G) :
    ((markedLayer S T X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (markedLayer_le S T X)).mpr
    (markedLayer_le_normalizer hFam X)

end CFSG.ComponentClassification.FooteMarked

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G] [Finite G]

theorem base_conjugate (X : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.ComponentClassification.FooteMarked.base X) g =
      CFSG.ComponentClassification.FooteMarked.base (CFSG.conjugate X g) := by
  unfold CFSG.conjugate CFSG.ComponentClassification.FooteMarked.base
  rw [Subgroup.map_sup,
    CFSG.ComponentClassification.Sol76.map_oddTwoCoreIn (MulAut.conj g⁻¹) X,
    CFSG.ComponentClassification.Sol76.map_twoLayerIn (MulAut.conj g⁻¹) X]

theorem exists_oddCore_conj_mem_of_sup {K J : Subgroup G} (hKJ : K ≤ J)
    (hsup : K ⊔ oddCoreIn J = J) {t : G} (htJ : t ∈ J) (ht2 : orderOf t = 2) :
    ∃ o ∈ oddCoreIn J, o * t * o⁻¹ ∈ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := oddCoreIn J with hO
  have hOJ : O ≤ J := by
    rw [hO]
    change (CFSG.pPrimeCore 2 ↥J).map J.subtype ≤ J
    exact Subgroup.map_subtype_le _
  have hOddO : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (CFSG.ComponentClassification.Sol76.coprime_card_oddCoreIn J)
  let π : J →* J ⧸ CFSG.pPrimeCore 2 ↥J :=
    QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥J)
  let f : K →* J ⧸ CFSG.pPrimeCore 2 ↥J :=
    { toFun := fun x => π ⟨(x : G), hKJ x.2⟩
      map_one' := by
        change π (1 : J) = 1
        exact map_one π
      map_mul' := by
        intro a b
        change π ⟨((a : K) : G) * ((b : K) : G), _⟩ =
          π ⟨((a : K) : G), _⟩ * π ⟨((b : K) : G), _⟩
        rw [← map_mul]
        rfl }
  have ht_sq : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2] at this
    simpa [pow_two] using this
  have hOπ : (O.subgroupOf J).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO
    have hxy : y = x := Subtype.ext hyx
    have hxker : x ∈ π.ker := by
      rw [show π.ker = CFSG.pPrimeCore 2 ↥J from QuotientGroup.ker_mk' _]
      exact hxy ▸ hy
    exact MonoidHom.mem_ker.mp hxker
  have hKtop : (K.subgroupOf J).map π = ⊤ := by
    have hsupJ : (K ⊔ O).subgroupOf J = K.subgroupOf J ⊔ O.subgroupOf J :=
      Subgroup.subgroupOf_sup hKJ hOJ
    have htop : K.subgroupOf J ⊔ O.subgroupOf J = ⊤ := by
      rw [← hsupJ, hsup]
      simp
    have hmap := congrArg (fun L : Subgroup J => L.map π) htop
    rw [Subgroup.map_sup, hOπ, sup_bot_eq,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at hmap
    exact hmap
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : y ∈ (K.subgroupOf J).map π := hKtop ▸ Subgroup.mem_top y
    obtain ⟨x, hxK, hxy⟩ := hy
    refine ⟨⟨x, (Subgroup.mem_subgroupOf.mp hxK)⟩, ?_⟩
    simpa [f] using hxy
  have hkerO : f.ker = (K ⊓ O).subgroupOf K := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxKJ : (x : G) ∈ J := hKJ x.2
      have hxπ : π ⟨(x : G), hxKJ⟩ = 1 := by
        simpa [f] using hx
      have hxP : (⟨(x : G), hxKJ⟩ : J) ∈ CFSG.pPrimeCore 2 ↥J :=
        (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 ↥J) _).mp hxπ
      have hxO : (x : G) ∈ O := ⟨⟨(x : G), hxKJ⟩, hxP, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxO⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxO : (x : G) ∈ O := (Subgroup.mem_subgroupOf.mp hx).2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO
      have hxy : y = ⟨(x : G), hKJ x.2⟩ := Subtype.ext hyx
      have hy1 : π y = 1 := (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 ↥J) y).mpr hy
      have hy1' : π ⟨(x : G), hKJ x.2⟩ = 1 := by
        rw [← hxy]
        exact hy1
      simpa [f] using hy1'
  have hOddInf : Odd (Nat.card ((K ⊓ O).subgroupOf K)) := by
    have hcard : Nat.card ((K ⊓ O).subgroupOf K) = Nat.card ↥(K ⊓ O) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ O ≤ K)).toEquiv
    rw [hcard]
    exact hOddO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hker_odd : Odd (Nat.card f.ker) := hkerO ▸ hOddInf
  have hπt2 : orderOf (π ⟨t, htJ⟩) = 2 := by
    apply orderOf_eq_prime
    · have hsq : (⟨t, htJ⟩ : J) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using ht_sq
      rw [← map_pow, hsq, map_one]
    · intro h1
      have htP : (⟨t, htJ⟩ : J) ∈ CFSG.pPrimeCore 2 ↥J :=
        (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 ↥J) _).mp h1
      have htO : t ∈ O := ⟨⟨t, htJ⟩, htP, rfl⟩
      have h2 : 2 ∣ Nat.card O := by
        rw [← ht2]
        exact O.orderOf_dvd_natCard htO
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (CFSG.ComponentClassification.Sol76.coprime_card_oddCoreIn J) h2
  obtain ⟨k, hk⟩ := CFSG.OrderReductions.OddKernelInvolutions.exists_involution_lift
    f hf_surj hker_odd ⟨π ⟨t, htJ⟩, hπt2⟩
  let kG : G := (k.val : G)
  have hkK : kG ∈ K := k.val.2
  have hk2 : orderOf kG = 2 := by
    have h := Subgroup.orderOf_mk (H := K) (a := kG) (ha := hkK)
    rw [← h]
    exact k.property
  have hk_sq : kG * kG = 1 := by
    have := pow_orderOf_eq_one kG
    rw [hk2] at this
    simpa [pow_two] using this
  have hkimg : π ⟨kG, hKJ hkK⟩ = π ⟨t, htJ⟩ := by
    simpa [f, kG] using hk
  have hktO : kG * t ∈ O := by
    have h1 : π ⟨kG, hKJ hkK⟩ * π ⟨t, htJ⟩ = 1 := by
      rw [hkimg, ← map_mul]
      have hsq : (⟨t, htJ⟩ : J) * ⟨t, htJ⟩ = 1 := by
        apply Subtype.ext
        simpa [pow_two] using ht_sq
      rw [hsq, map_one]
    have hq : π ⟨kG * t, mul_mem (hKJ hkK) htJ⟩ = 1 := by
      simpa [← map_mul] using h1
    have hmemP : (⟨kG * t, mul_mem (hKJ hkK) htJ⟩ : J) ∈ CFSG.pPrimeCore 2 ↥J :=
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 2 ↥J) _).mp hq
    exact ⟨⟨kG * t, mul_mem (hKJ hkK) htJ⟩, hmemP, rfl⟩
  obtain ⟨o, hoO, hok⟩ :=
    CFSG.ClassicalInvolution.Generic.DeltaClosure.exists_conj_of_mul_mem
      (u := t) (z := kG) ht_sq hk_sq hOddO hktO
  exact ⟨o, hoO, by rw [← hok]; exact hkK⟩

theorem transfer_pointwise_of_sup_oddCoreIn {K J H : Subgroup G} (hKJ : K ≤ J)
    (hsup : K ⊔ oddCoreIn J = J) (hJH : J ≤ H) {P : G → Prop}
    (hPconj : ∀ {u g : G}, g ∈ H → P u → P (g⁻¹ * u * g))
    (hPK : ∀ k ∈ K, orderOf k = 2 → P k) {t : G} (htJ : t ∈ J)
    (ht2 : orderOf t = 2) : P t := by
  obtain ⟨o, hoO, hotK⟩ := exists_oddCore_conj_mem_of_sup hKJ hsup htJ ht2
  have hoJ : o ∈ J := (show oddCoreIn J ≤ J from Subgroup.map_subtype_le _) hoO
  have hoH : o ∈ H := hJH hoJ
  have hk2 : orderOf (o * t * o⁻¹) = 2 := by
    have h := (MulAut.conj o).orderOf_eq t
    simpa [MulAut.conj_apply, ht2] using h
  have hPk : P (o * t * o⁻¹) := hPK _ hotK hk2
  have h := hPconj (u := o * t * o⁻¹) (g := o) hoH hPk
  have ht_eq : o⁻¹ * (o * t * o⁻¹) * o = t := by group
  rwa [ht_eq] at h

theorem all_pure_containment_of_oddCore_cover {K J H : Subgroup G} (hKJ : K ≤ J)
    (hcover : K ⊔ oddCoreIn J = J) (hJH : J ≤ H)
    (hK : ∀ t ∈ K, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H) :
    ∀ t ∈ J, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H := by
  intro t htJ ht2
  refine transfer_pointwise_of_sup_oddCoreIn hKJ hcover hJH (hPK := hK) ?_ htJ ht2
  intro u g hg hu
  constructor
  · rw [← oddCoreOfCentralizer_conjugate u g]
    exact conjugate_le_of_mem hu.1 hg
  · rw [← centralizer_singleton_conjugate u g,
      ← base_conjugate (centralizer ({u} : Set G)) g]
    exact conjugate_le_of_mem hu.2 hg

end CFSG.ComponentClassification.FooteMarked
