module

public import CFSG.Quasithin.Background.Ordering
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

theorem card_eq_of_isQuasisimple_of_normal {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hN : CFSG.Quasithin.conjClosure L T ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (X : Subgroup (↥(CFSG.Quasithin.conjClosure L T) ⧸
      CFSG.pCore 2 ↥(CFSG.Quasithin.conjClosure L T)))
    (hX : X.Normal) (hXq : CFSG.IsQuasisimple ↥X) :
    Nat.card X = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Mp : Subgroup G := CFSG.Quasithin.conjClosure L T
  have hLleMp : L ≤ Mp := CFSG.Quasithin.le_conjClosure L T
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) := hN
  let Lt : T → Subgroup G := fun t => L.map (MulAut.conj (t : G)).toMonoidHom
  have hLt_apply : ∀ t : T, Lt t = L.map (MulAut.conj (t : G)).toMonoidHom := fun _ => rfl
  have hLt_le : ∀ t : T, Lt t ≤ Mp := by
    intro t x hx
    rw [hLt_apply] at hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    simpa only [Mp, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      CFSG.Quasithin.mem_conjClosure (Z := L) (H := T) (h := t) t.2 hl
  have hLt_le_normalizer_L : ∀ u : T, Lt u ≤ Subgroup.normalizer (L : Set G) :=
    fun u => (hLt_le u).trans hMpN
  have hLt_conj : ∀ (g : G) (hg : g ∈ T) (u : T),
      Subgroup.map (MulAut.conj g).toMonoidHom (Lt u) = Lt (⟨g, hg⟩ * u) := by
    intro g hg u
    rw [hLt_apply, hLt_apply, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul]
    group
  have hL_le_normalizer_Lt : ∀ v : T, L ≤ Subgroup.normalizer (Lt v : Set G) := by
    intro v
    have hconj_mem : ∀ (n : G), n ∈ L → ∀ x ∈ Lt v, n * x * n⁻¹ ∈ Lt v := by
      intro n hn x hx
      rw [hLt_apply] at hx ⊢
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      have ha : v⁻¹ * n * v ∈ Lt v⁻¹ := by
        rw [hLt_apply]
        exact Subgroup.mem_map.mpr ⟨n, hn, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv, inv_inv]⟩
      have haN : v⁻¹ * n * v ∈ Subgroup.normalizer (L : Set G) :=
        hLt_le_normalizer_L v⁻¹ ha
      have hb : (v⁻¹ * n * v) * l * (v⁻¹ * n * v)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp haN l).mp hl
      exact Subgroup.mem_map.mpr ⟨_, hb, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv, inv_inv]
        group⟩
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj_mem m hm x
    · intro hx
      have h := hconj_mem m⁻¹ (L.inv_mem hm) (m * x * m⁻¹) hx
      simpa [mul_assoc] using h
  have hLt_normal : ∀ t : T, Mp ≤ Subgroup.normalizer (Lt t : Set G) := by
    intro t
    change CFSG.Quasithin.conjClosure L T ≤ Subgroup.normalizer (Lt t : Set G)
    refine CFSG.Quasithin.conjClosure_le fun s hs z hz => ?_
    have hzN : z ∈ Subgroup.normalizer (Lt ((⟨s, hs⟩ : T)⁻¹ * t) : Set G) :=
      hL_le_normalizer_Lt _ hz
    have hmem : MulAut.conj s z ∈ Subgroup.map (MulAut.conj s).toMonoidHom
        (Subgroup.normalizer (Lt ((⟨s, hs⟩ : T)⁻¹ * t) : Set G)) :=
      Subgroup.mem_map.mpr ⟨z, hzN, rfl⟩
    have hmap : Subgroup.map (MulAut.conj s).toMonoidHom
        (Subgroup.normalizer (Lt ((⟨s, hs⟩ : T)⁻¹ * t) : Set G)) =
        Subgroup.normalizer (Lt t : Set G) := by
      rw [Subgroup.map_equiv_normalizer_eq, hLt_conj s hs]
      rw [show (⟨s, hs⟩ : T) * ((⟨s, hs⟩ : T)⁻¹ * t) = t from by group]
    rw [hmap] at hmem
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  have hsup : (⨆ t : T, Lt t) = Mp := by
    change (⨆ t : T, Lt t) =
      Subgroup.closure {x : G | ∃ h ∈ T, ∃ z ∈ L, h * z * h⁻¹ = x}
    refine le_antisymm (iSup_le fun t => hLt_le t) ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨h, hh, z, hz, rfl⟩
    have hmem : MulAut.conj h z ∈ Lt ⟨h, hh⟩ := by
      rw [hLt_apply]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    refine le_iSup (fun t : T => Lt t) ⟨h, hh⟩ ?_
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  have hPcLt : ∀ t : T, pCoreOf 2 (Lt t) = pCoreOf 2 Mp ⊓ Lt t := by
    intro t
    refine le_antisymm ?_ ?_
    · exact le_inf (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 (Lt t)).trans (hLt_le t))
        ((hLt_normal t).trans (normalizer_le_normalizer_pCoreOf 2 (Lt t)))
        (pCoreOf_isPGroup 2 (Lt t))) (pCoreOf_le 2 (Lt t))
    · refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((pCoreOf_isPGroup 2 Mp).to_le inf_le_left)
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp
            ((le_normalizer_pCoreOf 2 Mp) (hLt_le t hx)) y).mp h1,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp
            ((le_normalizer_pCoreOf 2 Mp) (hLt_le t hx)) y).mpr h1,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y).mpr h2⟩
  let Q : Subgroup ↥Mp := CFSG.pCore 2 ↥Mp
  let π : ↥Mp →* (↥Mp ⧸ Q) := QuotientGroup.mk' Q
  let Y : T → Subgroup (↥Mp ⧸ Q) := fun t => Subgroup.map π ((Lt t).subgroupOf Mp)
  have hY_normal : ∀ t : T, (Y t).Normal := by
    intro t
    exact Subgroup.Normal.map (Subgroup.normal_subgroupOf_of_le_normalizer (hLt_normal t)) π
      (QuotientGroup.mk'_surjective Q)
  have hsupΛ : (⨆ t : T, (Lt t).subgroupOf Mp) = ⊤ := by
    apply Subgroup.map_injective Mp.subtype_injective
    have hterm : ∀ t : T, Subgroup.map Mp.subtype ((Lt t).subgroupOf Mp) = Lt t :=
      fun t => Subgroup.map_subgroupOf_eq_of_le (hLt_le t)
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    rw [show (⨆ t : T, Subgroup.map Mp.subtype ((Lt t).subgroupOf Mp)) = (⨆ t : T, Lt t) from
      iSup_congr hterm]
    exact hsup
  have hsupY : (⨆ t : T, Y t) = ⊤ := by
    change (⨆ t : T, Subgroup.map π ((Lt t).subgroupOf Mp)) = ⊤
    rw [← Subgroup.map_iSup, hsupΛ, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Q)
  let eL : ∀ t : T, ↥L ≃* ↥(Lt t) := fun t =>
    Subgroup.equivMapOfInjective L (MulAut.conj (t : G)).toMonoidHom
      (MulAut.conj (t : G)).injective
  let φ : T → (↥L →* (↥Mp ⧸ Q)) := fun t =>
    (QuotientGroup.mk' Q).comp ((Subgroup.inclusion (hLt_le t)).comp (eL t).toMonoidHom)
  have hφ_range : ∀ t : T, (φ t).range = Y t := by
    intro t
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      have hmem : ((Subgroup.inclusion (hLt_le t) (eL t l) : ↥Mp) : G) ∈ Lt t := by
        rw [Subgroup.coe_inclusion]
        exact (eL t l).2
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion (hLt_le t) (eL t l),
        Subgroup.mem_subgroupOf.mpr hmem, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hyG : (y : G) ∈ Lt t := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨l, hl⟩ := (eL t).surjective ⟨(y : G), hyG⟩
      refine ⟨l, ?_⟩
      change QuotientGroup.mk' Q (Subgroup.inclusion (hLt_le t) (eL t l)) =
        QuotientGroup.mk' Q y
      congr 1
      exact Subtype.ext (by
        rw [Subgroup.coe_inclusion]
        simpa using congrArg Subtype.val hl)
  have hφker : ∀ t : T, (φ t).ker = CFSG.pCore 2 ↥L := by
    intro t
    ext l
    rw [MonoidHom.mem_ker]
    have h1 : φ t l = QuotientGroup.mk' Q (Subgroup.inclusion (hLt_le t) (eL t l)) := rfl
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h2 : Subgroup.inclusion (hLt_le t) (eL t l) ∈ Q ↔
        ((eL t l : ↥(Lt t)) : G) ∈ pCoreOf 2 Mp := by
      have h := CFSG.mem_openPCoreOf_iff (p := 2) (H := Mp)
        (Subgroup.inclusion (hLt_le t) (eL t l))
      rw [Subgroup.coe_inclusion] at h
      exact h.symm
    rw [h2]
    have h3 : ((eL t l : ↥(Lt t)) : G) ∈ pCoreOf 2 Mp ↔
        ((eL t l : ↥(Lt t)) : G) ∈ pCoreOf 2 (Lt t) := by
      rw [hPcLt t]
      exact ⟨fun h => ⟨h, (eL t l).2⟩, fun h => h.1⟩
    rw [h3, CFSG.mem_openPCoreOf_iff,
      ← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (eL t)]
    exact Subgroup.mem_map_iff_mem (eL t).injective
  have hYq : ∀ t : T, CFSG.IsQuasisimple ↥(Y t) := by
    intro t
    have hq' : CFSG.IsQuasisimple (↥L ⧸ (φ t).ker) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq (hφker t).symm) hq
    rw [← hφ_range t]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange (φ t)) hq'
  have hXcomp : CFSG.IsComponent X := ⟨hXq, hX.isSubnormal⟩
  have hdich : ∀ t : T, X ≤ Y t ∨ ⁅X, Y t⁆ = ⊥ :=
    fun t => CFSG.LocalCores.component_normal_subgroup hXcomp (hY_normal t)
  have hnotall : ¬ ∀ t : T, ⁅X, Y t⁆ = ⊥ := by
    intro hcomm
    have hC := CFSG.subgroup_le_centralizer_iSup_of_le_centralizer (fun t : T => Y t)
      (fun t => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm t))
    rw [hsupY] at hC
    have hcent : X ≤ Subgroup.center (↥Mp ⧸ Q) := by
      intro x hx
      exact Subgroup.mem_center_iff.mpr fun y =>
        Subgroup.mem_centralizer_iff.mp (hC hx) y (Subgroup.mem_top y)
    haveI : IsMulCommutative ↥X :=
      ⟨⟨fun a b => Subtype.ext
        ((Subgroup.mem_center_iff.mp (hcent a.2) (b : ↥Mp ⧸ Q)).symm)⟩⟩
    haveI : Group.IsPerfect ↥X := hXq.1
    haveI : Subsingleton ↥X := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact (not_subsingleton_iff_nontrivial.mpr
      (CFSG.LocalCores.isQuasisimple_nontrivial hXq)) inferInstance
  obtain ⟨t, ht⟩ : ∃ t : T, X ≤ Y t := by
    by_contra h
    push Not at h
    exact hnotall fun t => (hdich t).resolve_left (h t)
  have hXt_top : X.subgroupOf (Y t) = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (hYq t)
      (Subgroup.Normal.subgroupOf hX (Y t)) with htop | hcenter
    · exact htop
    · exfalso
      have hcommX : ∀ a b : ↥X, a * b = b * a := by
        intro a b
        have ha : (⟨(a : ↥Mp ⧸ Q), ht a.2⟩ : ↥(Y t)) ∈ X.subgroupOf (Y t) :=
          Subgroup.mem_subgroupOf.mpr a.2
        have hc := Subgroup.mem_center_iff.mp (hcenter ha)
          (⟨(b : ↥Mp ⧸ Q), ht b.2⟩ : ↥(Y t))
        exact Subtype.ext (by
          simpa using (congrArg Subtype.val hc).symm)
      haveI : IsMulCommutative ↥X := ⟨⟨hcommX⟩⟩
      haveI : Group.IsPerfect ↥X := hXq.1
      haveI : Subsingleton ↥X := Group.IsPerfect.subsingleton_of_isMulCommutative
      exact (not_subsingleton_iff_nontrivial.mpr
        (CFSG.LocalCores.isQuasisimple_nontrivial hXq)) inferInstance
  have hXY : X = Y t := le_antisymm ht (Subgroup.subgroupOf_eq_top.mp hXt_top)
  have hcardY : Nat.card (Y t) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    calc Nat.card (Y t) = Nat.card ↥((φ t).range) := by rw [hφ_range t]
      _ = Nat.card (↥L ⧸ (φ t).ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ t)).toEquiv).symm
      _ = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by rw [hφker t]
  rw [hXY]
  exact hcardY

end CFSG.SectionRank.QTK.Insp443
