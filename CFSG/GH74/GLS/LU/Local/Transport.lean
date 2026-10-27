module

public import CFSG.GH74.GLS.LU.Local.Conj
public import CFSG.GH74.GLS.LU.Local.Core3
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section CompIn

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf_iff' {K M H : Subgroup G} (hMH : M ≤ H) :
    CFSG.IsComponent ((K.subgroupOf H).subgroupOf (M.subgroupOf H)) ↔
      CFSG.IsComponent (K.subgroupOf M) := by
  let e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMH
  have hmap : ((K.subgroupOf H).subgroupOf (M.subgroupOf H)).map e.toMonoidHom =
      K.subgroupOf M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [(CFSG.LocalCores.component_isomorphism e).1, hmap]

theorem isCompIn_mono' {A B K : Subgroup G} (h : IsCompIn A K) (hKB : K ≤ B) (hBA : B ≤ A) :
    IsCompIn B K := by
  refine ⟨hKB, ?_⟩
  have h1 : CFSG.IsComponent ((K.subgroupOf A).subgroupOf (B.subgroupOf A)) :=
    CFSG.LocalCores.component_overgroup h.2 (Subgroup.subgroupOf_mono A hKB)
  exact (isComponent_subgroupOf_iff' hBA).1 h1

theorem isCompIn_of_normal {C A K : Subgroup G} (h : IsCompIn A K) (hAC : A ≤ C)
    (hn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) : IsCompIn C K := by
  refine ⟨h.1.trans hAC, ?_⟩
  have h1 : CFSG.IsComponent ((K.subgroupOf C).subgroupOf (A.subgroupOf C)) :=
    (isComponent_subgroupOf_iff' hAC).2 h.2
  have hN : (A.subgroupOf C).Normal := by
    refine ⟨fun n hn' c => ?_⟩
    exact hn _ c.2 _ hn'
  have hq : CFSG.IsQuasisimple ↥(K.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe h.1).trans (Subgroup.subgroupOfEquivOfLe (h.1.trans hAC)).symm)
      h.2.1
  exact ⟨hq, Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono C h.1) h1.2
    (Subgroup.Normal.isSubnormal hN)⟩

theorem le_layer_of_isCompIn {C K : Subgroup G} (h : IsCompIn C K) :
    K ≤ (CFSG.layer ↥C).map C.subtype := by
  intro x hx
  have hxC : x ∈ C := h.1 hx
  have h1 : K.subgroupOf C ≤ CFSG.layer ↥C :=
    le_sSup (show K.subgroupOf C ∈ {K : Subgroup ↥C | CFSG.IsComponent K} from h.2)
  exact ⟨⟨x, hxC⟩, h1 (show (⟨x, hxC⟩ : ↥C) ∈ K.subgroupOf C from hx), rfl⟩

end CompIn

section Layer

variable {G : Type} [Group G]

abbrev Lay (z : G) : Subgroup G := (CFSG.layer ↥(Cz z)).map (Cz z).subtype

theorem Lay_le (z : G) : Lay z ≤ Cz z := Subgroup.map_subtype_le _

theorem Lay_conj {z c x : G} (hc : c ∈ Cz z) (hx : x ∈ Lay z) : c * x * c⁻¹ ∈ Lay z := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hch : (CFSG.layer ↥(Cz z)).Characteristic := CFSG.LocalCores.layer_characteristic
  have hN : (CFSG.layer ↥(Cz z)).Normal := inferInstance
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hN.conj_mem y hy ⟨c, hc⟩, rfl⟩

theorem isCompIn_of_isComponent_X [Finite G] {z : G} {S K : Subgroup G} (hS : IsPGroup 2 S)
    (hSC : S ≤ Cz z) (hKX : K ≤ layerTimesSylow z S)
    (hK : CFSG.IsComponent (K.subgroupOf (layerTimesSylow z S))) : IsCompIn (Cz z) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := layerTimesSylow z S with hX
  have hXdef : X = Lay z ⊔ S := rfl
  have hLX : Lay z ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hXC : X ≤ Cz z := sup_le (Lay_le z) hSC
  have hqK : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX) hK.1
  have hKL : K ≤ Lay z := by
    have hNn : ((Lay z).subgroupOf X).Normal := ⟨fun n hn c => Lay_conj (hXC c.2) hn⟩
    have hNS : (Lay z).subgroupOf X ⊔ S.subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLX hSX, ← hXdef, Subgroup.subgroupOf_self]
    have hSp : IsPGroup 2 ↥(S.subgroupOf X) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
    have hK0 : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X :=
      commutator_self_of_isPerfect _ hK.1.1
    have h1 := perfect_le_of_sup_eq_top_of_isPGroup hNS hSp hK0
    intro x hx
    exact h1 (show (⟨x, hKX hx⟩ : ↥X) ∈ K.subgroupOf X from hx)
  have h1 : IsCompIn (Lay z) K := isCompIn_mono' ⟨hKX, hK⟩ hKL hLX
  exact isCompIn_of_normal h1 (Lay_le z) (fun c hc a ha => Lay_conj hc ha)

theorem isCompIn_of_isPCompIn_two [Finite G] {X L : Subgroup G}
    (hcyc : IsCyclic ↥(pPrimeCoreOf 2 X)) (hL : IsPCompIn 2 X L) : IsCompIn X L := by
  obtain ⟨hLX, K, hKcomp, hsub, hmap, hmin⟩ := hL
  set O : Subgroup ↥X := pPrimeCore 2 ↥X with hO
  set L' : Subgroup ↥X := L.subgroupOf X with hL'
  set π : ↥X →* ↥X ⧸ O := QuotientGroup.mk' O with hπ
  have hKperf : ⁅K, K⁆ = K := commutator_self_of_isPerfect K hKcomp.1.1
  have hcn : (⁅L', L'⁆.subgroupOf L').Normal := by
    have := (inferInstance : (⁅L', L'⁆.subgroupOf (L' ⊔ L')).Normal)
    rwa [sup_idem] at this
  have hcsub : (⁅L', L'⁆).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.commutator_le_self L') hsub hcn
  have hcmap : (⁅L', L'⁆).map π = K := by
    rw [Subgroup.map_commutator]
    have : L'.map π = K := hmap
    rw [this, hKperf]
  have hperf : ⁅L', L'⁆ = L' := by
    by_contra hne
    exact hmin _ (lt_of_le_of_ne (Subgroup.commutator_le_self L') hne) hcsub hcmap
  have hOcyc : IsCyclic ↥O := by
    have : IsCyclic ↥(O.map X.subtype) := hcyc
    let e : ↥O ≃* ↥(O.map X.subtype) := O.equivMapOfInjective X.subtype X.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hON : L' ≤ normalizer (O : Set ↥X) := by
    rw [(Subgroup.normalizer_eq_top_iff).mpr (inferInstance : O.Normal)]
    exact le_top
  have hcent := perfect_le_centralizer_of_cyclic hperf hON
  have hmem : ∀ x : ↥L', (π.comp L'.subtype) x ∈ K := fun x => by
    rw [← hmap]; exact ⟨x, x.2, rfl⟩
  let f : ↥L' →* ↥K := (π.comp L'.subtype).codRestrict K hmem
  have hsurj : Function.Surjective f := by
    intro k
    have hk : (k : ↥X ⧸ O) ∈ L'.map π := by rw [hmap]; exact k.2
    obtain ⟨l, hl, hlk⟩ := hk
    exact ⟨⟨l, hl⟩, Subtype.ext hlk⟩
  have hker : f.ker ≤ center ↥L' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : π x = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
    have h2 : (x : ↥X) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have h3 := mem_centralizer_iff.mp (hcent g.2) (x : ↥X) h2
    exact Subtype.ext h3.symm
  have hperfL : Group.IsPerfect ↥L' := Subgroup.isPerfect_iff.mpr hperf
  have hq : CFSG.IsQuasisimple ↥L' :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperfL f hsurj hker).mpr hKcomp.1
  exact ⟨hLX, hq, hsub⟩

end Layer

section Compat

variable {G Gs : Type} [Group G] [Group Gs]

structure CompatIso (G : Type) [Group G] (z : G) (S : Sylow 2 G) {Gs : Type} [Group Gs] (z' : Gs)
    (S' : Sylow 2 Gs) where
  ψ : ↥(layerTimesSylow z (S : Subgroup G)) ≃* ↥(layerTimesSylow z' (S' : Subgroup Gs))
  mem_S : ∀ x : ↥(layerTimesSylow z (S : Subgroup G)),
    (x : G) ∈ (S : Subgroup G) ↔ ((ψ x : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
      (S' : Subgroup Gs)
  fusion : ∀ x y : ↥(layerTimesSylow z (S : Subgroup G)), (x : G) ∈ (S : Subgroup G) →
    (y : G) ∈ (S : Subgroup G) → orderOf (x : G) = 2 → orderOf (y : G) = 2 →
    (IsConj (x : G) (y : G) ↔
      IsConj ((ψ x : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs)
        ((ψ y : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs))

theorem mem_of_center_eq {S : Subgroup G} {z : G} (hz : (center ↥S).map S.subtype = zpowers z) :
    z ∈ S ∧ ∀ s ∈ S, s * z = z * s := by
  have h : z ∈ (center ↥S).map S.subtype := by rw [hz]; exact mem_zpowers z
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h
  refine ⟨y.2, fun s hs => ?_⟩
  have := Subgroup.mem_center_iff.mp hy ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem le_Cz_of_center_eq {S : Subgroup G} {z : G} (hz : (center ↥S).map S.subtype = zpowers z) :
    S ≤ Cz z := fun s hs => mem_centralizer_singleton_iff.mpr ((mem_of_center_eq hz).2 s hs)

theorem mem_center_of_comm {S : Subgroup G} {z : G} (hz : (center ↥S).map S.subtype = zpowers z)
    {w : G} (hwS : w ∈ S) (hw : ∀ s ∈ S, s * w = w * s) : w ∈ zpowers z := by
  rw [← hz]
  refine ⟨⟨w, hwS⟩, ?_, rfl⟩
  show (⟨w, hwS⟩ : ↥S) ∈ center ↥S
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (hw g g.2)

end Compat

section Psi

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

theorem z_mem_X (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z) :
    z ∈ layerTimesSylow z (S : Subgroup G) :=
  (le_sup_right : (S : Subgroup G) ≤ layerTimesSylow z (S : Subgroup G)) (mem_of_center_eq hz).1

theorem S_le_X (z : G) (S : Subgroup G) : S ≤ layerTimesSylow z S := le_sup_right

theorem CompatIso.psi_z (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    (hz'2 : orderOf z' = 2) :
    ((I.ψ ⟨z, z_mem_X hz⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = z' := by
  obtain ⟨hzS, hzc⟩ := mem_of_center_eq hz
  obtain ⟨hz'S', hz'c⟩ := mem_of_center_eq hz'
  have hz'X' : z' ∈ layerTimesSylow z' (S' : Subgroup Gs) := S_le_X _ _ hz'S'
  set ψ := I.ψ with hψ
  set w : ↥(layerTimesSylow z (S : Subgroup G)) := ψ.symm ⟨z', hz'X'⟩ with hw
  have hψw : ψ w = ⟨z', hz'X'⟩ := ψ.apply_symm_apply _
  have hwS : (w : G) ∈ (S : Subgroup G) := (I.mem_S w).mpr (by rw [hψw]; exact hz'S')
  have hwc : ∀ s ∈ (S : Subgroup G), s * (w : G) = (w : G) * s := by
    intro s hs
    have hsX : s ∈ layerTimesSylow z (S : Subgroup G) := S_le_X _ _ hs
    have hψs : ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
        (S' : Subgroup Gs) := (I.mem_S ⟨s, hsX⟩).mp hs
    have h1 : (ψ (⟨s, hsX⟩ * w) : ↥(layerTimesSylow z' (S' : Subgroup Gs))) =
        ψ (w * ⟨s, hsX⟩) := by
      rw [map_mul, map_mul, hψw]
      apply Subtype.ext
      exact hz'c _ hψs
    exact congrArg Subtype.val (ψ.injective h1)
  have hwz : (w : G) ∈ zpowers z := mem_center_of_comm hz hwS hwc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
  have hψzS' : ((ψ ⟨z, z_mem_X hz⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
      (S' : Subgroup Gs) := (I.mem_S ⟨z, z_mem_X hz⟩).mp hzS
  have hψzc : ∀ s' ∈ (S' : Subgroup Gs),
      s' * ((ψ ⟨z, z_mem_X hz⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) =
        ((ψ ⟨z, z_mem_X hz⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) * s' := by
    intro s' hs'
    have hs'X : s' ∈ layerTimesSylow z' (S' : Subgroup Gs) := S_le_X _ _ hs'
    set y := ψ.symm ⟨s', hs'X⟩ with hy
    have hψy : ψ y = ⟨s', hs'X⟩ := ψ.apply_symm_apply _
    have hyS : (y : G) ∈ (S : Subgroup G) := (I.mem_S y).mpr (by rw [hψy]; exact hs')
    have h1 : y * ⟨z, z_mem_X hz⟩ = ⟨z, z_mem_X hz⟩ * y := Subtype.ext (hzc _ hyS)
    have h2 := congrArg (fun a => ((ψ a : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs)) h1
    simp only [map_mul, hψy] at h2
    exact h2
  have hψzmem : ((ψ ⟨z, z_mem_X hz⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
      zpowers z' := mem_center_of_comm hz' hψzS' hψzc
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hψzmem
  have hψwk : ((ψ w : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = z' ^ (j * k) := by
    have : w = ⟨z, z_mem_X hz⟩ ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    rw [this, map_zpow, Subgroup.coe_zpow, ← hj, ← zpow_mul]
  rw [hψw] at hψwk
  have hjk : z' ^ (j * k - 1) = 1 := by
    have h1 : z' = z' ^ (j * k) := hψwk
    calc z' ^ (j * k - 1) = z' ^ (j * k) * z'⁻¹ := by rw [zpow_sub_one]
      _ = 1 := by rw [← h1]; exact mul_inv_cancel z'
  have hdvd : ((orderOf z' : ℕ) : ℤ) ∣ j * k - 1 := orderOf_dvd_iff_zpow_eq_one.mpr hjk
  rw [hz'2] at hdvd
  have hjodd : Odd j := by
    rcases Int.even_or_odd j with ⟨m, hm⟩ | hodd
    · exfalso
      have : j * k = 2 * (m * k) := by rw [hm]; ring
      omega
    · exact hodd
  obtain ⟨m, hm⟩ := hjodd
  have hz'sq : z' ^ (2 : ℤ) = 1 := by
    have : z' ^ 2 = 1 := by rw [← hz'2]; exact pow_orderOf_eq_one z'
    simpa using this
  rw [← hj, hm]
  calc z' ^ (2 * m + 1) = (z' ^ (2 : ℤ)) ^ m * z' := by rw [zpow_add_one, zpow_mul]
    _ = z' := by rw [hz'sq, one_zpow, one_mul]

end Psi

section TransportComps

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

theorem LUComps.transport [Finite G] [Finite Gs] {q : ℕ} (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    (hcyc : IsCyclic ↥(A0 z)) {E₁ E₂ : Subgroup Gs} (hM : LUComps Gs q z' E₁ E₂)
    (hz'2 : orderOf z' = 2) : LUComps G q z (pull I.ψ E₁) (pull I.ψ E₂) := by
  set ψ := I.ψ with hψ
  have hSC : (S : Subgroup G) ≤ Cz z := le_Cz_of_center_eq hz
  have hS'C : (S' : Subgroup Gs) ≤ Cz z' := le_Cz_of_center_eq hz'
  have hXC : layerTimesSylow z (S : Subgroup G) ≤ Cz z := sup_le (Lay_le z) hSC
  have hX'C : layerTimesSylow z' (S' : Subgroup Gs) ≤ Cz z' := sup_le (Lay_le z') hS'C
  have hE₁ : E₁ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn hM.comp₁).trans le_sup_left
  have hE₂ : E₂ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn hM.comp₂).trans le_sup_left
  have hzX := z_mem_X hz
  have hψz := I.psi_z hz hz' hz'2
  have e1 : ∀ {E : Subgroup Gs}, IsCompIn (Cz z') E → E ≤ layerTimesSylow z' (S' : Subgroup Gs) →
      IsCompIn (Cz z) (pull ψ E) := by
    intro E hEc hEX'
    have hcomp : CFSG.IsComponent (E.subgroupOf (layerTimesSylow z' (S' : Subgroup Gs))) :=
      (isCompIn_mono' hEc hEX' hX'C).2
    have hcompX : CFSG.IsComponent ((pull ψ E).subgroupOf (layerTimesSylow z (S : Subgroup G))) := by
      rw [pull_subgroupOf]
      exact CFSG.LocalCores.isComponent_map_mulEquiv ψ.symm hcomp
    exact isCompIn_of_isComponent_X S.isPGroup' hSC (pull_le ψ E) hcompX
  have hlay : ∀ {E₁ E₂ : Subgroup Gs}, E₁ ≤ layerTimesSylow z' (S' : Subgroup Gs) →
      E₂ ≤ layerTimesSylow z' (S' : Subgroup Gs) → E₁ ⊔ E₂ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    fun h₁ h₂ => sup_le h₁ h₂
  refine ⟨e1 hM.comp₁ hE₁, e1 hM.comp₂ hE₂, fun h => hM.ne (pull_inj ψ hE₁ hE₂ h), ?_, ?_, ?_,
    ?_, ?_⟩
  · intro L hL
    have hLc : IsCompIn (Cz z) L := isCompIn_of_isPCompIn_two hcyc hL
    have hLlay : L ≤ Lay z := le_layer_of_isCompIn hLc
    have hLX : L ≤ layerTimesSylow z (S : Subgroup G) := hLlay.trans le_sup_left
    have hLcX : CFSG.IsComponent (L.subgroupOf (layerTimesSylow z (S : Subgroup G))) :=
      (isCompIn_mono' hLc hLX hXC).2
    have hEX' : push ψ L ≤ layerTimesSylow z' (S' : Subgroup Gs) := push_le ψ L
    have hEcomp : CFSG.IsComponent ((push ψ L).subgroupOf
        (layerTimesSylow z' (S' : Subgroup Gs))) := by
      rw [push_subgroupOf]
      exact CFSG.LocalCores.isComponent_map_mulEquiv ψ hLcX
    have hEc : IsCompIn (Cz z') (push ψ L) :=
      isCompIn_of_isComponent_X S'.isPGroup' hS'C hEX' hEcomp
    have hEp : IsPCompIn 2 (Cz z') (push ψ L) :=
      ⟨hEc.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hEc.2⟩
    have hL' : pull ψ (push ψ L) = L := pull_push ψ hLX
    rcases hM.only _ hEp with h | h
    · left; rw [← hL', h]
    · right; rw [← hL', h]
  · obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hM.sl₁
    exact ⟨F, hF, hFin, hq, ⟨(pullEquiv ψ hE₁).trans e⟩⟩
  · obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hM.sl₂
    exact ⟨F, hF, hFin, hq, ⟨(pullEquiv ψ hE₂).trans e⟩⟩
  · rw [center_pull ψ hE₁, hM.cen₁]
    exact pull_zpowers ψ hzX hψz
  · rw [center_pull ψ hE₂, hM.cen₂]
    exact pull_zpowers ψ hzX hψz

end TransportComps

section TransportSyl

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

theorem LUSyl.transport [Finite G] [Finite Gs] {q : ℕ} (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    {E₁ E₂ : Subgroup Gs} {t' u' : Gs} (hM : LUComps Gs q z' E₁ E₂)
    (hMS : LUSyl Gs z' S' E₁ E₂ t' u') :
    ∃ (t u : G) (ht : t ∈ layerTimesSylow z (S : Subgroup G))
      (hu : u ∈ layerTimesSylow z (S : Subgroup G)),
      ((I.ψ ⟨t, ht⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = t' ∧
      ((I.ψ ⟨u, hu⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = u' ∧
      LUSyl G z S (pull I.ψ E₁) (pull I.ψ E₂) t u := by
  set ψ := I.ψ with hψ
  have hz'2 : orderOf z' = 2 := hMS.z_inv
  have hE₁ : E₁ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn hM.comp₁).trans le_sup_left
  have hE₂ : E₂ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn hM.comp₂).trans le_sup_left
  have hzX := z_mem_X hz
  have hψz := I.psi_z hz hz' hz'2
  have hzS : z ∈ (S : Subgroup G) := (mem_of_center_eq hz).1
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_psi ψ hzX, hψz]; exact hz'2
  obtain ⟨t, ht, hψt⟩ := exists_psi_eq ψ (S_le_X _ _ hMS.t_mem)
  obtain ⟨u, hu, hψu⟩ := exists_psi_eq ψ (S_le_X _ _ hMS.u_mem)
  have htS : t ∈ (S : Subgroup G) := (I.mem_S ⟨t, ht⟩).mpr (by rw [hψt]; exact hMS.t_mem)
  have huS : u ∈ (S : Subgroup G) := (I.mem_S ⟨u, hu⟩).mpr (by rw [hψu]; exact hMS.u_mem)
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_psi ψ ht, hψt, ← orderOf_eq_of_isConj hMS.t_conj]; exact hz'2
  have hu2 : orderOf u = 2 := by
    rw [← orderOf_psi ψ hu, hψu]; exact hMS.u_ord
  refine ⟨t, u, ht, hu, hψt, hψu, ?_⟩
  refine ⟨hz2, hz, htS, ?_, ?_, huS, hu2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (I.fusion ⟨z, hzX⟩ ⟨t, ht⟩ hzS htS hz2 ht2).mpr (by rw [hψz, hψt]; exact hMS.t_conj)
  · rw [pull_map_conj ψ ht, hψt, hMS.t_swap]
  · intro huz
    apply hMS.u_ne
    have h := (psi_eq_iff ψ hu hzX).mpr huz
    rw [hψu, hψz] at h
    exact h
  · exact (I.fusion ⟨z, hzX⟩ ⟨u, hu⟩ hzS huS hz2 hu2).mpr (by rw [hψz, hψu]; exact hMS.u_conj)
  · have huzX : u * z ∈ layerTimesSylow z (S : Subgroup G) := Subgroup.mul_mem _ hu hzX
    have huzS : u * z ∈ (S : Subgroup G) := Subgroup.mul_mem _ huS hzS
    have hψuz : ((ψ ⟨u * z, huzX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = u' * z' := by
      rw [psi_mul ψ hu hzX, hψu, hψz]
    have huz2 : orderOf (u * z) = 2 := by
      rw [← orderOf_psi ψ huzX, hψuz, ← orderOf_eq_of_isConj hMS.uz_conj]; exact hz'2
    exact (I.fusion ⟨z, hzX⟩ ⟨u * z, huzX⟩ hzS huzS hz2 huz2).mpr
      (by rw [hψz, hψuz]; exact hMS.uz_conj)
  · exact (mem_normalizer_pull ψ hE₁ hu).mpr (by rw [hψu]; exact hMS.u_norm)
  · exact (psi_eq_iff ψ (Subgroup.mul_mem _ hu ht) (Subgroup.mul_mem _ ht hu)).mp
      (by rw [psi_mul ψ hu ht, psi_mul ψ ht hu, hψu, hψt, hMS.ut])
  · intro s hs hsn
    have hsX : s ∈ layerTimesSylow z (S : Subgroup G) := S_le_X _ _ hs
    have hs'S' : ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
        (S' : Subgroup Gs) := (I.mem_S ⟨s, hsX⟩).mp hs
    have hs'n : ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∉
        normalizer (E₁ : Set Gs) := fun h => hsn ((mem_normalizer_pull ψ hE₁ hsX).mpr h)
    obtain ⟨k', hk', hkc⟩ := hMS.coset _ hs'S' hs'n
    obtain ⟨k, hk, hψk⟩ := exists_psi_eq ψ (S_le_X _ _ hk'.1)
    have hkS : k ∈ (S : Subgroup G) := (I.mem_S ⟨k, hk⟩).mpr (by rw [hψk]; exact hk'.1)
    have hkK : k ∈ pull ψ E₁ ⊔ pull ψ E₂ := by
      rw [← pull_sup ψ hE₁ hE₂, mem_pull ψ _ hk, hψk]; exact hk'.2
    have hksX : k * s ∈ layerTimesSylow z (S : Subgroup G) := Subgroup.mul_mem _ hk hsX
    have hψks : ((ψ ⟨k * s, hksX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) =
        k' * ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) := by
      rw [psi_mul ψ hk hsX, hψk]
    have hks2 : orderOf (k * s) = 2 := by
      rw [← orderOf_psi ψ hksX, hψks, ← orderOf_eq_of_isConj hkc]; exact hz'2
    refine ⟨k, ⟨hkS, hkK⟩, ?_⟩
    exact (I.fusion ⟨z, hzX⟩ ⟨k * s, hksX⟩ hzS (Subgroup.mul_mem _ hkS hs) hz2 hks2).mpr
      (by rw [hψz, hψks]; exact hkc)
  · intro s hs hsc
    have hsX : s ∈ layerTimesSylow z (S : Subgroup G) := S_le_X _ _ hs
    have hs'S' : ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
        (S' : Subgroup Gs) := (I.mem_S ⟨s, hsX⟩).mp hs
    have hcomm : ∀ k' ∈ E₁ ⊔ E₂, ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) * k' =
        k' * ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) := by
      intro k' hk'
      have hk'X : k' ∈ layerTimesSylow z' (S' : Subgroup Gs) := sup_le hE₁ hE₂ hk'
      obtain ⟨k, hk, hψk⟩ := exists_psi_eq ψ hk'X
      have hkK : k ∈ pull ψ E₁ ⊔ pull ψ E₂ := by
        rw [← pull_sup ψ hE₁ hE₂, mem_pull ψ _ hk, hψk]; exact hk'
      have hsk := hsc k hkK
      have h2 : ((ψ ⟨s * k, Subgroup.mul_mem _ hsX hk⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) :
          Gs) = ((ψ ⟨k * s, Subgroup.mul_mem _ hk hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) :
          Gs) := by
        have : (⟨s * k, Subgroup.mul_mem _ hsX hk⟩ : ↥(layerTimesSylow z (S : Subgroup G))) =
            ⟨k * s, Subgroup.mul_mem _ hk hsX⟩ := Subtype.ext hsk
        rw [this]
      rw [psi_mul ψ hsX hk, psi_mul ψ hk hsX, hψk] at h2
      exact h2
    have hzp : ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈ zpowers z' :=
      hMS.cs _ hs'S' hcomm
    have hspull : s ∈ pull ψ (zpowers z') := (mem_pull ψ _ hsX).mpr hzp
    rwa [pull_zpowers ψ hzX hψz] at hspull
  · have hSX' : (S' : Subgroup Gs) ≤ layerTimesSylow z' (S' : Subgroup Gs) := S_le_X _ _
    have hS_eq : (S : Subgroup G) = pull ψ (S' : Subgroup Gs) := by
      ext x
      constructor
      · intro hx
        have hxX : x ∈ layerTimesSylow z (S : Subgroup G) := S_le_X _ _ hx
        exact (mem_pull ψ _ hxX).mpr ((I.mem_S ⟨x, hxX⟩).mp hx)
      · intro hx
        have hxX := pull_le ψ _ hx
        exact (I.mem_S ⟨x, hxX⟩).mpr ((mem_pull ψ _ hxX).mp hx)
    have h1 : Nat.card ↥(S : Subgroup G) = Nat.card ↥(S' : Subgroup Gs) := by
      rw [hS_eq]; exact card_pull ψ hSX'
    have h2 : (S : Subgroup G) ⊓ (pull ψ E₁ ⊔ pull ψ E₂) =
        pull ψ ((S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂)) := by
      rw [pull_inf, pull_sup ψ hE₁ hE₂, ← hS_eq]
    have h3 : Nat.card ↥((S : Subgroup G) ⊓ (pull ψ E₁ ⊔ pull ψ E₂)) =
        Nat.card ↥((S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂)) := by
      rw [h2]; exact card_pull ψ (inf_le_left.trans hSX')
    rw [h1, h3]; exact hMS.card_S
  · intro s hs hsn hnc a ha b hb hsa hsb
    have hsX : s ∈ layerTimesSylow z (S : Subgroup G) := S_le_X _ _ hs
    have hs'S' : ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) ∈
        (S' : Subgroup Gs) := (I.mem_S ⟨s, hsX⟩).mp hs
    have hs'n := (mem_normalizer_pull ψ hE₁ hsX).mp hsn
    have haX := pull_le ψ _ ha
    have hbX := pull_le ψ _ hb
    have haE := (mem_pull ψ _ haX).mp ha
    have hbE := (mem_pull ψ _ hbX).mp hb
    have transfer : ∀ (x y : G) (hx : x ∈ layerTimesSylow z (S : Subgroup G))
        (hy : y ∈ layerTimesSylow z (S : Subgroup G)), x * y = y * x →
        ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) *
          ((ψ ⟨y, hy⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) =
        ((ψ ⟨y, hy⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) *
          ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) := by
      intro x y hx hy hxy
      rw [← psi_mul ψ hx hy, ← psi_mul ψ hy hx]
      exact (psi_eq_iff ψ (Subgroup.mul_mem _ hx hy) (Subgroup.mul_mem _ hy hx)).mpr hxy
    have untransfer : ∀ (x y : G) (hx : x ∈ layerTimesSylow z (S : Subgroup G))
        (hy : y ∈ layerTimesSylow z (S : Subgroup G)),
        ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) *
          ((ψ ⟨y, hy⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) =
        ((ψ ⟨y, hy⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) *
          ((ψ ⟨x, hx⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) → x * y = y * x := by
      intro x y hx hy h
      rw [← psi_mul ψ hx hy, ← psi_mul ψ hy hx] at h
      exact (psi_eq_iff ψ (Subgroup.mul_mem _ hx hy) (Subgroup.mul_mem _ hy hx)).mp h
    obtain ⟨k, hk, hkc⟩ := hnc
    have hkX := pull_le ψ _ hk
    have hkE := (mem_pull ψ _ hkX).mp hk
    have hnc' : ∃ k' ∈ E₁, ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) * k' ≠
        k' * ((ψ ⟨s, hsX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) :=
      ⟨_, hkE, fun h => hkc (untransfer s k hsX hkX h)⟩
    exact untransfer a b haX hbX (hMS.cen_ab _ hs'S' hs'n hnc' _ haE _ hbE
      (transfer a s haX hsX hsa) (transfer b s hbX hsX hsb))

end TransportSyl

end CFSG.GH74.GLS.LU.Local
