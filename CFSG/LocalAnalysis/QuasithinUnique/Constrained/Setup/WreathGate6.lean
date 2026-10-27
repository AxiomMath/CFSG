module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate2

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Transport

variable {G : Type} [Group G] [Finite G] {S P V : Subgroup G}

omit [Finite G] in
theorem charTwo_top_of_charTwo (hP : CharTwo P) : CharTwo (⊤ : Subgroup ↥P) := by
  intro x hx
  rw [CFSG.Quasithin.B6.pCoreOf_top] at hx ⊢
  have hxc : (x : G) ∈ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hx.2 q hq
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := hP ⟨x.2, hxc⟩
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

omit [Finite G] in
theorem noCharNormal_top_of (hSP : S ≤ P)
    (hno : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ S → (C.subgroupOf S).Characteristic →
      ¬ P ≤ Subgroup.normalizer (C : Set G)) :
    NoCharNormal (S.subgroupOf P) (⊤ : Subgroup ↥P) := by
  intro C' hC'R hC'ne hC'char hn
  set C : Subgroup G := C'.map P.subtype with hC
  have hCR : C ≤ S := by
    have := Subgroup.map_mono (f := P.subtype) hC'R
    rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this
  have hCP : C ≤ P := hCR.trans hSP
  have hCne : C ≠ ⊥ := by
    intro hb
    exact hC'ne ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hb)
  have hCsub : C.subgroupOf P = C' := Subgroup.comap_map_eq_self_of_injective P.subtype_injective C'
  have hchar : (C.subgroupOf S).Characteristic := by
    let e : ↥(S.subgroupOf P) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSP
    have h1 := characteristic_map_mulEquiv e hC'char
    have h2 : (C'.subgroupOf (S.subgroupOf P)).map e.toMonoidHom = C.subgroupOf S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : ↥P) ∈ C' := hy
        exact ⟨y, hy', rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨⟨x, hSP x.2⟩, ?_⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr x.2
        · show (⟨(x : G), hSP x.2⟩ : ↥P) ∈ C'
          have : (⟨(x : G), hSP x.2⟩ : ↥P) = y := Subtype.ext hyx.symm
          rw [this]
          exact hy
        · rfl
    rw [← h2]
    exact h1
  have hnor : C'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hn)
  refine hno C hCne hCR hchar ?_
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hCP, hCsub]
  exact hnor

omit [Finite G] in
theorem isTwoReducedIn_top_of (hV : IsTwoReducedIn P V) :
    IsTwoReducedIn (⊤ : Subgroup ↥P) (V.subgroupOf P) := by
  have hVP : V ≤ P := hV.1
  have hVn : (V.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).2 hV.2.1
  refine ⟨le_top, top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hVn), ?_, ?_⟩
  · have hel := hV.2.2.1
    have := hel.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact setLike_mul_comm (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
    · have := hel.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
  · intro D' _ hDn hDpow
    have hDnormal : D'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hDn)
    have hD₀P : D'.map P.subtype ≤ P := BlueprintB2.map_subtype_le_self D'
    have hD₀N : P ≤ Subgroup.normalizer ((D'.map P.subtype : Subgroup G) : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hD₀P,
        BlueprintB2.subgroupOf_map_subtype_self]
      exact hDnormal
    have hres := hV.2.2.2 (D'.map P.subtype) hD₀P hD₀N (by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨k, hk⟩ := hDpow d hd
      refine ⟨k, ?_⟩
      have := (BlueprintB2.mem_centralizer_subgroupOf_iff hVP (d ^ 2 ^ k)).mp hk
      simpa using this)
    intro d hd
    exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVP d).mpr (hres ⟨d, hd, rfl⟩)

omit [Finite G] in
theorem solvable_autOn_top (hV : P ≤ Subgroup.normalizer (V : Set G)) (hVP : V ≤ P)
    (hsolv : Group.IsSolvable ↥(autOn P V)) :
    Group.IsSolvable ↥(autOn (⊤ : Subgroup ↥P) (V.subgroupOf P)) := by
  have hVn : (V.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).2 hV
  let e : ↥(V.subgroupOf P) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVP
  have hrho : rho V P hV = (MulAut.congr e).toMonoidHom.comp
      (MulAut.conjNormal : ↥P →* MulAut ↥(V.subgroupOf P)) := by
    apply MonoidHom.ext
    intro p
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [rho_apply_coe]
    simp [e, MulAut.congr_apply, MulAut.conjNormal_apply]
  have hmap : autOn P V = (autOn (⊤ : Subgroup ↥P) (V.subgroupOf P)).map
      (MulAut.congr e).toMonoidHom := by
    rw [← range_rho hV, autOn_eq_map, Subgroup.map_map, hrho, MonoidHom.range_eq_map]
  rw [hmap] at hsolv
  exact (Layer.solvable_map_mulEquiv_iff (MulAut.congr e)).1 hsolv

theorem gateHyp_of_pushUpObstruction (h : PushUpObstruction S P)
    (hsolv : Group.IsSolvable ↥(autOn P (Top.reducedModule S P))) :
    GateHyp (S.subgroupOf P) ((uniqueMaxOver S P).subgroupOf P)
      ((Top.reducedModule S P).subgroupOf P) := by
  have hR := reducedAction_of_pushUpObstruction h
  obtain ⟨hSI, hIP, hmaxI⟩ := uniqueMaxOver_spec h.minParabolic
  have hSP : S ≤ P := h.sylow.1
  have hVP : Top.reducedModule S P ≤ P := hR.reduced.1
  refine GateHyp.of_noChar (Layer.isSylowTwoOf_subgroupOf_top' h.sylow)
    (fun hn => h.minParabolic.2.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mp hn))
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hSI (Subgroup.mem_subgroupOf.mp hx))) ?_ ?_
    (noCharNormal_top_of hSP h.noCharNormal) (isTwoReducedIn_top_of hR.reduced) ?_
    (solvable_autOn_top hR.le_normalizer hVP hsolv)
  · refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hPK : P ≤ uniqueMaxOver S P := fun x hx =>
      Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥P) ∈ (uniqueMaxOver S P).subgroupOf P by
        rw [htop]; trivial)
    exact absurd hPK (not_le_of_gt hIP)
  · intro Y hRY hY
    have hRY' : S ≤ Y.map P.subtype := by
      have := Subgroup.map_mono (f := P.subtype) hRY
      rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this
    have hYP : Y.map P.subtype < P := by
      refine lt_of_le_of_ne (BlueprintB2.map_subtype_le_self Y) fun heq => ?_
      apply (lt_top_iff_ne_top.mp hY)
      refine top_unique fun x _ => ?_
      have hx : (x : G) ∈ Y.map P.subtype := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hmaxI _ hRY' hYP ⟨y, hy, rfl⟩)
  · intro htop
    apply hR.not_le_centralizer
    intro y hy
    exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVP ⟨y, hy⟩).mp (htop (Subgroup.mem_top _))

end Transport

end CFSG.QuasithinUnique.Setup.Wreath
