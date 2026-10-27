module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUE6
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF4Perfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.Steinberg.TwistedE6 (sigma fixedGroup rhoPerm sigma_hm sigma_xm_single
  sigma_xm_neg_single mem_fixedGroup rhoPerm_apply_rhoPerm)
open CFSG.ClassicalInvolution.ModelFacts.A2Isogeny (charHom_toWeight_single_eq_zero
  charHom_toWeight_eq_zero exists_toWeight_eq_three_E6)
open CFSG.LieType.Steinberg.Isogeny (e6IsogenyT ker_e6IsogenyT_le_center eltElement_simpleRoot_E6
  eltElement_neg_simpleRoot_E6)
open scoped commutatorElement

@[expose] def orbitWeightVec : Fin (Tag.rank .E6) → Fin (Tag.rank .E6) → ℤ :=
  ![![2, 2, 3, 4, 3, 2], ![2, 4, 4, 6, 4, 2], ![3, 4, 6, 8, 6, 3], ![4, 6, 8, 12, 8, 4],
    ![3, 4, 6, 8, 6, 3], ![2, 2, 3, 4, 3, 2]]

theorem toWeight_orbit_check : ∀ j : Fin (Tag.rank .E6),
    MinData.toWeight (orbitWeightVec j) = Pi.single j 1 + Pi.single (rhoPerm j) 1 := by
  decide +kernel

section Centre

variable (K : Type) [Field K]

@[expose] noncomputable def charDiag (u : Fin (Tag.rank .E6) → Kˣ) :
    Module.End K (Fin e6Data.d →₀ K) :=
  diagOp fun a => ((Additive.toMul (MinData.Valid.charHom K u (e6Data.wt a)) : Kˣ) : K)

theorem exists_char_sigma_of_mem_iSup_torus {g : e6Data_valid.minGroup K}
    (hg : g ∈ ⨆ i, e6Data_valid.torus K i) :
    ∃ u : Fin (Tag.rank .E6) → Kˣ, e6Data_valid.endo K g = charDiag K u ∧
      e6Data_valid.endo K (sigma K (RingHom.id K) g) = charDiag K (u ∘ rhoPerm) := by
  refine Subgroup.iSup_induction _ (C := fun x => ∃ u : Fin (Tag.rank .E6) → Kˣ,
    e6Data_valid.endo K x = charDiag K u ∧
      e6Data_valid.endo K (sigma K (RingHom.id K) x) = charDiag K (u ∘ rhoPerm)) hg
    (fun j x hx => ?_) ?_ ?_
  · obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus K).1 hx
    have hσ : sigma K (RingHom.id K) (e6Data_valid.hm K j t) =
        e6Data_valid.hm K (rhoPerm j) t := by
      rw [sigma_hm]
      congr 1
    have key : ∀ (i : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → Kˣ), v = Pi.mulSingle i t →
        e6Data_valid.endo K (e6Data_valid.hm K i t) = charDiag K v := by
      rintro i v rfl
      rw [MinData.Valid.endo_hm, MinData.hDiag, charDiag]
      congr 1
      funext a
      rw [MinData.Valid.charHom_apply, Finset.prod_eq_single i
        (fun l _ hl => by simp [Pi.mulSingle_eq_of_ne hl]) (by simp)]
      simp
    refine ⟨Pi.mulSingle j t, key j _ rfl, ?_⟩
    rw [hσ]
    refine key (rhoPerm j) _ ?_
    funext l
    simp only [Function.comp_apply]
    by_cases hl : l = rhoPerm j
    · subst hl
      rw [rhoPerm_apply_rhoPerm, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have hl' : rhoPerm l ≠ j := fun h => hl (by rw [← h, rhoPerm_apply_rhoPerm])
      rw [Pi.mulSingle_eq_of_ne hl', Pi.mulSingle_eq_of_ne hl]
  · refine ⟨1, ?_, ?_⟩
    · rw [MinData.Valid.endo_one, charDiag, ← diagOp_one]
      congr 1
      funext a
      simp [MinData.Valid.charHom_apply]
    · rw [map_one, MinData.Valid.endo_one, charDiag, ← diagOp_one]
      congr 1
      funext a
      simp [MinData.Valid.charHom_apply]
  · rintro x y ⟨u, hux, hσx⟩ ⟨u', huy, hσy⟩
    refine ⟨u * u', ?_, ?_⟩
    · rw [MinData.Valid.endo_mul, hux, huy, charDiag, charDiag, charDiag, diagOp_mul]
      congr 1
      funext a
      simp [MinData.Valid.charHom_apply, mul_zpow, Finset.prod_mul_distrib]
    · rw [map_mul, MinData.Valid.endo_mul, hσx, hσy, charDiag, charDiag, charDiag, diagOp_mul]
      congr 1
      funext a
      simp [MinData.Valid.charHom_apply, mul_zpow, Finset.prod_mul_distrib]

theorem eq_one_of_mem_center_of_sigma_eq {z : e6Data_valid.minGroup K}
    (hz : z ∈ center (e6Data_valid.minGroup K)) (hσ : sigma K (RingHom.id K) z = z) : z = 1 := by
  have hct := e6Datum_isCTGroupDatum K
  have h1 := (CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct
    (e6Datum_steinbergExtras K) (e6Datum_bruhatExtras K)) ▸ hz
  have hzT := CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct (e6Datum_bruhatExtras K) h1
  obtain ⟨u, hu, hσu⟩ := exists_char_sigma_of_mem_iSup_torus K hzT
  rw [hσ] at hσu
  have hdiag : ∀ a : Fin e6Data.d, MinData.Valid.charHom K u (e6Data.wt a) =
      MinData.Valid.charHom K (u ∘ rhoPerm) (e6Data.wt a) := by
    intro a
    have h := congrFun (diagOp_injective (hu.symm.trans hσu)) a
    exact Additive.toMul.injective (Units.ext h)
  have hρ : ∀ i, u i = u (rhoPerm i) := fun i => e6Data_valid.charHom_eq_of_wt K hdiag i
  have hzero := charHom_toWeight_eq_zero K
    (charHom_toWeight_single_eq_zero e6Data_valid K hz (u := u) hu)
  have hu1 : ∀ j, u j = 1 := by
    intro j
    obtain ⟨n, hn⟩ := exists_toWeight_eq_three_E6 j
    have h3 : u j ^ 3 = 1 := by
      have h := hzero n
      rw [hn, map_zsmul] at h
      have h2 := congrArg Additive.toMul h
      rw [toMul_zsmul, MinData.Valid.charHom_single, zpow_natCast] at h2
      exact h2
    have h2 : u j * u (rhoPerm j) = 1 := by
      have h := hzero (orbitWeightVec j)
      rw [toWeight_orbit_check j, map_add] at h
      have h2 := congrArg Additive.toMul h
      rw [toMul_add, MinData.Valid.charHom_single, MinData.Valid.charHom_single] at h2
      exact h2
    rw [← hρ j] at h2
    calc u j = u j ^ 3 * (u j * u j)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  apply e6Data_valid.endo_injective K
  rw [hu, MinData.Valid.endo_one, charDiag, ← diagOp_one]
  congr 1
  funext a
  simp [MinData.Valid.charHom_apply, hu1]

end Centre

local instance e7ClassUF4IsoNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def f4Idx (j : Fin 4) : Fin Tag.F4.rank := ⟨j.1, j.2⟩

@[expose] def uOrbitWordE6 : Fin 4 → List (Fin (Tag.rank .E6)) := ![[1], [3], [2, 4], [0, 5]]

theorem orbitWord_check (j : Fin 4) :
    TwistTag.E6.orbitWord (f4FoldedIndex (f4Idx j)) = uOrbitWordE6 j := by
  fin_cases j <;> rfl

theorem orbitWord_map_e6Node : ∀ j : Fin 4, (uOrbitWordE6 j).map e6Node = uOrbitWord j := by
  decide

theorem rhoPerm_check : rhoPerm 1 = 1 ∧ rhoPerm 3 = 3 ∧ rhoPerm 2 = 4 ∧ rhoPerm 4 = 2 ∧
    rhoPerm 0 = 5 ∧ rhoPerm 5 = 0 := by
  decide

variable (K : Type) [Field K]

@[expose] noncomputable def uOrbitSCX (j : Fin 4) (c : K) : e6Data_valid.minGroup K :=
  ((uOrbitWordE6 j).map fun i => e6Data_valid.xm K (Pi.single i 1) c).prod

@[expose] noncomputable def uOrbitSCY (j : Fin 4) (c : K) : e6Data_valid.minGroup K :=
  ((uOrbitWordE6 j).map fun i => e6Data_valid.xm K (-Pi.single i 1) c).prod

@[expose] noncomputable def uF4SC : Subgroup (e6Data_valid.minGroup K) :=
  closure {g | ∃ (j : Fin 4) (c : K), g = uOrbitSCX K j c ∨ g = uOrbitSCY K j c}

variable {K}

theorem commute_xm_of_isRootB {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (hne : γ + δ ≠ 0)
    (hr : CFSG.LieType.Chevalley.RootOps.isRootB .E6 (γ + δ) = false) (c d : K) :
    Commute (e6Data_valid.xm K γ c) (e6Data_valid.xm K δ d) := by
  have hr' : ¬ IsRoot .E6 (γ + δ) := fun h => by
    rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff, hr] at h
    exact Bool.false_ne_true h
  exact commutatorElement_eq_one_iff_commute.1
    ((e6Data_valid.commutator_xm K hγ hδ hne).2 hr' c d)

theorem orbitPair_check :
    (CFSG.LieType.Chevalley.RootOps.isRootB .E6
        ((Pi.single 4 1 : Fin (Tag.rank .E6) → ℤ) + Pi.single 2 1) = false ∧
      (Pi.single 4 1 : Fin (Tag.rank .E6) → ℤ) + Pi.single 2 1 ≠ 0) ∧
    (CFSG.LieType.Chevalley.RootOps.isRootB .E6
        (-(Pi.single 4 1 : Fin (Tag.rank .E6) → ℤ) + -Pi.single 2 1) = false ∧
      -(Pi.single 4 1 : Fin (Tag.rank .E6) → ℤ) + -Pi.single 2 1 ≠ 0) ∧
    (CFSG.LieType.Chevalley.RootOps.isRootB .E6
        ((Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) + Pi.single 0 1) = false ∧
      (Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) + Pi.single 0 1 ≠ 0) ∧
    (CFSG.LieType.Chevalley.RootOps.isRootB .E6
        (-(Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) + -Pi.single 0 1) = false ∧
      -(Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) + -Pi.single 0 1 ≠ 0) := by
  decide +kernel

theorem uOrbitSC_mem_fixedGroup (j : Fin 4) (c : K) :
    uOrbitSCX K j c ∈ fixedGroup K (RingHom.id K) ∧
      uOrbitSCY K j c ∈ fixedGroup K (RingHom.id K) := by
  obtain ⟨r1, r3, r2, r4, r0, r5⟩ := rhoPerm_check
  obtain ⟨⟨p1, p1'⟩, ⟨p2, p2'⟩, ⟨p3, p3'⟩, ⟨p4, p4'⟩⟩ := orbitPair_check
  rw [mem_fixedGroup, mem_fixedGroup, uOrbitSCX, uOrbitSCY]
  fin_cases j
  · show sigma K (RingHom.id K) (e6Data_valid.xm K (Pi.single 1 1) c * 1) =
        e6Data_valid.xm K (Pi.single 1 1) c * 1 ∧
      sigma K (RingHom.id K) (e6Data_valid.xm K (-Pi.single 1 1) c * 1) =
        e6Data_valid.xm K (-Pi.single 1 1) c * 1
    rw [map_mul, map_mul, map_one, sigma_xm_single, sigma_xm_neg_single, r1, RingHom.id_apply]
    exact ⟨rfl, rfl⟩
  · show sigma K (RingHom.id K) (e6Data_valid.xm K (Pi.single 3 1) c * 1) =
        e6Data_valid.xm K (Pi.single 3 1) c * 1 ∧
      sigma K (RingHom.id K) (e6Data_valid.xm K (-Pi.single 3 1) c * 1) =
        e6Data_valid.xm K (-Pi.single 3 1) c * 1
    rw [map_mul, map_mul, map_one, sigma_xm_single, sigma_xm_neg_single, r3, RingHom.id_apply]
    exact ⟨rfl, rfl⟩
  · show sigma K (RingHom.id K) (e6Data_valid.xm K (Pi.single 2 1) c *
          (e6Data_valid.xm K (Pi.single 4 1) c * 1)) =
        e6Data_valid.xm K (Pi.single 2 1) c * (e6Data_valid.xm K (Pi.single 4 1) c * 1) ∧
      sigma K (RingHom.id K) (e6Data_valid.xm K (-Pi.single 2 1) c *
          (e6Data_valid.xm K (-Pi.single 4 1) c * 1)) =
        e6Data_valid.xm K (-Pi.single 2 1) c * (e6Data_valid.xm K (-Pi.single 4 1) c * 1)
    rw [map_mul, map_mul, map_mul, map_mul, map_one, sigma_xm_single, sigma_xm_single,
      sigma_xm_neg_single, sigma_xm_neg_single, r2, r4, RingHom.id_apply, mul_one, mul_one]
    exact ⟨(commute_xm_of_isRootB (isRoot_single .E6 4) (isRoot_single .E6 2) p1' p1 c c).eq,
      (commute_xm_of_isRootB (isRoot_neg_single .E6 4) (isRoot_neg_single .E6 2) p2' p2 c c).eq⟩
  · show sigma K (RingHom.id K) (e6Data_valid.xm K (Pi.single 0 1) c *
          (e6Data_valid.xm K (Pi.single 5 1) c * 1)) =
        e6Data_valid.xm K (Pi.single 0 1) c * (e6Data_valid.xm K (Pi.single 5 1) c * 1) ∧
      sigma K (RingHom.id K) (e6Data_valid.xm K (-Pi.single 0 1) c *
          (e6Data_valid.xm K (-Pi.single 5 1) c * 1)) =
        e6Data_valid.xm K (-Pi.single 0 1) c * (e6Data_valid.xm K (-Pi.single 5 1) c * 1)
    rw [map_mul, map_mul, map_mul, map_mul, map_one, sigma_xm_single, sigma_xm_single,
      sigma_xm_neg_single, sigma_xm_neg_single, r0, r5, RingHom.id_apply, mul_one, mul_one]
    exact ⟨(commute_xm_of_isRootB (isRoot_single .E6 5) (isRoot_single .E6 0) p3' p3 c c).eq,
      (commute_xm_of_isRootB (isRoot_neg_single .E6 5) (isRoot_neg_single .E6 0) p4' p4 c c).eq⟩

theorem uF4SC_le_fixedGroup : uF4SC K ≤ fixedGroup K (RingHom.id K) :=
  (closure_le _).2 fun _ ⟨j, c, h⟩ => h.elim (fun h => h ▸ (uOrbitSC_mem_fixedGroup j c).1)
    (fun h => h ▸ (uOrbitSC_mem_fixedGroup j c).2)

theorem uF4SC_inf_center :
    uF4SC K ⊓ center (e6Data_valid.minGroup K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  exact (mem_bot).2 (eq_one_of_mem_center_of_sigma_eq K (mem_inf.1 hz).2
    ((mem_fixedGroup _).1 (uF4SC_le_fixedGroup (mem_inf.1 hz).1)))

section Iso

variable [Finite K] [CharP K 2]

theorem coe_e6ToE7_uOrbitSC (j : Fin 4) (c : K) :
    ((e6ToE7 K (uOrbitSCX K j c) : adjointGroup .E7 K) : ModGL .E7 K) = uOrbitX K j c ∧
      ((e6ToE7 K (uOrbitSCY K j c) : adjointGroup .E7 K) : ModGL .E7 K) = uOrbitY K j c := by
  constructor
  · rw [uOrbitSCX, map_list_prod, List.map_map, SubmonoidClass.coe_list_prod, List.map_map,
      uOrbitX, ← orbitWord_map_e6Node j, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    rw [e6ToE7_xm (isRoot_single .E6 i), coe_e6LeviPar, e6Embed_single]
  · rw [uOrbitSCY, map_list_prod, List.map_map, SubmonoidClass.coe_list_prod, List.map_map,
      uOrbitY, ← orbitWord_map_e6Node j, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    rw [e6ToE7_xm (isRoot_neg_single .E6 i), coe_e6LeviPar, e6Embed_neg, e6Embed_single]

theorem map_e6ToE7_uF4SC : (uF4SC K).map (e6ToE7 K) = uF4AS K := by
  rw [uF4SC, MonoidHom.map_closure, uF4AS]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨j, c, rfl | rfl⟩, rfl⟩
    · exact ⟨j, c, Or.inl (coe_e6ToE7_uOrbitSC j c).1⟩
    · exact ⟨j, c, Or.inr (coe_e6ToE7_uOrbitSC j c).2⟩
  · rintro ⟨j, c, h | h⟩
    · exact ⟨_, ⟨j, c, Or.inl rfl⟩, Subtype.ext ((coe_e6ToE7_uOrbitSC j c).1.trans h.symm)⟩
    · exact ⟨_, ⟨j, c, Or.inr rfl⟩, Subtype.ext ((coe_e6ToE7_uOrbitSC j c).2.trans h.symm)⟩

theorem e6ToE7_injOn_uF4SC {g h : e6Data_valid.minGroup K} (hg : g ∈ uF4SC K)
    (hh : h ∈ uF4SC K) (e : e6ToE7 K g = e6ToE7 K h) : g = h := by
  have hk : g * h⁻¹ ∈ (e6ToE7 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, mul_inv_cancel]
  have hz : g * h⁻¹ ∈ uF4SC K ⊓ center (e6Data_valid.minGroup K) :=
    mem_inf.2 ⟨mul_mem hg (inv_mem hh), ker_e6ToE7_le_center hk⟩
  rw [uF4SC_inf_center, mem_bot] at hz
  exact mul_inv_eq_one.1 hz

variable (K) in
@[expose] noncomputable def uF4SCEquivAS : uF4SC K ≃* uF4AS K :=
  MulEquiv.ofBijective
    (((e6ToE7 K).comp (uF4SC K).subtype).codRestrict (uF4AS K) fun g => by
      rw [← map_e6ToE7_uF4SC]
      exact ⟨g, g.2, rfl⟩)
    ⟨fun g h e => Subtype.ext (e6ToE7_injOn_uF4SC g.2 h.2 (congrArg Subtype.val e)), by
      rintro ⟨x, hx⟩
      rw [← map_e6ToE7_uF4SC] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      exact ⟨⟨g, hg⟩, rfl⟩⟩

theorem coe_e6IsogenyT_uOrbitSC (j : Fin 4) (c : K) :
    ((e6IsogenyT K (uOrbitSCX K j c) : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = f4OrbitXUnit K (f4Idx j) c ∧
      ((e6IsogenyT K (uOrbitSCY K j c) : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = f4OrbitYUnit K (f4Idx j) c := by
  constructor
  · rw [uOrbitSCX, map_list_prod, List.map_map, SubmonoidClass.coe_list_prod, List.map_map,
      f4OrbitXUnit, orbitWord_check j]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    change ((e6Isogeny K (e6Data_valid.xm K (Pi.single i 1) c) : adjointGroup .E6 K) :
      ModGL .E6 K) = _
    rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]
    rfl
  · rw [uOrbitSCY, map_list_prod, List.map_map, SubmonoidClass.coe_list_prod, List.map_map,
      f4OrbitYUnit, orbitWord_check j]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    change ((e6Isogeny K (e6Data_valid.xm K (-Pi.single i 1) c) : adjointGroup .E6 K) :
      ModGL .E6 K) = _
    rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
    rfl

theorem map_e6IsogenyT_uF4SC :
    (uF4SC K).map ((adjointGroup TwistTag.E6.tag K).subtype.comp (e6IsogenyT K)) =
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  rw [twistedFixedGroup_id_eq_closure, uF4SC, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨j, c, rfl | rfl⟩, rfl⟩
    · exact ⟨f4Idx j, c, Or.inl (coe_e6IsogenyT_uOrbitSC j c).1⟩
    · exact ⟨f4Idx j, c, Or.inr (coe_e6IsogenyT_uOrbitSC j c).2⟩
  · rintro ⟨j, c, rfl | rfl⟩
    · exact ⟨_, ⟨⟨j.1, j.2⟩, c, Or.inl rfl⟩, (coe_e6IsogenyT_uOrbitSC ⟨j.1, j.2⟩ c).1⟩
    · exact ⟨_, ⟨⟨j.1, j.2⟩, c, Or.inr rfl⟩, (coe_e6IsogenyT_uOrbitSC ⟨j.1, j.2⟩ c).2⟩

theorem e6IsogenyT_injOn_uF4SC {g h : e6Data_valid.minGroup K} (hg : g ∈ uF4SC K)
    (hh : h ∈ uF4SC K) (e : e6IsogenyT K g = e6IsogenyT K h) : g = h := by
  have hk : g * h⁻¹ ∈ (e6IsogenyT K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, mul_inv_cancel]
  have hz : g * h⁻¹ ∈ uF4SC K ⊓ center (e6Data_valid.minGroup K) :=
    mem_inf.2 ⟨mul_mem hg (inv_mem hh), ker_e6IsogenyT_le_center K hk⟩
  rw [uF4SC_inf_center, mem_bot] at hz
  exact mul_inv_eq_one.1 hz

variable (K) in
@[expose] noncomputable def uF4SCEquivFixed :
    uF4SC K ≃* twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  MulEquiv.ofBijective
    ((((adjointGroup TwistTag.E6.tag K).subtype.comp (e6IsogenyT K)).comp
      (uF4SC K).subtype).codRestrict _ fun g => by
        rw [← map_e6IsogenyT_uF4SC]
        exact ⟨g, g.2, rfl⟩)
    ⟨fun g h e => Subtype.ext (e6IsogenyT_injOn_uF4SC g.2 h.2
        (Subtype.ext (by
          have e' := congrArg Subtype.val e
          exact e'))), by
      rintro ⟨x, hx⟩
      rw [← map_e6IsogenyT_uF4SC] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      exact ⟨⟨g, hg⟩, rfl⟩⟩

variable (K) in
@[expose] noncomputable def uF4ASEquiv : uF4AS K ≃* adjointGroup .F4 K :=
  (uF4SCEquivAS K).symm.trans ((uF4SCEquivFixed K).trans (e6FixedF4Equiv K CharTwo.two_eq_zero))

variable (K) in
@[expose] noncomputable def uF4Equiv : uF4 K ≃* adjointGroup .F4 K :=
  ((MulAut.conj (e7RepConj K 3)).subgroupMap (uF4AS K)).symm.trans (uF4ASEquiv K)

omit [CharP K 2] in
theorem isSimpleGroup_adjointGroup_f4 : IsSimpleGroup (adjointGroup .F4 K) := by
  have h : IsSimpleGroup (adjointGroup .F4 K ⧸ center (adjointGroup .F4 K)) :=
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isSimpleGroup_uF4 : IsSimpleGroup (uF4 K) := by
  have := isSimpleGroup_adjointGroup_f4 (K := K)
  exact (uF4Equiv K).isSimpleGroup

theorem forall_normal_isPGroup_eq_bot_uF4 (N : Subgroup (uF4 K)) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have := isSimpleGroup_uF4 (K := K)
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    subst h
    have hP : IsPGroup 2 (uF4 K) :=
      h2.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup (uF4 K)) ≃* uF4 K)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite (uF4 K) := inferInstance
    have hsol : Group.IsSolvable (uF4 K) := by
      have := hP.isNilpotent
      exact inferInstance
    have hperf : commutator (uF4 K) = ⊤ := by
      have e := commutator_uF4 (K := K)
      rw [_root_.commutator_def]
      apply Subgroup.map_injective (uF4 K).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact e
    obtain ⟨n, hn⟩ := hsol.solvable
    have hall : ∀ m, derivedSeries (uF4 K) m = ⊤ := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hperf]
    rw [hall n] at hn
    exact (top_ne_bot : (⊤ : Subgroup (uF4 K)) ≠ ⊥) hn

end Iso

end CFSG.SeitzReduction.E7Pilot
