module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped commutatorElement

section Bin

noncomputable abbrev binRep (M : Type*) [CommGroup M] [Module (ZMod 2) (Additive M)] :
    MulAut M →* Module.End (ZMod 2) (Additive M) :=
  CFSG.RankThree.FFModules.autRep M

variable {M : Type*} [CommGroup M] [Module (ZMod 2) (Additive M)]

theorem binRep_apply (φ : MulAut M) (a : Additive M) :
    binRep M φ a = Additive.ofMul (φ (Additive.toMul a)) := rfl

theorem binRep_injective : Function.Injective (binRep M) :=
  CFSG.RankThree.FFModules.autRep_injective

noncomputable abbrev binModule (hsq : ∀ v : M, v ^ 2 = 1) : Module (ZMod 2) (Additive M) :=
  CFSG.RankThree.FFModules.moduleOfSq hsq

end Bin


section Setting

variable {X : Type} [Group X] (T : Subgroup X)

instance : (gnV T).Normal := by unfold gnV; infer_instance

theorem mem_normalizer_gnV (g : X) :
    g ∈ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Subgroup.Normal.conj_mem inferInstance h hh g
  · intro hh
    have h1 := Subgroup.Normal.conj_mem (inferInstance : (gnV T).Normal) _ hh g⁻¹
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h1

omit [Group X] in
theorem conjClosure_top_eq [Group X] (Z : Subgroup X) :
    conjClosure Z ⊤ = Subgroup.normalClosure (Z : Set X) := by
  unfold conjClosure Subgroup.normalClosure
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Group.mem_conjugatesOfSet_iff, Subgroup.mem_top, true_and,
    isConj_iff]
  constructor
  · rintro ⟨h, z, hz, rfl⟩
    exact ⟨z, hz, h, rfl⟩
  · rintro ⟨z, hz, h, rfl⟩
    exact ⟨h, z, hz, rfl⟩

theorem gnV_eq_conjClosure : gnV T = conjClosure (quasithinOmegaOneCenter T) ⊤ :=
  (conjClosure_top_eq _).symm

section Fin

variable [Finite X]

theorem isElemAbelian_gnV (hGN : GNSetting X T) : IsElemAbelian 2 (gnV T) := by
  have := (conjClosure_isTwoReducedIn_of_charTwo (H := ⊤) hGN.sylow hGN.charTwo
    (Z := quasithinOmegaOneCenter T) le_rfl).2.1
  rwa [← gnV_eq_conjClosure] at this

theorem gnV_le (hGN : GNSetting X T) : gnV T ≤ T := by
  have := (conjClosure_isTwoReducedIn_of_charTwo (H := ⊤) hGN.sylow hGN.charTwo
    (Z := quasithinOmegaOneCenter T) le_rfl).1
  rw [← gnV_eq_conjClosure] at this
  exact this.trans (inf_le_left.trans (pCoreOf_le_of_isSylowTwoOf hGN.sylow))

end Fin

variable {T}

@[expose] noncomputable def gnConj (hV : IsElemAbelian 2 (gnV T)) : X →* MulAut (IntMod (gnV T) hV) :=
  (convI hV).comp
    (MonoidHom.codRestrict (MonoidHom.id X) _ (fun g => mem_normalizer_gnV T g))

theorem gnConj_apply_val (hV : IsElemAbelian 2 (gnV T)) (g : X) (v : IntMod (gnV T) hV) :
    (gnConj hV g v).val = g * v.val * g⁻¹ :=
  convI_apply_val hV ⟨g, mem_normalizer_gnV T g⟩ v

theorem gnConj_eq_one_iff (hV : IsElemAbelian 2 (gnV T)) (g : X) :
    gnConj hV g = 1 ↔ g ∈ gnC T :=
  convI_eq_one_iff hV ⟨g, mem_normalizer_gnV T g⟩

@[expose] noncomputable def gnIota (hV : IsElemAbelian 2 (gnV T)) :
    X ⧸ gnC T →* MulAut (IntMod (gnV T) hV) :=
  QuotientGroup.lift (gnC T) (gnConj hV) (fun g hg => (gnConj_eq_one_iff hV g).2 hg)

theorem gnIota_mk (hV : IsElemAbelian 2 (gnV T)) (g : X) :
    gnIota hV (QuotientGroup.mk g) = gnConj hV g := rfl

theorem gnIota_injective (hV : IsElemAbelian 2 (gnV T)) : Function.Injective (gnIota hV) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | _ g =>
    rw [QuotientGroup.eq_one_iff]
    exact (gnConj_eq_one_iff hV g).1 hq

theorem map_mk_map_gnIota (hV : IsElemAbelian 2 (gnV T)) (A : Subgroup X) :
    (A.map (QuotientGroup.mk' (gnC T))).map (gnIota hV) = autI hV A := by
  ext φ
  rw [mem_autI, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hq
    exact ⟨⟨a, mem_normalizer_gnV T a⟩, ha, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨QuotientGroup.mk g, Subgroup.mem_map_of_mem _ hg, rfl⟩

section Rep

variable (hV : IsElemAbelian 2 (gnV T)) [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

@[expose] noncomputable def gnRep :
    Representation (ZMod 2) (X ⧸ gnC T) (Additive (IntMod (gnV T) hV)) :=
  (binRep (IntMod (gnV T) hV)).comp (gnIota hV)

theorem gnRep_apply (q : X ⧸ gnC T) (a : Additive (IntMod (gnV T) hV)) :
    gnRep hV q a = Additive.ofMul (gnIota hV q (Additive.toMul a)) := rfl

theorem gnRep_injective : Function.Injective (gnRep hV) :=
  (binRep_injective).comp (gnIota_injective hV)

theorem mem_fixSub_gnRep (B : Subgroup (X ⧸ gnC T)) (w : Additive (IntMod (gnV T) hV)) :
    w ∈ fixSub (gnRep hV) B ↔ Additive.toMul w ∈ fixV (B.map (gnIota hV)) :=
  mem_fixSub_autRep_comp (gnIota hV) B w

theorem card_fixSub_gnRep (B : Subgroup (X ⧸ gnC T)) :
    Nat.card (fixSub (gnRep hV) B) = Nat.card (fixV (B.map (gnIota hV))) :=
  card_fixSub_autRep_comp (gnIota hV) B

omit [Module (ZMod 2) (Additive (IntMod (gnV T) hV))] in
theorem card_map_gnIota (B : Subgroup (X ⧸ gnC T)) :
    Nat.card (B.map (gnIota hV)) = Nat.card B :=
  Subgroup.card_map_of_injective (gnIota_injective hV)

end Rep

end Setting


section Offender

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}
  (hV : IsElemAbelian 2 (gnV T)) [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem isBestOffender_gnRep (hGN : GNSetting X T) {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    IsBestOffender (gnRep hV) (A.map (QuotientGroup.mk' (gnC T))) := by
  intro B hB
  have hTN : T ≤ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) :=
    fun g _ => mem_normalizer_gnV T g
  have hBA : B.map (gnIota hV) ≤ autI hV A := by
    rw [← map_mk_map_gnIota hV A]
    exact Subgroup.map_mono hB
  have h := (offender_core hV (gnV_le T hGN) hTN hA hBA).1
  rw [← map_mk_map_gnIota hV A, card_map_gnIota hV, card_map_gnIota hV] at h
  rw [card_fixSub_gnRep hV, card_fixSub_gnRep hV]
  exact h

omit [Finite X] in
theorem isElementaryAbelian_map_mk {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    IsElementaryAbelian 2 (A.map (QuotientGroup.mk' (gnC T))) :=
  BlueprintB2.isElementaryAbelian_map
    ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).1 hA.2.1) _

end Offender


theorem exists_rep_offender (X : Type) [Group X] [Finite X] (T : Subgroup X) (hGN : GNSetting X T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (ρ : Representation (ZMod 2) (X ⧸ gnC T) W), Function.Injective ρ ∧
      ∃ A : Subgroup (X ⧸ gnC T), CFSG.IsElementaryAbelian 2 A ∧
        CFSG.RankThree.FFModules.IsBestOffender ρ A ∧
        A ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ∧ ⁅L, A⁆ = L := by
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hGN
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have hC : CFSG.IsComponent L := (isComponent_iff_open L).2 hL
  have hQ : CFSG.IsQuasisimple L := hC.1
  have hLbot : L ≠ ⊥ := by
    intro h
    have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    subst h
    have : Nontrivial (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) :=
      hs.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
  have hnorm : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := fun A hA =>
    (le_bestOffenderSub (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep hV hGN hA)).trans
      (bestOffenderSub_le_normalizer_component (gnRep hV) hinj hC)
  have key : ∃ A : Subgroup X, IsMaxElemAbelian T A ∧ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L := by
    by_contra hno
    push Not at hno
    have hcen : ∀ A : Subgroup X, IsMaxElemAbelian T A →
        A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
      intro A hA
      by_cases hb : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = ⊥
      · intro a ha l hl
        have : ⁅l, a⁆ ∈ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ := Subgroup.commutator_mem_commutator hl ha
        rw [hb, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.1 this
      · exact absurd (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commutator_eq_of_ne_bot hQ
          (hnorm A hA) hb) (hno A hA)
    have hJle : gnImg T (thompsonJ T) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
      unfold gnImg thompsonJ
      rw [Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hA => hcen A hA
    apply hLbot
    rw [← hJ, eq_bot_iff, Subgroup.commutator_le]
    intro l hl j hj
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 (hJle hj) l hl)
  obtain ⟨A, hAmax, hLA⟩ := key
  exact ⟨Additive (IntMod (gnV T) hV), inferInstance, inferInstance, inferInstance, gnRep hV, hinj,
    A.map (QuotientGroup.mk' (gnC T)), isElementaryAbelian_map_mk hAmax,
    isBestOffender_gnRep hV hGN hAmax, hnorm A hAmax, hLA⟩

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
