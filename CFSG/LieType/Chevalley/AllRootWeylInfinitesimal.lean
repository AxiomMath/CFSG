module

public import CFSG.LieType.Chevalley.AllRootWeylSignsCheck
public import CFSG.LieType.Chevalley.AllRootWeylSignsCheckE7
public import CFSG.LieType.Chevalley.AllRootWeylSignsCheckE8
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem pinnedSignTable_eq : ∀ τ : Tag,
    pinnedSignTable τ = (List.range τ.witnesses.roots.length).map (pinnedSignW τ)
  | .G2 => pinnedSignTable_G2
  | .F4 => pinnedSignTable_F4
  | .D4 => pinnedSignTable_D4
  | .E6 => pinnedSignTable_E6
  | .E7 => pinnedSignTable_E7
  | .E8 => pinnedSignTable_E8

theorem witnessCertTable_eq : ∀ τ : Tag,
    witnessCertTable τ = (List.range τ.witnesses.roots.length).map (witnessCertPos τ)
  | .G2 => witnessCertTable_G2
  | .F4 => witnessCertTable_F4
  | .D4 => witnessCertTable_D4
  | .E6 => witnessCertTable_E6
  | .E7 => witnessCertTable_E7
  | .E8 => witnessCertTable_E8

theorem certWitnessTable_eq : ∀ τ : Tag,
    certWitnessTable τ = (List.range τ.rootCertificate.roots.length).map (certWitnessPos τ)
  | .G2 => certWitnessTable_G2
  | .F4 => certWitnessTable_F4
  | .D4 => certWitnessTable_D4
  | .E6 => certWitnessTable_E6
  | .E7 => certWitnessTable_E7
  | .E8 => certWitnessTable_E8

theorem allRootWeylSigns_row (τ : Tag) (i : Fin τ.rank) :
    (allRootWeylSigns τ).getD i [] =
      (List.range τ.witnesses.roots.length).map (weylSignT τ i) := by
  cases τ
  · fin_cases i
    · exact allRootWeylSigns_G2_row0
    · exact allRootWeylSigns_G2_row1
  · fin_cases i
    · exact allRootWeylSigns_F4_row0
    · exact allRootWeylSigns_F4_row1
    · exact allRootWeylSigns_F4_row2
    · exact allRootWeylSigns_F4_row3
  · fin_cases i
    · exact allRootWeylSigns_D4_row0
    · exact allRootWeylSigns_D4_row1
    · exact allRootWeylSigns_D4_row2
    · exact allRootWeylSigns_D4_row3
  · fin_cases i
    · exact allRootWeylSigns_E6_row0
    · exact allRootWeylSigns_E6_row1
    · exact allRootWeylSigns_E6_row2
    · exact allRootWeylSigns_E6_row3
    · exact allRootWeylSigns_E6_row4
    · exact allRootWeylSigns_E6_row5
  · fin_cases i
    · exact allRootWeylSigns_E7_row0
    · exact allRootWeylSigns_E7_row1
    · exact allRootWeylSigns_E7_row2
    · exact allRootWeylSigns_E7_row3
    · exact allRootWeylSigns_E7_row4
    · exact allRootWeylSigns_E7_row5
    · exact allRootWeylSigns_E7_row6
  · fin_cases i
    · exact allRootWeylSigns_E8_row0
    · exact allRootWeylSigns_E8_row1
    · exact allRootWeylSigns_E8_row2
    · exact allRootWeylSigns_E8_row3
    · exact allRootWeylSigns_E8_row4
    · exact allRootWeylSigns_E8_row5
    · exact allRootWeylSigns_E8_row6
    · exact allRootWeylSigns_E8_row7

theorem allRootWeylSigns_length (τ : Tag) : (allRootWeylSigns τ).length = τ.rank := by
  cases τ <;> rfl

theorem getD_map_range {β : Type*} (f : ℕ → β) (d : β) {n b : ℕ} (hb : b < n) :
    ((List.range n).map f).getD b d = f b := by
  rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_range]

theorem weylSignT_eq_weylSignW
    (i : Fin τ.rank) {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    weylSignT τ i b = weylSignW τ i b := by
  have himg := rootCertificate_image_lt (witnessCertPos_lt hb) i
  unfold weylSignT weylSignW
  rw [pinnedSignTable_eq, witnessCertTable_eq, certWitnessTable_eq, getD_map_range _ _ hb,
    getD_map_range _ _ hb, getD_map_range _ _ himg,
    getD_map_range _ _ (certWitnessPos_lt himg)]

theorem allRootWeylSigns_getD
    (i : Fin τ.rank) {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    ((allRootWeylSigns τ).getD i []).getD b 0 = weylSignW τ i b := by
  rw [allRootWeylSigns_row, getD_map_range _ _ hb, weylSignT_eq_weylSignW i hb]

variable (τ) in
@[expose] def rootColumn (α : Fin τ.rank → ℤ) : ℕ :=
  τ.witnesses.roots.findIdx fun c => decide (decodeVec c = α)

theorem rootColumn_spec
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootColumn τ α < τ.witnesses.roots.length ∧
      decodeVec (τ.witnesses.roots.getD (rootColumn τ α) 0) = α := by
  obtain ⟨m, hm, hroot⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  have hmem : τ.rootCertificate.roots[m] ∈ τ.witnesses.roots :=
    (witnessCheck_spec (τ := τ)).2 _ (List.getElem_mem hm)
  have hex : ∃ x ∈ τ.witnesses.roots, decide (decodeVec (τ := τ) x = α) = true := by
    refine ⟨_, hmem, decide_eq_true ?_⟩
    rw [← hroot, RootCertificate.root, List.getD_eq_getElem _ _ hm]
  have hlt := List.findIdx_lt_length_of_exists hex
  refine ⟨hlt, ?_⟩
  rw [rootColumn, List.getD_eq_getElem _ _ hlt]
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

variable (τ) in
@[expose] def allRootWeylSign (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℤ :=
  ((allRootWeylSigns τ).getD i []).getD (rootColumn τ α) 0

theorem weylElt_mul_pinnedE_mul_weylElt_of_family
    (R : Type) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * pinnedE τ R α *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) =
      (((rootOperatorFamily τ).pinnedFamilySign α * (rootOperatorFamily τ).sign i ⟨α, hα⟩ *
        (rootOperatorFamily τ).pinnedFamilySign (reflect τ i α) : ℤ) : R) •
        pinnedE τ R (reflect τ i α) := by
  set F := rootOperatorFamily τ
  have hβ : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
  have hroot : simple τ i • (⟨α, hα⟩ : Root τ) = ⟨reflect τ i α, hβ⟩ :=
    Subtype.ext (by rw [coe_smul_root, simple_smul])
  have h3 := F.weylElt_mul_D_mul_inv R i ⟨α, hα⟩ 1
  rw [hroot, pow_one] at h3
  have h4 : F.D R ⟨reflect τ i α, hβ⟩ 1 =
      (F.pinnedFamilySign (reflect τ i α) : R) • pinnedE τ R (reflect τ i α) := by
    rw [F.pinnedE_eq_smul_D R hβ, smul_smul, F.pinnedFamilySign_mul_self, one_smul]
  rw [← weylElt_inv, F.pinnedE_eq_smul_D R hα, mul_smul_comm, smul_mul_assoc, h3, h4, smul_smul,
    smul_smul]
  congr 1
  push_cast
  ring

theorem baseChange_pinnedE
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (α : Fin τ.rank → ℤ) : BaseChange f (pinnedE τ R α) (pinnedE τ S α) := by
  have hW := baseChange_prod_reverse_weylElt (τ := τ) f (pinnedData τ α).2.1
  have hx := BaseChange.xCoeff (τ := τ) (f := f) (pinnedData τ α).1 1
  rw [xCoeff_one, xCoeff_one] at hx
  simp only [pinnedE, pinnedWeyl]
  exact ((hW.mul hx).mul (BaseChange.units_inv hW)).intCast_smul _

theorem weylSignW_eq_of_decodeVec
    {b : ℕ} (hb : b < τ.witnesses.roots.length) (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h : decodeVec (τ.witnesses.roots.getD b 0) = α) :
    weylSignW τ i b = (rootOperatorFamily τ).pinnedFamilySign α *
      (rootOperatorFamily τ).sign i ⟨α, hα⟩ *
      (rootOperatorFamily τ).pinnedFamilySign (reflect τ i α) := by
  subst h
  exact weylSignW_eq hb i

theorem allRootWeylSign_eq
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank) :
    allRootWeylSign τ i α = (rootOperatorFamily τ).pinnedFamilySign α *
      (rootOperatorFamily τ).sign i ⟨α, hα⟩ *
      (rootOperatorFamily τ).pinnedFamilySign (reflect τ i α) := by
  obtain ⟨hb, hdec⟩ := rootColumn_spec hα
  rw [allRootWeylSign, allRootWeylSigns_getD i hb, weylSignW_eq_of_decodeVec hb i hα hdec]

theorem weylElt_mul_pinnedE_mul_weylElt
    (R : Type*) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * pinnedE τ R α *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) =
      (allRootWeylSign τ i α : R) • pinnedE τ R (reflect τ i α) := by
  have hZ := weylElt_mul_pinnedE_mul_weylElt_of_family ℤ i hα
  rw [← allRootWeylSign_eq hα i, Int.cast_id] at hZ
  set f := Int.castRingHom R
  have hL : BaseChange f ((weylElt τ ℤ i 1 : Module.End ℤ (RootModule τ ℤ)) * pinnedE τ ℤ α *
        (weylElt τ ℤ i (-1) : Module.End ℤ (RootModule τ ℤ)))
      ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * pinnedE τ R α *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R))) := by
    rw [← weylElt_inv, ← weylElt_inv]
    exact ((BaseChange.weylElt_one i).mul (baseChange_pinnedE f α)).mul
      (BaseChange.units_inv (BaseChange.weylElt_one i))
  have hR := (baseChange_pinnedE (τ := τ) f (reflect τ i α)).intCast_smul (allRootWeylSign τ i α)
  rw [Int.cast_id, ← hZ] at hR
  exact hL.unique hR

theorem all_root_weyl_infinitesimal
    (τ : Tag) :
    (allRootWeylSigns τ).length = τ.rank ∧
    (∀ i : Fin τ.rank, ((allRootWeylSigns τ).getD i []).length = τ.witnesses.roots.length) ∧
    (∀ α, IsRoot τ α → rootColumn τ α < τ.witnesses.roots.length ∧
      decodeVec (τ.witnesses.roots.getD (rootColumn τ α) 0) = α) ∧
    (∀ (i : Fin τ.rank) α, IsRoot τ α →
      allRootWeylSign τ i α = 1 ∨ allRootWeylSign τ i α = -1) ∧
    (∀ (R : Type*) [CommRing R] (i : Fin τ.rank) α, IsRoot τ α →
      (weylElt τ R i 1 : Module.End R (RootModule τ R)) * pinnedE τ R α *
          (weylElt τ R i (-1) : Module.End R (RootModule τ R)) =
        (allRootWeylSign τ i α : R) • pinnedE τ R (reflect τ i α)) ∧
    (∀ (i : Fin τ.rank) α, IsRoot τ α → ∀ σ : ℤ,
      (weylElt τ ℤ i 1 : Module.End ℤ (RootModule τ ℤ)) * pinnedE τ ℤ α *
          (weylElt τ ℤ i (-1) : Module.End ℤ (RootModule τ ℤ)) = σ • pinnedE τ ℤ (reflect τ i α) →
        σ = allRootWeylSign τ i α) ∧
    ∀ α, IsRoot τ α → (pinnedData τ α).2.1.foldl (fun v i => reflect τ (τ.idx i) v)
      (Pi.single (pinnedData τ α).1 1) = α := by
  refine ⟨allRootWeylSigns_length τ, fun i => ?_, fun α hα => rootColumn_spec hα,
    fun i α hα => ?_, fun R _ i α hα => weylElt_mul_pinnedE_mul_weylElt R i hα,
    fun i α hα σ h => ?_, fun α hα => foldl_reflect_pinnedData hα⟩
  · rw [allRootWeylSigns_row, List.length_map, List.length_range]
  · rw [allRootWeylSign_eq hα i]
    rcases (rootOperatorFamily τ).pinnedFamilySign_eq α with h1 | h1 <;>
      rcases (rootOperatorFamily τ).sign_eq i ⟨α, hα⟩ with h2 | h2 <;>
        rcases (rootOperatorFamily τ).pinnedFamilySign_eq (reflect τ i α) with h3 | h3 <;>
          simp [h1, h2, h3]
  · have h' := weylElt_mul_pinnedE_mul_weylElt ℤ i hα
    rw [Int.cast_id] at h'
    exact smul_pinnedE_injective (τ := τ) (R := ℤ) (reflect τ i α) (h.symm.trans h')

end CFSG.LieType.Chevalley
