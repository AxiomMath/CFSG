module

public import CFSG.GF2Type.Smith1980Orth.S3ThmAEnd
public import CFSG.GF2Type.Smith1980Orth.S3ThmACaseI
public import CFSG.GF2Type.Smith1980Orth.S3ThmACaseII
public import CFSG.GF2Type.Smith1980Orth.SixCore
public import CFSG.GF2Type.Smith1980Orth.S3Good
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.GF2Type.Smith1980Orth.Reduction
public import CFSG.GF2Type.Smith1980Orthogonal
public import CFSG.Timmesfeld.Moufang.Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

section Rel

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

theorem commute_of_bad {k : G} (D' : S2Data (S.conjBy k)) (hbad : Bad S k) :
    ∀ u ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G),
      ∀ v ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G), u * v = v * u := by
  have hbad' := hbad.symm
  have hxC' : (S.conjBy k).ρ ⟨_, hbad'.mem_M⟩ ∈ D'.Cbar := by
    by_contra h
    exact D'.not_bad_of_not_mem_Cbar hbad'.mem_M h hbad'
  have hcomm' := D'.lbar_comm_of_bad hbad' hxC'
  intro u hu v hv
  have hQa : (S.conjBy k).Qa k⁻¹ = S.QG := Bad.conjBy_Qa_inv S k
  have huM : u ∈ (S.conjBy k).M := hu.2
  have hvM : v ∈ (S.conjBy k).M := hv.2
  have huL : u ∈ (S.conjBy k).L0 k⁻¹ := ⟨hQa ▸ hu.1, huM⟩
  have hvL : v ∈ (S.conjBy k).L0 k⁻¹ := ⟨hQa ▸ hv.1, hvM⟩
  have h1 := hcomm' _ ⟨⟨u, huM⟩, mem_subgroupOf.mpr huL, rfl⟩ _
    ⟨⟨v, hvM⟩, mem_subgroupOf.mpr hvL, rfl⟩
  have hcM : u * v * u⁻¹ * v⁻¹ ∈ (S.conjBy k).M :=
    (S.conjBy k).M.mul_mem ((S.conjBy k).M.mul_mem ((S.conjBy k).M.mul_mem huM hvM)
      ((S.conjBy k).M.inv_mem huM)) ((S.conjBy k).M.inv_mem hvM)
  have h2 : (S.conjBy k).ρ ⟨u * v * u⁻¹ * v⁻¹, hcM⟩ = 1 := by
    have : (⟨u * v * u⁻¹ * v⁻¹, hcM⟩ : (S.conjBy k).M) =
        ⟨u, huM⟩ * ⟨v, hvM⟩ * (⟨u, huM⟩ : (S.conjBy k).M)⁻¹ * (⟨v, hvM⟩ : (S.conjBy k).M)⁻¹ :=
      rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have h3 : u * v * u⁻¹ * v⁻¹ ∈ S.Qa k := ((S.conjBy k).ρ_eq_one_iff _).mp h2
  rcases S.commutator_eq_one_or_z hu.1 hv.1 with e | e
  · calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
      _ = v * u := by rw [e, one_mul]
  · exfalso
    rw [e] at h3
    exact SMK.z_not_mem_Qa S hbad.not_mem_QG h3

theorem half_of_bad_of_comm {k : G} (hbad : Bad S k)
    (hx1 : S.ρ ⟨_, hbad.mem_M⟩ ∈ M1)
    (hcomm : ∀ u ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G),
      ∀ v ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G), u * v = v * u) : D.BadData k := by
  have hxM := hbad.mem_M
  have hxQ := hbad.not_mem_QG
  have hxC : S.ρ ⟨_, hxM⟩ ∈ D.Cbar := by
    by_contra h
    exact D.not_bad_of_not_mem_Cbar_of_mem_M1 hxM hx1 h hbad
  obtain ⟨hhalf, hfix, hcommQt⟩ := D.half_of_commute hxM hxQ hxC hcomm
  have hdl : S.QG ⊓ S.Qa k = ⊥ ∨ (¬ IsConj S.z (k * S.z * k⁻¹ * S.z) ∧ ∃ p : Vt S D.g D.t,
      p ∈ commSpace (ρV ⟨_, hxC⟩) ∧ D.QV p = 1 ∧
      ∀ v : S.Qt, v ∈ S.clSub (S.QG ⊓ S.Qa k) ↔ ∃ α β : ZMod 2, v = D.coord (α • p, β • p)) := by
    rcases D.residual_of_bad hbad hxC with ⟨-, h⟩ | h | ⟨-, hJ⟩
    · exact Or.inl h
    · exact Or.inr h
    · left
      rw [eq_bot_iff]
      intro d hd
      rw [Subgroup.mem_bot]
      refine hJ d hd ⟨hd.1, ?_⟩
      rw [hcommQt]
      exact S.clSub_centralizer_le_fixQt hxM (S.cl_mem_clSub (SMK.Dl_le_Kz S hd) hd.1)
  have hlfix := D.lbar_fix_of_fixQt_eq hxM hxQ hxC hfix
    (hdl.imp id fun h => h.2)
  have htt : ρV ⟨_, hxC⟩ * ρV ⟨_, hxC⟩ = 1 := LinearEquiv.ext fun w => by
    rw [LinearEquiv.mul_apply, D.resC_resC_apply (rho_conj_mul_self S hxM)]
    rfl
  refine ⟨hbad, hxC, hhalf, hfix, hdl, fun a ha => ?_⟩
  obtain ⟨haC, hfa⟩ := hlfix a ha
  exact ⟨haC, fun v hv => hfa v (commSpace_le_fixSpace htt hv)⟩

end Rel

section Full

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem half_of_bad {k : G} (D' : S2Data (S.conjBy k)) (hbad : Bad S k) : D.BadData k :=
  D.half_of_bad_of_comm hbad (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    (commute_of_bad D' hbad)

end Full

end S2Data


theorem OrthData.nonempty_s2Data_conjBy [IsSimpleGroup G] (I : TimInputs) (O : OrthData S)
    (hw : 6 ≤ S.width) (g : G) : Nonempty (S2Data (S.conjBy g)) :=
  exists_s2Data_of_six_le I (O.conjBy g) (by rw [Setting.width_conjBy]; exact hw)
    twoRankSixBound

theorem OrthData.not_bad [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width)
    (k : G) : ¬ Bad S k := by
  intro hbad
  obtain ⟨D⟩ := exists_s2Data_of_six_le I O hw twoRankSixBound
  refine D.false_of_bad hw (fun T DT j hj hD => ?_) (O.nonempty_s2Data_conjBy I hw)
    (fun g h => (O.conjBy g).nonempty_s2Data_conjBy I
      (by rw [Setting.width_conjBy]; exact hw) h) hbad
  obtain ⟨D'⟩ := hD
  exact DT.half_of_bad D' hj

theorem OrthData.oTypes [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width)
    (D : S2Data S) : D.OTypes := by
  intro x hx hxM hxQ
  obtain ⟨k, rfl⟩ := isConj_iff.mp hx
  exact D.types_of_good hw hxM hxQ (exists_of_not_bad (O.not_bad I hw k) hxM hxQ)

theorem OrthData.oe34a [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width) :
    OE34a S := by
  obtain ⟨D⟩ := exists_s2Data_of_six_le I O hw twoRankSixBound
  exact D.oe34a_of_forall_not_bad (O.not_bad I hw)

theorem OrthData.oDelta [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : 6 ≤ S.width) :
    ODelta S := by
  intro k hxM hxQ hbot
  obtain ⟨a, ha, haΔ⟩ := exists_of_not_bad (O.not_bad I hw k) hxM hxQ
  rw [hbot, Subgroup.mem_bot] at haΔ
  subst haΔ
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  apply S.z_ne_one
  calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
    _ = 1 := by rw [hg]; group

end CFSG.GF2Type.Smith1980Orth
