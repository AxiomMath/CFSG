module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.MinRep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTypeE6

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

theorem e6_dominant : ∀ a : Fin e6Data.d, (∀ i, e6Data.wt a i ≠ -1) → a = ⟨0, by decide⟩ := by
  decide +kernel

theorem e6_reach : reachCheck e6Data 0 20 = true := by decide +kernel

abbrev e6n0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩

theorem e6_wt_zero_aux : ∀ s : Fin (Tag.rank .E6),
    e6Data.wt 0 s = if s = (⟨0, by decide⟩ : Fin (Tag.rank .E6)) then 1 else 0 := by
  decide +kernel

theorem e6_wt_zero (s : Fin TwistTag.E6.tag.rank) :
    e6Data.wt 0 s = if s = e6n0 then 1 else 0 := e6_wt_zero_aux s

theorem e6_wt_one : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) e6n0 = 1 := by decide +kernel

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] def e6Rep27 : Representation K ↥(e6Data_valid.minGroup K) (Fin e6Data.d →₀ K) :=
  pullRep e6Data_valid (MonoidHom.id ↥(e6Data_valid.minGroup K))

@[expose] def e6Y27 : Fin e6Data.d →₀ K := Finsupp.single ⟨0, by decide⟩ 1

@[expose] def e6Chi27 (g : ↥(e6Data_valid.minGroup K)) : K := e6Rep27 K g e6Y27 ⟨0, by decide⟩

theorem e6_xm_mem_U (i : Fin (Tag.rank .E6)) :
    e6Data_valid.xm K (Pi.single i 1) 1 ∈ (e6CoverData K).datum.U :=
  (e6CoverRankOne K).x_mem_lU i 1

theorem e6_hX (i : Fin (Tag.rank .E6)) :
    ∃ g ∈ (e6CoverData K).datum.U, (MonoidHom.id ↥(e6Data_valid.minGroup K)) g =
      e6Data_valid.xm K (Pi.single i 1) 1 := ⟨_, e6_xm_mem_U i, rfl⟩

theorem e6Y27_mem_fixU : (e6Y27 : Fin e6Data.d →₀ K) ∈ (e6CoverData K).datum.fixU (e6Rep27 K) :=
  single_mem_fixU (hV := e6Data_valid) (K := K) (MonoidHom.id _) (e6CoverData K).datum e6_hX
    e6_dominant

theorem e6Y27_ne_zero : (e6Y27 : Fin e6Data.d →₀ K) ≠ 0 := by
  intro h
  have := congrArg (fun v : Fin e6Data.d →₀ K => v ⟨0, by decide⟩) h
  simp [e6Y27] at this

theorem e6Chi27_hm (s : Fin TwistTag.E6.tag.rank) (u : Kˣ) :
    e6Chi27 (e6Data_valid.hm K s u) = ((u ^ (if s = e6n0 then (1 : ℤ) else 0) : Kˣ) : K) := by
  unfold e6Chi27 e6Rep27 e6Y27
  rw [show pullRep e6Data_valid (MonoidHom.id ↥(e6Data_valid.minGroup K))
      (e6Data_valid.hm K s u) (Finsupp.single ⟨0, by decide⟩ 1) = _ from
    minRep_hm_single e6Data_valid s u ⟨0, by decide⟩, e6_wt_zero]
  simp

theorem e6Rep27_H (h : ↥(e6Data_valid.minGroup K))
    (hh : h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K)) :
    e6Rep27 K h e6Y27 = e6Chi27 h • e6Y27 :=
  pullRep_H_smul (hV := e6Data_valid) (K := K) (MonoidHom.id _) (e6CoverData K).datum e6_hX
    e6_dominant hh

theorem e6_heckeT_y (s : Fin TwistTag.E6.tag.rank) [Fintype K] :
    (e6CoverData K).datum.heckeT (e6Rep27 K) s e6Y27 =
      ∑ c : K, e6Rep27 K (e6Data_valid.xm K (Pi.single s 1) c * e6Data_valid.nm K s) e6Y27 := by
  rw [(e6CoverRankOne K).heckeT_datum]
  exact Finset.sum_congr rfl fun c _ => congrArg (fun z => e6Rep27 K (_ * z) e6Y27) (nhat_e6 s)

theorem e6Rep27_isCoverType :
    IsCoverType (e6CoverRankOne K) (e6Rep27 K) e6Y27 e6Chi27 (Finset.univ.erase e6n0) := by
  have := Fintype.ofFinite K
  refine ⟨e6Y27_mem_fixU, e6Y27_ne_zero, e6Rep27_H, fun s => ?_⟩
  by_cases hs : s = e6n0
  · subst hs
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := h
    have h1' : ∀ u : Kˣ, (u : K) = 1 := fun u => by
      have := h1 u
      change e6Chi27 (e6Data_valid.hm K e6n0 u) = 1 at this
      rwa [e6Chi27_hm, if_pos rfl, zpow_one] at this
    have h3 : (e6CoverData K).datum.heckeT (e6Rep27 K) e6n0 e6Y27 = -(∑ c : K, c) • e6Y27 :=
      (e6_heckeT_y e6n0).trans (sum_xm_nm_of_wt_one (hV := e6Data_valid)
        (a₀ := ⟨0, by decide⟩) (s := e6n0) e6_wt_one)
    rw [h3, sum_eq_one_of_units_eq_one h1'] at h2
    exact e6Y27_ne_zero (by simpa using h2)
  · have hw : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) s = 0 := by
      have := e6_wt_zero s
      rw [if_neg hs] at this
      exact this
    refine ⟨fun _ => ⟨fun u => ?_, ?_⟩, fun _ => Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩⟩
    · change e6Chi27 (e6Data_valid.hm K s u) = 1
      rw [e6Chi27_hm, if_neg hs, zpow_zero]
      rfl
    · exact (e6_heckeT_y s).trans (sum_xm_nm_of_wt_zero (hV := e6Data_valid)
        (a₀ := ⟨0, by decide⟩) (s := s) hw)

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
