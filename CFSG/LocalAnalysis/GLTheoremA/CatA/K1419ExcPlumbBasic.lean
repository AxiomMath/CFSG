module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)

theorem l3u3Plumb_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : L3U3 X) :
    L3U3 Y := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem l3u3Pumpup_iff {P : Type} [Group P] (ψ : MulAut P) :
    L3U3Pumpup P ψ ↔ ψ ^ 3 = 1 ∧ ψ ≠ 1 ∧ ¬ NoL3U3Layer ψ := by
  unfold L3U3Pumpup NoL3U3Layer
  constructor
  · rintro ⟨h3, h1, I, hI, hI34⟩
    exact ⟨h3, h1, fun h => h I hI hI34⟩
  · rintro ⟨h3, h1, h⟩
    push Not at h
    obtain ⟨I, hI, hI34⟩ := h
    exact ⟨h3, h1, I, hI, hI34⟩

theorem L3U3Pumpup.of_congr {S T : Type} [Group S] [Finite S] [Group T] [Finite T] (e : S ≃* T)
    {α : MulAut S} (h : L3U3Pumpup S α) : L3U3Pumpup T (MulAut.congr e α) := by
  obtain ⟨hα3, hα1, I, hI, hI34⟩ := h
  have hker : (e : S →* T).ker ≤ Subgroup.center S := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  refine ⟨?_, ?_, I.map (e : S →* T), ?_, ?_⟩
  · rw [← map_pow, hα3, map_one]
  · intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  · exact glaPComponent_map_fixSubgroup (e : S →* T) hker α (MulAut.congr e α)
      (fun y => by simp [MulAut.congr_apply]) e.surjective Nat.prime_three hI
  · let e' : ↥I ≃* ↥(I.map (e : S →* T)) :=
      Subgroup.equivMapOfInjective I (e : S →* T) e.injective
    exact l3u3Plumb_of_mulEquiv (QuotientGroup.congr (GLAPPrimeCore 3 ↥I)
      (GLAPPrimeCore 3 ↥(I.map (e : S →* T))) e'
      (CFSG.HardMathSupport.Timmesfeld.Balance.map_gLAPPrimeCore_mulEquiv 3 e')) hI34

section Simple


theorem l3u3Plumb_isSimpleGroup {X : Type} [Group X] (h : L3U3 X) : IsSimpleGroup X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie])
  | alternating _ _ => exact absurd hi (by simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie])
  | lie d =>
    haveI : IsSimpleGroup d.Group := (CFSG.Assembly.lie_finite_simple d).2
    exact e.isSimpleGroup_congr.mpr inferInstance
  | sporadic _ => exact absurd hi (by simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie])

theorem l3u3Plumb_center_eq_bot {X : Type} [Group X] (h : L3U3 X) (hq : CFSG.Open.IsQuasisimple X) :
    Subgroup.center X = ⊥ := by
  haveI := l3u3Plumb_isSimpleGroup h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
  · exact h0
  · exfalso
    have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [h0]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.2 hsub) hq.2.toNontrivial

end Simple

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
