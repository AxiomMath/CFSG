module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Open.GLADefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open

section Generic

variable {X Y : Type} [Group X] [Group Y]

theorem isComponentOf_top_map (Q : X ≃* Y) (M : Subgroup X) (h : IsComponentOf M ⊤) :
    IsComponentOf (M.map Q.toMonoidHom) ⊤ := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨le_top, ?_, ?_⟩
  · have h' := CFSG.Open.IsSubnormal.map Q.toMonoidHom h2
    rwa [Subgroup.map_top_of_surjective Q.toMonoidHom Q.surjective] at h'
  · exact (CFSG.Open.IsQuasisimple.congr (M.equivMapOfInjective Q.toMonoidHom Q.injective)).1 h3

theorem map_map_symm_eq (Q : X ≃* Y) (M : Subgroup X) :
    (M.map Q.toMonoidHom).map Q.symm.toMonoidHom = M := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨Q x, ⟨x, hx, rfl⟩, by simp⟩

theorem isComponentOf_top_iff_map (Q : X ≃* Y) (M : Subgroup X) :
    IsComponentOf M ⊤ ↔ IsComponentOf (M.map Q.toMonoidHom) ⊤ := by
  refine ⟨isComponentOf_top_map Q M, fun h => ?_⟩
  have h' := isComponentOf_top_map Q.symm (M.map Q.toMonoidHom) h
  rwa [map_map_symm_eq] at h'

end Generic

section Sub

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_iff {J A L : Subgroup G} (hLA : L ≤ A) (hAJ : A ≤ J) :
    IsSubnormal L A ↔ IsSubnormal (L.subgroupOf J) (A.subgroupOf J) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := CFSG.Open.IsSubnormal.comap J.subtype h
    rwa [Subgroup.comap_subtype, Subgroup.comap_subtype] at h'
  · have h' := CFSG.Open.IsSubnormal.map J.subtype h
    rwa [Subgroup.map_subgroupOf_eq_of_le (hLA.trans hAJ),
      Subgroup.map_subgroupOf_eq_of_le hAJ] at h'

theorem map_subgroupOf_equiv {J A : Subgroup G} (hAJ : A ≤ J) (Y : Subgroup J) :
    (Y.subgroupOf (A.subgroupOf J)).map (Subgroup.subgroupOfEquivOfLe hAJ).toMonoidHom =
      (Y.map J.subtype).subgroupOf A := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.2 ⟨w.1, Subgroup.mem_subgroupOf.1 hw, rfl⟩
  · intro hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz
    have hyA : y ∈ A.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      have hyz' : (y : G) = (z : G) := hyz
      rw [hyz']
      exact z.2
    refine ⟨⟨y, hyA⟩, ?_, ?_⟩
    · exact hy
    · exact Subtype.ext hyz

theorem map_primeCore_subgroupOf {p : ℕ} {J A : Subgroup G} (hAJ : A ≤ J) :
    (GLAPPrimeCore p ↥(A.subgroupOf J)).map (Subgroup.subgroupOfEquivOfLe hAJ).toMonoidHom =
      GLAPPrimeCore p ↥A :=
  CFSG.pPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hAJ)

theorem glaPComponent_subgroupOf {p : ℕ} {J A L : Subgroup G} (hAJ : A ≤ J)
    (h : GLAPComponent p A L) : GLAPComponent p (A.subgroupOf J) (L.subgroupOf J) := by
  unfold GLAPComponent at h ⊢
  obtain ⟨hLA, hsub, hcomp, hmin⟩ := h
  have hLJ : L ≤ J := hLA.trans hAJ
  let e : ↥(A.subgroupOf J) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAJ
  let Q : ↥(A.subgroupOf J) ⧸ GLAPPrimeCore p ↥(A.subgroupOf J) ≃*
      ↥A ⧸ GLAPPrimeCore p ↥A :=
    QuotientGroup.congr _ _ e (map_primeCore_subgroupOf hAJ)
  have hfun : Q.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥(A.subgroupOf J))) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥A)).comp e.toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk _ _ e (map_primeCore_subgroupOf hAJ) x
  have hcomp_map : ∀ Y : Subgroup J,
      ((Y.subgroupOf (A.subgroupOf J)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(A.subgroupOf J)))).map
          Q.toMonoidHom =
        ((Y.map J.subtype).subgroupOf A).map (QuotientGroup.mk' (GLAPPrimeCore p ↥A)) := by
    intro Y
    rw [Subgroup.map_map, ← map_subgroupOf_equiv hAJ Y, Subgroup.map_map, hfun]
  have hLmap : ((L.subgroupOf J).map J.subtype) = L := Subgroup.map_subgroupOf_eq_of_le hLJ
  have hAmap : ((A.subgroupOf J).map J.subtype) = A := Subgroup.map_subgroupOf_eq_of_le hAJ
  refine ⟨Subgroup.comap_mono hLA, (isSubnormal_subgroupOf_iff hLA hAJ).1 hsub, ?_, ?_⟩
  · refine (isComponentOf_top_iff_map Q _).2 ?_
    rw [hcomp_map (L.subgroupOf J), hLmap]
    exact hcomp
  · intro K hKlt hKsub heq
    have hK0lt : K.map J.subtype < L := by
      rw [← hLmap]
      refine lt_of_le_of_ne (Subgroup.map_mono hKlt.le) ?_
      intro heq'
      exact hKlt.ne (Subgroup.map_injective Subtype.val_injective heq')
    have hK0sub : IsSubnormal (K.map J.subtype) A := by
      have h := CFSG.Open.IsSubnormal.map J.subtype hKsub
      rwa [hAmap] at h
    apply hmin (K.map J.subtype) hK0lt hK0sub
    have h2 := congrArg (fun S => S.map Q.toMonoidHom) heq
    rw [hcomp_map K, hcomp_map (L.subgroupOf J), hLmap] at h2
    exact h2

end Sub

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
