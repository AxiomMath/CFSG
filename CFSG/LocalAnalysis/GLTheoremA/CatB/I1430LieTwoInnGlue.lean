module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType)

@[expose] def ComponentsNoA6 {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∀ K : Subgroup S, IsComponentOf K (Coordinator.fixSubgroup β) →
    IsEmpty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6))

theorem ComponentsNoA6.of_congr {S G : Type} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    (h : ComponentsNoA6 (MulAut.congr e β)) : ComponentsNoA6 β := by
  intro K hK
  have hfix : Coordinator.fixSubgroup (MulAut.congr e β) =
      (Coordinator.fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [Coordinator.mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [Coordinator.mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hmapc : IsComponentOf (K.map (e : S →* G))
      (Coordinator.fixSubgroup (MulAut.congr e β)) := by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  let g : ↥K ≃* ↥(K.map (e : S →* G)) := K.equivMapOfInjective (e : S →* G) e.injective
  have hZ : (Subgroup.center ↥K).map (g : ↥K →* _) = Subgroup.center ↥(K.map (e : S →* G)) :=
    Subgroup.map_center_eq g
  let g' : (↥K ⧸ Subgroup.center ↥K) ≃*
      (↥(K.map (e : S →* G)) ⧸ Subgroup.center ↥(K.map (e : S →* G))) :=
    QuotientGroup.congr _ _ g hZ
  exact ⟨fun a => (h _ hmapc).false (g'.symm.trans a)⟩

private theorem nonempty_equiv_a6 {T : Type} [Group T] (h : catalogIs T isA6) :
    Nonempty (T ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have h6 : n = 6 := hi
      subst h6
      exact ⟨f⟩
    | _ => exact False.elim hi
  · cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact False.elim hi
        · have hq : q.card = 9 := hi
          rw [TauCeti.LieTypeIndex.valid_iff,
            TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
          exact absurd (Or.inl ⟨rfl, Or.inr (Or.inr hq)⟩) hv.2
        · exact False.elim hi
      | _ => exact False.elim hi
    | _ => exact False.elim hi

theorem not_compOfType_isA6 {S : Type} [Group S] [Finite S] {α : MulAut S}
    (hlayer : PerfectInLayer α) (hno : ComponentsNoA6 α) : ¬ CompOfType S α isA6 := by
  rintro ⟨J, hJ, hT⟩
  obtain ⟨ψ⟩ := nonempty_equiv_a6 hT
  have hJle := hlayer J hJ.1 (glaPComponent_perfect hJ)
  have hJc := (glaPComponent_isComponent_of_le_layer hJ hJle).1
  haveI : Nontrivial (PSimple 3 J) := by
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr ψ.toEquiv, h360]
    norm_num
  obtain ⟨φ⟩ := I1431C2.nonempty_centerQuot_equiv_psimple hJc.2.2 inferInstance
  exact (hno J hJc).false (φ.trans ψ)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
