module

public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.NodeAux
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def ConclusionFor (H : Type) [Group H] : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), IsElemAbelian 2 N ∧
    (ZStarCase (H ⧸ N) ∨ IsCoveringOfList (H ⧸ N))

theorem thmAConclusion_iff {G : Type} [Group G] (T : Subgroup G) :
    ThmAConclusion T ↔ ConclusionFor ↥(Subgroup.normalClosure (T : Set G)) :=
  Iff.rfl

section Transport

variable {H H' : Type*} [Group H] [Group H']

theorem fusionOddCore_le_map_mulEquiv (e : H ≃* H') :
    fusionOddCore H' ≤ (fusionOddCore H).map e.toMonoidHom := by
  refine sSup_le ?_
  rintro N' ⟨hN', hodd⟩
  intro x hx
  rw [Subgroup.mem_map_equiv]
  have hnormal : (N'.map e.symm.toMonoidHom).Normal := hN'.map _ e.symm.surjective
  have hcard : Odd (Nat.card (N'.map e.symm.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective e.symm.injective]
  have hle : N'.map e.symm.toMonoidHom ≤ fusionOddCore H := le_sSup ⟨hnormal, hcard⟩
  exact hle ⟨x, hx, rfl⟩

theorem fusionOddCore_map_mulEquiv (e : H ≃* H') :
    (fusionOddCore H).map e.toMonoidHom = fusionOddCore H' := by
  refine le_antisymm ?_ (fusionOddCore_le_map_mulEquiv e)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := fusionOddCore_le_map_mulEquiv e.symm hy
  have hzy' : e y = z := by
    rw [← hzy]
    exact e.apply_symm_apply z
  rw [show (e.toMonoidHom : H → H') y = e y from rfl, hzy']
  exact hz

theorem mem_fusionZStar_iff {x : H} :
    x ∈ fusionZStar H ↔ ∀ y : H, (y * x)⁻¹ * (x * y) ∈ fusionOddCore H := by
  unfold fusionZStar
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro h y
    exact QuotientGroup.eq.1 (h (QuotientGroup.mk' (fusionOddCore H) y))
  · intro h g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    exact QuotientGroup.eq.2 (h y)

theorem zStarCase_iff :
    ZStarCase H ↔ ∀ x y : H, (y * x)⁻¹ * (x * y) ∈ fusionOddCore H := by
  unfold ZStarCase
  rw [eq_top_iff]
  constructor
  · intro h x y
    exact mem_fusionZStar_iff.1 (h (Subgroup.mem_top x)) y
  · intro h x _
    exact mem_fusionZStar_iff.2 (h x)

theorem zStarCase_of_mulEquiv (e : H ≃* H') (h : ZStarCase H) : ZStarCase H' := by
  rw [zStarCase_iff] at h ⊢
  intro x y
  have hmem : e ((e.symm y * e.symm x)⁻¹ * (e.symm x * e.symm y)) ∈ fusionOddCore H' := by
    rw [← fusionOddCore_map_mulEquiv e]
    exact Subgroup.mem_map_of_mem _ (h (e.symm x) (e.symm y))
  simpa using hmem

theorem map_commutator_mulEquiv (e : H ≃* H') :
    (commutator H).map e.toMonoidHom = commutator H' := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem isCoveringOfList_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    IsCoveringOfList H → IsCoveringOfList H' := by
  rintro ⟨hperfect, Z, hZ, hnormal, hlist⟩
  have hnormal' : (Z.map e.toMonoidHom).Normal := hnormal.map _ e.surjective
  refine ⟨?_, Z.map e.toMonoidHom, ?_, hnormal', ?_⟩
  · rw [← map_commutator_mulEquiv e, hperfect, Subgroup.map_top_of_surjective _ e.surjective]
  · exact (Subgroup.map_mono hZ).trans (Subgroup.map_center_le_center e.surjective)
  · exact ListGroup.of_mulEquiv (QuotientGroup.congr Z (Z.map e.toMonoidHom) e rfl) hlist

theorem isElemAbelian_map_mulEquiv {p : ℕ} (e : H ≃* H') {E : Subgroup H}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map e.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem conclusionFor_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    ConclusionFor H → ConclusionFor H' := by
  rintro ⟨N, hN, habel, hcase⟩
  have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
  refine ⟨N.map e.toMonoidHom, hN', isElemAbelian_map_mulEquiv e habel, ?_⟩
  have φ : H ⧸ N ≃* H' ⧸ N.map e.toMonoidHom := QuotientGroup.congr N _ e rfl
  rcases hcase with h | h
  · exact Or.inl (zStarCase_of_mulEquiv φ h)
  · exact Or.inr (isCoveringOfList_of_mulEquiv φ h)

end Transport

end CFSG.CGT.Timmesfeld75
