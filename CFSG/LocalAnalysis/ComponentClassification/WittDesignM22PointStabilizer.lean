module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneCollineation
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Fischer
open scoped Pointwise

theorem eq_top_of_not_dvd_factorial_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (h : ¬Nat.card G ∣ H.index.factorial) : H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
  · exfalso
    apply h
    have := H.index_normalCore_dvd_factorial_index
    rwa [hb, Subgroup.index_bot] at this
  · exact eq_top_iff.2 (ht ▸ H.normalCore_le)

theorem eq_of_relIndex_le_six {K : Type*} [Group K] [Finite K] {N I L : Subgroup K}
    (hI : I ≤ L) (hidx : N.relIndex L ≤ 6) (hcard : Nat.card I = Nat.card N)
    (hsimple : IsSimpleGroup N) (hbig : ¬Nat.card N ∣ 720) : I = N := by
  have h1 : N.relIndex I ≤ 6 :=
    (Subgroup.relIndex_le_of_le_right hI
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)).trans hidx
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := I)
  have h3 := Subgroup.relIndex_mul_card (H := I) (K := N)
  rw [inf_comm] at h3
  have hpos : 0 < Nat.card (N ⊓ I : Subgroup K) := Nat.card_pos
  have h4 : I.relIndex N = N.relIndex I := by
    rw [hcard] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos (h3.trans h2.symm)
  have hJ : I.subgroupOf N = ⊤ := by
    refine eq_top_of_not_dvd_factorial_index _ fun hd => hbig (hd.trans ?_)
    rw [← Subgroup.relIndex, h4]
    exact (Nat.factorial_dvd_factorial h1).trans (by decide)
  have hNI : N ≤ I := Subgroup.subgroupOf_eq_top.1 hJ
  exact (Subgroup.eq_of_le_of_card_ge hNI hcard.le).symm

variable (a : Fin 22)

theorem stabilizer_apply_self (g : stabilizer M22 a) : (g.1 : Equiv.Perm (Fin 22)) a = a := g.2

@[expose] def resPoint : stabilizer M22 a →* Equiv.Perm {x : Fin 22 // x ≠ a} where
  toFun g := (g.1 : Equiv.Perm (Fin 22)).subtypePerm fun x => by
    have hg := stabilizer_apply_self a g
    constructor
    · intro hx e
      exact hx (by rw [e]; exact hg)
    · intro hx e
      exact hx ((g.1 : Equiv.Perm (Fin 22)).injective (e.trans hg.symm))
  map_one' := by
    ext
    rfl
  map_mul' g h := by
    ext
    rfl

theorem coe_resPoint_apply (g : stabilizer M22 a) (x : {x : Fin 22 // x ≠ a}) :
    ((resPoint a g x : {x : Fin 22 // x ≠ a}) : Fin 22) = (g.1 : Equiv.Perm (Fin 22)) x := rfl

theorem resPoint_injective : Function.Injective (resPoint a) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
  by_cases hx : x = a
  · subst hx
    exact stabilizer_apply_self x g
  · have := congrArg (fun σ : Equiv.Perm {x : Fin 22 // x ≠ a} => ((σ ⟨x, hx⟩ : _) : Fin 22)) hg
    exact this

theorem map_resPoint_mem (g : stabilizer M22 a) {L : Finset {x : Fin 22 // x ≠ a}}
    (hL : L ∈ derivedLines hexads a) :
    L.map (resPoint a g).toEmbedding ∈ derivedLines hexads a := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hL
  rw [Finset.mem_filter] at hB
  have hgB : (g.1 • B) ∈ hexads := smul_mem_hexads g.1 hB.1
  have haB : a ∈ g.1 • B := by
    rw [Subgroup.smul_def, Finset.mem_smul_finset]
    exact ⟨a, hB.2, stabilizer_apply_self a g⟩
  refine Finset.mem_image.2 ⟨g.1 • B, Finset.mem_filter.2 ⟨hgB, haB⟩, ?_⟩
  ext y
  rw [Finset.mem_map_equiv, mem_subtype_ne, mem_subtype_ne, Subgroup.smul_def,
    ← Finset.inv_smul_mem_iff]
  have h : (((resPoint a g).symm y : {x : Fin 22 // x ≠ a}) : Fin 22) =
      ((g.1 : Equiv.Perm (Fin 22))⁻¹ • (y : Fin 22)) := by
    rw [eq_inv_smul_iff, Equiv.Perm.smul_def, ← coe_resPoint_apply, Equiv.apply_symm_apply]
  rw [h]

theorem map_resPoint_mem_iff (g : stabilizer M22 a) (L : Finset {x : Fin 22 // x ≠ a}) :
    L.map (resPoint a g).toEmbedding ∈ derivedLines hexads a ↔ L ∈ derivedLines hexads a := by
  refine ⟨fun h => ?_, map_resPoint_mem a g⟩
  have := map_resPoint_mem a g⁻¹ h
  rwa [← map_perm_mul', ← map_mul, inv_mul_cancel, map_one,
    show (1 : Equiv.Perm {x : Fin 22 // x ≠ a}).toEmbedding = Function.Embedding.refl _ from rfl,
    Finset.map_refl] at this

@[expose] def stabilizerToPG (e : {x : Fin 22 // x ≠ a} ≃ PG24Point) :
    stabilizer M22 a →* Equiv.Perm PG24Point :=
  e.permCongrHom.toMonoidHom.comp (resPoint a)

theorem stabilizerToPG_injective (e : {x : Fin 22 // x ≠ a} ≃ PG24Point) :
    Function.Injective (stabilizerToPG a e) :=
  e.permCongrHom.injective.comp (resPoint_injective a)

theorem range_stabilizerToPG_le (e : {x : Fin 22 // x ≠ a} ≃ PG24Point)
    (he : ∀ L, L ∈ derivedLines hexads a ↔ L.map e.toEmbedding ∈ PG24Lines) :
    (stabilizerToPG a e).range ≤ blockAut PG24Lines := by
  rintro _ ⟨g, rfl⟩
  rw [mem_blockAut]
  intro B
  have hB : B = (B.map e.symm.toEmbedding).map e.toEmbedding := by
    rw [Finset.map_map, ← Equiv.trans_toEmbedding, Equiv.symm_trans_self]
    exact Finset.map_refl.symm
  have hmap : B.map (stabilizerToPG a e g).toEmbedding =
      ((B.map e.symm.toEmbedding).map (resPoint a g).toEmbedding).map e.toEmbedding := by
    rw [Finset.map_map, Finset.map_map]
    rfl
  rw [hmap, ← he, map_resPoint_mem_iff, he, ← hB]

theorem isSimpleGroup_range_SL : IsSimpleGroup (rhoGL.comp slHom).range := by
  have : Nontrivial (rhoGL.comp slHom).range := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_range_rhoGL_comp_slHom]
    norm_num
  have h := (CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact IsSimpleGroup.isSimpleGroup_of_surjective rangeSLEquivPSL.symm.toMonoidHom
    rangeSLEquivPSL.symm.surjective

theorem nonempty_stabilizer_equiv_PSL :
    Nonempty (stabilizer M22 a ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) := by
  obtain ⟨e, he⟩ := iso_PG24 (isSteinerTriple_hexads.derived a)
  have hI : (stabilizerToPG a e).range = (rhoGL.comp slHom).range := by
    refine eq_of_relIndex_le_six (range_stabilizerToPG_le a e he)
      relIndex_range_rhoGL_comp_slHom.le ?_ isSimpleGroup_range_SL ?_
    · rw [card_range_rhoGL_comp_slHom, ← card_stabilizer_point a]
      exact Nat.card_congr (MonoidHom.ofInjective (stabilizerToPG_injective a e)).toEquiv.symm
    · rw [card_range_rhoGL_comp_slHom]
      decide
  exact ⟨(MonoidHom.ofInjective (stabilizerToPG_injective a e)).trans
    ((MulEquiv.subgroupCongr hI).trans rangeSLEquivPSL)⟩

theorem isSimpleGroup_stabilizer : IsSimpleGroup (stabilizer M22 a) := by
  obtain ⟨φ⟩ := nonempty_stabilizer_equiv_PSL a
  have : Nontrivial (stabilizer M22 a) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_stabilizer_point]
    norm_num
  have h := (CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact IsSimpleGroup.isSimpleGroup_of_surjective φ.symm.toMonoidHom φ.symm.surjective

end CFSG.ComponentClassification.WittDesign
