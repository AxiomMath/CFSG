module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8C
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Link
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

section Model

variable {M : Type} [Group M] (e : M ≃* ↥omegaT)

@[expose] noncomputable def emb : M →* Equiv.Perm (Fin 360) := omegaT.subtype.comp e.toMonoidHom

theorem emb_injective : Function.Injective (emb e) :=
  Subtype.val_injective.comp e.injective

theorem range_emb : (emb e).range = omegaT := by
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    exact (e m).2
  · intro hg
    exact ⟨e.symm ⟨g, hg⟩, by simp [emb]⟩


theorem o82QuatIdent {K : Subgroup M} {s : M} (hd : QuatTwinDatum K s) :
    ∃ m : M, conjSub (emb e m) (K.map (emb e)) = K0 := by
  have had := Vtx.ambientQuatDatum_map (emb e) (emb_injective e) hd
  rw [range_emb] at had
  obtain ⟨g, hg, hgK⟩ := ident_omega had
  rw [← range_emb e] at hg
  obtain ⟨m, rfl⟩ := hg
  exact ⟨m, hgK⟩

include e in
theorem exists_emb {K : Subgroup M} {s : M} (hd : QuatTwinDatum K s) :
    ∃ φ : M →* Equiv.Perm (Fin 360), Function.Injective φ ∧ φ.range = omegaT ∧ K.map φ = K0 := by
  obtain ⟨m, hm⟩ := o82QuatIdent e hd
  refine ⟨(MulAut.conj (emb e m)).toMonoidHom.comp (emb e),
    (MulAut.conj (emb e m)).injective.comp (emb_injective e), ?_, ?_⟩
  · rw [MonoidHom.range_comp, range_emb]
    exact conjSub_eq_self_of_mem (e m).2
  · rw [← Subgroup.map_map]
    exact hm

end Model


theorem eq_x0_of_isUniqueInvolution {sc : Equiv.Perm (Fin 360)} (h : IsUniqueInvolution K0 sc) :
    sc = mainPerm 0 := by
  have hu0K : u0 ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hsq : u0 * u0 * (u0 * u0) = 1 := by rw [u0_sq, x0_sq]
  have hne : u0 * u0 ≠ 1 := by
    rw [u0_sq]
    exact x0_ne_one
  rw [← (h.unique _ (K0.mul_mem hu0K hu0K) hsq).resolve_left hne, u0_sq]



theorem e4QuatGraphFacts_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : E4QuatGraphFacts M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  refine Vtx.e4QuatGraphFacts_of_model omegaT K0
    [conjSub (wsP.getD 1 1) K0, conjSub (wsP.getD 3 1) K0, conjSub (wsP.getD 4 1) K0] (by simp)
    (fun K s hd => exists_emb e hd) ⟨wsP.getD 1 1, ws_mem 1, edge⟩
    (fun h hh => reflTransGen_starRel hh) (fun h hh hne hle => ?_)
  obtain ⟨k, hk, he⟩ := mem_twins_of_le_normalizer hh hne hle
  rw [he]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> simp

theorem e4QuatNbrInv_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : E4QuatNbrInv M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  refine Vtx.e4QuatNbrInv_of_model omegaT K0 (fun K s hd => exists_emb e hd)
    (fun sc hsc h hh hne hle => ?_)
  obtain ⟨k, hk, he⟩ := mem_twins_of_le_normalizer hh hne hle
  rw [he]
  have h1 := hsc.conj (wsP.getD k 1)
  rwa [show wsP.getD k 1 * sc * (wsP.getD k 1)⁻¹ = sc by
    rw [eq_x0_of_isUniqueInvolution hsc, ws_comm_x0 k hk]
    group] at h1

theorem e4QuatActs3_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : E4QuatActs3 M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  obtain ⟨h3, hn, hc⟩ := three_facts
  exact Vtx.e4QuatActs3_of_model omegaT K0 (fun K s hd => exists_emb e hd)
    ⟨three, three_spec.2, h3, hn, u0, Subgroup.subset_closure (Set.mem_insert _ _), hc⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
