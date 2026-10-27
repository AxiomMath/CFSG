module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Embed.Std
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Embed.Incl

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] (Y : Subgroup H)

omit [Finite H] in
theorem map_subtype_conj_eq_iff {L : Subgroup ↥Y} (s : ↥Y) :
    (L.map Y.subtype).map (MulAut.conj (s : H)).toMonoidHom = L.map Y.subtype ↔
      L.map (MulAut.conj s).toMonoidHom = L := by
  rw [← map_subtype_conj]
  exact ⟨fun h => Subgroup.map_injective Y.subtype_injective h, fun h => by rw [h]⟩

theorem embed_links {M T : Subgroup H} {n : ℕ} {Lt Tt : ℕ → Subgroup ↥Y} {st : ℕ → ↥Y}
    (hl : Sol78Links ↥Y n Lt Tt st) (hMY : M ≤ Y) (hMYn : (M.subgroupOf Y).Normal)
    (hM : IsCompIn M (centralizer (T : Set H)))
    (hperfY : ∀ P : Subgroup ↥Y, ⁅P, P⁆ = P → P ≤ M.subgroupOf Y)
    (hLM : ∀ i, Lt i ≤ M.subgroupOf Y) (hTU : ∀ i ≤ n, T ≤ (Tt i).map Y.subtype) :
    Sol78Links H n (fun i => (Lt i).map Y.subtype) (fun i => (Tt i).map Y.subtype)
      (fun i => ((st i : ↥Y) : H)) := by
  have hzp : ∀ i, (zpowers (st i)).map Y.subtype = zpowers ((st i : ↥Y) : H) := fun i =>
    MonoidHom.map_zpowers _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(hl.comp i hi).1.map _, isCompIn_map_subtype Y hMY hM (hTU i hi) (hLM i)
      (hl.comp i hi).2⟩
  · intro i hi1 hi
    obtain ⟨hp, hsn, hs2, hc⟩ := hl.elem i hi1 hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hzp]
      exact hp.map _
    · exact Subgroup.le_normalizer_map Y.subtype ⟨st i, hsn, rfl⟩
    · exact ⟨st i ^ 2, hs2, rfl⟩
    · have hTU' : T ≤ (Tt i ⊔ zpowers (st i)).map Y.subtype :=
        (hTU i hi).trans (Subgroup.map_mono le_sup_left)
      have := isCompIn_map_subtype Y hMY hM hTU' (hLM (i - 1)) hc
      rwa [Subgroup.map_sup, hzp] at this
  · intro i hi1 hi
    obtain ⟨h1, h2⟩ := hl.incl i hi1 hi
    refine ⟨?_, ?_⟩
    · have := Subgroup.map_mono (f := Y.subtype) h1
      rwa [Subgroup.map_sup, map_subtype_conj] at this
    · exact embed_layer_eq Y hMY hMYn hM hperfY (hTU i hi) (hl.elem i hi1 hi).2.1
        (hLM i) (hl.comp i hi).2 h1 h2
  · intro i hi1 hi
    rcases hl.link i hi1 hi with ⟨hne, hiso⟩ | ⟨heq, hstd⟩
    · refine Or.inl ⟨fun h => hne ((map_subtype_conj_eq_iff Y (st i)).1 h.symm).symm, ?_⟩
      obtain ⟨e⟩ := hiso
      exact ⟨((cqEquivMapSubtype Y (Lt i)).symm.trans e).trans (cqEquivMapSubtype Y (Lt (i - 1)))⟩
    · refine Or.inr ⟨((map_subtype_conj_eq_iff Y (st i)).2 heq.symm).symm, ?_⟩
      exact jstdModulo_map_subtype Y (st i) hstd

end CFSG.EvenSporadicStandard.Induction.Junction
