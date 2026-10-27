module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshWord
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.CosetTable CFSG.EvenSporadicStandard.Fin76b

@[expose] def modelCheck (n m k : ℕ) (g : Array Table) (ws : List (List (Fin k × Bool)))
    (size : ℕ) : Bool :=
  enumOK n m g (mulClosureS n m g 4000) size &&
  wordsTrivial n (fun i : Fin k => g[i.val]!) (fun i : Fin k => (g.map (invT n))[i.val]!) ws &&
  (List.range k).all (fun i => invOK n g[i]! (g.map (invT n))[i]!)

structure ModelOK (n m k : ℕ) (g : Array Table) (ws : List (List (Fin k × Bool))) (size : ℕ) :
    Prop where
  check : modelCheck n m k g ws size = true
  fin : Finite (PG k ws)
  card_le : Nat.card (PG k ws) ≤ size

noncomputable abbrev modelGens (n k : ℕ) (g : Array Table) : Fin k → Equiv.Perm (Fin n) :=
  fun i => tp n g[i.val]!

noncomputable abbrev modelGroup (n k : ℕ) (g : Array Table) : Subgroup (Equiv.Perm (Fin n)) :=
  closure (Set.range (modelGens n k g))

theorem range_modelGens {n k : ℕ} {g : Array Table} (hk : g.size = k) :
    Set.range (modelGens n k g) = tp n '' {x | x ∈ g} := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨g[i.val]!, getElem!_mem_array (by rw [hk]; exact i.2), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
    exact ⟨⟨j, by rw [← hk]; exact hj⟩, by simp [modelGens, getElem!_pos g j hj]⟩

structure ModelSpec (n k : ℕ) (g : Array Table) (ws : List (List (Fin k × Bool))) (size : ℕ) :
    Prop where
  rep : ∀ i : Fin k, Rep n g[i.val]! (modelGens n k g i)
  repInv : ∀ i : Fin k, Rep n (g.map (invT n))[i.val]! (modelGens n k g i)⁻¹
  rel : ∀ r ∈ ws, FreeGroup.lift (modelGens n k g) (FreeGroup.mk r) = 1
  fin : Finite (PG k ws)
  card_pg : Nat.card (PG k ws) ≤ size
  card_group : Nat.card (modelGroup n k g) = size

theorem modelCheck_spec {n m k size : ℕ} (hn : n < 2 ^ 32) {g : Array Table}
    (hk : g.size = k) {ws : List (List (Fin k × Bool))} (h : ModelOK n m k g ws size) :
    ModelSpec n k g ws size ∧ ∃ L : Array Table, EnumSpec n g L ∧ L.size = size := by
  obtain ⟨h, hfin, hle⟩ := h
  simp only [modelCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hE, hW⟩, hI⟩ := h
  obtain ⟨hspec, hsize⟩ := enumOK_spec hn hE
  have hperm : ∀ i : Fin k, permOK n g[i.val]! = true := fun i =>
    hspec.perm _ (getElem!_mem_array (by rw [hk]; exact i.2))
  have hrep : ∀ i : Fin k, Rep n g[i.val]! (modelGens n k g i) := fun i => rep_tp (hperm i)
  have hinv : ∀ i : Fin k, invOK n g[i.val]! (g.map (invT n))[i.val]! = true := by
    intro i
    have := List.all_eq_true.1 hI i.val (List.mem_range.2 i.2)
    exact this
  have hmapget : ∀ i : Fin k, (g.map (invT n))[i.val]! = invT n g[i.val]! := by
    intro i
    have hi : i.val < g.size := by rw [hk]; exact i.2
    rw [getElem!_pos (g.map (invT n)) i.val (by simpa using hi), Array.getElem_map,
      getElem!_pos g i.val hi]
  have hrepInv : ∀ i : Fin k, Rep n (g.map (invT n))[i.val]! (modelGens n k g i)⁻¹ := fun i =>
    Rep.inv_of_invOK (hrep i) (hinv i)
  have hrel : ∀ r ∈ ws, FreeGroup.lift (modelGens n k g) (FreeGroup.mk r) = 1 :=
    lift_eq_one_of_wordsTrivial hn (modelGens n k g) hrep hrepInv hW
  refine ⟨⟨hrep, hrepInv, hrel, hfin, hle, ?_⟩, ⟨(mulClosureS n m g 4000).1, hspec, hsize⟩⟩
  have := hspec.card
  rw [← range_modelGens hk] at this
  rw [hsize] at this
  exact this

theorem presHom_injective {k : ℕ} (ws : List (List (Fin k × Bool)))
    {H : Type*} [Group H] (x : Fin k → H)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) (hfin : Finite (PG k ws))
    (hle : Nat.card (PG k ws) ≤ Nat.card (closure (Set.range x))) :
    Function.Injective (presHom ws x hx) := by
  have hsurj : Function.Surjective (presHom ws x hx).rangeRestrict :=
    (presHom ws x hx).rangeRestrict_surjective
  have hcard : Nat.card (PG k ws) ≤ Nat.card (presHom ws x hx).range := by
    rw [range_presHom]; exact hle
  have hb := hsurj.bijective_of_nat_card_le hcard
  intro a b hab
  apply hb.1
  exact Subtype.ext hab

@[expose] noncomputable def presEquiv {k n : ℕ} (ws : List (List (Fin k × Bool)))
    (gm : Fin k → Equiv.Perm (Fin n)) (hx : ∀ r ∈ ws, FreeGroup.lift gm (FreeGroup.mk r) = 1)
    (hfin : Finite (PG k ws))
    (hle : Nat.card (PG k ws) ≤ Nat.card (closure (Set.range gm))) :
    PG k ws ≃* closure (Set.range gm) :=
  (MulEquiv.ofBijective (presHom ws gm hx).rangeRestrict
    ⟨by
      intro a b hab
      exact presHom_injective ws gm hx hfin hle (congrArg Subtype.val hab),
     (presHom ws gm hx).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (range_presHom ws gm hx))

theorem presEquiv_mk {k n : ℕ} (ws : List (List (Fin k × Bool)))
    (gm : Fin k → Equiv.Perm (Fin n)) (hx : ∀ r ∈ ws, FreeGroup.lift gm (FreeGroup.mk r) = 1)
    (hfin : Finite (PG k ws))
    (hle : Nat.card (PG k ws) ≤ Nat.card (closure (Set.range gm))) (w : List (Fin k × Bool)) :
    ((presEquiv ws gm hx hfin hle (PresentedGroup.mk _ (FreeGroup.mk w)) :
      closure (Set.range gm)) : Equiv.Perm (Fin n)) = FreeGroup.lift gm (FreeGroup.mk w) := rfl

end CFSG.EvenSporadicStandard.M12Std.Yosh
