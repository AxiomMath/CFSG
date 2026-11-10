
module

public import CFSG.Fischer.Polar.Span
public import CFSG.Fischer.Polar.CertBase
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb
public import CFSG.Fischer.HermitianEquiv

@[expose] public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs

local notation "PT" => perpTab ()
local notation "PL" => perpLists (perpTab ())
local notation "LT" => lineTab (perpTab ())
local notation "LL" => lineList (perpTab ()) (lineTab (perpTab ()))
local notation "LI" => lineIdx (lineList (perpTab ()) (lineTab (perpTab ())))

structure PolarLinesFacts : Prop where
  size : allIn 0 693 (fun p => PL[p]!.size == 181) = true
  lines : linesOK PT PL LT = true
  list : lineListOK PT LT LL LI = true
  twins : twinsOK PT PL LT = true
  perpPerp : perpPerpOK PT PL LT = true

theorem mem_perpLists {x : Fin 693} {y : ℕ} :
    y ∈ PL[x.val]! ↔ ∃ h : y < 693, perp x ⟨y, h⟩ := by
  unfold perpLists perpList
  rw [getElem!_pos _ x.val (by simp), Array.getElem_ofFn]
  simp only [List.mem_toArray, mem_filterRange]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, (perpTab_spec x ⟨y, hy⟩).1 h⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, (perpTab_spec x ⟨y, hy⟩).2 h⟩

theorem mem_perpLists_zero {y : ℕ} : y ∈ PL[0]! ↔ ∃ h : y < 693, perp 0 ⟨y, h⟩ :=
  mem_perpLists (x := 0)

theorem mem_perpLists_fin {x y : Fin 693} : y.val ∈ PL[x.val]! ↔ perp x y := by
  rw [mem_perpLists]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨y.2, h⟩⟩

theorem lt_of_mem_perpLists {x : Fin 693} {y : ℕ} (h : y ∈ PL[x.val]!) : y < 693 :=
  (mem_perpLists.1 h).1

theorem nodup_perpLists (x : Fin 693) : PL[x.val]!.toList.Nodup := by
  unfold perpLists perpList
  rw [getElem!_pos _ x.val (by simp), Array.getElem_ofFn, List.toList_toArray]
  exact nodup_filterRange _ _

theorem perpTab_spec' {x : Fin 693} {y : ℕ} (hy : y < 693) :
    (PT[x.val]!)[y]! = true ↔ perp x ⟨y, hy⟩ :=
  perpTab_spec x ⟨y, hy⟩

theorem lineThru_comm (x y : Fin 693) : lineThru x y = lineThru y x := by
  ext z
  constructor <;> rintro ⟨a, b, h⟩ <;> exact ⟨b, a, by rw [h, add_comm]⟩

theorem left_mem_lineThru (x y : Fin 693) : x ∈ lineThru x y :=
  ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩

theorem right_mem_lineThru (x y : Fin 693) : y ∈ lineThru x y :=
  ⟨0, 1, by rw [one_smul, zero_smul, zero_add]⟩

theorem isLine_lineThru {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) : IsLine (lineThru x y) :=
  ⟨x, y, hxy, h, rfl⟩

theorem lineC_size (x y : Fin 693) : (lineC x.val y.val).size = 5 := by
  rw [lineC_eq]
  rfl

theorem lineThru_eq_setOf_lineC {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) :
    lineThru x y = {z : Fin 693 | z.val ∈ (lineC x.val y.val).toList} := by
  ext z
  rw [mem_lineThru_iff hxy h, Set.mem_ofPred_eq, Array.mem_toList_iff]

def lineSet (i : ℕ) : Set (Fin 693) := {p | p.val ∈ LL[i]!}

theorem IsClosedHyperoval.exists_ne {O L : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (hL : IsLine L) {x : Fin 693} (hxL : x ∈ L) (hxO : x ∈ O) : ∃ y ∈ L, y ∈ O ∧ y ≠ x := by
  rcases hO.inter L hL with h | h
  · exfalso
    rw [Set.ncard_eq_zero (Set.toFinite _)] at h
    exact (show (L ∩ O).Nonempty from ⟨x, hxL, hxO⟩).ne_empty h
  · obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.1 h
    have hx : x ∈ L ∩ O := ⟨hxL, hxO⟩
    have ha : a ∈ L ∩ O := by rw [he]; exact Set.mem_insert _ _
    have hb : b ∈ L ∩ O := by rw [he]; exact Set.mem_insert_of_mem _ rfl
    rw [he] at hx
    rcases hx with rfl | rfl
    · exact ⟨b, hb.1, hb.2, hab.symm⟩
    · exact ⟨a, ha.1, ha.2, hab⟩

theorem IsClosedHyperoval.eq_of_mem
    {O L : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (hL : IsLine L) {a b c : Fin 693} (ha : a ∈ L ∩ O) (hb : b ∈ L ∩ O) (hc : c ∈ L ∩ O)
    (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  by_contra hbc
  have h3 : ({a, b, c} : Set (Fin 693)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set (Fin 693)) ⊆ L ∩ O := by
    intro z hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rcases hO.inter L hL with h | h <;> omega

theorem perpLists_zero_eq : PL[(0 : Fin 693).val]! = PL[0]! := rfl

theorem lineTab_zero {x : Fin 693} (h : perp 0 x) : LT[x.val]! = lineC 0 x.val := by
  have := lineTab_get h
  simpa using this

theorem exists_smul_zero (p : Fin 693) : ∃ g : Equiv.Perm (Fin 693), g ∈ T46 ∧ g 0 = p := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T46 (0 : Fin 693) p
  exact ⟨g, g.2, hg⟩

end CFSG.Fischer
