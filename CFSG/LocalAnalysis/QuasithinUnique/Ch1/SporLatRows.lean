module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

theorem quot_le_order {Γ : Type} [Group Γ] [Finite Γ] (Y : Subgroup Γ) (N : Subgroup Y) [N.Normal] :
    Nat.card (Y ⧸ N) ≤ Nat.card Y :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card N)

@[expose] def defaultRow {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (k : ℕ)
    (D : LatData Lab) (Ot : Array (OmegaData (List Lab))) (j : ℕ) : Mem :=
  ⟨D.Om[j]!.lbl.size * 2 ^ k, 2 ^ k / Ot[j]!.lbl.size, D.Om[j]!.lbl.size * 2 ^ k⟩

namespace LatCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem memStmt_of_O2 {Ot : Array (OmegaData (List Lab))} (hO2 : O2OK C.A.act C.D Ot) {j : ℕ}
    (hj : j < C.J) (m : Mem) (hord : C.D.Om[j]!.lbl.size * 2 ^ C.k = m.order)
    (ho2 : Ot[j]!.lbl.size * m.o2 = 2 ^ C.k)
    (hq : ∀ (N : Subgroup (C.Y j)) [N.Normal], IsPGroup 2 (C.Y j ⧸ N) →
      Nat.card (C.Y j ⧸ N) ≤ m.quot2) : MemStmt (C.Y j) m := by
  obtain ⟨-, hj2⟩ := hO2
  obtain ⟨hodd, hOt⟩ := hj2 j hj
  refine ⟨?_, ?_, hq⟩
  · rw [C.Y_card hj, hord]
  · have h1 := C.core_card hj hodd Ot[j]! hOt
    have hpos : 0 < Ot[j]!.lbl.size := (hOt.2.1)
    rw [← ho2, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem memStmt_default {Ot : Array (OmegaData (List Lab))} (hO2 : O2OK C.A.act C.D Ot) {j : ℕ}
    (hj : j < C.J) : MemStmt (C.Y j) (defaultRow C.k C.D Ot j) := by
  obtain ⟨-, hj2⟩ := hO2
  obtain ⟨hodd, hOt⟩ := hj2 j hj
  have hpos : 0 < Ot[j]!.lbl.size := hOt.2.1
  refine ⟨C.Y_card hj, ?_, fun N _ _ => ?_⟩
  · have h1 := C.core_card hj hodd Ot[j]! hOt
    exact (Nat.eq_div_of_mul_eq_left hpos.ne' h1)
  · rw [defaultRow]
    exact (quot_le_order _ N).trans (by rw [C.Y_card hj])

theorem rows_of_default {Ot : Array (OmegaData (List Lab))} (hO2 : O2OK C.A.act C.D Ot)
    (mems : List Mem) (hm : (List.range C.J).map (defaultRow C.k C.D Ot) = mems) :
    ∀ j < C.J, ∃ m ∈ mems, MemStmt (C.Y j) m := by
  intro j hj
  refine ⟨defaultRow C.k C.D Ot j, ?_, C.memStmt_default hO2 hj⟩
  rw [← hm]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

end LatCtx

end CFSG.QuasithinUnique.Ch1.SporLat
