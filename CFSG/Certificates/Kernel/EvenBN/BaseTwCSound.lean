module

public import CFSG.Certificates.Kernel.EvenBN.BaseTwSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.MonsterB.Co2MatSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

theorem baseTwC_eq {kS kO BP NS CH Y Z k : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup) (hk : k < tot5 LR)
    (hYc : canonK 1755 11 (mask 11) (1755 * 11) Y = true)
    (hY : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 Y) = true)
    (hZc : canonK 1755 11 (mask 11) (1755 * 11) Z = true)
    (hZ : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 Z) = true) :
    baseTw BP 5 (gptC LR TR k) (pgR Y) (pgR Z) =
      eqA 1755 (compA 1755 (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k))
        (unpack 1755 11 Y))
        (compA 1755 (unpack 1755 11 Z)
          (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k))) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have rX := prodCode_rep hb hp hl hk
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
  have sX : siftA 1755 (rawLevels 1755 S base) base 0
      (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) = true := by
    rw [prodCode_eq]
    exact (tr5_rep hb hp hl d0 d1 d2 d3 d4).2
  obtain ⟨-, -, -, rYc⟩ := canonK_facts hYc
  obtain ⟨-, -, -, rZc⟩ := canonK_facts hZc
  obtain ⟨τ, rY⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rYc i hi) hY
  obtain ⟨ρ, rZ⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rZc i hi) hZ
  exact baseTw_of_sep hsep hbl (fun t ht => hb.2.2.2.2.2.2 t ht) rX rY rZ ((hmem _ _ rX).1 sX)
    ((hmem _ _ rY).1 hY) ((hmem _ _ rZ).1 hZ) (gptC_get hb hp hl hk)
    (fun i hi => by rw [pgR_eq, unpack_getT hi]) (fun i hi => by rw [pgR_eq, unpack_getT hi])

theorem eqA_conjL {A C V U Z : Array Nat}
    (hA : ∀ i < 1755, ∀ j < 1755, A[i]! = A[j]! → i = j) (hC : ∀ i < 1755, C[i]! < 1755)
    (hV : ∀ i < 1755, V[i]! < 1755) (hZ : ∀ i < 1755, Z[i]! < 1755)
    (hUA : ∀ i < 1755, U[A[i]!]! = A[Z[i]!]!) :
    eqA 1755 (compA 1755 (compA 1755 A C) V) (compA 1755 U (compA 1755 A C)) =
      eqA 1755 (compA 1755 C V) (compA 1755 Z C) := by
  rw [Bool.eq_iff_iff, CFSG.KC.Co2Mem.eqA_iff, CFSG.KC.Co2Mem.eqA_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  simp only [CFSG.KC.Co2Mem.compA_get hi, CFSG.KC.Co2Mem.compA_get (hV i hi)]
  rw [hUA _ (hC i hi)]
  exact ⟨hA _ (hC _ (hV i hi)) _ (hZ _ (hC i hi)), fun h => by rw [h]⟩

end CFSG.KS.SporSch

end
