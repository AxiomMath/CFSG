module

public import Certificates.Data.Kernel.D4PhiK
public import Certificates.Data.TriD4TwoRow
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.D4Phi

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.StandardType.TriD4TwoRow

theorem sqK_eq : ∀ c < 8, sqK c = CFSG.Quasithin.GF8.mulNat c c := by decide

theorem sgK_eq : ∀ k < 18, sgK k = CFSG.AGLEmbedding.ChevOuter.sg k := by decide

theorem frobAt_sound {V W : Nat} (h : frobAt V W = true) :
    unpack 8 3 W = frobCode (unpack 8 3 V) := by
  have h' := Orb.allN_iff.1 h
  apply Array.ext
  · simp [unpack, frobCode]
  · intro j h1 _
    have hj : j < 8 := by simpa [unpack] using h1
    simp only [unpack, frobCode, Array.getElem_map, Array.getElem_ofFn]
    rw [Nat.eq_of_beq_eq_true (h' j hj), sqK_eq _ (by rw [Orb.pg_eq]; exact Nat.mod_lt _ (by norm_num))]

theorem phiK_sound {F : Nat} {LV LP : Nat → Nat} (h : phiK F LV LP = true) :
    permB 2457 12 F = true ∧
      (∀ i < 2457, unpack 8 3 (LV (pg 12 (mask 12) F i)) = frobCode (unpack 8 3 (LV i))) ∧
      (∀ i < 2457, pg 12 (mask 12) F (pg 12 (mask 12) F (pg 12 (mask 12) F i)) = i) ∧
      ∀ k < 18, ∀ i < 2457, pg 12 (mask 12) F (pg 12 (mask 12) (LP k) i) =
        pg 12 (mask 12) (LP (CFSG.AGLEmbedding.ChevOuter.sg k)) (pg 12 (mask 12) F i) := by
  unfold phiK at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun i hi => frobAt_sound (Orb.allN_iff.1 h2 i hi),
    fun i hi => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h3 i hi), fun k hk i hi => ?_⟩
  have := Orb.allN_iff.1 (Orb.allN_iff.1 h4 k hk) i hi
  rw [sgK_eq k hk] at this
  exact Nat.eq_of_beq_eq_true this

end CFSG.KC.D4Phi

end
