
module

public import Certificates.Data.Kernel.H13J4.Cls
public import CFSG.Certificates.Kernel.SporSch.J4SSylowSound
public import CFSG.Quasithin.H13.J4ClassCheckInputs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.H13J4

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KS.Raw.Orb
open CFSG.Quasithin.H13.J4 CFSG.Quasithin.H13.J4.Native

theorem conj_eq (P Q B : Nat) :
    conjCols (unpack11 P) (unpack11 Q) (unpack11 B) = unpack11 (conjK P Q B) := by
  change CFSG.Sporadic.J4Schreier.comp11 (CFSG.Sporadic.J4Schreier.comp11 _ _) _ = _
  rw [comp_eq, comp_eq]
  rfl

theorem colsBounded_unpack (P : Nat) : colsBounded (unpack11 P) = true := by
  obtain ⟨h1, h2⟩ := unpack11_bounded P
  simp only [colsBounded, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem stepK_spec {G GI T PAR GEN NX : Nat → Nat} {m n i : Nat}
    (h : stepK G GI T PAR GEN NX m n i = true) :
    (0 < i → PAR i < i ∧ GEN i < m ∧ T i = conjK (G (GEN i)) (GI (GEN i)) (T (PAR i))) ∧
      ∀ g < m, NX (m * i + g) < n ∧ T (NX (m * i + g)) = conjK (GI g) (G g) (T i) := by
  unfold stepK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun hi => ?_, fun g hg => ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hne : Nat.beq (i + 1) 0 = false := rfl
    rw [bIf_eq, hne] at h1
    simp only [Bool.false_eq_true, ↓reduceIte, strictB_eq] at h1
    obtain ⟨a, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨b, c⟩ := (bAnd_iff _ _).1 h1
    exact ⟨Nat.le_of_ble_eq_true a, Nat.le_of_ble_eq_true b, Nat.eq_of_beq_eq_true c⟩
  · have := allN_spec h2 g hg
    simp only [strictB_eq] at this
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
    exact ⟨Nat.le_of_ble_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem clsFacts_of {G GI T PAR GEN NX SO SOI : Nat → Nat} {m n : Nat}
    {gens : Array (Array ℕ × Array ℕ)} {M : Array ℕ} (hgs : gens.size = m)
    (hG : ∀ g < m, (gens[g]!).1 = unpack11 (G g)) (hGI : ∀ g < m, (gens[g]!).2 = unpack11 (GI g))
    (hM : M = unpack11 (T 0)) (hd : distinctK T SO SOI n = true)
    (hs : ∀ i < n, stepK G GI T PAR GEN NX m n i = true) : ClsFacts gens M n := by
  refine ⟨fun i => unpack11 (T i), hM.symm, fun i _ => colsBounded_unpack _,
    fun i hi j hj => distinctK_sound hd i hi j hj, fun i hi hi0 => ?_, fun i hi g hg => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (stepK_spec (hs i hi)).1 hi0
    refine ⟨PAR i, h1, GEN i, hgs ▸ h2, ?_⟩
    beta_reduce
    rw [hG _ h2, hGI _ h2, conj_eq, h3]
  · rw [hgs] at hg
    obtain ⟨h1, h2⟩ := (stepK_spec (hs i hi)).2 g hg
    refine ⟨NX (m * i + g), h1, ?_⟩
    beta_reduce
    rw [hG _ hg, hGI _ hg, conj_eq, h2]

theorem step_of_slices {G GI T PAR GEN NX : Nat → Nat} {m n k S : Nat} (hn : n ≤ k * S)
    (h : ∀ s < S, allBlk (k * s) (stepAt G GI T PAR GEN NX m n) k = true) :
    ∀ i < n, stepK G GI T PAR GEN NX m n i = true := by
  intro i hi
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · omega
    · exact hk
  have hs : i / k < S := by
    rw [Nat.div_lt_iff_lt_mul hk]
    rw [Nat.mul_comm] at hn
    omega
  have := allBlk_spec (h _ hs) (i % k) (Nat.mod_lt i hk)
  have e : Nat.add (k * (i / k)) (i % k) = i := Nat.div_add_mod i k
  rw [e] at this
  unfold stepAt at this
  simp only [bIf_eq, Nat.blt_eq, hi, decide_true, ↓reduceIte] at this
  exact this

end CFSG.KS.H13J4

end
