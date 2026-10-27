module

public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem siftK_of_siftA {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hg : g = unpack n w G) (hG : Nat.shiftRight G (n * w) = 0)
    (hr : allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true)
    (h : siftA n (rawLevels n S base) base 0 g = true) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true := by
  have hbl := base_lt_of_levels hb hl
  have hsz : n < 16777216 := by have := hb.2.2.1; omega
  have hw : n + 1 < 2 ^ w := hb.2.1
  have hw0 : 0 < w := PF.w_pos hw
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹ :=
    fun l hl' => ⟨_, agree_levelK hb hp hbl hl' (hl l hl')⟩
  suffices key : ∀ d l, l + d = nb → ∀ (G : Nat) (g : Array Nat), G >>> (n * w) = 0 →
      (∀ i < n, g[i]! = pg w (mask w) G i ∧ pg w (mask w) G i < n) →
      siftA n (rawLevels n S base) base l g = true →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true from
    key nb 0 (Nat.zero_add nb) G g hG
      (fun i hi => ⟨by rw [hg, unpack_get hi], Nat.blt_eq.mp (allN_spec hr i hi)⟩) h
  intro d
  induction d with
  | zero =>
    intro l hl G g hG0 hGg h
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)] at h
    unfold eqA at h
    rw [allLt_iff] at h
    have he : G = pidn n w := PF.eq_of_fields hw0 hG0 (PF.pidn_shr hsz hw) fun i hi => by
      have hi' := h i hi
      rw [(hGg i hi).1, idA_get hi] at hi'
      rw [PF.pg_pidn hsz hw hi]
      exact beq_iff_eq.1 hi'
    rw [siftK_zero]
    refine (bAnd_iff _ _).2 ⟨?_, ?_⟩
    · unfold szOK
      refine (bAnd_iff _ _).2 ⟨Nat.blt_eq.mpr hsz, Nat.blt_eq.mpr ?_⟩
      rw [PF.shl_eq, Nat.one_mul]
      exact hw
    · rw [he]
      exact Nat.beq_refl _
  | succ d ih =>
    intro l hl G g hG0 hGg h
    have hlb : l < nb := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    obtain ⟨TK, A, hT⟩ := hag l hlb
    have hbt : base[l]! = pg w (mask w) BP l := hb.2.2.2.2.2.2 l hlb
    have hbl' := hbl l hlb
    have hz : g[base[l]!]! = pg w (mask w) G base[l]! := (hGg _ hbl').1
    have hzn : pg w (mask w) G base[l]! < n := (hGg _ hbl').2
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls, hz] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hK, h⟩ := h
    have hk' := (A.pos _ hzn).2 hK
    have hKe := A.posE _ hzn hK
    rw [← hKe] at h
    rw [siftK_succ, ← hbt]
    simp only [strictB_eq, bIf_eq]
    rw [ite_eq_left (Nat.blt_eq.mpr hk')]
    refine ih (l + 1) (by omega) _ _ (PF.pcomp_shr _ _ (by omega) hw0) (fun i hi => ?_) h
    have hgi := hGg i hi
    have hR := (A.tr _ (hKe ▸ hK)).2
    have e := (hT _ hk').2 ⟨_, hgi.2⟩
    rw [compA_get hi, hgi.1, PF.pg_pcomp (by omega) hi]
    exact ⟨(hR.apply hgi.2).trans e.symm, lt_of_eq_of_lt e (Fin.is_lt _)⟩

end CFSG.KS.Raw.Orb

end
