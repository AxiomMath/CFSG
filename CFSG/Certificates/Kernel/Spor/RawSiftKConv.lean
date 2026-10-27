module

public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

section Sift

variable {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
include hb

theorem siftK_of_siftA_rng (hsz : szOK n w = true) {LR TR TRI : Nat → Nat}
    (hbl : ∀ t < nb, base[t]! < n)
    (hag : ∀ l < nb, ∃ TK : Nat → Equiv.Perm (Fin n), Agree n w (LR l) (lev n S base l) TK ∧
      ∀ k < rcnt (LR l), PRep n w (TR (roff n (n * w) (LR l) + k)) (TK k) ∧
        PRep n w (TRI (roff n (n * w) (LR l) + k)) (TK k)⁻¹) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (g : Array Nat), G >>> (n * w) = 0 →
      (∀ i < n, g[i]! = pg w (mask w) G i ∧ pg w (mask w) G i < n) →
      siftA n (rawLevels n S base) base l g = true →
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP d l G = true := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  obtain ⟨hn, hw⟩ := szOK_facts hsz
  have hw0 : 0 < w := PF.w_pos hw
  intro d
  induction d with
  | zero =>
    intro l hl G g hhi hG h
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)] at h
    unfold eqA at h
    rw [allLt_iff] at h
    have hGe : G = pidn n w := PF.eq_of_fields hw0 hhi (PF.pidn_shr hn hw) fun i hi => by
      have e := h i hi
      rw [beq_iff_eq, idA_get hi, (hG i hi).1] at e
      rw [e, PF.pg_pidn hn hw hi]
    rw [siftK_zero, hsz, hGe]
    simp only [Nat.beq_refl]
  | succ d ih =>
    intro l hl G g hhi hG h
    have hlb : l < nb := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    obtain ⟨TK, A, hT⟩ := hag l hlb
    have hbt : base[l]! = pg w (mask w) BP l := hb.2.2.2.2.2.2 l hlb
    have hbl' := hbl l hlb
    have hz : g[base[l]!]! = pg w (mask w) G base[l]! := (hG _ hbl').1
    have hzn : pg w (mask w) G base[l]! < n := (hG _ hbl').2
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls, hz] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hK, h⟩ := h
    have hk' := (A.pos _ hzn).2 hK
    have hKe := A.posE _ hzn hK
    rw [siftK_succ, ← hbt]
    simp only [strictB_eq, bIf_eq]
    simp only [Nat.blt_eq.mpr hk', ↓reduceIte]
    rw [← hKe] at h
    refine ih (l + 1) (by omega) _ _ (PF.pcomp_shr _ _ (by omega) hw0) (fun i hi => ?_) h
    have hgi := hG i hi
    have hR := (A.tr _ (hKe ▸ hK)).2
    have e := (hT _ hk').2 ⟨_, hgi.2⟩
    rw [compA_get hi, hgi.1, PF.pg_pcomp (by omega) hi]
    exact ⟨(hR.apply hgi.2).trans e.symm, lt_of_eq_of_lt e (Fin.is_lt _)⟩

end Sift

theorem siftA_false_of_K {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hsz : szOK n w = true)
    (hhi : G >>> (n * w) = 0) (hr : allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true)
    (h : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = false) :
    siftA n (rawLevels n S base) base 0 (unpack n w G) = false := by
  have hbl := base_lt_of_levels hb hl
  cases hs : siftA n (rawLevels n S base) base 0 (unpack n w G)
  · rfl
  · have := siftK_of_siftA_rng hb hsz hbl
      (fun l hl' => ⟨_, agree_levelK hb hp hbl hl' (hl l hl')⟩) nb 0 (Nat.zero_add nb) G _ hhi
      (fun i hi => ⟨unpack_get hi, Nat.blt_eq.mp (allN_spec hr i hi)⟩) hs
    rw [h] at this
    exact absurd this Bool.false_ne_true

end CFSG.KS.Raw.Orb

end
