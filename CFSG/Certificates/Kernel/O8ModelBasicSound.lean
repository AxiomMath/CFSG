module

public import CFSG.Certificates.Kernel.O8ModelDefs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.F2WordSound

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmulVec)
open CFSG.KC.Enum (pidn permOK pg pcomp)
open CFSG.Monster.B.Co2 PA

private theorem perm_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    CFSG.KC.Enum.allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

private theorem pk {n w P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∃ g : Equiv.Perm (Fin n), Rep n (unpack n w P) g ∧ Orb.PRep n w P g ∧ Orb.PRep n w Q g⁻¹ := by
  have hr := rep_permOfArr (Orb.isInvA_unpack h)
  exact ⟨_, hr.1, Orb.prep_of_rep hr.1, Orb.prep_of_rep hr.2⟩

private theorem popc_mod (x : ℕ) : ∀ m,
    popc m x % 2 = (CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold m fun j => x.testBit j).toNat
  | 0 => rfl
  | m + 1 => by
    have e : popc (m + 1) x = Nat.land (Nat.shiftRight x m) 1 + popc m x := rfl
    have hb : Nat.land (Nat.shiftRight x m) 1 = (x.testBit m).toNat := by
      change (x >>> m) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]
    rw [e, CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold_succ, Nat.add_mod, popc_mod x m, hb]
    cases CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold m (fun j => x.testBit j) <;>
      cases x.testBit m <;> rfl

private theorem toNat_testBit0 (b : Bool) : b.toNat.testBit 0 = b := by
  cases b <;> rfl

private theorem bvecK_eq (RP y : ℕ) : bmulVec 6 6 (decR RP) y = bvecK RP y ∧ bvecK RP y < 64 := by
  have hf : ∀ i < 6, par6 (Nat.land (frow RP i) y) < 2 ^ 1 := fun i _ =>
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have he : bvecK RP y = orN 6 fun i => par6 (Nat.land (frow RP i) y) <<< (1 * i) := by
    unfold bvecK
    exact congrArg (orN 6) (funext fun i => by rw [Nat.one_mul]; rfl)
  have hb : ∀ p, (bvecK RP y).testBit p = (decide (p < 6) &&
      CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold 6 fun j => (frow RP p).testBit j && y.testBit j) := by
    intro p
    rw [he, F2W.testBit_orN_fields hf, Nat.one_mul, Nat.div_one, Nat.mod_one]
    have hp6 : ∀ x, par6 x = (CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold 6
        fun j => x.testBit j).toNat := fun x => by
      change (popc 6 x) &&& 1 = _
      rw [Nat.and_one_is_mod, popc_mod]
    rw [hp6, toNat_testBit0]
    congr
    funext j
    exact Nat.testBit_land _ _ _
  have hd : ∀ p < 6, (decR RP).getD p 0 = frow RP p := fun p hp => by
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨Nat.eq_of_testBit_eq fun p => ?_, ?_⟩
  · rw [hb, bmulVec, CFSG.EvenSmallLie.UnitarySix.YamadaPar.testBit_bitsOf]
    by_cases hp : p < 6
    · rw [hd p hp]
    · simp [hp]
  · have : bvecK RP y < 2 ^ 6 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [hb]
      simp [show ¬ i < 6 by omega]
    exact this

private theorem conj_eq {n w P PI X Y : ℕ} {g x : Equiv.Perm (Fin n)} (h32 : n < 2 ^ 32)
    (hR : Rep n (unpack n w P) g) (hP : Orb.PRep n w P g) (hPI : Orb.PRep n w PI g⁻¹)
    (hX : Orb.PRep n w X x) (e : pc n w (pc n w P X) PI = Y) :
    eqA n (conjA n (unpack n w P) (unpack n w X)) (unpack n w Y) = true := by
  have hY : Orb.PRep n w Y (g * x * g⁻¹) := by
    rw [← e]
    exact Orb.prep_pcomp h32 (Orb.prep_pcomp h32 hP hX) hPI
  exact (eqA_iff (rep_compA (rep_compA hR (Orb.rep_unpack hX)) (rep_invCand hR))
    (Orb.rep_unpack hY)).2 rfl

theorem basic_sound {n w : Nat} {T pA uA G UR : ℕ → Array ℕ} {LS PS US : Array (Array ℕ)}
    {LB PB UB : Array ℕ} {PSI PA PAI UA UAI : Nat → Nat} {GP URP : Nat}
    {SL SIL LRL TRL TRIL SP SIP LRP TRP TRIP SU SIU LRU TRU TRIU : Nat → Nat}
    {kSL kOL nbL BPL kSP kOP nbP BPP kSU kOU nbU BPU : Nat} {DL DP DU : List (List Int)}
    (hL : LevelsK n w SL SIL LRL TRL TRIL kSL kOL nbL BPL DL LS LB)
    (hP : LevelsK n w SP SIP LRP TRP TRIP kSP kOP nbP BPP DP PS PB)
    (hU : LevelsK n w SU SIU LRU TRU TRIU kSU kOU nbU BPU DU US UB)
    (hT : ∀ y < 64, (T y).toList = (List.range n).map fun i => fget (PSI y) i w)
    (hpA : ∀ i < 6, pA i = unpack n w (PA i)) (huA : ∀ k < 6, uA k = unpack n w (UA k))
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hUR : ∀ k < 6, UR k = decR (mat URP k))
    (h : basicOK n w PSI PA PAI UA UAI GP URP ⟨LRL, TRIL, BPL, nbL⟩ ⟨LRP, TRIP, BPP, nbP⟩
      ⟨LRU, TRIU, BPU, nbU⟩ = true) :
    basicCheckG n T LS LB PS PB US UB pA uA G UR = true := by
  obtain ⟨hbL, hhL, hlL⟩ := hL
  obtain ⟨hbP, hhP, hlP⟩ := hP
  obtain ⟨hbU, hhU, hlU⟩ := hU
  have h32 : n < 2 ^ 32 := by have := hbL.2.2.1; omega
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · have := hbL.2.1
      rw [h0] at this
      omega
    · exact h0
  have hT' : ∀ y < 64, T y = unpack n w (PSI y) := fun y hy => unpack_of_toList (hT y hy)
  unfold basicOK at h
  simp only [ctAndB_eq, ctOrB_eq, ctNotB_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', ctAllN_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold basicCheckG
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨⟨⟨fun y hy => ?_, fun y hy y' hy' => ?_⟩, fun i hi => ?_⟩, fun k hk => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨hp, hsL, hsP, hsU⟩ := h1 y hy
    obtain ⟨g, hR, -, -⟩ := pk hp
    rw [hT' y hy]
    refine ⟨⟨⟨isInvA_of_rep hR (rep_invCand hR), ?_⟩, ?_⟩, ?_⟩
    · exact siftK_sound hbL (perm_head hhL) hlL rfl (range_of_permOK hp) hsL
    · exact siftK_sound hbP (perm_head hhP) hlP rfl (range_of_permOK hp) hsP
    · exact siftK_sound hbU (perm_head hhU) hlU rfl (range_of_permOK hp) hsU
  · obtain ⟨he, hinj⟩ := h2 y hy y' hy'
    have hxy : y ^^^ y' < 64 := by
      have := Nat.xor_lt_two_pow (n := 6) (by simpa using hy) (by simpa using hy')
      simpa using this
    obtain ⟨gy, hRy, hPy, -⟩ := pk (h1 y hy).1
    obtain ⟨gy', hRy', hPy', -⟩ := pk (h1 y' hy').1
    have e : PSI (y ^^^ y') = pc n w (PSI y) (PSI y') := Nat.eq_of_beq_eq_true he
    have hPxy : Orb.PRep n w (PSI (y ^^^ y')) (gy * gy') := by
      rw [e]
      exact Orb.prep_pcomp h32 hPy hPy'
    rw [hT' _ hxy, hT' y hy, hT' y' hy']
    refine ⟨(eqA_iff (Orb.rep_unpack hPxy) (rep_compA hRy hRy')).2 rfl, ?_⟩
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    rcases hinj with hyy | hne
    · exact Or.inl (Nat.eq_of_beq_eq_true hyy)
    · right
      rw [Bool.eq_false_iff]
      intro hq
      have hg : gy = gy' := (eqA_iff hRy hRy').1 hq
      have hc1 := (Orb.permOK_facts (h1 y hy).1).1
      have hc2 := (Orb.permOK_facts (h1 y' hy').1).1
      have : PSI y = PSI y' := PF.eq_of_fields hw hc1 hc2 fun i hi => by
        rw [hPy ⟨i, hi⟩, hPy' ⟨i, hi⟩, hg]
      rw [this] at hne
      exact absurd hne (by simp [Nat.beq_refl])
  · obtain ⟨hpa, hsL, hc⟩ := h3 i hi
    obtain ⟨g, hRg, hPg, hPgi⟩ := pk hpa
    rw [hpA i hi]
    refine ⟨⟨isInvA_of_rep hRg (rep_invCand hRg),
      siftK_sound hbL (perm_head hhL) hlL rfl (range_of_permOK hpa) hsL⟩, fun y hy => ?_⟩
    obtain ⟨hz1, hz2⟩ := bvecK_eq (mat GP i) y
    obtain ⟨x, -, hPx, -⟩ := pk (h1 y hy).1
    rw [hG i hi, hz1, hT' y hy, hT' _ hz2]
    exact conj_eq h32 hRg hPg hPgi hPx (Nat.eq_of_beq_eq_true (hc y hy))
  · obtain ⟨hpa, hsL, hc⟩ := h4 k hk
    obtain ⟨g, hRg, hPg, hPgi⟩ := pk hpa
    rw [huA k hk]
    refine ⟨⟨isInvA_of_rep hRg (rep_invCand hRg),
      siftK_sound hbL (perm_head hhL) hlL rfl (range_of_permOK hpa) hsL⟩, fun y hy => ?_⟩
    obtain ⟨hz1, hz2⟩ := bvecK_eq (mat URP k) y
    obtain ⟨x, -, hPx, -⟩ := pk (h1 y hy).1
    rw [hUR k hk, hz1, hT' y hy, hT' _ hz2]
    exact conj_eq h32 hRg hPg hPgi hPx (Nat.eq_of_beq_eq_true (hc y hy))
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    rcases h5 y hy with hn | h0 | h1'
    · left
      left
      rw [Bool.eq_false_iff]
      intro hall
      rw [allLt_iff] at hall
      have : CFSG.KLie.CT.allN 6 (fun k => Nat.beq (bvecK (mat URP k) y) y) = true := by
        rw [ctAllN_iff]
        intro k hk
        have := hall k hk
        rw [hUR k hk, (bvecK_eq (mat URP k) y).1, beq_iff_eq] at this
        rw [this]
        exact Nat.beq_refl y
      rw [this] at hn
      exact absurd hn (by decide)
    · exact Or.inl (Or.inr (Nat.eq_of_beq_eq_true h0))
    · exact Or.inr (Nat.eq_of_beq_eq_true h1')

end CFSG.KC.O8

end
