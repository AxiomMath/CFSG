module

public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Sporadic.J4.QT2LocX0Native
import CFSG.Certificates.Kernel.J4Q.MOrbBFS

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2

theorem obfs_sound {step : Array V2 → Nat → Array V2} {nl : Nat} {stepK : Nat → Nat → Nat}
    (_hstep : ∀ X g, WfA X → g < nl → WfA (step X g) ∧ encR (step X g) = stepK (encR X) g)
    {w : Array V2} (_hw : WfA w) {cap bits : Nat} (_hcap : cap < 2 ^ bits)
    (_h32 : 4 * 2 ^ bits < 2 ^ 32) (_hpos : 0 < cap) {MS PAR LAB SIG : Nat → Nat} {TT : Nat → Nat → Nat}
    (_hroot : MS 0 = encR w)
    (_htree : ∀ k, 0 < k → k < cap → PAR k < k ∧ LAB k < nl ∧ MS k = stepK (MS (PAR k)) (LAB k))
    (_hclos : ∀ k < cap, ∀ g < nl, TT k g < cap ∧ stepK (MS k) g = MS (TT k g))
    {SIGI : Nat → Nat} (_hsig : ∀ i < cap, SIG i < cap)
    (_hsurj : ∀ k < cap, SIGI k < cap ∧ SIG (SIGI k) = k)
    (_hsort : ∀ i, i + 1 < cap → MS (SIG i) < MS (SIG (i + 1)))
    (_hord : ∀ k, 0 < k → k + 1 < cap → PAR k * nl + LAB k < PAR (k + 1) * nl + LAB (k + 1))
    (_hfirst : ∀ k < cap, ∀ g < nl, TT k g = 0 ∨ PAR (TT k g) * nl + LAB (TT k g) ≤ k * nl + g) :
    oOrbOK step nl w (obfs step nl w cap bits) cap = true ∧
      (obfs step nl w cap bits).mats.toList.map encR = (List.range cap).map MS ∧
      ∀ X ∈ (obfs step nl w cap bits).mats.toList, WfA X := by
  have hmono : ∀ i j, i < j → j < cap → MS (SIG i) < MS (SIG j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact (ih h (by omega)).trans (_hsort j hj)
      · exact _hsort i hj
  have hinj : ∀ i < cap, ∀ j < cap, MS i = MS j → i = j := by
    intro i hi j hj he
    obtain ⟨hi1, hi2⟩ := _hsurj i hi
    obtain ⟨hj1, hj2⟩ := _hsurj j hj
    rcases Nat.lt_trichotomy (SIGI i) (SIGI j) with h | h | h
    · have := hmono _ _ h hj1
      rw [hi2, hj2] at this
      omega
    · rw [← hi2, ← hj2, h]
    · have := hmono _ _ h hi1
      rw [hi2, hj2] at this
      omega
  have hT : BfsOrder.Tree cap 1 nl PAR LAB TT :=
    { sn := by omega
      par := fun k hk hkn => ⟨(_htree k (by omega) hkn).1, (_htree k (by omega) hkn).2.1⟩
      same := fun k hk hkn => by
        obtain ⟨h1, h2, h3⟩ := _htree k (by omega) hkn
        obtain ⟨h4, h5⟩ := _hclos (PAR k) (by omega) (LAB k) h2
        exact hinj _ h4 _ hkn (h5.symm.trans h3.symm)
      clos := fun k hk g hg => (_hclos k hk g hg).1
      ord := fun k hk hkn => _hord k (by omega) hkn
      first := fun k hk g hg => (_hfirst k hk g hg).imp (fun h => by omega) id }
  have Hy : MOrbBFS.Hyp step nl stepK w cap bits MS PAR LAB TT :=
    ⟨_hstep, _hw, _h32, _hcap, _hpos, _hroot, hinj, hT, fun k hk hkn => (_htree k hk hkn).2.2,
      fun k hk g hg => (_hclos k hk g hg).2⟩
  obtain ⟨hok, henc, hsz⟩ := MOrbBFS.obfs_order Hy
  refine ⟨hok, ?_, ?_⟩
  · apply List.ext_getElem (by simp [hsz])
    intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
    exact (henc i (by simpa using h1)).2
  · intro X hX
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hX
    have := (henc i (by simpa using hi)).1
    simpa using this

end CFSG.KC.J4Q

end
