module

public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import Certificates.Data.Kernel.Spor.RawOrbOut

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem sub_of_orbit {m c r : Nat} {P Q : Nat → Nat} {F : Nat → Nat → Nat} (hc : 0 < c)
    (h0 : P 0 = Q 0) (hPe : ∀ k < m, 0 < k → ∃ h < k, ∃ j < r, F j (P h) = P k)
    (hQc : ∀ h < c, ∀ j < r, ∃ k < c, Q k = F j (Q h)) : ∀ k < m, ∃ k' < c, Q k' = P k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨0, hc, h0.symm⟩
    · obtain ⟨h, hh, j, hj, e⟩ := hPe k hk hk0
      obtain ⟨k₁, hk₁, e₁⟩ := ih h hh (by omega)
      obtain ⟨k', hk', e'⟩ := hQc k₁ hk₁ j hj
      exact ⟨k', hk', by rw [e', e₁, e]⟩

variable {n w kS kO nb BP NS CH : Nat} {PS PSI LR : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {W : Array (List Int)} (hd : Hd n S base kO W)
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
include hd hb hp ho hN

theorem lev_mem_rec {l : Nat} (hl : l < nb) {k : Nat} (hk : k < (lev n S base l).pts.size) :
    rpos w (mask w) (n * w) (LR l) (lev n S base l).pts[k]! < rcnt (LR l) := by
  have R := recFacts_of (ho.1 l hl) (ho.2 l hl) hN
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have F := lev_facts hd (hbs ▸ hl : l < base.size)
  have hbl := base_lt_of hb ho.1 ho.2 hN
  obtain ⟨hcnt, hstep⟩ := steps_eq hb hp R.kS_lt (Nat.le_of_lt hl) hbl
  obtain ⟨k', hk', e⟩ := sub_of_orbit (m := (lev n S base l).pts.size) (c := rcnt (LR l))
    (r := (rawSteps n S base l).size)
    (P := fun k => (lev n S base l).pts[k]!) (Q := fun k => rpt w (mask w) (LR l) k)
    (F := fun j p => ((rawSteps n S base l)[j]!)[p]!) R.c_pos
    (by
      change (lev n S base l).pts[0]! = rpt w (mask w) (LR l) 0
      rw [F.root, R.root, hb.2.2.2.2.2.2 l hl])
    (fun k hk hk0 => ⟨_, F.par_lt k hk hk0, _, F.lab_lt k hk hk0, F.edge k hk hk0⟩)
    (fun h hh' j hj => by
      have hj' : j < stCnt (stepsAt n w PS kS BP l) := by rw [hcnt]; exact hj
      have hpn := (R.pt h hh').1
      have hc := R.closed h hh' j hj'
      rw [hstep j hj _ hpn] at hc
      exact ⟨_, hc, R.pos _ (steps_lt hd j hj _ hpn) hc⟩) k hk
  change rpt w (mask w) (LR l) k' = (lev n S base l).pts[k]! at e
  rw [← e, (R.pt k' hk').2]
  exact hk'

variable (hcard : Nat.card (Gen n S kO) ≤ (rawOrbitSizes n S base).prod)
include hcard

theorem not_mem_Fix_of_out {l : Nat} (hl : l < nb) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Fix n S kO base l)
    (hout : ∀ h : base[l]! < n, rcnt (LR l) ≤ rpos w (mask w) (n * w) (LR l) (g ⟨base[l]!, h⟩)) :
    False := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hl' : l < base.size := hbs ▸ hl
  obtain ⟨k, hk, e⟩ := fix_surj hd hcard hl' hg
  have h1 := lev_mem_rec hd hb hp ho hN hl hk
  have h2 := hout (hd.base_lt l hl')
  rw [e] at h2
  omega

theorem not_mem_Gen_of_outK {l : Nat} (hl : l < nb) {X : Nat} {ρ : Equiv.Perm (Fin n)}
    (hX : PRep n w X ρ) {iw : List Int}
    (h : outK n w (mask w) (n * w) (pidn n w) PS PSI kS BP l (LR l) iw X = true) :
    ρ ∉ Gen n S kO := by
  intro hρ
  have hb0 := hb
  obtain ⟨-, hw, hn, hS, -, -, hbt⟩ := hb0
  unfold outK at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, strictB_eq] at h
  obtain ⟨hlet, hfix, hout⟩ := h
  have hn' : n < 16777216 := by omega
  have h32 : n < 2 ^ 32 := by omega
  obtain ⟨hW, -⟩ := prep_wordK (gs := fun h => permOfArr n S[h]!) hn' hw
    (fun h hh => (prep_PS hb hp hh).1) (fun h hh => (prep_PS hb hp hh).2) iw hlet
  set ω := Quiver.SchreierGraph.evalWord (fun h : Fin kS => permOfArr n S[(h : Nat)]!)
    (toLetters kS iw)
  have hω : ω ∈ Gen n S kO := by
    refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    rintro _ ⟨i, rfl⟩
    exact S_mem_Gen hd i.val (by rw [hS]; exact i.2)
  have hq := prep_pcomp h32 hW hX
  set q := pcomp n w (mask w) (wordK n w (mask w) (pidn n w) PS PSI iw) X
  refine not_mem_Fix_of_out hd hb hp ho hN hcard hl
    (g := ω * ρ) ⟨Subgroup.mul_mem _ hω hρ, fun t ht hbn => ?_⟩ fun hbn => ?_
  · apply Fin.ext
    have e := hq ⟨base[t]!, hbn⟩
    have hf := Nat.eq_of_beq_eq_true (by
      have := allN_iff.1 hfix t ht
      rwa [strictB_eq] at this)
    rw [← e]
    change pg w (mask w) q base[t]! = base[t]!
    rw [hbt t (by omega)]
    exact hf
  · have e := hq ⟨base[l]!, hbn⟩
    have hle := Nat.le_of_ble_eq_true hout
    change rcnt (LR l) ≤ rpos w (mask w) (n * w) (LR l) ((ω * ρ) ⟨base[l]!, hbn⟩ : Nat)
    rw [← e]
    change rcnt (LR l) ≤ rpos w (mask w) (n * w) (LR l) (pg w (mask w) q base[l]!)
    rw [hbt l hl]
    exact hle

end CFSG.KS.Raw.Orb

end
