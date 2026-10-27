module

public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.ClassOneH
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.KS.HBfs
open CFSG.EvenSporadicStandard.HypOne CFSG.Monster.B.Co2.Native CFSG.KS.BfsReplay

theorem closedOKH_of_hreplay {n cnt : Nat} {gens : Array Table} {γ : Nat → Equiv.Perm (Fin n)}
    {U : Nat → Table} {par lab : Nat → Nat} {pos : Nat → Nat → Nat} (hn : n < 2 ^ 32)
    (hg : ∀ j < gens.size, Rep n gens[j]! (γ j) ∧ Rep n (invT n gens[j]!) (γ j)⁻¹)
    (R : HReplay (hkey n) (fun j y => compT n y gens[j]!) gens.size (idT n) cnt U par lab pos) :
    closedOKH n (gens ++ gens.map (invT n)) (Array.ofFn (n := cnt) fun i => U i.val) = true := by
  classical
  have hrep : ∀ i, i < cnt → ∃ σ : Equiv.Perm (Fin n), Rep n (U i) σ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact ⟨1, by rw [R.root_eq]; exact Rep.idT hn⟩
      · obtain ⟨h1, h2, h3⟩ := R.tree i h0 hi
        obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
        exact ⟨σ * γ (lab i), by rw [h3]; exact Rep.compT hσ (hg _ h2).1⟩
  choose! σ hσ using hrep
  have hsz : (Array.ofFn (n := cnt) fun i => U i.val).size = cnt := Array.size_ofFn
  have hget : ∀ i < cnt, (Array.ofFn (n := cnt) fun i => U i.val)[i]! = U i := fun i hi => by
    rw [getElem!_pos _ i (by rw [hsz]; exact hi)]
    simp
  have hd : ∀ a < (Array.ofFn (n := cnt) fun i => U i.val).size,
      ∀ b < (Array.ofFn (n := cnt) fun i => U i.val).size,
      hkey n (Array.ofFn (n := cnt) fun i => U i.val)[a]! =
        hkey n (Array.ofFn (n := cnt) fun i => U i.val)[b]! → a = b := by
    intro a ha b hb e
    rw [hsz] at ha hb
    rw [hget a ha, hget b hb] at e
    exact R.kinj a ha b hb e
  have hmem : ∀ p < cnt, ∀ y : Table, Rep n y (σ p) →
      memTH n (Array.ofFn (n := cnt) fun i => U i.val)
        (hashIndex n (Array.ofFn (n := cnt) fun i => U i.val)) y = true :=
    fun p hp y hy => ClassOneH.memTH_of_rep hd (by rw [hsz]; exact hp)
      (by rw [hget p hp]; exact hσ p hp) hy
  have hfw : ∀ i < cnt, ∀ j < gens.size, Rep n (compT n (U i) gens[j]!) (σ (pos i j)) := by
    intro i hi j hj
    obtain ⟨h1, h2, -⟩ := R.close i hi j hj
    rw [h2]
    exact hσ _ h1
  have hinj : ∀ j < gens.size, ∀ a < cnt, ∀ b < cnt, pos a j = pos b j → a = b := by
    intro j hj a ha b hb e
    have ea : Rep n (compT n (U a) gens[j]!) (σ a * γ j) := Rep.compT (hσ a ha) (hg j hj).1
    have eb : Rep n (compT n (U b) gens[j]!) (σ b * γ j) := Rep.compT (hσ b hb) (hg j hj).1
    have fa := hfw a ha j hj
    have fb := hfw b hb j hj
    rw [e] at fa
    have h1 : σ a * γ j = σ b * γ j := (rep_unique ea fa).trans (rep_unique eb fb).symm
    have h2 : σ a = σ b := mul_right_cancel h1
    apply R.kinj a ha b hb
    rw [hkey_eq_hkeyOf (hσ a ha), hkey_eq_hkeyOf (hσ b hb), h2]
  have hsurj : ∀ j < gens.size, ∀ i < cnt, ∃ p < cnt, pos p j = i := by
    intro j hj
    let f : Fin cnt → Fin cnt := fun a => ⟨pos a j, (R.close a a.2 j hj).1⟩
    have hf : Function.Injective f := fun a b e =>
      Fin.ext (hinj j hj a a.2 b b.2 (congrArg Fin.val e))
    have hs := Finite.injective_iff_surjective.1 hf
    intro i hi
    obtain ⟨p, hp⟩ := hs ⟨i, hi⟩
    exact ⟨p, p.2, congrArg Fin.val hp⟩
  unfold closedOKH
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < cnt := by rwa [hsz] at hi
  have hx : (Array.ofFn (n := cnt) fun i => U i.val)[i] = U i := by
    rw [← getElem!_pos _ i hi, hget i hi']
  rw [hx, Array.all_append, Bool.and_eq_true, Array.all_eq_true, Array.all_map, Array.all_eq_true]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [← getElem!_pos gens j hj]
    exact hmem _ (R.close i hi' j hj).1 _ (hfw i hi' j hj)
  · rw [← getElem!_pos gens j hj]
    obtain ⟨p, hp, rfl⟩ := hsurj j hj i hi'
    have e1 := hfw p hp j hj
    obtain ⟨h1, h2, -⟩ := R.close p hp j hj
    have ep : Rep n (compT n (U p) gens[j]!) (σ p * γ j) := Rep.compT (hσ p hp) (hg j hj).1
    rw [h2] at ep
    have := Rep.compT ep (hg j hj).2
    rw [mul_inv_cancel_right] at this
    exact hmem p hp _ this

theorem closedOKH_of_mulH {n w k cnt cap : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {gens : Array Table} {γ : Nat → Equiv.Perm (Fin n)} (hn : szOK n w = true)
    (hG : ∀ j < k, G j = pidn n w) (hg : TabsOK n w k GI gens)
    (hγ : ∀ j < gens.size, Rep n gens[j]! (γ j) ∧ Rep n (invT n gens[j]!) (γ j)⁻¹)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    closedOKH n (gens ++ gens.map (invT n)) (hRec n w cnt T PL).1 = true := by
  obtain ⟨hk, hgj⟩ := hg
  have hid := (CFSG.KC.BfsPin.PP.id hn).1
  obtain ⟨R, -⟩ := hreplay_of (k := k) (step := fun j a => compA n a (unpack n w (GI j)))
    (stepα := fun j y => compT n y gens[j]!) (root := idA n)
    (fun j hj t ht => by
      change _ = unpack n w (pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j))
      rw [hG j hj, ← CFSG.KC.BfsPin.compA_unpack (CFSG.KC.BfsPin.canonK_pcomp hid ht)
        (hgj j hj).2, ← CFSG.KC.BfsPin.compA_unpack hid ht, ← CFSG.KC.BfsPin.idA_eq hn,
        compA_idA_unpack ht])
    (fun j hj t _ => by
      rw [(hgj j hj).1, compT_tabT _ _ fun x _ => unpack_lt (hgj j hj).2])
    (CFSG.KC.BfsPin.idA_eq hn) hh hp hs
  subst hk
  rw [← idT_tabT n] at R
  have hn32 : n < 2 ^ 32 := by
    obtain ⟨hn', -⟩ := CFSG.KS.PF.canon_facts hid
    omega
  exact closedOKH_of_hreplay hn32 hγ R

end CFSG.KS.MulH

end
