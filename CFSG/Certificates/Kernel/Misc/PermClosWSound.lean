module

public import Certificates.Data.Kernel.Misc.PermClosW
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.Spor.PinvSSound
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Misc.ClosW

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.Clos CFSG.KS.PF CFSG.KS.PinvS

@[expose] def wcode {n : ℕ} (w : ℕ) (σ : Perm (Fin n)) : ℕ :=
  ((List.finRange n).map fun i => (σ i : ℕ) * 2 ^ (w * (i : ℕ))).sum

@[expose] def tcode (n w : ℕ) (t : Array ℕ) : ℕ :=
  ((List.finRange n).map fun i : Fin n => t[(i : ℕ)]! * 2 ^ (w * (i : ℕ))).sum

theorem wcode_eq_tcode {n w : ℕ} {t : Array ℕ} {σ : Perm (Fin n)}
    (h : ∀ i : Fin n, t[(i : ℕ)]! = (σ i : ℕ)) : wcode w σ = tcode n w t := by
  unfold wcode tcode
  congr 1
  refine List.map_congr_left fun i _ => ?_
  change (σ i : ℕ) * 2 ^ (w * (i : ℕ)) = t[(i : ℕ)]! * 2 ^ (w * (i : ℕ))
  rw [h i]

@[expose] def img {n : ℕ} (σ : Perm (Fin n)) (i : ℕ) : ℕ := if h : i < n then σ ⟨i, h⟩ else 0

theorem sum_eq_ofFnW (w : ℕ) (g : ℕ → ℕ) (hg : ∀ i, g i < 2 ^ w) : ∀ m,
    ((List.range m).map fun i => g i * 2 ^ (w * i)).sum = CFSG.KC.LQT.PW.ofFnW m w g ∧
      CFSG.KC.LQT.PW.ofFnW m w g < 2 ^ (w * m)
  | 0 => ⟨rfl, by simp [CFSG.KC.LQT.PW.ofFnW]⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := sum_eq_ofFnW w g hg m
    have e : CFSG.KC.LQT.PW.ofFnW (m + 1) w g =
        CFSG.KC.LQT.PW.ofFnW m w g + g m * 2 ^ (w * m) := by
      change CFSG.KC.LQT.PW.ofFnW m w g ||| g m <<< (w * m) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h2, Nat.shiftLeft_eq, Nat.add_comm]
    rw [e]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ, List.map_append, List.sum_append, h1]
      simp
    · have e2 : 2 ^ (w * (m + 1)) = 2 ^ w * 2 ^ (w * m) := by
        rw [Nat.mul_succ, pow_add, mul_comm]
      rw [e2]
      calc CFSG.KC.LQT.PW.ofFnW m w g + g m * 2 ^ (w * m)
          < 2 ^ (w * m) + g m * 2 ^ (w * m) := Nat.add_lt_add_right h2 _
        _ = (g m + 1) * 2 ^ (w * m) := by ring
        _ ≤ 2 ^ w * 2 ^ (w * m) := Nat.mul_le_mul_right _ (hg m)

theorem wcode_eq_ofFnW {n w : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) :
    wcode w σ = CFSG.KC.LQT.PW.ofFnW n w (img σ) := by
  have hg : ∀ i, img σ i < 2 ^ w := fun i => by
    unfold img
    split
    · exact (Fin.isLt _).trans hw
    · exact Nat.two_pow_pos w
  rw [← (sum_eq_ofFnW w (img σ) hg n).1]
  unfold wcode
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < n := by simpa using h1
  simp [img, hi]

theorem fld_wcode {n w : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) :
    Fld w (wcode w σ) (fun i => if i < n then img σ i else 0) := by
  rw [wcode_eq_ofFnW hw]
  refine fld_ofFnW w (img σ) (fun i => ?_) n
  unfold img
  split
  · exact (Fin.isLt _).trans hw
  · exact Nat.two_pow_pos w

theorem pg_wcode {n w : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) (i : Fin n) :
    pg w (mask w) (wcode w σ) i = σ i := by
  have e : (if (i : ℕ) < n then img σ i else 0) = σ i := by
    rw [if_pos i.isLt]
    unfold img
    rw [dif_pos i.isLt]
  have h := pg_of_fld (i := i) (fld_wcode hw σ) (by rw [e]; exact (Fin.isLt _).trans hw)
  rw [h, e]

theorem pg_wcode_nat {n w i : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) (hi : i < n) :
    pg w (mask w) (wcode w σ) i = σ ⟨i, hi⟩ :=
  pg_wcode hw σ ⟨i, hi⟩

theorem wcode_shr {n w : ℕ} (hw : n + 1 < 2 ^ w) (σ : Perm (Fin n)) :
    wcode w σ >>> (n * w) = 0 :=
  shr_zero_of_fld (w_pos hw) (fld_wcode (by omega) σ) (fun i hi => by
    have : ¬ i < n := by omega
    simp [this])

theorem wcode_enc {n w : ℕ} (hw : n + 1 < 2 ^ w) (hn : n < 16777216) :
    ClosEnc (wcode (n := n) w) (pcomp n w (mask w)) (pidn n w) := by
  have hw' : n < 2 ^ w := by omega
  have h32 : n < 2 ^ 32 := Nat.lt_of_lt_of_le hn (by decide)
  have hw0 := w_pos hw
  refine ⟨?_, fun a b => ?_, fun a b h => ?_⟩
  · refine eq_of_fields hw0 (wcode_shr hw 1) (pidn_shr hn hw) fun i hi => ?_
    rw [pg_wcode_nat hw' 1 hi, pg_pidn hn hw hi]
    rfl
  · refine eq_of_fields hw0 (wcode_shr hw _) (pcomp_shr _ _ h32 hw0) fun i hi => ?_
    rw [pg_wcode_nat hw' (a * b) hi, pg_pcomp h32 hi, pg_wcode_nat hw' b hi,
      pg_wcode hw' a (b ⟨i, hi⟩)]
    rfl
  · ext i
    rw [← pg_wcode hw' a i, ← pg_wcode hw' b i, h]

theorem injK_wcode {n w : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) : InjK n w (wcode w σ) := by
  refine ⟨fun i hi => ?_, fun a ha b hb e => ?_⟩
  · rw [pg_wcode_nat hw σ hi]
    exact Fin.isLt _
  · rw [pg_wcode_nat hw σ ha, pg_wcode_nat hw σ hb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))

theorem wcode_inv {n w : ℕ} (hw : n + 1 < 2 ^ w) (σ : Perm (Fin n)) :
    pinvS n w (mask w) (wcode w σ) = wcode w σ⁻¹ := by
  have hw' : n < 2 ^ w := by omega
  refine eq_of_fields (w_pos hw) (pinvS_shr hw' (injK_wcode hw' σ).1) (wcode_shr hw _)
    fun i hi => ?_
  have e : pg w (mask w) (wcode w σ) (σ⁻¹ ⟨i, hi⟩) = i := by
    rw [pg_wcode hw' σ]
    simp
  have h1 := pg_pinvS hw' (injK_wcode hw' σ) (Fin.isLt (σ⁻¹ ⟨i, hi⟩))
  rw [e] at h1
  rw [h1, pg_wcode_nat hw' σ⁻¹ hi]

theorem wword_mem {n w : ℕ} (hw : n + 1 < 2 ^ w) (hn : n < 16777216) (gs : List (Perm (Fin n)))
    {A : ℕ → ℕ} (hA : ∀ a < gs.length, A a = wcode w (gs.getD a 1)) {wd : List ℕ}
    (hwd : lettersK gs.length wd = true) :
    ∃ g ∈ Subgroup.closure {g | g ∈ gs}, wcode w g = wWord n w A gs.length wd := by
  have henc := wcode_enc hw hn
  induction wd with
  | nil => exact ⟨1, Subgroup.one_mem _, henc.enc_one⟩
  | cons l wd ih =>
    change CFSG.KC.Ord.andB (Nat.blt l (gs.length + gs.length)) (lettersK gs.length wd) = true
      at hwd
    obtain ⟨hl, hwd⟩ := andB_eq_true hwd
    obtain ⟨g, hg, hgw⟩ := ih hwd
    have hl' : l < gs.length + gs.length := Nat.blt_eq.mp hl
    have hmem : ∀ a < gs.length, gs.getD a 1 ∈ Subgroup.closure {g | g ∈ gs} := fun a ha =>
      Subgroup.subset_closure (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
        exact List.getElem_mem ha)
    have hlet : ∃ u ∈ Subgroup.closure {g | g ∈ gs}, wcode w u = wLetter n w A gs.length l := by
      unfold wLetter
      cases hb : Nat.blt l gs.length
      · have hge : gs.length ≤ l := Nat.not_lt.1 fun h => by
          rw [Nat.blt_eq.mpr h] at hb
          cases hb
        have hlt : l - gs.length < gs.length := by omega
        refine ⟨(gs.getD (l - gs.length) 1)⁻¹, Subgroup.inv_mem _ (hmem _ hlt), ?_⟩
        change wcode w _ = pinvS n w (mask w) (A (l - gs.length))
        rw [hA _ hlt, wcode_inv hw]
      · exact ⟨gs.getD l 1, hmem l (Nat.blt_eq.mp hb), (hA l (Nat.blt_eq.mp hb)).symm⟩
    obtain ⟨u, hu, hul⟩ := hlet
    refine ⟨u * g, Subgroup.mul_mem _ hu hg, ?_⟩
    change wcode w (u * g) = pcomp n w (mask w) (wLetter n w A gs.length l) (wWord n w A gs.length wd)
    rw [henc.enc_mul, hul, hgw]

end CFSG.KC.Misc.ClosW

end
