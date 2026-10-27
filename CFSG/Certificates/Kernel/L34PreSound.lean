module

public import Certificates.Data.Kernel.L34Pre
public import CFSG.Certificates.Kernel.L34KSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

namespace CFSG.KC.L34Pre

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (notB)

theorem strictB_val (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem PinE.pp {n w : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} (P : PinE n w gs cap ng N L K ew G T E C S SI) :
    ∀ i < N, PP n w (T i) := by
  obtain ⟨htabs, hok⟩ := enum_sound P
  have hcan := P.canon
  have hcG := P.canonG
  unfold enumOK treeOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨-, h0⟩, hall⟩ := hok
  rw [htabs] at h0 hall
  unfold pts at h0 hall
  rw [Array.size_ofFn] at hall
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hsz := CFSG.KC.L34KSnd.canon_sz (hcan i hi)
    have hG : ∀ k < ng, PP n w (G k) := fun k hk => PP_of_permOK hsz (P.perm k hk)
    have hx := CFSG.KS.BfsReplay.allBelow_iff.1 hall i hi
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    obtain ⟨-, hx⟩ := hx
    rcases hx with h | ⟨⟨hp, hl⟩, he⟩
    · subst h
      rw [CFSG.KC.L34KSnd.pts_get hi, CFSG.KC.L34KSnd.idTab_unpack' hsz] at h0
      rw [CFSG.KC.L34KSnd.unpack_inj' (hcan 0 hi) (CFSG.KC.L34KSnd.canon_pidn hsz) h0]
      exact PP.id hsz
    · rw [P.size] at hl
      have hpN : (enumBFS n gs cap).par[i]! < N := by omega
      rw [CFSG.KC.L34KSnd.pts_get hi, CFSG.KC.L34KSnd.pts_get hpN] at he
      unfold leftStep at he
      rw [P.bind _ hl, CFSG.KC.L34KSnd.comp_unpack' (hcG _ hl) (hcan _ hpN)] at he
      have hPP := (hG _ hl).mul (ih _ hp hpN)
      rw [CFSG.KC.L34KSnd.unpack_inj' (hcan i hi) hPP.1 he]
      exact hPP

theorem pcomp_pinvS_PP {n w t : Nat} (ht : PP n w t) :
    pcomp n w (mask w) t (pinvS n w (mask w) t) = pidn n w := by
  obtain ⟨-, hw, -, -⟩ := CFSG.KS.PF.canon_facts ht.1
  have hsz := ht.sz
  refine CFSG.KC.L34KSnd.eq_of_pg (ht.mul ht.inv).1 (CFSG.KC.L34KSnd.canon_pidn hsz)
    fun x hx => ?_
  rw [CFSG.KS.PackFld.pg_pcomp ht.lt32 hx, CFSG.KC.L34KSnd.pg_pidn' hsz hx]
  obtain ⟨y, hy, rfl⟩ := CFSG.KS.PinvS.surj_of_injK ht.2 x hx
  rw [CFSG.KS.PinvS.pg_pinvS (by omega) ht.2 hy]

theorem mvFix_false {n w nf : Nat} {F : Nat → Nat} {t a : Nat} (ht : PP n w t)
    (hF : ∀ q < nf, canonK n w (mask w) (n * w) (F q) = true)
    (hd : ∀ i < nf, ∀ j < nf, F i = F j → i = j)
    (hfix : ∀ q < nf, pg w (mask w) (F q) a = a) (ha : a < n)
    (hc : ∀ i < nf, ∃ q < nf,
      F q = pcomp n w (mask w) (pcomp n w (mask w) t (F i)) (pinvS n w (mask w) t)) :
    mvFix w nf F t a = false := by
  obtain ⟨-, hw, -, -⟩ := CFSG.KS.PF.canon_facts ht.1
  have hn32 := ht.lt32
  have hwn : n < 2 ^ w := by omega
  have hTi := ht.inv
  have hl : ∀ x < n, pg w (mask w) (pinvS n w (mask w) t) (pg w (mask w) t x) = x :=
    fun x hx => CFSG.KS.PinvS.pg_pinvS hwn ht.2 hx
  have hconj : ∀ i < nf, ∀ x < n,
      pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) t (F i)) (pinvS n w (mask w) t)) x =
        pg w (mask w) t (pg w (mask w) (F i) (pg w (mask w) (pinvS n w (mask w) t) x)) := by
    intro i hi x hx
    rw [CFSG.KS.PackFld.pg_pcomp hn32 hx, CFSG.KS.PackFld.pg_pcomp hn32 (hTi.2.1 x hx)]
  choose σ hσ hσe using hc
  have hinj : ∀ i₁ i₂ (h₁ : i₁ ∈ Finset.range nf) (h₂ : i₂ ∈ Finset.range nf),
      σ i₁ (Finset.mem_range.1 h₁) = σ i₂ (Finset.mem_range.1 h₂) → i₁ = i₂ := by
    intro i₁ i₂ h₁ h₂ e
    have m1 := Finset.mem_range.1 h₁
    have m2 := Finset.mem_range.1 h₂
    have ec : pcomp n w (mask w) (pcomp n w (mask w) t (F i₁)) (pinvS n w (mask w) t) =
        pcomp n w (mask w) (pcomp n w (mask w) t (F i₂)) (pinvS n w (mask w) t) := by
      rw [← hσe i₁ m1, ← hσe i₂ m2, e]
    apply hd i₁ m1 i₂ m2
    refine CFSG.KC.L34KSnd.eq_of_pg (hF _ m1) (hF _ m2) fun y hy => ?_
    have hx : pg w (mask w) t y < n := ht.2.1 y hy
    have e1 := hconj i₁ m1 _ hx
    rw [ec, hconj i₂ m2 _ hx, hl y hy] at e1
    exact (ht.2.2 _ ((CFSG.KS.PF.canon_facts (hF _ m1)).2.2.2 y hy) _
      ((CFSG.KS.PF.canon_facts (hF _ m2)).2.2.2 y hy) e1.symm)
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range nf) (t := Finset.range nf)
    (fun i hi => σ i (Finset.mem_range.1 hi)) (fun i hi => Finset.mem_range.2 (hσ i _)) hinj le_rfl
  have hall : allN nf (fun i => Nat.beq (pg w (mask w) (F i) (pg w (mask w) t a))
      (pg w (mask w) t a)) = true := by
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro q hq
    obtain ⟨i, hi, e⟩ := hsurj q (Finset.mem_range.2 hq)
    have hi' := Finset.mem_range.1 hi
    have hq' : F q = pcomp n w (mask w) (pcomp n w (mask w) t (F i)) (pinvS n w (mask w) t) := by
      rw [e]
      exact hσe i hi'
    rw [hq', hconj i hi' _ (ht.2.1 a ha), hl a ha, hfix i hi', Nat.beq_refl]
  unfold mvFix
  rw [strictB_val, hall]
  rfl

end CFSG.KC.L34Pre

end
