module

public import Certificates.Data.Kernel.SporLatDcS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Certificates.Kernel.E64FSound
import CFSG.Certificates.Kernel.SporLatDcLat
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

theorem dcCheckS_sound {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (C : DcCtx)
    (hn : C.n = n) (D : DcData) (s : ℕ) (a b : Γ)
    (gen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    (sl : List Γ) (hsl : sl.length = C.ns)
    (hL : ∀ l < 2 + C.ns, Good n (tab n ((a :: b :: sl).getD l 1)).toArray (C.L l))
    (hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng})
    (hk : Nat.card (Subgroup.closure {x | x ∈ sl.take C.ng}) = s)
    (hN : Nat.card Γ = C.N * s)
    (hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1)
    (hΔ : PtValid n C.Δ) (h : dcCheckS C D s = true) :
    (∀ g : Γ, lab n ptLab C.Δ g = C.Δ ↔ g ∈ Subgroup.closure {x | x ∈ sl.take C.ng}) ∧
    ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sl.take C.ng} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length
        (fun j => Subgroup.closure {x | x ∈ sl.take C.ng ++ (D.mw.getD j []).map (wordElt a b)})
        j := by
  let P : DcSoundCtx Γ n :=
    ⟨C, D, hn, a, b, gen, sl, hsl, hL, hS, s, hk, hN, hsep, hΔ, h⟩
  exact ⟨fun g => DcSoundCtx.lab_eq_iff_S P g, DcSoundCtx.family_complete_apply P⟩

theorem dcCheck_sound {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (C : DcCtx)
    (hn : C.n = n) (D : DcData) (a b : Γ) (gen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    (sl : List Γ) (hsl : sl.length = C.ns)
    (hL : ∀ l < 2 + C.ns, Good n (tab n ((a :: b :: sl).getD l 1)).toArray (C.L l))
    (hS : ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng})
    (hk : Nat.card (Subgroup.closure {x | x ∈ sl.take C.ng}) = 2 ^ C.k)
    (hN : Nat.card Γ = C.N * 2 ^ C.k)
    (hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1)
    (hΔ : PtValid n C.Δ) (h : dcCheck C D = true) :
    (∀ g : Γ, lab n ptLab C.Δ g = C.Δ ↔ g ∈ Subgroup.closure {x | x ∈ sl.take C.ng}) ∧
    ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sl.take C.ng} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length
        (fun j => Subgroup.closure {x | x ∈ sl.take C.ng ++ (D.mw.getD j []).map (wordElt a b)})
        j :=
  dcCheckS_sound C hn D (2 ^ C.k) a b gen sl hsl hL hS hk hN hsep hΔ
    (by rw [← dcCheck_eq_dcCheckS]; exact h)

section OmOKG

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem omOKG_sound {act : Array Nat → Lab → Lab} {letters : Array (Array Nat)}
    {actF : Nat → Lab → Lab} {x0 : Lab} {O : OmegaData Lab} (P : Lab → Prop) (hP0 : P x0)
    (hP : ∀ l < letters.size, ∀ x, P x → P (actF l x) ∧ act letters[l]! x = actF l x)
    (h : omOKG actF x0 letters.size O = true) :
    OmegaSpec act letters x0 O ∧ ∀ i < O.lbl.size, P O.lbl[i]! := by
  unfold omOKG at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, hpos⟩, hpn⟩, htree⟩, hnd⟩ := h
  have hpn' : ∀ l < letters.size, ∀ i < O.lbl.size,
      (O.pn[l]!)[i]! < O.lbl.size ∧ O.lbl[(O.pn[l]!)[i]!]! = actF l O.lbl[i]! := by
    intro l hl i hi
    have e := List.all_eq_true.1 (List.all_eq_true.1 hpn l (List.mem_range.2 hl)) i
      (List.mem_range.2 hi)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using e
  have htree' : ∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < letters.size ∧
      (O.pn[O.via[i]!]!)[O.par[i]!]! = i := by
    intro i hi hi0
    have e := List.all_eq_true.1 htree i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at e
    rcases e with e | ⟨⟨e1, e2⟩, e3⟩
    · omega
    · exact ⟨e1, e2, e3⟩
  have hPi : ∀ i < O.lbl.size, P O.lbl[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0]; exact hP0
      · obtain ⟨hp, hv, he⟩ := htree' i hi hi0
        have h1 := hpn' _ hv O.par[i]! (by omega)
        rw [he] at h1
        rw [h1.2]
        exact (hP _ hv _ (ih _ hp (by omega))).1
  refine ⟨⟨h0, hpos, fun l hl i hi => ?_, htree',
    CFSG.Quasithin.GoldD3.distinctB_of_nodup hnd⟩, hPi⟩
  refine ⟨(hpn' l hl i hi).1, ?_⟩
  rw [(hpn' l hl i hi).2, (hP l hl _ (hPi i hi)).2]

end OmOKG

end CFSG.KC.SLDc

end
