module

public import Certificates.Data.Kernel.Sp6Root
public import CFSG.Certificates.Kernel.SporSch.ChainKPack

public section

namespace CFSG.KS.Sp6Root

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11
open CFSG.KS.SporSch.MOC

variable {n w : Nat}

@[expose] def commAllB (qs : List (Equiv.Perm (Fin n))) (x : Equiv.Perm (Fin n)) : Bool :=
  qs.all fun g => decide (x * (g * x * g⁻¹) = g * x * g⁻¹ * x)

theorem commQ_cons (n w m P Q : Nat) (QL : List Nat) :
    commQ n w m P (Q :: QL) =
      (Nat.beq (pcomp n w m P (pcomp n w m (pcomp n w m Q P) (pcomp n w m Q Q)))
        (pcomp n w m (pcomp n w m (pcomp n w m Q P) (pcomp n w m Q Q)) P) &&
        commQ n w m P QL) := by
  change bAnd(strictB _ _, commQ n w m P QL) = _
  rw [Orb.bAnd_eq, Orb.strictB_eq]

theorem commQ_eq (hn : n < 2 ^ 32) (hw : 0 < w) {P : Nat} {x : Equiv.Perm (Fin n)}
    (hP : PRep n w P x) :
    ∀ {QL : List Nat} {qs : List (Equiv.Perm (Fin n))},
      List.Forall₂ (fun Q q => PRep n w Q q) QL qs → (∀ q ∈ qs, q * q = q⁻¹) →
        commQ n w (mask w) P QL = commAllB qs x
  | [], [], .nil, _ => rfl
  | Q :: QL, q :: qs, .cons hQ hr, h3 => by
    have hC : PRep n w (pcomp n w (mask w) (pcomp n w (mask w) Q P) (pcomp n w (mask w) Q Q))
        (q * x * q⁻¹) := by
      rw [← h3 q List.mem_cons_self]
      exact prep_pcomp hn (prep_pcomp hn hQ hP) (prep_pcomp hn hQ hQ)
    rw [commQ_cons, beq_pcomp_iff hn hw hP hC hC hP,
      commQ_eq hn hw hP hr fun q' hq' => h3 q' (List.mem_cons_of_mem q hq')]
    simp only [commAllB, List.all_cons]

theorem k1P_eq (hsz : szOK n w = true) {QL : List Nat} {qs : List (Equiv.Perm (Fin n))}
    (hq : List.Forall₂ (fun Q q => PRep n w Q q) QL qs) (h3 : ∀ q ∈ qs, q * q = q⁻¹)
    {P : Nat} {x : Equiv.Perm (Fin n)} (hP : PRep n w P x) (sP : P >>> (n * w) = 0) :
    k1P n w (mask w) (pidn n w) QL P = (decide (orderOf x = 2) && commAllB qs x) := by
  have hn := szOK_lt hsz
  have hw := PF.w_pos (szOK_facts hsz).2
  change bAnd(ordIs n w (mask w) (pidn n w) P (2 - 1), commQ n w (mask w) P QL) = _
  rw [Orb.bAnd_eq, ordIs_eq hsz hP sP (by norm_num), commQ_eq hn hw hP hq h3]

theorem rowK_spec (n w m idn X : Nat) :
    ∀ S0 : List Nat, rowK n w m idn X S0 = true →
      ∀ Y ∈ S0, ordIs n w m idn (pcomp n w m X Y) 3 = false
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | Y :: S0, h => by
    change bIf(ordIs n w m idn (pcomp n w m X Y) 3, false, rowK n w m idn X S0) = true at h
    rw [Orb.bIf_eq] at h
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i hY
      intro Y' hY'
      rcases List.mem_cons.1 hY' with rfl | hY'
      · simpa using hY
      · exact rowK_spec n w m idn X S0 h Y' hY'

theorem pairsK_spec (n w m idn : Nat) (S0 : List Nat) :
    ∀ S : List Nat, pairsK n w m idn S0 S = true →
      ∀ X ∈ S, ∀ Y ∈ S0, ordIs n w m idn (pcomp n w m X Y) 3 = false
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | X :: S, h => by
    change bAnd(rowK n w m idn X S0, pairsK n w m idn S0 S) = true at h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h
    intro X' hX'
    rcases List.mem_cons.1 hX' with rfl | hX'
    · exact rowK_spec n w m idn X' S0 h.1
    · exact pairsK_spec n w m idn S0 S h.2 X' hX'

end CFSG.KS.Sp6Root

end
