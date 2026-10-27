module

public import Certificates.Certificate55122
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4.E4A
open CFSG.ClassicalInvolution.Q3.TL4.E4C

section Tests

variable {w : List (Array ℕ)} {g : Equiv.Perm (Fin 820)}

theorem twW_iff (hw : RepW 820 w g) {a b : Array ℕ} {A B : Equiv.Perm (Fin 820)}
    (ha : Rep 820 a A) (hb : Rep 820 b B) : twW a b w = true ↔ g * A = B * g := by
  rw [twW, allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := h x x.2
    rw [beq_iff_eq, ha x, hw (A x), hw x, hb (g x)] at this
    exact this
  · intro h i hi
    have e1 : evR w i = (g ⟨i, hi⟩ : ℕ) := hw ⟨i, hi⟩
    rw [beq_iff_eq, ha.apply hi, hw (A ⟨i, hi⟩), e1, hb (g ⟨i, hi⟩)]
    have := congrArg (fun F : Equiv.Perm (Fin 820) => (F ⟨i, hi⟩ : ℕ)) h
    simpa only [Equiv.Perm.mul_apply] using this

end Tests

theorem cfg_classify {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) {k : ℕ} (hk : k < 8)
    (hcfg : CfgCore (g * tP k)) : ∃ c ∈ gamP, g * tP k = c * d2P * c⁻¹ :=
  Certificates.certificate55122.1 g hg k hk hcfg

theorem card_inf_centralizer_d2 :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820)))) = 6048 :=
  Certificates.certificate55122.2

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
