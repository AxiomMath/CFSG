module

public import CFSG.CGT.T75F.E710Simple
public import CFSG.Timmesfeld.Bridge.Asc72Theorem

public section

namespace CFSG.CGT.T75F

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem quot_not_comm :
    ¬ ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := by
  intro hcomm
  obtain ⟨y, hy, -⟩ := h.exists_out
  have hz : (QuotientGroup.mk y : X ⧸ Subgroup.center X) ∈
      Subgroup.center (X ⧸ Subgroup.center X) :=
    Subgroup.mem_center_iff.2 fun g => hcomm g _
  rw [h.center_quot_eq_bot, Subgroup.mem_bot] at hz
  exact h.mk_ne_one hy hz

theorem quot_isBender (hG : CFSG.CGT.Timmesfeld75.Goldschmidt1974) (hA : TheoremOne) :
    IsBenderGroup (X ⧸ Subgroup.center X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.quot_isSimple hG
  have hncomm := h.quot_not_comm
  obtain ⟨x₀, hx₀⟩ := h.Dhat_isConj
  have hradical : ∀ N : Subgroup (X ⧸ Subgroup.center X), N.Normal → Group.IsSolvable N →
      N = ⊥ := by
    intro N hN hsolv
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h1 | h1
    · exact h1
    · exfalso
      subst h1
      have : Group.IsSolvable (X ⧸ Subgroup.center X) :=
        Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv (G := X ⧸ Subgroup.center X)).toMonoidHom)
          (Subgroup.topEquiv (G := X ⧸ Subgroup.center X)).surjective
      exact hncomm (IsSimpleGroup.comm_iff_isSolvable.2 this)
  have hconcl := hA (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' D)
    ⟨x₀, hx₀⟩ (fun d hd => orderOf_eq_prime (by rw [pow_two]; exact h.Dhat_sq hd)
      (h.Dhat_ne_one hd))
    (fun d hd e he => h.Dhat_odd hd he) h.Dhat_closure hradical ?_
  · rcases hconcl with hB | ⟨f, n, hf, hn, ⟨e⟩⟩ | ⟨M₀, hM₀n, hmin, -, -, -, hidx, -⟩
    · exact hB
    · exfalso
      have hperf : commutator (X ⧸ Subgroup.center X) = ⊤ := by
        rcases Subgroup.Normal.eq_bot_or_eq_top (commutator (X ⧸ Subgroup.center X)) with h1 | h1
        · exfalso
          apply hncomm
          intro a b
          have : ⁅a, b⁆ ∈ commutator (X ⧸ Subgroup.center X) := Subgroup.commutator_mem_commutator
            (Subgroup.mem_top a) (Subgroup.mem_top b)
          rw [h1, Subgroup.mem_bot, commutatorElement_def] at this
          exact (mul_inv_eq_one.1 (by simpa [mul_assoc] using this) : a * b = b * a)
        · exact h1
      exact commutator_ne_top_of_l2Wreath (by rcases hn with rfl | rfl <;> norm_num) e hperf
    · exfalso
      obtain ⟨-, hM₀bot, -⟩ := hmin
      rcases Subgroup.Normal.eq_bot_or_eq_top M₀ with h1 | h1
      · exact hM₀bot h1
      · rw [h1, Subgroup.index_top] at hidx
        omega
  ·
    refine ⟨Mhat M, ?_, ?_, ?_⟩
    · obtain ⟨y, hy, hyM⟩ := h.exists_out
      intro htop
      have : (QuotientGroup.mk y : X ⧸ Subgroup.center X) ∈ Mhat M := htop ▸ Subgroup.mem_top _
      exact hyM ((h.mk_mem_Mhat_iff hy).1 this)
    · obtain ⟨β, hβ, hβM⟩ := h.exists_mem_delta
      exact ⟨QuotientGroup.mk β, ⟨β, hβ, rfl⟩, Subgroup.mem_map.2 ⟨β, hβM, rfl⟩⟩
    · intro u hu huM v hv hc
      exact h.H3hat hu huM hv hc.symm.eq

end Endgame710

end CFSG.CGT.T75F
