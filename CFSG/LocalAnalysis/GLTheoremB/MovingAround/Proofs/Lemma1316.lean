module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1316

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def LocalPFactorStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D),
    CFSG.GH74.GLS.oResidual p ↥(Subgroup.normalizer ((CFSG.GH74.GLS.Bg.kLowInfty R : Subgroup G) : Set G)) ≠ ⊤

theorem oResidual_normal (p : ℕ) (X : Type) [Group X] :
    (CFSG.GH74.GLS.oResidual p X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : Subgroup.closure {x : X | Nat.Coprime (orderOf x) p} ≤
      (Subgroup.closure {x : X | Nat.Coprime (orderOf x) p}).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : Nat.Coprime (orderOf x) p := hx
    have ho : orderOf ((MulAut.conj g).toMonoidHom x) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure ?_)
    show Nat.Coprime (orderOf ((MulAut.conj g).toMonoidHom x)) p
    rw [ho]
    exact hx'
  exact Subgroup.mem_comap.1 (hle hn)

theorem isPGroup_of_oResidual_eq_bot {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hbot : CFSG.GH74.GLS.oResidual p G = ⊥) : IsPGroup p G := by
  unfold IsPGroup
  intro g
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨e, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  refine ⟨e, ?_⟩
  have hpow : (g ^ p ^ e) ^ n' = 1 := by
    rw [← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hdvd : orderOf (g ^ p ^ e) ∣ n' := orderOf_dvd_of_pow_eq_one hpow
  have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
  have hmem' : g ^ p ^ e ∈ Subgroup.closure {x : G | Nat.Coprime (orderOf x) p} :=
    Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left hdvd hcop)
  have hmem : g ^ p ^ e ∈ CFSG.GH74.GLS.oResidual p G := hmem'
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1316

end
