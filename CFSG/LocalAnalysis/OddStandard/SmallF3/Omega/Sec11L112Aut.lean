module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112QA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_card_le_of_aut [Finite G] {Q P X : Subgroup G}
    (hXN : X ≤ normalizer (Q : Set G)) (hXP : ∀ x ∈ X, ∀ p ∈ P, x * p = p * x)
    (hΦ : ∀ Φ : Subgroup (MulAut ↥Q),
      (∀ γ ∈ Φ, ∀ p : ↥Q, (p : G) ∈ P → γ p = p) → Nat.card ↥Φ ≤ 8) :
    Nat.card ↥X ≤ 8 * Nat.card ↥(X ⊓ centralizer (Q : Set G)) := by
  let Θ : ↥X →* MulAut ↥Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  have hcoe : ∀ (x : ↥X) (p : ↥Q), ((Θ x p : ↥Q) : G) = (x : G) * (p : G) * (x : G)⁻¹ :=
    fun x p => rfl
  have hΦ8 : Nat.card ↥Θ.range ≤ 8 := by
    refine hΦ Θ.range ?_
    rintro γ ⟨x, rfl⟩ p hp
    apply Subtype.ext
    rw [hcoe, hXP x x.2 p hp]
    group
  have hker : Nat.card ↥Θ.ker ≤ Nat.card ↥(X ⊓ centralizer (Q : Set G)) := by
    have hmem : ∀ k : ↥Θ.ker, (k.1 : G) ∈ centralizer (Q : Set G) := by
      intro k
      refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      have h : ((Θ k.1 ⟨q, hq⟩ : ↥Q) : G) = q := by
        rw [MonoidHom.mem_ker.mp k.2]
        rfl
      rw [hcoe] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    refine Nat.card_le_card_of_injective
      (fun k => (⟨(k.1 : G), k.1.2, hmem k⟩ : ↥(X ⊓ centralizer (Q : Set G)))) ?_
    intro k k' h
    have h' : (k.1 : G) = (k'.1 : G) :=
      congrArg (fun y : ↥(X ⊓ centralizer (Q : Set G)) => (y : G)) h
    exact Subtype.ext (Subtype.ext h')
  calc Nat.card ↥X = Nat.card ↥Θ.ker * Nat.card ↥Θ.range :=
        (Subgroup.card_ker_mul_card_range Θ).symm
    _ ≤ Nat.card ↥(X ⊓ centralizer (Q : Set G)) * 8 := Nat.mul_le_mul hker hΦ8
    _ = 8 * Nat.card ↥(X ⊓ centralizer (Q : Set G)) := mul_comm _ _

namespace Sec11Model

variable {t z : G} {L S : Subgroup G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem card_P (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    Nat.card ↥(secA t S L ⊓ secQ K1 K2) = 8 := by
  let f : {v : Fin 6 → ZMod 2 // (∑ i, v i = 0 ∧ v 0 = v 1) ∧ v 5 = 0} →
      ↥(secA t S L ⊓ secQ K1 K2) := fun v =>
    ⟨φ v.1, hm.perm.mem _, (hm.mem_Q _).mpr v.2.1⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro v w h
      have h' : φ v.1 = φ w.1 := congrArg Subtype.val h
      rcases (hm.perm.eq_iff _ _).mp h' with h1 | h1
      · exact Subtype.ext (sec11_vec_eq_of_add_eq_zero h1)
      · exfalso
        have := congrFun h1 5
        simp only [Pi.add_apply, v.2.2, w.2.2] at this
        exact absurd this (by decide)
    · rintro ⟨a, ha, haQ⟩
      obtain ⟨v, hv⟩ := hm.perm.surj a ha
      obtain ⟨v', hv', h5⟩ := sec11_exists_rep v
      have hφ : φ v' = a := by
        rcases hv' with rfl | rfl
        · exact hv
        · rw [hm.perm.map_add_one, hv]
      exact ⟨⟨v', (hm.mem_Q v').mp (hφ ▸ haQ), h5⟩, Subtype.ext hφ⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card]
  decide +kernel

theorem isElemAb2_P (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    IsElemAb2 (secA t S L ⊓ secQ K1 K2) 3 := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, by rw [hm.card_P]; norm_num⟩
  · obtain ⟨v, hv⟩ := hm.perm.surj a.1 a.2.1
    obtain ⟨w, hw⟩ := hm.perm.surj b.1 b.2.1
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hw, hm.perm.comm])
  · obtain ⟨v, hv⟩ := hm.perm.surj x hx.1
    rw [← hv, pow_two]
    exact hm.perm.sq v

end Sec11Model

theorem sec11_aut_bound [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec11Model t L S z K1 K2 T Alt φ) (Φ : Subgroup (MulAut ↥(secQ K1 K2)))
    (hΦ : ∀ γ ∈ Φ, ∀ p : ↥(secQ K1 K2), (p : G) ∈ secA t S L ⊓ secQ K1 K2 → γ p = p) :
    Nat.card ↥Φ ≤ 8 := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hcomm : ⁅K1, K2⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (sec10Z_comm hp.facts.pockets5 hpsp hctx.toSec10Ctx a ha b hb).symm
  obtain ⟨e1, e2⟩ := sec10KS_equiv hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx
  exact hp.facts.autQ G K1 K2 hcomm
    (sec10KS_card_sup hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx) e1 e2
    (secA t S L ⊓ secQ K1 K2) inf_le_right hm.isElemAb2_P Φ hΦ

end CFSG.OddStandard.SmallF3.Omega
