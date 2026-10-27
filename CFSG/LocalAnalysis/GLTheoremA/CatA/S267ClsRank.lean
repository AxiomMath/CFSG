module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.CGT.T75P.SylowSplit
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem card_le_card_of_involution (hp : p.Prime)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) {E : Subgroup Ω} (hE : IsElemAbelian p E)
    {t : Ω} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (hEt : ∀ e ∈ E, e * t = t * e) :
    Nat.card E ≤ Nat.card B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hE.isPGroup)
  have hEN : E ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Ω) : Set Ω) := fun e he =>
    mem_normalizer_of_forall_comm fun k hk => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact (Commute.zpow_right (hEt e he) m).eq
  have hloc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Ω) : Set Ω)) :=
    ⟨_, zpowers_ne_bot_of_ne_one ht1, isPGroup_two_zpowers_of_sq ht2, rfl⟩
  have h1 : j ≤ CFSG.Open.pRank p
      (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Ω) : Set Ω)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hEN hE hj
  have h2 :=
    CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_isTwoLocal hp hloc
  rw [hj]
  exact (Nat.pow_le_pow_right hp.pos (h1.trans h2)).trans hrank

theorem card_transfer_le (hp : p.Prime) (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    {H : Type} [Group H] (φ : H →* Ω) (hφS : φ.range = S) {E : Subgroup H}
    (hE : IsElemAbelian p E) {b' : Ω} (hb'B : b' ∈ B) (hb'E : ∀ e ∈ E, b' * φ e = φ e * b')
    {z : H} (hz2 : z ^ 2 = 1) (hz1 : φ z ≠ 1) (hzE : ∀ e ∈ E, e * z = z * e)
    (hb'z : b' * φ z = φ z * b') :
    Nat.card ↥((B ⊓ centModSubgroup p S) ⊔ E.map φ ⊔ Subgroup.zpowers b') ≤ Nat.card B := by
  set B₀ := B ⊓ centModSubgroup p S with hB₀
  have hEφS : E.map φ ≤ S := by
    rw [← hφS]
    exact Subgroup.map_le_range φ E
  have hB₀S : ∀ b ∈ B₀, ∀ s ∈ S, b * s = s * b := fun b hb s hs =>
    comm_of_mem_centMod hSn hcore hb.2 hs
  have hB₀el : IsElemAbelian p B₀ := hB.mono inf_le_left
  have hEφ : IsElemAbelian p (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE φ
  have hb'p : b' ^ p = 1 := hB.2 b' hb'B
  have hzel : IsElemAbelian p (Subgroup.zpowers b') := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb'p, one_zpow]
  have h1 : IsElemAbelian p (B₀ ⊔ E.map φ) :=
    hB₀el.sup_of_commute hEφ fun b hb e he => hB₀S b hb e (hEφS he)
  have hcb' : B₀ ⊔ E.map φ ≤ Subgroup.centralizer ((Subgroup.zpowers b' : Subgroup Ω) : Set Ω) := by
    refine sup_le (fun b hb => ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (hB.comm hb'B hb.1) n).eq
    · rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (hb'E e he) n).eq
  have h2 : IsElemAbelian p (B₀ ⊔ E.map φ ⊔ Subgroup.zpowers b') :=
    h1.sup_of_commute hzel fun x hx y hy => ((Subgroup.mem_centralizer_iff.1 (hcb' hx)) y hy).symm
  have hzS : φ z ∈ S := hφS ▸ ⟨z, rfl⟩
  have hcz : B₀ ⊔ E.map φ ⊔ Subgroup.zpowers b' ≤ Subgroup.centralizer ({φ z} : Set Ω) := by
    refine sup_le (sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
      (hB₀S b hb _ hzS)) ?_) ?_
    · rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, (hzE e he).symm]
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hb'z
  refine card_le_card_of_involution hp hrank h2 hz1 (by rw [← map_pow, hz2, map_one]) fun e he => ?_
  exact Subgroup.mem_centralizer_singleton_iff.1 (hcz he)

theorem card_transfer_eq (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {H : Type} [Group H] (φ : H →* Ω) (hφS : φ.range = S) {E : Subgroup H}
    (hEC : E.map φ ⊓ centModSubgroup p S = ⊥) {b' : Ω} (hb'B : b' ∈ B)
    (hb'E : ∀ e ∈ E, b' * φ e = φ e * b')
    (hb'out : Subgroup.zpowers b' ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥) :
    Nat.card ↥((B ⊓ centModSubgroup p S) ⊔ E.map φ ⊔ Subgroup.zpowers b') =
      p * Nat.card ↥(E.map φ) * Nat.card ↥(Subgroup.zpowers b') := by
  set B₀ := B ⊓ centModSubgroup p S with hB₀
  have hEφS : E.map φ ≤ S := by
    rw [← hφS]
    exact Subgroup.map_le_range φ E
  have hB₀S : ∀ b ∈ B₀, ∀ s ∈ S, b * s = s * b := fun b hb s hs =>
    comm_of_mem_centMod hSn hcore hb.2 hs
  have hinf1 : B₀ ⊓ E.map φ = ⊥ := by
    rw [eq_bot_iff, ← hEC]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  have hcard1 : Nat.card ↥(B₀ ⊔ E.map φ) = p * Nat.card ↥(E.map φ) := by
    rw [CFSG.CGT.T75P.card_sup_of_commute (fun b hb e he => hB₀S b hb e (hEφS he)) hinf1, hBC]
  have hcomm : ∀ x ∈ B₀ ⊔ E.map φ, ∀ y ∈ Subgroup.zpowers b', x * y = y * x := by
    have hle : B₀ ⊔ E.map φ ≤
        Subgroup.centralizer ((Subgroup.zpowers b' : Subgroup Ω) : Set Ω) := by
      refine sup_le (fun b hb => ?_) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact (Commute.zpow_left (hB.comm hb'B hb.1) n).eq
      · rintro _ ⟨e, he, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact (Commute.zpow_left (hb'E e he) n).eq
    exact fun x hx y hy => ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm
  have hle2 : B₀ ⊔ E.map φ ≤ S ⊔ Subgroup.centralizer (S : Set Ω) := by
    refine sup_le (fun b hb => Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.2
      fun s hs => (hB₀S b hb s hs).symm)) (hEφS.trans le_sup_left)
  have hinf2 : (B₀ ⊔ E.map φ) ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff, ← hb'out, inf_comm]
    exact inf_le_inf_left _ hle2
  rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf2, hcard1]

theorem card_mul_le_of_involution (hp : p.Prime) (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {H : Type} [Group H] (φ : H →* Ω)
    (hφS : φ.range = S) {E : Subgroup H} (hE : IsElemAbelian p E)
    (hEC : E.map φ ⊓ centModSubgroup p S = ⊥) {b' : Ω} (hb'B : b' ∈ B)
    (hb'E : ∀ e ∈ E, b' * φ e = φ e * b')
    (hb'out : Subgroup.zpowers b' ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥)
    {z : H} (hz2 : z ^ 2 = 1) (hz1 : φ z ≠ 1) (hzE : ∀ e ∈ E, e * z = z * e)
    (hb'z : b' * φ z = φ z * b') :
    p * Nat.card ↥(E.map φ) * Nat.card ↥(Subgroup.zpowers b') ≤ Nat.card B := by
  rw [← card_transfer_eq hSn hcore hB hBC φ hφS hEC hb'B hb'E hb'out]
  exact card_transfer_le hp hSn hcore hB hrank φ hφS hE hb'B hb'E hz2 hz1 hzE hb'z

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
