module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.GroupTheory.InnerNormalizedAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

section Model


theorem exists_twistedE6RootGroup_of_catalogIs_isTE6two {S : Type} [Group S]
    (h : catalogIs S isTE6two) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = 4 ∧
      (∀ c, σ c = c ^ 2) ∧ Nonempty (S ≃* twistedE6RootGroup K σ) := by
  obtain ⟨d, hv, hP, ⟨e0⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | twistedE6 q =>
    have hq2 : q.card = 2 := hP
    obtain ⟨K, hKfield, σ, hK, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    letI : Field K := hKfield
    have hq : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
    have hK4 : Nat.card K = 4 := by rw [hK, hq]; norm_num
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
    exact ⟨K, hKfield, inferInstance, σ, hK4, fun c => by rw [hσ c, hq], ⟨e0.trans e⟩⟩
  | _ => exact hP.elim

end Model

section ElementaryAbelian


theorem exists_conj_gen_of_elemAbelian_nine {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {A : Subgroup (MulAut (twistedE6RootGroup K σ))} (hA : IsElemAbelian 3 A)
    (h9 : Nat.card A = 3 ^ 2) :
    ∃ s : twistedE6RootGroup K σ, orderOf s = 3 ∧ ∃ b ∈ A,
      Subgroup.closure {MulAut.conj s, b} = A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 : ℕ) := hσ
  have hA9 : Nat.card A = 9 := by rw [h9]; norm_num
  have hfr : ∀ a : ↥A, (QuotientGroup.mk' (twistedE6Inn K σ)) (a : MulAut _) ∈
      (twistedE6Diag K σ).map (QuotientGroup.mk' (twistedE6Inn K σ)) := by
    intro a
    have ha : (a : MulAut _) ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ :=
      Bal209TwoOuterInAux.mem_inn_sup_diag_of_pow_three hK σ hσ (hA.2 a.val a.2)
    obtain ⟨i, hi, d, hd, hid⟩ := Subgroup.mem_sup_of_normal_left.1 ha
    refine ⟨d, hd, ?_⟩
    show QuotientGroup.mk' (twistedE6Inn K σ) d =
      QuotientGroup.mk' (twistedE6Inn K σ) (a : MulAut _)
    rw [← hid, map_mul]
    have hi1 : QuotientGroup.mk' (twistedE6Inn K σ) i = 1 :=
      (QuotientGroup.eq_one_iff i).2 hi
    rw [hi1, one_mul]
  let f : ↥A →* MulAut (twistedE6RootGroup K σ) ⧸ twistedE6Inn K σ :=
    (QuotientGroup.mk' (twistedE6Inn K σ)).comp A.subtype
  have hfrange : f.range ≤ (twistedE6Diag K σ).map
      (QuotientGroup.mk' (twistedE6Inn K σ)) := by
    rintro y ⟨a, rfl⟩
    exact hfr a
  have hΔ3 : Nat.card ((twistedE6Diag K σ).map
      (QuotientGroup.mk' (twistedE6Inn K σ))) ≤ 3 := by
    have h := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_card_range_diag_outer_le_three
      (q := 2) hK2 σ hσ2
    have hmap : (twistedE6Diag K σ).map (QuotientGroup.mk' (twistedE6Inn K σ)) =
        ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
          (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range :=
      MonoidHom.map_range _ _
    rw [hmap]
    exact h
  have hf3 : Nat.card f.range ≤ 3 := (Subgroup.card_le_of_le hfrange).trans hΔ3
  have hprod : Nat.card ↥f.ker * Nat.card ↥f.range = 9 := by
    have h := Subgroup.card_ker_mul_card_range f
    rwa [hA9] at h
  have hkbot : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at hprod
    omega
  obtain ⟨⟨x, hxker⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hkbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hmk : QuotientGroup.mk' (twistedE6Inn K σ)
      (x : MulAut (twistedE6RootGroup K σ)) = 1 := by
    simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using
      (MonoidHom.mem_ker.1 hxker)
  have hxInn : (x : MulAut (twistedE6RootGroup K σ)) ∈ twistedE6Inn K σ :=
    (QuotientGroup.eq_one_iff (x : MulAut (twistedE6RootGroup K σ))).1 hmk
  have hxRange : (x : MulAut (twistedE6RootGroup K σ)) ∈
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
    simpa [twistedE6Inn, CFSG.ComponentClassification.OuterAutomorphisms.inner] using hxInn
  obtain ⟨s, hs⟩ := hxRange
  have hxne : (x : MulAut (twistedE6RootGroup K σ)) ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hc3 : (MulAut.conj s) ^ 3 = 1 := by
    rw [hs]
    exact hA.2 (x : MulAut (twistedE6RootGroup K σ)) x.2
  have hc1 : MulAut.conj s ≠ 1 := by
    rw [hs]
    exact hxne
  have hs1 : s ≠ 1 := fun h => hc1 (by rw [h, map_one])
  have hs3 : s ^ 3 = 1 := by
    have hconj : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hc3]
    have hmem := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconj
    rwa [CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective, Subgroup.mem_bot] at hmem
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hco : orderOf (MulAut.conj s) = 3 := orderOf_eq_prime hc3 hc1
  have hbex : ∃ b ∈ A, b ∉ Subgroup.zpowers (MulAut.conj s) := by
    by_contra h
    push Not at h
    have hle : A ≤ Subgroup.zpowers (MulAut.conj s) := h
    have hz : Nat.card (Subgroup.zpowers (MulAut.conj s)) = 3 := by
      rw [Nat.card_zpowers, hco]
    have hcard := Subgroup.card_le_of_le hle
    rw [hA9, hz] at hcard
    norm_num at hcard
  obtain ⟨b, hbA, hbnot⟩ := hbex
  have hcA : MulAut.conj s ∈ A := by rw [hs]; exact x.2
  have hzcard : Nat.card (Subgroup.zpowers (MulAut.conj s)) = 3 := by
    rw [Nat.card_zpowers, hco]
  have hclA : Subgroup.closure {MulAut.conj s, b} ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hcA
    · exact hbA
  have hzcl : Subgroup.zpowers (MulAut.conj s) ≤ Subgroup.closure {MulAut.conj s, b} :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hge : 3 ≤ Nat.card (Subgroup.closure {MulAut.conj s, b}) := by
    rw [← hzcard]
    exact Subgroup.card_le_of_le hzcl
  have hdvd : Nat.card (Subgroup.closure {MulAut.conj s, b}) ∣ 9 := by
    rw [← hA9]
    exact Subgroup.card_dvd_of_le hclA
  have hne3 : Nat.card (Subgroup.closure {MulAut.conj s, b}) ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers (MulAut.conj s) = Subgroup.closure {MulAut.conj s, b} :=
      Subgroup.eq_of_le_of_card_ge hzcl (by rw [h3, hzcard])
    exact hbnot (heq.symm ▸ Subgroup.subset_closure (by simp))
  have hdvd' : Nat.card (Subgroup.closure {MulAut.conj s, b}) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]
    exact hdvd
  have hcard : Nat.card (Subgroup.closure {MulAut.conj s, b}) = 9 := by
    obtain ⟨k, hk, hkr⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).1 hdvd'
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h0 | h1 | h2
    · rw [h0, pow_zero] at hkr
      omega
    · rw [h1, pow_one] at hkr
      omega
    · rw [h2] at hkr
      have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h9] at hkr
      omega
  exact ⟨s, hso, b, hbA, Subgroup.eq_of_le_of_card_ge hclA (by rw [hcard, hA9])⟩

end ElementaryAbelian

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
