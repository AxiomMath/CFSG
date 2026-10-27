module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedReduction

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup CFSG
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem nonabelian_of_centralizer_eq_bot {K : Type} [Group K] (S : Subgroup K)
    [IsSimpleGroup ↥S] (hcent : centralizer (S : Set K) = ⊥) :
    ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra hcon
  have hcom : ∀ a b : ↥S, a * b = b * a := by
    intro a b
    by_contra h
    exact hcon ⟨a, b, h⟩
  have hsub : ∀ s : ↥S, s = 1 := by
    intro s
    apply Subtype.ext
    have hs : (s : K) ∈ Subgroup.centralizer (S : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      simpa using congrArg Subtype.val (hcom ⟨k, hk⟩ s)
    rw [hcent, Subgroup.mem_bot] at hs
    simpa using hs
  obtain ⟨s, t, hst⟩ := exists_pair_ne ↥S
  exact hst ((hsub s).trans (hsub t).symm)

theorem z2_reduction {A : Type} [Group A] [IsSimpleGroup A] (hA : ∃ a b : A, a * b ≠ b * a)
    {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal] [IsSimpleGroup ↥S]
    (hcent : centralizer (S : Set K) = ⊥) {z : K} (hz : orderOf z = 2)
    (φ : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) :
    (∃ w : ↥S, orderOf w = 2 ∧
        Nonempty (↥(centralizer ({w} : Set ↥S)) ≃* Multiplicative (ZMod 2) × A)) ∨
      (∃ σ : MulAut ↥S, orderOf σ = 2 ∧ σ ∉ (MulAut.conj : ↥S →* MulAut ↥S).range ∧
        Nonempty (↥(fixedSubgroup σ) ≃* A)) := by
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := nonabelian_of_centralizer_eq_bot S hcent
  have hzC : z ∈ Subgroup.centralizer ({z} : Set K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let zC : Subgroup.centralizer ({z} : Set K) := ⟨z, hzC⟩
  have hz2 : z * z = 1 := by
    have h2 : z ^ orderOf z = 1 := pow_orderOf_eq_one z
    rw [hz, sq] at h2
    exact h2
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by decide)
  have hzC1 : zC ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hcen : ∀ g : Multiplicative (ZMod 2) × A, g * φ zC = φ zC * g := by
    intro g
    have h1 : φ.symm g * zC = zC * φ.symm g := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (φ.symm g).2
    simpa using congrArg φ h1
  have he2 : (φ zC).2 = 1 := by
    apply eq_one_of_central_of_simple hA
    intro b
    simpa using (congrArg Prod.snd (hcen ((1 : Multiplicative (ZMod 2)), b))).symm
  have he1 : φ zC ≠ 1 := fun h => hzC1 (φ.injective (h.trans φ.map_one.symm))
  have hy1 : (φ zC).1 ≠ 1 := fun h => he1 (Prod.ext h he2)
  have hZ2 : ∀ y y' : Multiplicative (ZMod 2), y ≠ 1 → y' ≠ 1 → y = y' := by decide
  have hyeq : ∀ y : Multiplicative (ZMod 2), y ≠ 1 → y = (φ zC).1 :=
    fun y hy => hZ2 y _ hy hy1
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (Subgroup.centralizer ({z} : Set K)),
      N = S.subgroupOf (Subgroup.centralizer ({z} : Set K)) := ⟨_, rfl⟩
  have hNn : N.Normal := by
    rw [hNdef]
    infer_instance
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup (Multiplicative (ZMod 2) × A), M = N.map φ.toMonoidHom :=
    ⟨_, rfl⟩
  have hMn : M.Normal := by
    rw [hMdef]
    exact hNn.map φ.toMonoidHom φ.surjective
  have hMmem : ∀ c : Subgroup.centralizer ({z} : Set K), φ c ∈ M ↔ (c : K) ∈ S := by
    intro c
    constructor
    · intro hc
      rw [hMdef] at hc
      obtain ⟨n, hn, hnc⟩ := Subgroup.mem_map.mp hc
      have hnc' : n = c := φ.injective hnc
      rw [hNdef] at hn
      rw [← hnc']
      exact Subgroup.mem_subgroupOf.mp hn
    · intro hc
      rw [hMdef]
      refine Subgroup.mem_map_of_mem φ.toMonoidHom ?_
      rw [hNdef]
      exact Subgroup.mem_subgroupOf.mpr hc
  by_cases hzS : z ∈ S
  ·
    left
    have hzSord : orderOf (⟨z, hzS⟩ : S) = 2 := (Subgroup.orderOf_coe _).symm.trans hz
    have heM : φ zC ∈ M := (hMmem zC).mpr hzS
    refine ⟨⟨z, hzS⟩, hzSord, ?_⟩
    rcases normal_prod_dichotomy hA M with hD | hD
    ·
      have hCS : ∀ c : Subgroup.centralizer ({z} : Set K), (c : K) ∈ S := by
        intro c
        rw [← hMmem c]
        by_cases hy : (φ c).1 = 1
        · have hx : φ c = ((1 : Multiplicative (ZMod 2)), (φ c).2) := Prod.ext hy rfl
          rw [hx]
          exact hD _
        · have hx : φ c = φ zC * ((1 : Multiplicative (ZMod 2)), (φ c).2) := by
            apply Prod.ext
            · show (φ c).1 = (φ zC).1 * 1
              rw [mul_one]
              exact hyeq _ hy
            · show (φ c).2 = (φ zC).2 * (φ c).2
              rw [he2, one_mul]
          rw [hx]
          exact M.mul_mem heM (hD _)
      have hCS' : Subgroup.centralizer ({z} : Set K) ≤ S := fun k hk => hCS ⟨k, hk⟩
      have hTC : (Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S)).map S.subtype =
          Subgroup.centralizer ({z} : Set K) := by
        rw [map_subtype_centralizer_singleton S hzS, inf_eq_right.mpr hCS']
      exact ⟨(Subgroup.equivMapOfInjective (Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S))
        S.subtype Subtype.val_injective).trans ((MulEquiv.subgroupCongr hTC).trans φ)⟩
    ·
      exfalso
      have hMz : M = Subgroup.zpowers (φ zC) := by
        apply le_antisymm
        · intro x hx
          by_cases hx1 : x.1 = 1
          · have hx' : x = 1 := Prod.ext hx1 (hD x hx)
            rw [hx']
            exact Subgroup.one_mem _
          · have hx' : x = φ zC := Prod.ext (hyeq _ hx1) (by rw [he2]; exact hD x hx)
            rw [hx']
            exact Subgroup.mem_zpowers _
        · exact Subgroup.zpowers_le.mpr heM
      have horder : orderOf (φ zC) = 2 :=
        (orderOf_injective φ.toMonoidHom φ.injective zC).trans
          ((Subgroup.orderOf_coe zC).symm.trans hz)
      have hcardM : Nat.card M = 2 := by
        rw [hMz, Nat.card_zpowers, horder]
      have hTN : (Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S)).map S.subtype =
          N.map (Subgroup.centralizer ({z} : Set K)).subtype := by
        rw [hNdef, map_subtype_centralizer_singleton S hzS, Subgroup.subgroupOf_map_subtype]
      have eT : Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S) ≃* M :=
        (Subgroup.equivMapOfInjective (Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S)) S.subtype
          Subtype.val_injective).trans
          ((MulEquiv.subgroupCongr hTN).trans
            ((Subgroup.equivMapOfInjective N (Subgroup.centralizer ({z} : Set K)).subtype
              Subtype.val_injective).symm.trans
              ((Subgroup.equivMapOfInjective N φ.toMonoidHom φ.injective).trans
                (MulEquiv.subgroupCongr hMdef.symm))))
      exact card_centralizer_involution_ne_two hSna hzSord
        ((Nat.card_congr eT.toEquiv).trans hcardM)
  ·
    right
    have heM : φ zC ∉ M := fun h => hzS ((hMmem zC).mp h)
    obtain ⟨σ, hσdef⟩ : ∃ σ : MulAut S, σ = MulAut.conjNormal (H := S) z := ⟨_, rfl⟩
    have hσσ : σ * σ = 1 := by
      rw [hσdef, ← map_mul, hz2, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h
      have hzcent : z ∈ Subgroup.centralizer (S : Set K) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have h1 : MulAut.conjNormal (H := S) z ⟨s, hs⟩ = ⟨s, hs⟩ := by
          rw [← hσdef, h]
          rfl
        have h2 : z * s * z⁻¹ = s := by
          have := congrArg Subtype.val h1
          rw [MulAut.conjNormal_apply] at this
          exact this
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      rw [hcent, Subgroup.mem_bot] at hzcent
      rw [hzcent, orderOf_one] at hz
      exact absurd hz (by decide)
    have hσ_ord : orderOf σ = 2 := by
      apply orderOf_eq_prime
      · rw [sq]
        exact hσσ
      · exact hσ1
    have hσ_out : σ ∉ (MulAut.conj : S →* MulAut S).range := by
      rintro ⟨s, hs⟩
      have hcom : (s : K)⁻¹ * z ∈ Subgroup.centralizer (S : Set K) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 : MulAut.conj s ⟨x, hx⟩ = MulAut.conjNormal (H := S) z ⟨x, hx⟩ := by
          rw [hs, hσdef]
        have h2 : (s : K) * x * (s : K)⁻¹ = z * x * z⁻¹ := congrArg Subtype.val h1
        have h3 : z * x = (s : K) * x * (s : K)⁻¹ * z := by
          rw [h2, inv_mul_cancel_right]
        calc x * ((s : K)⁻¹ * z) = (s : K)⁻¹ * ((s : K) * x * (s : K)⁻¹ * z) := by group
          _ = (s : K)⁻¹ * (z * x) := by rw [h3]
          _ = (s : K)⁻¹ * z * x := by group
      rw [hcent, Subgroup.mem_bot] at hcom
      have hzs : z = (s : K) := (inv_mul_eq_one.mp hcom).symm
      exact hzS (by rw [hzs]; exact s.2)
    have eqv : N ≃* fixedSubgroup σ := by
      rw [hNdef, hσdef]
      exact CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z
    refine ⟨σ, hσ_ord, hσ_out, ?_⟩
    rcases normal_prod_dichotomy hA M with hD | hD
    ·
      have hinj : Function.Injective (MonoidHom.inr (Multiplicative (ZMod 2)) A) :=
        fun a b h => congrArg Prod.snd h
      have hMr : M = (MonoidHom.inr (Multiplicative (ZMod 2)) A).range := by
        ext x
        constructor
        · intro hx
          rw [MonoidHom.mem_range]
          have hx1 : x.1 = 1 := by
            by_contra hne
            apply heM
            have hx' : φ zC = x * ((1 : Multiplicative (ZMod 2)), x.2⁻¹) := by
              apply Prod.ext
              · show (φ zC).1 = x.1 * 1
                rw [mul_one]
                exact (hyeq _ hne).symm
              · show (φ zC).2 = x.2 * x.2⁻¹
                rw [he2, mul_inv_cancel]
            rw [hx']
            exact M.mul_mem hx (hD _)
          exact ⟨x.2, Prod.ext hx1.symm rfl⟩
        · rintro ⟨a, rfl⟩
          exact hD a
      have isoA : A ≃* ↥(fixedSubgroup σ) :=
        (MonoidHom.ofInjective hinj).trans ((MulEquiv.subgroupCongr hMr.symm).trans
          ((MulEquiv.subgroupCongr hMdef).trans
            ((Subgroup.equivMapOfInjective N φ.toMonoidHom φ.injective).symm.trans eqv)))
      exact ⟨isoA.symm⟩
    ·
      exfalso
      have hbot : fixedSubgroup σ = ⊥ := by
        rw [eq_bot_iff]
        intro s hs
        rw [Subgroup.mem_bot]
        have hσs : MulAut.conjNormal (H := S) z s = s := by
          rw [← hσdef]
          exact hs
        have hsz : (s : K) * z = z * (s : K) := by
          have h1 := congrArg Subtype.val hσs
          rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul] at h1
          exact h1.symm
        have hc : (s : K) ∈ Subgroup.centralizer ({z} : Set K) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hsz
        obtain ⟨c0, hc0⟩ : ∃ c0 : Subgroup.centralizer ({z} : Set K), (c0 : K) = s :=
          ⟨⟨s, hc⟩, rfl⟩
        have hc0M : φ c0 ∈ M := (hMmem c0).mpr (by rw [hc0]; exact s.2)
        have h2 : (φ c0).2 = 1 := hD _ hc0M
        have h1 : (φ c0).1 = 1 := by
          by_contra hne
          apply heM
          have hEq : φ zC = φ c0 := Prod.ext (hyeq _ hne).symm (by rw [he2, h2])
          rw [hEq]
          exact hc0M
        have hφ1 : φ c0 = 1 := Prod.ext h1 h2
        have hc01 : c0 = 1 := φ.injective (hφ1.trans φ.map_one.symm)
        apply Subtype.ext
        rw [← hc0]
        exact congrArg Subtype.val hc01
      exact not_fixedSubgroup_eq_bot hSna hσσ hbot

end CFSG.EvenSporadicStandard.M24Std.KForm
