module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonCatZ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveLemma
public import CFSG.GH74.GLS.LU.Local.GenCore
public import CFSG.Holt.FoundationsFusion
public import CFSG.CharacterTheory.Semidihedral.OddCentralizerSylowTwo

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus (aut_inv_of_fixed_point_free commute_of_aut_inv)

@[expose] def NoInnerZ2 (A : Type) [Group A] : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) → Catalog S →
    ∀ z : S, orderOf z = 2 →
      ¬ Nonempty (↥(Subgroup.centralizer ({z} : Set S)) ≃* Multiplicative (ZMod 2) × A)

@[expose] def NoOuterFixed (A : Type) [Group A] : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) → Catalog S →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
      ¬ Nonempty (↥(fixedSubgroup σ) ≃* A)

theorem eq_one_of_central_of_simple {A : Type} [Group A] [IsSimpleGroup A]
    (hna : ∃ a b : A, a * b ≠ b * a) {u : A} (h : ∀ b : A, u * b = b * u) : u = 1 := by
  have hu : u ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr (fun g => (h g).symm)
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center A) with hc | hc
  · rw [hc, Subgroup.mem_bot] at hu
    exact hu
  · exfalso
    obtain ⟨p, q, hpq⟩ := hna
    have hp : p ∈ Subgroup.center A := by
      rw [hc]
      exact Subgroup.mem_top p
    exact hpq (Subgroup.mem_center_iff.mp hp q).symm

theorem normal_prod_dichotomy {A : Type} [Group A] [IsSimpleGroup A]
    (hna : ∃ a b : A, a * b ≠ b * a) (N : Subgroup (Multiplicative (ZMod 2) × A)) [N.Normal] :
    (∀ a : A, ((1 : Multiplicative (ZMod 2)), a) ∈ N) ∨ (∀ x ∈ N, x.2 = 1) := by
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup A, M = N.comap (MonoidHom.inr (Multiplicative (ZMod 2)) A) :=
    ⟨_, rfl⟩
  have hMn : M.Normal := by
    rw [hMdef]
    exact Subgroup.Normal.comap inferInstance _
  have hmem : ∀ a : A, a ∈ M ↔ ((1 : Multiplicative (ZMod 2)), a) ∈ N := by
    intro a
    rw [hMdef]
    exact Iff.rfl
  rcases Subgroup.Normal.eq_bot_or_eq_top M with h | h
  · right
    rintro ⟨y, a⟩ hx
    show a = 1
    apply eq_one_of_central_of_simple hna
    intro b
    have hg := Subgroup.Normal.conj_mem ‹N.Normal› _ hx ((1 : Multiplicative (ZMod 2)), b)
    have hprod := N.mul_mem (N.inv_mem hx) hg
    have hone : ∀ t : Multiplicative (ZMod 2),
        t⁻¹ * (1 * t * (1 : Multiplicative (ZMod 2))⁻¹) = 1 := by decide
    have hcal : ((y, a) : Multiplicative (ZMod 2) × A)⁻¹ *
        (((1 : Multiplicative (ZMod 2)), b) * (y, a) * ((1 : Multiplicative (ZMod 2)), b)⁻¹) =
          ((1 : Multiplicative (ZMod 2)), a⁻¹ * (b * a * b⁻¹)) := by
      apply Prod.ext
      · exact hone y
      · rfl
    have hprod' : ((1 : Multiplicative (ZMod 2)), a⁻¹ * (b * a * b⁻¹)) ∈ N := by
      rw [← hcal]
      exact hprod
    have hM1 : a⁻¹ * (b * a * b⁻¹) ∈ M := (hmem _).mpr hprod'
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hM1
    exact eq_mul_inv_iff_mul_eq.mp hM1
  · left
    intro a
    exact (hmem a).mp (by rw [h]; exact Subgroup.mem_top a)

theorem map_subtype_centralizer_singleton {K : Type} [Group K] (S : Subgroup K) {z : K}
    (hzS : z ∈ S) :
    (Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S)).map S.subtype =
      S ⊓ Subgroup.centralizer ({z} : Set K) := by
  ext k
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : t * (⟨z, hzS⟩ : S) = (⟨z, hzS⟩ : S) * t :=
      Subgroup.mem_centralizer_singleton_iff.mp ht
    refine Subgroup.mem_inf.mpr ⟨t.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg Subtype.val ht'
  · intro hk
    obtain ⟨hkS, hkC⟩ := Subgroup.mem_inf.mp hk
    refine ⟨⟨k, hkS⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hkC

theorem card_centralizer_involution_ne_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {z : S} (hz : orderOf z = 2) :
    Nat.card (Subgroup.centralizer ({z} : Set S)) ≠ 2 := by
  intro h2
  have hC : ∀ P : Sylow 2 (Subgroup.centralizer ({z} : Set S)), Nat.card P = 2 := by
    intro P
    rw [Sylow.card_eq_multiplicity, h2, Nat.Prime.factorization_self Nat.prime_two, pow_one]
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 S))
  have hP := CFSG.Semidihedral.OddCentralizerSylowTwo.all_sylow_two_card_eq_two z hz hC P
  rw [Sylow.card_eq_multiplicity] at hP
  have hD : (Nat.card S).factorization 2 = 1 := by
    apply Nat.pow_right_injective (le_refl 2)
    simpa using hP
  obtain ⟨O, -, hOi⟩ := CFSG.GH74.GLS.LU.Local.exists_index_two_of_card_two_sylow hD
  exact CFSG.Holt.subgroup_index_ne_two_of_isSimpleGroup hna O hOi

theorem not_fixedSubgroup_eq_bot {S : Type} [Group S] [Finite S]
    (hna : ∃ a b : S, a * b ≠ b * a) {σ : MulAut S} (hσ : σ * σ = 1)
    (h : fixedSubgroup σ = ⊥) : False := by
  have hfix : ∀ n ∈ (⊤ : Subgroup S), σ n = n → n = 1 := by
    intro n _ hn
    have hmem : n ∈ fixedSubgroup σ := hn
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hinv := aut_inv_of_fixed_point_free σ ⊤ (fun n _ => Subgroup.mem_top _) hσ hfix
  obtain ⟨a, b, hab⟩ := hna
  exact hab (commute_of_aut_inv hinv a (Subgroup.mem_top a) b (Subgroup.mem_top b))

theorem catNoAlmostSimpleZ2_of_noInner_noOuter {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hA : ∃ a b : A, a * b ≠ b * a) (hin : NoInnerZ2 A) (hout : NoOuterFixed A) :
    CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 A := by
  intro K _ _ S hSn hSs hcat hcent z hz hne
  obtain ⟨φ⟩ := hne
  have hSna : ∃ a b : S, a * b ≠ b * a := by
    by_contra hcon
    push_neg at hcon
    have hsub : ∀ s : S, s = 1 := by
      intro s
      apply Subtype.ext
      have hs : (s : K) ∈ Subgroup.centralizer (S : Set K) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        simpa using congrArg Subtype.val (hcon ⟨k, hk⟩ s)
      rw [hcent, Subgroup.mem_bot] at hs
      simpa using hs
    obtain ⟨s, t, hst⟩ := exists_pair_ne S
    exact hst ((hsub s).trans (hsub t).symm)
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
    have hzSord : orderOf (⟨z, hzS⟩ : S) = 2 := (Subgroup.orderOf_coe _).symm.trans hz
    have heM : φ zC ∈ M := (hMmem zC).mpr hzS
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
      exact hin ↥S hSna hcat (⟨z, hzS⟩ : S) hzSord
        ⟨(Subgroup.equivMapOfInjective (Subgroup.centralizer ({(⟨z, hzS⟩ : S)} : Set S)) S.subtype
          Subtype.val_injective).trans ((MulEquiv.subgroupCongr hTC).trans φ)⟩
    ·
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
      exact hout ↥S hSna hcat σ hσ_ord hσ_out ⟨isoA.symm⟩
    ·
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

end CFSG.ComponentClassification.CatFC
