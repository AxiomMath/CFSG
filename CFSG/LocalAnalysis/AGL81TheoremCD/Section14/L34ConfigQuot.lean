module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigR
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.GL23TwoSub
import CFSG.RankThree.PartTwo.Sec12.Coordinates

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThree.Asc83Table
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {A T R : Subgroup G}

private lemma inf_pCoreOf_eq_bot (hA9 : Nat.card A = 9) :
    A ⊓ CFSG.Open.pCoreOf 2 (A ⊔ T) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 (CFSG.Open.pCoreOf 2 (A ⊔ T)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (A ⊔ T)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hA9, hk]
  simpa using Nat.Coprime.pow 2 k (by norm_num : Nat.Coprime 3 2)

private lemma card_sup_pCoreOf (hA9 : Nat.card A = 9) :
    Nat.card ↥(A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T)) =
      Nat.card A * Nat.card (CFSG.Open.pCoreOf 2 (A ⊔ T)) := by
  classical
  have hdisj : Disjoint A (CFSG.Open.pCoreOf 2 (A ⊔ T)) :=
    disjoint_iff.mpr (inf_pCoreOf_eq_bot (T := T) hA9)
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hmul : ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G) =
      (A : Set G) * (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A _ hAR
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : ↥A × ↥(CFSG.Open.pCoreOf 2 (A ⊔ T)) =>
      (⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ :
        ↥(A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T)))) ⟨?_, ?_⟩).symm
  · intro x y hxy
    have h : ((x.1 : G) * x.2) = ((y.1 : G) * y.2) := congrArg Subtype.val hxy
    exact Subgroup.mul_injective_of_disjoint hdisj h
  · intro y
    have hy' : (y : G) ∈ (A : Set G) * (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) := by
      rw [← hmul]
      exact y.2
    obtain ⟨a, ha, s, hs, has⟩ := hy'
    exact ⟨(⟨a, ha⟩, ⟨s, hs⟩), Subtype.ext has⟩

private lemma isSylowOf_three_sup_pCoreOf (hA9 : Nat.card A = 9) :
    CFSG.ABGLocalTools.IsSylowOf 3 A (A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRp : IsPGroup 2 (CFSG.Open.pCoreOf 2 (A ⊔ T)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (A ⊔ T)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
  have h3 : ¬ 3 ∣ 2 ^ k := by
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left ?_
  rw [card_sup_pCoreOf (T := T) hA9, hA9, hk,
    show (9 : ℕ) = 3 ^ 2 by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd h3, add_zero]

private lemma isSylowOf_conj_sup_pCoreOf (hA9 : Nat.card A = 9)
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G)) {t : G} (ht : t ∈ T) :
    CFSG.ABGLocalTools.IsSylowOf 3 (A.map (MulAut.conj t).toMonoidHom)
      (A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A
      (A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T)) := isSylowOf_three_sup_pCoreOf (T := T) hA9
  have hAtle : A.map (MulAut.conj t).toMonoidHom ≤ A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    simpa using (Subgroup.mem_normalizer_iff.mp (hTAR ht) a).mp (Subgroup.mem_sup_left ha)
  refine CFSG.ABGLocalTools.isSylowOf_of_card hAtle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hAsyl.card_eq]

private lemma mem_normalizer_of_conj_eq {t : G}
    {r : G} (hrconj : ∀ x : G,
      x ∈ A.map (MulAut.conj t).toMonoidHom ↔ r⁻¹ * x * r ∈ A) :
    r⁻¹ * t ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 : t * a * t⁻¹ ∈ A.map (MulAut.conj t).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h2 := (hrconj (t * a * t⁻¹)).mp h1
    rwa [show r⁻¹ * (t * a * t⁻¹) * r = (r⁻¹ * t) * a * (r⁻¹ * t)⁻¹ by group] at h2
  · intro ha
    have h1 : r⁻¹ * (t * a * t⁻¹) * r ∈ A := by
      rwa [show r⁻¹ * (t * a * t⁻¹) * r = (r⁻¹ * t) * a * (r⁻¹ * t)⁻¹ by group]
    have h2 : t * a * t⁻¹ ∈ A.map (MulAut.conj t).toMonoidHom := (hrconj _).mpr h1
    obtain ⟨a', ha', hconj⟩ := h2
    change (MulAut.conj t) a' = t * a * t⁻¹ at hconj
    rw [MulAut.conj_apply] at hconj
    have h3 : a = a' := by
      have := congrArg (fun x => t⁻¹ * x * t) hconj
      simpa [mul_assoc] using this.symm
    rwa [h3]

private lemma eq_mul_of_mem_normalizer (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T)
    {t r : G} (htT : t ∈ T) (hrAR : r ∈ A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T))
    (hy : r⁻¹ * t ∈ Subgroup.normalizer (A : Set G)) :
    ∃ n ∈ T ⊓ Subgroup.normalizer (A : Set G),
      ∃ s ∈ CFSG.Open.pCoreOf 2 (A ⊔ T), t = n * s := by
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hr_mul : r ∈ (A : Set G) * (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A _ hAR]
    exact hrAR
  obtain ⟨a, ha, s, hs, hrs⟩ := hr_mul
  have hleART : A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ A ⊔ T :=
    sup_le le_sup_left (hRT.trans le_sup_right)
  have hyAT : r⁻¹ * t ∈ A ⊔ T :=
    (A ⊔ T).mul_mem ((A ⊔ T).inv_mem (hleART hrAR)) (Subgroup.mem_sup_right htT)
  have hRnorm : A ⊔ T ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T)
  have hs' : (r⁻¹ * t)⁻¹ * s * (r⁻¹ * t) ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hRnorm ((A ⊔ T).inv_mem hyAT)) s).mp hs
  have ht1 : t = r * (r⁻¹ * t) := by group
  have ht2 : r * (r⁻¹ * t) = (a * (r⁻¹ * t)) * ((r⁻¹ * t)⁻¹ * s * (r⁻¹ * t)) := by
    rw [← hrs]
    group
  have ht_eq : t = (a * (r⁻¹ * t)) * ((r⁻¹ * t)⁻¹ * s * (r⁻¹ * t)) := ht1.trans ht2
  have hnT : a * (r⁻¹ * t) ∈ T := by
    have h1 : a * (r⁻¹ * t) = t * ((r⁻¹ * t)⁻¹ * s * (r⁻¹ * t))⁻¹ := by
      calc a * (r⁻¹ * t)
          = ((a * (r⁻¹ * t)) * ((r⁻¹ * t)⁻¹ * s * (r⁻¹ * t))) *
              ((r⁻¹ * t)⁻¹ * s * (r⁻¹ * t))⁻¹ := by group
        _ = t * ((r⁻¹ * t)⁻¹ * s * (r⁻¹ * t))⁻¹ := by rw [← ht_eq]
    rw [h1]
    exact T.mul_mem htT (T.inv_mem (hRT hs'))
  have hna : a * (r⁻¹ * t) ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).mul_mem (Subgroup.le_normalizer ha) hy
  exact ⟨a * (r⁻¹ * t), ⟨hnT, hna⟩, (r⁻¹ * t)⁻¹ * s * (r⁻¹ * t), hs', ht_eq⟩

private lemma le_mul_normalizer_pCoreOf (hA9 : Nat.card A = 9)
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T)
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G)) :
    ∀ t ∈ T, ∃ n ∈ T ⊓ Subgroup.normalizer (A : Set G),
      ∃ s ∈ CFSG.Open.pCoreOf 2 (A ⊔ T), t = n * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro t htT
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A
      (A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T)) := isSylowOf_three_sup_pCoreOf (T := T) hA9
  have hAtsyl := isSylowOf_conj_sup_pCoreOf (T := T) hA9 hTAR htT
  obtain ⟨r, hrAR, hrconj⟩ := hAsyl.exists_mem_conj hAtsyl
  exact eq_mul_of_mem_normalizer (T := T) hRT htT hrAR
    (mem_normalizer_of_conj_eq hrconj)

open CFSG.RankThree.PartTwo.Sec4 (autIn)

private noncomputable def rhoNT (f : Multiplicative (Fin 2 → ZMod 3) ≃* A) :
    ↥(T ⊓ Subgroup.normalizer (A : Set G)) →* GL23 :=
  (rho f).comp (Subgroup.inclusion inf_le_right)

private lemma ker_rhoNT (f : Multiplicative (Fin 2 → ZMod 3) ≃* A) :
    (rhoNT (T := T) f).ker =
      (T ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
        (T ⊓ Subgroup.normalizer (A : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, rhoNT, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_rho,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨x.2.1, by simpa using h⟩
  · rintro ⟨-, h⟩
    simpa using h

private lemma ker_quot_mk_inclusion [hN : (R.subgroupOf T).Normal] :
    ((QuotientGroup.mk' (R.subgroupOf T)).comp
        (Subgroup.inclusion (inf_le_left :
          T ⊓ Subgroup.normalizer (A : Set G) ≤ T))).ker =
      (R ⊓ (T ⊓ Subgroup.normalizer (A : Set G))).subgroupOf
        (T ⊓ Subgroup.normalizer (A : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientGroup.ker_mk',
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro h
    exact ⟨by simpa using h, x.2⟩
  · rintro ⟨h, -⟩
    simpa using h

private noncomputable def rangeEquivOfKerEq {G₁ G₂ G₃ : Type*}
    [Group G₁] [Group G₂] [Group G₃] (φ : G₁ →* G₂) (ψ : G₁ →* G₃) (h : φ.ker = ψ.ker) :
    ↥φ.range ≃* ↥ψ.range :=
  (QuotientGroup.quotientKerEquivRange φ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange ψ))

private lemma inf_normalizer_pCoreOf_eq (hA9 : Nat.card A = 9)
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T)
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G))
    (hTp : IsPGroup 2 T) :
    CFSG.Open.pCoreOf 2 (A ⊔ T) ⊓ (T ⊓ Subgroup.normalizer (A : Set G)) =
      T ⊓ Subgroup.centralizer (A : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxR, hxT, hxN⟩
    refine ⟨hxT, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have hcommA : x * a * x⁻¹ * a⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN a).mp ha) (A.inv_mem ha)
    have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
      (le_sup_left : A ≤ A ⊔ T).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
    have hcommR : x * a * x⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
      have h2 : a * x * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) :=
        (Subgroup.mem_normalizer_iff.mp (hAR ha) x).mp hxR
      have h3 : a * x⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
        have := (CFSG.Open.pCoreOf 2 (A ⊔ T)).inv_mem h2
        simpa [mul_assoc] using this
      have := (CFSG.Open.pCoreOf 2 (A ⊔ T)).mul_mem hxR h3
      simpa [mul_assoc] using this
    have hbot : x * a * x⁻¹ * a⁻¹ = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hcommA, hcommR⟩
      rwa [inf_pCoreOf_eq_bot (T := T) hA9, Subgroup.mem_bot] at this
    calc a * x = (x * a * x⁻¹ * a⁻¹) * (a * x) := by rw [hbot, one_mul]
      _ = x * a := by group
  · rintro ⟨hxT, hxC⟩
    have hxR : x ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
      refine mem_pCoreOf_sup_of_forall_commutator_mem (A := A) (T := T) hTp hRT hTAR hxT ?_
      intro a ha
      have h1 : a * x = x * a := (Subgroup.mem_centralizer_iff.mp hxC) a ha
      have h2 : x * a * x⁻¹ * a⁻¹ = 1 := by
        calc x * a * x⁻¹ * a⁻¹ = a * x * x⁻¹ * a⁻¹ := by rw [h1]
          _ = 1 := by simp
      rw [h2]
      exact Subgroup.one_mem _
    exact ⟨hxR, hxT, Subgroup.centralizer_le_normalizer (A : Set G) hxC⟩

private lemma range_quot_mk_inclusion_eq_top (hA9 : Nat.card A = 9)
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T)
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G))
    [hN : ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T).Normal] :
    ((QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T)).comp
        (Subgroup.inclusion (inf_le_left :
          T ⊓ Subgroup.normalizer (A : Set G) ≤ T))).range = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨n, hnNT, s, hsR, ht_eq⟩ := le_mul_normalizer_pCoreOf (T := T) hA9 hRT hTAR t t.2
  refine ⟨⟨n, hnNT⟩, ?_⟩
  have h2 : (t : ↥T) = ⟨n, hnNT.1⟩ * ⟨s, hRT hsR⟩ := Subtype.ext ht_eq
  change QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T) ⟨n, hnNT.1⟩ =
    QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T) t
  rw [h2]
  change QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T) ⟨n, hnNT.1⟩ =
    QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T) (⟨n, hnNT.1⟩ * ⟨s, hRT hsR⟩)
  rw [map_mul]
  have hs1 : QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T)
      (⟨s, hRT hsR⟩ : ↥T) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    exact hsR
  rw [hs1, mul_one]

private lemma nonempty_quotEquiv_rhoNT (hA9 : Nat.card A = 9)
    (hTp : IsPGroup 2 T)
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T)
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G))
    (f : Multiplicative (Fin 2 → ZMod 3) ≃* A) :
    ∃ _ : ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T).Normal,
      Nonempty (↥T ⧸ (CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T ≃*
        (rhoNT (T := T) f).range) := by
  have hN : ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRT).mpr
      ((le_sup_right : T ≤ A ⊔ T).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T)))
  haveI : ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T).Normal := hN
  refine ⟨hN, ?_⟩
  have hφtop := range_quot_mk_inclusion_eq_top (T := T) (A := A) hA9 hRT hTAR
  have hker : ((QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 (A ⊔ T)).subgroupOf T)).comp
      (Subgroup.inclusion (inf_le_left :
        T ⊓ Subgroup.normalizer (A : Set G) ≤ T))).ker = (rhoNT (T := T) f).ker := by
    rw [ker_quot_mk_inclusion (T := T) (A := A) (R := CFSG.Open.pCoreOf 2 (A ⊔ T)),
      ker_rhoNT (T := T) (A := A) f, inf_normalizer_pCoreOf_eq (T := T) (A := A) hA9 hRT hTAR hTp]
  exact ⟨(Subgroup.topEquiv.symm).trans
    ((MulEquiv.subgroupCongr hφtop).symm.trans (rangeEquivOfKerEq _ _ hker))⟩

variable {M E H : Subgroup G}

private lemma nonempty_range_rhoNT_comp_quaternion (h : HypCGen G M 3 A H)
    (hC3 : CaseThree M H) (hAK : A ≤ kSub 3 M H) {W T : Subgroup G} (hWT : W ≤ T)
    {hWNT : W ≤ T ⊓ Subgroup.normalizer (A : Set G)}
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W
      (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H))
    (f : Multiplicative (Fin 2 → ZMod 3) ≃* A) :
    Nonempty (↥((rhoNT (T := T) f).comp (Subgroup.inclusion hWNT)).range ≃*
      QuaternionGroup 2) := by
  have hWN : W ≤ Subgroup.normalizer (A : Set G) := hW.le.trans inf_le_left
  let θ : ↥W →* MulAut ↥A :=
    A.normalizerMonoidHom.comp (Subgroup.inclusion hWN)
  have hψx : ∀ x : ↥W,
      ((rhoNT (T := T) f).comp (Subgroup.inclusion hWNT)) x = 1 ↔
        (x : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro x
    rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_rhoNT, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · rintro ⟨-, h⟩
      simpa using h
    · intro h
      exact ⟨(Subgroup.inclusion hWNT x).2.1, by simpa using h⟩
  have hθx : ∀ x : ↥W, θ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro x
    change (A.normalizerMonoidHom.comp (Subgroup.inclusion hWN)) x = 1 ↔
      (x : G) ∈ Subgroup.centralizer (A : Set G)
    rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.mem_subgroupOf]
    rfl
  have hker : ((rhoNT (T := T) f).comp (Subgroup.inclusion hWNT)).ker = θ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (hψx x).trans (hθx x).symm
  have hθrange : θ.range = autIn W A := by
    change (A.normalizerMonoidHom.comp (Subgroup.inclusion hWN)).range = autIn W A
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    simp only [autIn, inf_eq_left.mpr hWN]
  obtain ⟨e⟩ := HypCGen.nonempty_autIn_sylowTwo h hC3 (HypCGen.isSylowOf_three_E h hC3 hAK) hW
  exact ⟨(rangeEquivOfKerEq _ _ hker).trans ((MulEquiv.subgroupCongr hθrange).trans e)⟩

theorem HypCGen.l34Config_quotient
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {W T : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) (hWT : W ≤ T) :
    CFSG.LocalAnalysis.RankThreeUC.S15.QuotEquiv T (CFSG.Open.pCoreOf 2 (A ⊔ T))
        (QuaternionGroup 2) ∨
      CFSG.LocalAnalysis.RankThreeUC.S15.QuotEquiv T (CFSG.Open.pCoreOf 2 (A ⊔ T))
        (CFSG.Open.SemidihedralGroup 4) := by
  classical
  have hA9 : Nat.card A = 9 := by rw [h.card]; norm_num
  have hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T := h.pCoreOf_sup_le_of_isSylowOf h.E_le_H hT
  have hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G) :=
    h.sylowTwo_le_normalizer_sup_pCoreOf hC3 hTwo hK hL hAK hNA hT
  obtain ⟨f⟩ := CFSG.RankThree.PartTwo.Sec12.exists_coords (A := A) h.elem (n := 2) h.card
  obtain ⟨hN, ⟨eTR⟩⟩ := nonempty_quotEquiv_rhoNT (T := T) (A := A) hA9 hT.isPGroup hRT hTAR f
  have hWN : W ≤ Subgroup.normalizer (A : Set G) := hW.le.trans inf_le_left
  have hWNT : W ≤ T ⊓ Subgroup.normalizer (A : Set G) := le_inf hWT hWN
  have hQP : ((rhoNT (T := T) f).comp (Subgroup.inclusion hWNT)).range ≤
      (rhoNT (T := T) f).range := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion hWNT x, rfl⟩
  have hNTp : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (A : Set G)) := hT.isPGroup.to_le inf_le_left
  have hP : IsPGroup 2 (rhoNT (T := T) f).range := by
    rw [MonoidHom.range_eq_map]
    exact (hNTp.of_equiv Subgroup.topEquiv.symm).map (rhoNT (T := T) f)
  have hQ : Nonempty (↥((rhoNT (T := T) f).comp (Subgroup.inclusion hWNT)).range ≃*
      QuaternionGroup 2) :=
    nonempty_range_rhoNT_comp_quaternion (T := T) h hC3 hAK hWT hW f
  rcases gl23_two_subgroup_quaternion_or_semidihedral hP hQP hQ with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨hN, ⟨eTR.trans e⟩⟩
  · obtain ⟨e⟩ := he
    exact Or.inr ⟨hN, ⟨eTR.trans e⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
