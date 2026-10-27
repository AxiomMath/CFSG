module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGFam
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentA

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.CatFactsL4U4.AltCent

section Involution

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_support_eq_two_mul_of_sq_eq_one {σ : Perm α} (h2 : σ ^ 2 = 1) :
    σ.support.card = 2 * σ.cycleFactorsFinset.card := by
  rw [← sum_cycleType, cycleType_of_pow_prime_eq_one h2, Multiset.sum_replicate, smul_eq_mul,
    mul_comm, cycleType_def, Multiset.card_map]
  rfl

theorem card_support_eq_two_of_mem_cycleFactorsFinset {σ : Perm α} (h2 : σ ^ 2 = 1) {c : Perm α}
    (hc : c ∈ σ.cycleFactorsFinset) : c.support.card = 2 :=
  pow_prime_eq_one_iff.mp h2 _ (by rw [cycleType_def]; exact Multiset.mem_map_of_mem _ hc)

theorem four_dvd_card_support_of_sq_eq_one {σ : Perm α} (h2 : σ ^ 2 = 1) (hs : sign σ = 1) :
    4 ∣ σ.support.card := by
  have hct := cycleType_of_pow_prime_eq_one h2
  have h := hs
  rw [sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    pow_add, pow_mul, Int.units_pow_two, one_mul, neg_one_pow_eq_one_iff_even (by decide)] at h
  rw [← sum_cycleType, hct, Multiset.sum_replicate, smul_eq_mul]
  obtain ⟨r, hr⟩ := h
  omega

theorem not_isSolvable_centralizer_of_sq_eq_one {σ : Perm α} (h2 : σ ^ 2 = 1)
    (h10 : 10 ≤ σ.support.card) : ¬ Group.IsSolvable ↥(centralizer ({σ} : Set (Perm α))) := by
  intro hs
  have hsurj : Function.Surjective (OnCycleFactors.toPermHom σ) := fun τ =>
    MonoidHom.mem_range.mp (OnCycleFactors.mem_range_toPermHom_iff.mpr fun c => by
      rw [card_support_eq_two_of_mem_cycleFactorsFinset h2 (τ c).2,
        card_support_eq_two_of_mem_cycleFactorsFinset h2 c.2])
  have hP := Group.isSolvable_of_surjective hsurj
  have h5 : 5 ≤ σ.cycleFactorsFinset.card := by
    have := card_support_eq_two_mul_of_sq_eq_one h2
    omega
  refine Equiv.Perm.not_isSolvable σ.cycleFactorsFinset ?_ hP
  rw [Cardinal.mk_fintype, Fintype.card_coe]
  exact_mod_cast h5

end Involution

section Alternating

variable {X : Type} [Group X] {n : ℕ}

theorem isSolvable_centralizer_perm_of_range_eq (ι : X →* Perm (Fin n))
    (hι : Function.Injective ι) (hrange : ι.range = alternatingGroup (Fin n)) (x : X)
    (hs : Group.IsSolvable ↥(centralizer ({x} : Set X))) :
    Group.IsSolvable ↥(centralizer ({ι x} : Set (Perm (Fin n)))) := by
  set H := centralizer ({ι x} : Set (Perm (Fin n))) with hH
  let f : ↥(centralizer ({x} : Set X)) →* ↥H :=
    (ι.comp (centralizer ({x} : Set X)).subtype).codRestrict H fun c => by
      rw [MonoidHom.comp_apply, hH, mem_centralizer_singleton_iff, coe_subtype, ← map_mul,
        ← map_mul, mem_centralizer_singleton_iff.mp c.2]
  let g : ↥H →* ℤˣ := sign.comp H.subtype
  have : Group.IsSolvable ℤˣ := Group.isSolvable_of_comm mul_comm
  refine Group.isSolvable_of_ker_le_range f g fun y hy => ?_
  have hyA : (y : Perm (Fin n)) ∈ ι.range := by
    rw [hrange, mem_alternatingGroup]
    exact MonoidHom.mem_ker.mp hy
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hyA
  have hwC : w ∈ centralizer ({x} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul, hw]
    exact mem_centralizer_singleton_iff.mp y.2
  exact MonoidHom.mem_range.mpr ⟨⟨w, hwC⟩, Subtype.ext hw⟩

theorem map_eq_altOff_of_isTwoComponentAt (ι : X →* Perm (Fin n)) (hι : Function.Injective ι)
    (hrange : ι.range = alternatingGroup (Fin n)) {z : X} {K : Subgroup X}
    (hK : IsTwoComponentAt z K) :
    5 ≤ n - (ι z).support.card ∧ K.map ι = altOff (ι z).support := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hz2, hKC, hKp⟩ := hK
  set τ := ι z with hτdef
  have hτ2 : orderOf τ = 2 := by rw [hτdef, orderOf_injective ι hι, hz2]
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin n))) with hNdef
  set C := centralizer ({z} : Set X) with hCdef
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute τ g from hg) k).eq)
  have hιC : ∀ c : C, τ * ι c = ι c * τ := fun c => by
    rw [hτdef, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp c.2]
  let ιC : C →* N := (ι.comp C.subtype).codRestrict N fun c => hcN _ (hιC c)
  have hιC_inj : Function.Injective ιC := fun x y hxy =>
    Subtype.ext (hι (congrArg (fun w : N => (w : Perm (Fin n))) hxy))
  set R : Subgroup N := (alternatingGroup (Fin n)).subgroupOf N with hRdef
  have hrangeC : ιC.range = R := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      change ι c ∈ alternatingGroup (Fin n)
      rw [← hrange]
      exact ⟨c, rfl⟩
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ := by
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      rw [← hrange] at hyA
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hyA
      have hwC : w ∈ C := by
        rw [hCdef, mem_centralizer_singleton_iff]
        apply hι
        rw [map_mul, map_mul, hw, ← hτdef]
        exact hcomm.symm
      exact MonoidHom.mem_range.mpr ⟨⟨w, hwC⟩, Subtype.ext hw⟩
  let e₁ : C ≃* R := (MonoidHom.ofInjective hιC_inj).trans (MulEquiv.subgroupCongr hrangeC)
  have hL₁ : IsPComponent 2 ((K.subgroupOf C).map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hKp
  have hL := CatalogueBAlternating.pComponent_of_normal_subgroup 2 R _ hL₁
  obtain ⟨hdeg, hLeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ _ hL
  have hmapL : (((K.subgroupOf C).map e₁.toMonoidHom).map R.subtype).map N.subtype =
      K.map ι := by
    rw [Subgroup.map_map, Subgroup.map_map]
    have hcomp : (N.subtype.comp R.subtype).comp e₁.toMonoidHom = ι.comp C.subtype :=
      MonoidHom.ext fun c => rfl
    rw [hcomp, ← Subgroup.map_map, map_subgroupOf_eq_of_le hKC]
  have hfix : ∀ a, a ∈ MulAction.fixedPoints Q (Fin n) ↔ a ∉ τ.support := by
    intro a
    rw [MulAction.mem_fixedPoints, Perm.notMem_support]
    constructor
    · intro h
      exact h ⟨τ, mem_zpowers τ⟩
    · rintro h ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self_of_apply_eq_self h k
  have hcardFix : Nat.card (MulAction.fixedPoints Q (Fin n)) = n - τ.support.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), Nat.card_eq_fintype_card, card_compl]
  have h5 : 5 ≤ n - τ.support.card := hcardFix ▸ hdeg
  have hle : K.map ι ≤ altOff τ.support := by
    intro y hy
    have hyA : y ∈ alternatingGroup (Fin n) := by
      rw [← hrange]
      exact map_le_range ι K hy
    rw [← hmapL, hLeq, Subgroup.map_map] at hy
    obtain ⟨f, -, rfl⟩ := hy
    refine mem_altOff (fun a ha => ?_) (mem_alternatingGroup.mp hyA)
    change (CatalogueBAlternating.fixedPointsNormalizerHom Q f : Perm (Fin n)) a = a
    rw [CatalogueBAlternating.fixedPointsNormalizerHom_coe]
    exact ofSubtype_apply_of_not_mem f fun h => (hfix a).mp h ha
  have hcard : Nat.card (altOff τ.support) ≤ Nat.card (K.map ι) := by
    have : Nontrivial (MulAction.fixedPoints Q (Fin n)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    rw [card_altOff _ (by omega), ← hmapL, hLeq, card_map_of_injective N.subtype_injective,
      card_map_of_injective (CatalogueBAlternating.fixedPointsNormalizerHom_injective Q),
      nat_card_alternatingGroup, hcardFix]
  exact ⟨h5, eq_of_le_of_card_ge hle hcard⟩

theorem eight_le_card_support_of_eight_dvd {m : ℕ} {τ : Perm (Fin m)} (hτ2 : τ ^ 2 = 1)
    (hτs : sign τ = 1) (hτ1 : τ ≠ 1) {D : Subgroup (Perm (Fin m))}
    (hDτ : ∀ x ∈ D, x * τ = τ * x) (hDfix : ∀ x ∈ D, ∀ a ∉ τ.support, x a = a)
    (hDs : ∀ x ∈ D, sign x = 1) (h8 : 8 ∣ Nat.card D) : 8 ≤ τ.support.card := by
  have h4 := four_dvd_card_support_of_sq_eq_one hτ2 hτs
  have hpos : τ.support.card ≠ 0 := fun h =>
    hτ1 (support_eq_empty_iff.mp (Finset.card_eq_zero.mp h))
  by_contra hlt
  have h4' : τ.support.card = 4 := by omega
  let r : ↥D →* alternatingGroup {a // a ∈ τ.support} :=
    { toFun := fun x => ⟨(x : Perm (Fin m)).subtypePerm (mem_support_iff_of_comm (hDτ x x.2)), by
        have h := sign_subtypePerm (x : Perm (Fin m)) (mem_support_iff_of_comm (hDτ x x.2))
          (fun a ha => by_contra fun h => ha (hDfix x x.2 a h))
        rw [hDs x x.2] at h
        rw [mem_alternatingGroup]
        convert h⟩
      map_one' := by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hr : Function.Injective r := by
    intro x y hxy
    refine Subtype.ext (Equiv.ext fun a => ?_)
    by_cases ha : a ∈ τ.support
    · exact congrArg (fun f : alternatingGroup {a // a ∈ τ.support} =>
        ((f : Perm {a // a ∈ τ.support}) ⟨a, ha⟩ : Fin m)) hxy
    · rw [hDfix x x.2 a ha, hDfix y y.2 a ha]
  have hdvd := card_dvd_of_injective r hr
  have : Nontrivial {a // a ∈ τ.support} :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [Nat.card_eq_finsetCard]; omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_finsetCard, h4'] at hdvd
  exact absurd (dvd_trans h8 hdvd) (by decide)

theorem endKnownGroupsInputOn_alternating : EndKnownGroupsInputOn fun X _ =>
    ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n)) := by
  intro X _ _ _ hX z t K P D hK _ hKs _ _ hP htP ht hzt _ hD _ hDd hD8 _ _
  obtain ⟨n, -, ⟨e⟩⟩ := hX
  set ι : X →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιA : ∀ x : X, ι x ∈ alternatingGroup (Fin n) := fun x => (e x).2
  have hrange : ι.range = alternatingGroup (Fin n) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hιA x
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      change ((e (e.symm ⟨y, hy⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) = y
      rw [MulEquiv.apply_symm_apply]
  have hzo : orderOf z = 2 := hK.1
  obtain ⟨h5, hKeq⟩ := map_eq_altOff_of_isTwoComponentAt ι hι hrange hK
  set τ := ι z with hτdef
  have : IsSimpleGroup (altOff τ.support) := isSimpleGroup_altOff _ h5
  have : IsSimpleGroup K :=
    ((K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hKeq)).isSimpleGroup
  have hOK : pPrimeCore 2 K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 K) with h | h
    · exact h
    · exfalso
      have : IsSimpleGroup (K ⧸ pPrimeCore 2 K) := hKs
      obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ pPrimeCore 2 K)
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.mpr (by rw [h]; exact mem_top _))
  have hDK : ∀ d ∈ D, ∀ k ∈ K, d * k = k * d := by
    intro d hd k hk
    obtain ⟨-, hdK⟩ := (mem_inf.mp (hD hd)).2
    have h1 := hdK k hk
    rw [hOK, Subgroup.map_bot, mem_bot] at h1
    calc d * k = d * k * (k⁻¹ * d⁻¹ * k * d) := by rw [h1, mul_one]
      _ = k * d := by group
  have hDfix : ∀ d ∈ D, ∀ a ∉ τ.support, ι d a = a := by
    intro d hd a ha
    refine eq_of_comm_altOff h5 (fun x hx => ?_) ha
    rw [← hKeq] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [← map_mul, ← map_mul, hDK d hd k hk]
  have hz2 : z ^ 2 = 1 := by rw [← hzo, pow_orderOf_eq_one]
  have hτ2 : τ ^ 2 = 1 := by rw [hτdef, ← map_pow, hz2, map_one]
  have hτ1 : τ ≠ 1 := fun h => by
    have h1 : z = 1 := hι (by rw [← hτdef, h, map_one])
    rw [h1, orderOf_one] at hzo
    omega
  have h8 : 8 ≤ τ.support.card := by
    refine eight_le_card_support_of_eight_dvd hτ2 (mem_alternatingGroup.mp (hιA z)) hτ1
      (D := D.map ι) ?_ ?_ ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      rw [hτdef, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.mp (mem_inf.mp (hD hd)).1]
    · rintro _ ⟨d, hd, rfl⟩
      exact hDfix d hd
    · rintro _ ⟨d, hd, rfl⟩
      exact mem_alternatingGroup.mp (hιA d)
    · rw [card_map_of_injective hι]
      obtain ⟨m, hm, ⟨eD⟩⟩ := hDd
      have hc : Nat.card D = 2 ^ m := by
        rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, ← pow_succ']
        congr 1
        omega
      rw [hc] at hD8 ⊢
      have h3 : 3 ≤ m := by
        by_contra h
        have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact Nat.pow_dvd_pow 2 h3
  have htK : t ∈ K := hP.le htP
  have ht'alt : ι t ∈ altOff τ.support := by
    rw [← hKeq]
    exact mem_map_of_mem ι htK
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have ht'2 : ι t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have ht'1 : (ι t).support.card ≠ 0 := fun h => by
    have h1 : t = 1 := hι (by rw [support_eq_empty_iff.mp (Finset.card_eq_zero.mp h), map_one])
    rw [h1, orderOf_one] at ht
    omega
  have h4t := four_dvd_card_support_of_sq_eq_one ht'2 (mem_alternatingGroup.mp (hιA t))
  have hdisj : Perm.Disjoint τ (ι t) := fun a => by
    by_cases ha : a ∈ τ.support
    · exact Or.inr (apply_eq_of_mem_altOff ht'alt ha)
    · exact Or.inl (Perm.notMem_support.mp ha)
  have hcard : 10 ≤ (ι (z * t)).support.card := by
    rw [map_mul, ← hτdef, hdisj.card_support_mul]
    omega
  have hσ2 : ι (z * t) ^ 2 = 1 := by
    rw [← map_pow, Commute.mul_pow hzt 2, hz2, ht2, mul_one, map_one]
  intro hsolv
  exact not_isSolvable_centralizer_of_sq_eq_one hσ2 hcard
    (isSolvable_centralizer_perm_of_range_eq ι hι hrange (z * t) hsolv)

end Alternating

end CFSG.ComponentClassification.Foote5
