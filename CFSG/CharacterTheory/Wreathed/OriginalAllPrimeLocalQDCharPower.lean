module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDPerfect
public import CFSG.GroupTheory.ABGDGroups.LinearQuotient
public import CFSG.GroupTheory.ABGQGroups.Defs
public import CFSG.GroupTheory.QuasiDihedralFusion.SimpleNormal
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionSupport

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.QuasiDihedralFusion CFSG.ABGQGroups CFSG.Semidihedral.ProjectiveSL2Cover

universe u v

section SL2

variable {F : Type} [Field F] [Finite F]

theorem eq_bot_of_normal_of_odd_card_sl2
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [X.Normal] (hX : Odd (Nat.card X)) :
    X = ⊥ := by
  have hF2 : ringChar F ≠ 2 := by
    obtain ⟨p, f, -, hpodd, -, hcard⟩ := hF
    exact ringChar_ne_two_of_card hpodd hcard
  have : (X.map (nativeQuotient F)).Normal :=
    Subgroup.Normal.map inferInstance _ (nativeQuotient_surjective F)
  have hodd : Odd (Nat.card (X.map (nativeQuotient F))) := by
    have h := card_eq_card_map_mul_card_inf (nativeQuotient F) X
    exact hX.of_dvd_nat (Dvd.intro _ h.symm)
  have hbot := CFSG.ABGDGroups.eq_bot_of_normal_of_odd_card_psl2 hF _ hodd
  have hle : X ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro g hg
    have h1 : nativeQuotient F g ∈ X.map (nativeQuotient F) := ⟨g, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : g ∈ (nativeQuotient F).ker := h1
    rwa [nativeQuotient_ker, ← center_eq_zpowers_minusIdentity] at h2
  have hdvd : Nat.card X ∣ 2 := by
    have h := Subgroup.card_dvd_of_le hle
    rw [center_card F hF2] at h
    exact h
  have h1 : Nat.card X = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hX
      exact absurd hX (by decide)
  exact Subgroup.card_eq_one.mp h1

theorem isPerfect_sl2 (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  apply CFSG.LinearGroups.special_linear_dimension_two_perfect
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact ⟨s, hs⟩

end SL2

theorem hasNormalSL2_of_surjective {K : Type u} [Group K] [Finite K] {F : Type} [Field F]
    [Finite F] (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F)) {Λ : Subgroup K}
    (hΛ : Λ.Normal) (ψ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ (CFSG.oddCore K).subgroupOf Λ) :
    HasNormalSL2 (K ⧸ CFSG.oddCore K) (Nat.card F) := by
  let π : K →* K ⧸ CFSG.oddCore K := QuotientGroup.mk' (CFSG.oddCore K)
  have himg : ((CFSG.oddCore K).subgroupOf Λ).map ψ = ⊥ := by
    have : ((CFSG.oddCore K).subgroupOf Λ).Normal := Subgroup.Normal.subgroupOf inferInstance Λ
    have : (((CFSG.oddCore K).subgroupOf Λ).map ψ).Normal :=
      Subgroup.Normal.map inferInstance ψ hψ
    apply eq_bot_of_normal_of_odd_card_sl2 hF
    have h1 := card_eq_card_map_mul_card_inf ψ ((CFSG.oddCore K).subgroupOf Λ)
    have h2 : Odd (Nat.card ((CFSG.oddCore K).subgroupOf Λ)) :=
      (CFSG.ABGDGroups.odd_card_oddCore K).of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective (CFSG.oddCore K) Λ.subtype Λ.subtype_injective)
    exact h2.of_dvd_nat (Dvd.intro _ h1.symm)
  have hkerEq : (π.subgroupMap Λ).ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxO : (x : K) ∈ CFSG.oddCore K :=
        (QuotientGroup.eq_one_iff (x : K)).mp (congrArg Subtype.val hx)
      have h1 : ψ x ∈ ((CFSG.oddCore K).subgroupOf Λ).map ψ := ⟨x, hxO, rfl⟩
      rw [himg, Subgroup.mem_bot] at h1
      exact h1
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : K)).mpr (hker hx)
  let e : Λ.map π ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientKerEquivOfSurjective _ (π.subgroupMap_surjective Λ)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))
  exact ⟨Λ.map π, F, inferInstance, inferInstance, hΛ.map π (QuotientGroup.mk'_surjective _), rfl,
    ⟨e⟩⟩

section Transport

theorem hasNormalSL2_of_mulEquiv {X : Type u} {Y : Type v} [Group X] [Group Y] (e : X ≃* Y)
    {q : ℕ} (h : HasNormalSL2 X q) : HasNormalSL2 Y q := by
  obtain ⟨L, F, hF, hfin, hLn, hcard, ⟨eL⟩⟩ := h
  exact ⟨L.map e.toMonoidHom, F, hF, hfin, hLn.map _ e.surjective, hcard,
    ⟨(L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eL⟩⟩

theorem hasQCharPower_of_mulEquiv {X : Type u} {Y : Type v} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) {q : ℕ} (h : HasQCharPower X q) : HasQCharPower Y q :=
  ⟨IsQGroup.of_mulEquiv e h.1, h.2.1, hasNormalSL2_of_mulEquiv
    (QuotientGroup.congr (CFSG.oddCore X) (CFSG.oddCore Y) e
      (ReducedInvolution.oddCore_map_mulEquiv e)) h.2.2⟩

theorem map_conj_centralizer {X : Type u} [Group X] (c x : X) :
    (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * x * c⁻¹} : Set X) := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g * (c * x * c⁻¹) = c * (c⁻¹ * g * c * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * g * c)) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * g := by group
  · intro h
    calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * g) * c := by rw [h]
      _ = x * (c⁻¹ * g * c) := by group

theorem hasQCharPower_of_isConj {X : Type u} [Group X] [Finite X] {x y : X} (hxy : IsConj x y)
    {q : ℕ} (h : HasQCharPower (Subgroup.centralizer ({x} : Set X)) q) :
    HasQCharPower (Subgroup.centralizer ({y} : Set X)) q := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  exact hasQCharPower_of_mulEquiv (((Subgroup.centralizer ({x} : Set X)).equivMapOfInjective _
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr (map_conj_centralizer c x))) h

end Transport

section Perfect

theorem exists_perfect_map_eq {X : Type u} {Y : Type v} [Group X] [Group Y] [Finite X]
    (π : X →* Y) (hπ : Function.Surjective π) (L : Subgroup Y) [Group.IsPerfect L] :
    ∃ P : Subgroup X, Group.IsPerfect P ∧ P.map π = L := by
  obtain ⟨P, hP, hmin⟩ := Set.exists_min_image {P : Subgroup X | P.map π = L}
    (fun P => Nat.card P) (Set.toFinite _)
    ⟨L.comap π, Subgroup.map_comap_eq_self_of_surjective hπ L⟩
  have hP' : P.map π = L := hP
  have hc : (⁅P, P⁆ : Subgroup X).map π = L := by
    rw [Subgroup.map_commutator, hP', Subgroup.commutator_eq_self]
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  have heq : ⁅P, P⁆ = P := Subgroup.eq_of_le_of_card_ge hle (hmin _ hc)
  exact ⟨P, Subgroup.isPerfect_iff.mpr heq, hP'⟩

theorem card_dvd_of_perfect_of_ker_le
    {P : Type u} [Group P] [Finite P] [Group.IsPerfect P]
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) {F' : Type} [Field F'] [Finite F'] (hF' : 7 ≤ Nat.card F')
    (α : P →* Matrix.SpecialLinearGroup (Fin 2) F)
    (β : P →* Matrix.SpecialLinearGroup (Fin 2) F') (hβ : Function.Surjective β)
    (hker : α.ker ≤ β.ker) (hodd : Odd (Nat.card β.ker)) : Nat.card F' ∣ p ^ f := by
  have hs := α.rangeRestrict_surjective
  have hB : Group.IsPerfect α.range := Group.IsPerfect.ofSurjective hs
  let ν : α.range →* Matrix.SpecialLinearGroup (Fin 2) F' :=
    α.rangeRestrict.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs)
      ⟨β, by rw [MonoidHom.ker_rangeRestrict]; exact hker⟩
  have hν : ∀ x, ν (α.rangeRestrict x) = β x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hνs : Function.Surjective ν := by
    intro y
    obtain ⟨x, rfl⟩ := hβ y
    exact ⟨_, hν x⟩
  have hνker : ν.ker = β.ker.map α.rangeRestrict := by
    have h1 : ν.comp α.rangeRestrict = β := MonoidHom.ext hν
    rw [← h1, ← MonoidHom.comap_ker, Subgroup.map_comap_eq_self_of_surjective hs]
  have hνodd : Odd (Nat.card ν.ker) := by
    rw [hνker]
    have h := card_eq_card_map_mul_card_inf α.rangeRestrict β.ker
    exact hodd.of_dvd_nat (Dvd.intro _ h.symm)
  exact card_dvd_of_perfect hp hpodd hf hcard hB hF' ν hνs hνodd

end Perfect

section QGroups

theorem isQGroup_range {K : Type u} {X : Type v} [Group K] [Group X] [Finite K] (θ : K →* X)
    (hodd : Odd (Nat.card θ.ker)) (hK : IsQGroup K) : IsQGroup θ.range :=
  (isQGroup_iff_of_oddKernel θ.rangeRestrict θ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict])).mpr hK

theorem le_oddCore_of_normal {K : Type u} [Group K] {Z : Subgroup K} (hZ : Z.Normal)
    (hodd : Odd (Nat.card Z)) : Z ≤ CFSG.oddCore K :=
  le_sSup ⟨hZ, hodd⟩

theorem IsQDGroup.eq_bot_of_normal_isPGroup_two {H : Type u} [Group H] [Finite H]
    (hH : IsQDGroup H) {R : Subgroup H} (hRn : R.Normal) (hR : IsPGroup 2 R) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : H →* H ⧸ CFSG.oddCore H := QuotientGroup.mk' (CFSG.oddCore H)
  set L := SimpleOddIndexQuotient.involutionClosure (H ⧸ CFSG.oddCore H) with hL
  obtain ⟨-, -, hQD, -, hmin⟩ := hH.involutionClosure_quotient_oddCore
  by_cases hbot : R.map π = ⊥
  · have hle : R ≤ CFSG.oddCore H := by
      intro r hr
      have h1 : π r ∈ R.map π := ⟨r, hr, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff r).mp h1
    have hodd : Odd (Nat.card R) :=
      (CFSG.ABGDGroups.odd_card_oddCore H).of_dvd_nat (Subgroup.card_dvd_of_le hle)
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    have hk0 : k = 0 := by
      by_contra h0
      rw [hk] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' h0).mpr even_two)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · exfalso
    have hLR := hmin (R.map π) (hRn.map π (QuotientGroup.mk'_surjective _)) hbot
    have hLp : IsPGroup 2 L := (hR.map π).to_le hLR
    obtain ⟨P⟩ : Nonempty (Sylow 2 L) := inferInstance
    have h4 := four_dvd_card_sylow hQD.sylow P
    have h2 : 2 ∣ Nat.card L :=
      ((by norm_num : 2 ∣ 4).trans h4).trans (Subgroup.card_subgroup_dvd_card _)
    obtain ⟨M, hM⟩ := exists_index_two_of_isPGroup hLp h2
    exact hQD.noIndexTwo M hM

end QGroups

end CFSG.Wreathed.OriginalAllPrime.LocalQD
