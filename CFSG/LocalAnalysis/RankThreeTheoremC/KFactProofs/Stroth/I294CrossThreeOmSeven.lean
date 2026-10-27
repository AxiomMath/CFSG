module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeProj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenElem
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

open CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap

abbrev Idx7 : Type := Fin 3 ⊕ Fin 3 ⊕ Unit

section Model

variable {K : Type} [Field K]

theorem three_ne_zero_of_not_dvd_card [Finite K] (h : ¬ 3 ∣ Nat.card K) : (3 : K) ≠ 0 := by
  intro h0
  apply h
  haveI := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp' : p.Prime := CharP.char_is_prime K p
  have h3p : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h0)
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_three).1 h3p
  subst hp3
  have hc : ((Nat.card K : ℕ) : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    simp
  exact (CharP.cast_eq_zero_iff K 3 _).1 hc

theorem toLinEquiv_mem_orthogonalGroup_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) {A : GL ι K}
    (hA : A ∈ StatedOmega Q₀) :
    toLinEquiv ι K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hA
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  exact hle hA

theorem scalar_sq_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
    {A : GL ι K} (hAO : toLinEquiv ι K A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hAs : A ∈ StatedScalars ι K) {v : ι → K} (hv : Q v = 1) :
    ∃ c : K, c ^ 2 = 1 ∧ ∀ w, toLinEquiv ι K A w = c • w := by
  obtain ⟨c, hc⟩ := mem_scalars.1 ((mem_statedScalars_iff A).1 hAs)
  refine ⟨c, ?_, hc⟩
  have h1 := map_of_mem hAO v
  rw [hc, map_smul_eq_sq, hv, mul_one] at h1
  exact h1

theorem eq_one_of_mem_scalars_of_pow_three {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {v : V} (hv : Q v = 1) {h : V ≃ₗ[K] V}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h3 : h ^ 3 = 1) (hs : h ∈ scalars K V) :
    h = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.1 hs
  have hc2 : c ^ 2 = 1 := by
    have h1 := map_of_mem hO v
    rw [hc, map_smul_eq_sq, hv, mul_one] at h1
    exact h1
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hv; exact zero_ne_one hv
  have hpow : ∀ n : ℕ, (h ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hc3 : c ^ 3 = 1 := by
    have h1 := hpow 3
    rw [h3] at h1
    have h2 : (c ^ 3) • v = (1 : K) • v := by rw [← h1, one_smul]; rfl
    exact smul_left_injective K hv0 h2
  have hc1 : c = 1 := by
    have : c ^ 3 = c * c ^ 2 := by ring
    rw [hc2, mul_one] at this
    rw [← this, hc3]
  exact LinearEquiv.ext fun w => by rw [hc, hc1, one_smul]; rfl

theorem statedQuadOdd_single_z : StatedQuadOdd 3 K (Pi.single (Sum.inr (Sum.inr ())) 1) = 1 := by
  simp [StatedQuadOdd, Pi.single_apply]

end Model

end OmSeven

open OmSeven CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem i294CrossModelPOmega7_holds : I294CrossModelPOmega7 := by
  intro K _ _ hK3 hKodd x hx
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hKodd
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_not_dvd_card hK3
  have hQ0 : ⇑(CFSG.LieType.Universal.Spin.quadOdd 3 K) = StatedQuadOdd 3 K :=
    CFSG.LieType.Universal.Spin.coe_quadOdd 3 K
  obtain ⟨hQnd, hT⟩ := regular_quadOdd (n := 3) (K := K) h2 le_rfl
  set Q := CFSG.LieType.Universal.Spin.quadOdd 3 K with hQ
  have hvQ : Q (Pi.single (Sum.inr (Sum.inr ())) 1) = 1 := by
    rw [congrFun hQ0]
    exact statedQuadOdd_single_z
  have hZ : ∀ z ∈ (StatedScalars Idx7 K).subgroupOf (StatedOmega (StatedQuadOdd 3 K)),
      z ^ 2 = 1 := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    have hzO := toLinEquiv_mem_orthogonalGroup_of_mem_statedOmega hQ0 z.2
    obtain ⟨c, hc2, hc⟩ := scalar_sq_eq_one hzO hz hvQ
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply (toLinEquiv Idx7 K).injective
    refine LinearEquiv.ext fun w => ?_
    rw [map_pow, pow_two, LinearEquiv.mul_apply, hc, hc, smul_smul, ← pow_two, hc2, one_smul,
      map_one]
    rfl
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three (by norm_num) hZ hx3
  have hgO : toLinEquiv Idx7 K (g : GL Idx7 K) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    toLinEquiv_mem_orthogonalGroup_of_mem_statedOmega hQ0 g.2
  have hgL3 : toLinEquiv Idx7 K (g : GL Idx7 K) ^ 3 = 1 := by
    rw [← map_pow]
    have : (g : GL Idx7 K) ^ 3 = 1 := by simpa using congrArg Subtype.val hg3
    rw [this, map_one]
  have hdim : 7 ≤ Module.finrank K (Idx7 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨f, hfinj, hfO, hfc⟩ := exists_hom_triple hKodd h3 hQnd hdim hgO hgL3
  have hpowA : ∀ a : Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)),
      a ^ 3 = 1 := by
    rintro ⟨a, b, c⟩
    have h : ∀ d : Multiplicative (ZMod 3), d ^ 3 = 1 := by decide
    exact Prod.ext (h a) (Prod.ext (h b) (h c))
  have hf3 : ∀ a, f a ^ 3 = 1 := fun a => by rw [← map_pow, hpowA, map_one]
  obtain ⟨-, -, -, -, -, -, hoddlift, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQnd hT
  have hfΩ : ∀ a, f a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    intro a
    refine hoddlift (f a) (hfO a) ?_
    have hd : orderOf (f a) ∣ 3 := orderOf_dvd_of_pow_eq_one (hf3 a)
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      decide
  let φ : (Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) →*
      GL Idx7 K := (toLinEquiv Idx7 K).symm.toMonoidHom.comp f
  have hφ : ∀ a, toLinEquiv Idx7 K (φ a) = f a := fun a => MulEquiv.apply_symm_apply _ _
  have hφinj : Function.Injective φ := (toLinEquiv Idx7 K).symm.injective.comp hfinj
  have hH : ∀ a, φ a ∈ StatedOmega (StatedQuadOdd 3 K) := by
    intro a
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap]
    show toLinEquiv Idx7 K (φ a) ∈ _
    rw [hφ]
    exact hfΩ a
  have hsc : ∀ a, φ a ∈ StatedScalars Idx7 K → a = 1 := by
    intro a ha
    have hfa : f a ∈ scalars K (Idx7 → K) := by
      rw [← hφ a]
      exact (mem_statedScalars_iff _).1 ha
    have h1 := eq_one_of_mem_scalars_of_pow_three hvQ (hfO a) (hf3 a) hfa
    exact hfinj (by rw [h1, map_one])
  have hgcomm : ∀ a, (g : GL Idx7 K) * φ a = φ a * (g : GL Idx7 K) := by
    intro a
    apply (toLinEquiv Idx7 K).injective
    rw [map_mul, map_mul, hφ]
    exact (hfc a).eq
  have hA : Nat.card (Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) ×
      Multiplicative (ZMod 3))) = 3 ^ 3 := by
    simp [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]
  exact le_pRank_centralizer_statedProj (fun a b => mul_comm a b) hpowA hA φ hφinj hH hsc g
    hgcomm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
