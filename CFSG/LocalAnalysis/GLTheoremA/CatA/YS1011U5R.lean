module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem rawDatum_twA_four_iff (n : ℕ) (Q : CFSG.Assembly.LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 4, n⟩ Q ↔
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
        Q (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSUGroup (Fin 5) F (2 ^ n)))
          (CFSG.Assembly.LargeEvenMatConjImage
            (CFSG.Assembly.LargeEvenProjMk (CFSG.Assembly.LargeEvenSUGroup (Fin 5) F (2 ^ n)))
            (CFSG.Assembly.LargeEvenGUSet (Fin 5) F (2 ^ n)))
          (CFSG.Assembly.LargeEvenMatFieldImage
            (CFSG.Assembly.LargeEvenProjMk (CFSG.Assembly.LargeEvenSUGroup (Fin 5) F (2 ^ n)))) :=
  Iff.rfl

theorem mem_conjImage_of_pow_five {n : ℕ} (F : Type) [Field F] [Finite F] (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcop : Nat.Coprime 5 (2 * n))
    (φ : MulAut (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSUGroup (Fin 5) F (2 ^ n))))
    (hφ : φ ^ 5 = 1) :
    φ ∈ CFSG.Assembly.LargeEvenMatConjImage
      (CFSG.Assembly.LargeEvenProjMk (CFSG.Assembly.LargeEvenSUGroup (Fin 5) F (2 ^ n)))
      (CFSG.Assembly.LargeEvenGUSet (Fin 5) F (2 ^ n)) := by
  have hU := CFSG.StandardType.unitaryFieldData_of_card hn hF
  obtain ⟨Θ, -, hker, -⟩ := CFSG.StandardType.RecipeFieldSU.exists_fieldFactor hU
    (by norm_num : 3 ≤ 5) (by norm_num)
  have hcard2 : Nat.card F = 2 ^ (2 * n) := by rw [hF, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hcard2
  haveI : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hAut]; omega)
  have h5 : Θ φ ^ 5 = 1 := by rw [← map_pow, hφ, map_one]
  have hd5 : orderOf (Θ φ) ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hd2n : orderOf (Θ φ) ∣ 2 * n := by
    rw [← hAut]
    exact orderOf_dvd_natCard (Θ φ)
  have hΘ : Θ φ = 1 := by
    have h1 : orderOf (Θ φ) ∣ Nat.gcd 5 (2 * n) := Nat.dvd_gcd hd5 hd2n
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h1
    exact orderOf_eq_one_iff.mp h1
  have hmem := (hker φ).mp hΘ
  rw [← SetLike.mem_coe,
    CFSG.StandardType.RecipeFieldSU.coe_recIU (d := 5) hU hF (by norm_num)] at hmem
  exact hmem

theorem u5out_holds (G : Type) [Group G] [Finite G] : U5OutAt G := by
  intro X K A _hK hA hAN hM
  unfold InnDiagOn
  refine ⟨hAN, ?_⟩
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hM
  obtain ⟨R0, hgR, I0, F0, hQ0⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab5⟩ := hQ0
  obtain ⟨n, rfl, hn26⟩ : ∃ n, lab = ⟨.twA, 4, n⟩ ∧ (n = 2 ∨ n = 6) := by
    rcases hlab5 with h | h
    · exact ⟨2, h, Or.inl rfl⟩
    · exact ⟨6, h, Or.inr rfl⟩
  have hn : 1 ≤ n := by omega
  have hcop : Nat.Coprime 5 (2 * n) := by
    rcases hn26 with rfl | rfl <;> norm_num
  obtain ⟨F, hFf, hFfin, hFcard, hQ⟩ := (rawDatum_twA_four_iff n _).1 hraw
  obtain ⟨hs, hna, θ, -⟩ := hQ
  refine And.intro hcomm ?_
  refine ⟨⟨.twA, 4, n⟩, hlab, (rawDatum_twA_four_iff n _).2
    ⟨F, hFf, hFfin, hFcard, hs, hna, θ, fun a ha => ?_⟩⟩
  have hγ : a⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ (hAN ha)
  have h5 : a⁻¹ ^ 5 = 1 := by rw [inv_pow, hA.2 a ha, inv_one]
  refine ⟨MulAut.congr θ (chevAut 5 K ⟨a⁻¹, hγ⟩), ?_, ?_⟩
  · apply mem_conjImage_of_pow_five F hn hFcard hcop
    rw [← map_pow (MulAut.congr θ), chevAut_pow_eq_one 5 K hγ h5, map_one]
  · rintro l l' ⟨x, y, rfl, rfl, hxy⟩
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    show chevAut 5 K ⟨a⁻¹, hγ⟩ (chevQuotHom 5 K x) = chevQuotHom 5 K y
    rw [chevAut_chevQuotHom]
    congr 1
    refine Subtype.ext ?_
    show a⁻¹ * (x : G) * (a⁻¹)⁻¹ = (y : G)
    rw [inv_inv, hxy]

theorem card_mulAut_u4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    Nat.card (MulAut S) = 51840 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two h
  obtain ⟨e'⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.nonempty_equiv_timmesfeldPSU 3 q hv hq2 e
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv,
      CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU (by norm_num)]
    norm_num
  obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two h
  have hPS : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  have hsimple : IsSimpleGroup S := by
    haveI := hPS
    exact MulEquiv.isSimpleGroup eS
  haveI := hsimple
  have hS : Nat.card S = 25920 := by
    rw [Nat.card_congr (eS.trans CFSG.GH74.Exceptional.psp43EquivU2).toEquiv,
      CFSG.GH74.Exceptional.card_U2_four]
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h1 | h1
    · exact h1
    · exfalso
      have hc : IsMulCommutative S := Subgroup.center_eq_top_iff.1 h1
      have hp := (@Group.is_simple_iff_prime_card S _ hc).1 hsimple
      rw [hS] at hp
      norm_num at hp
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) = Nat.card S := by
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hc : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
        have := congrArg (fun α : MulAut S => α x) hg
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc x * g = g * x * g⁻¹ * g := by rw [this]
          _ = g * x := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hMul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  have hOut' : Nat.card (MulAut S ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 2 :=
    hOut
  rw [hinner, hS, hOut'] at hMul
  rw [hMul]

theorem card_mulAut_a6 {S : Type} [Group S] (h : catalogIs S S10.isA6) :
    Nat.card (MulAut S) = 1440 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating d hd =>
    have hd6 : d = 6 := hi
    subst hd6
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6
  | lie _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim

theorem card_mulAut_small {S : Type} [Group S]
    (h : catalogIs S S9.isU4two ∨ catalogIs S S10.isA6) :
    Nat.card (MulAut S) = 51840 ∨ Nat.card (MulAut S) = 1440 :=
  h.elim (fun h => Or.inl (card_mulAut_u4two h)) (fun h => Or.inr (card_mulAut_a6 h))

theorem eq_three_of_sq_dvd {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : N = 51840 ∨ N = 1440)
    (hdvd : p ^ 2 ∣ N) : p = 3 := by
  have hpN : p ∣ N := (dvd_pow_self p two_ne_zero).trans hdvd
  have key : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 := by
    rcases hN with rfl | rfl
    · have h : p ∣ (2 ^ 7 * 3 ^ 4) * 5 := by norm_num; exact hpN
      rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
        · exact Or.inl (hp.dvd_of_dvd_pow h'')
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h''))
      · exact Or.inr (Or.inr h')
    · have h : p ∣ (2 ^ 5 * 3 ^ 2) * 5 := by norm_num; exact hpN
      rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
        · exact Or.inl (hp.dvd_of_dvd_pow h'')
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h''))
      · exact Or.inr (Or.inr h')
  rcases key with h | h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  · have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h5
    rcases hN with rfl | rfl <;> norm_num at hdvd

theorem rank_holds (G : Type) [Group G] [Finite G] : RankAutSmallAt G := by
  intro p X K A hp hp2 hK hsmall hAN hA hcard
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let H : Subgroup N := A.subgroupOf N
  let ψ : H →* MulAut (PSimple p K) := (chevAut p K).comp H.subtype
  have hcardH : Nat.card H = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hmap : ψ.ker.map (N.subtype.comp H.subtype) = A ⊓ centModSubgroup p K := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : chevAut p K x.1 = 1 := hx
      have hcent : CentMod p K (x.1 : G) := (chevAut_eq_one_iff hp hK x.1.2).1 hx'
      exact ⟨Subgroup.mem_subgroupOf.1 x.2, centMod_iff.1 hcent⟩
    · rintro ⟨hgA, hgC⟩
      have hgN : g ∈ N := (mem_centModSubgroup.1 hgC).1
      refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgA⟩, ?_, rfl⟩
      show chevAut p K ⟨g, hgN⟩ = 1
      exact (chevAut_eq_one_iff hp hK hgN).2 (centMod_iff.2 hgC)
  have hf : Function.Injective (N.subtype.comp H.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hkerCard : Nat.card ψ.ker = Nat.card ↥(A ⊓ centModSubgroup p K) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hsplitA : Nat.card A = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← hcardH, hsplit]
  have hdvdR : Nat.card ψ.range ∣ p ^ m := by
    rw [← hm, hsplitA]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdR
  have hcpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hRge : p ^ 2 ≤ Nat.card ψ.range := by
    refine Nat.le_of_mul_le_mul_right ?_ hcpos
    rw [← hsplitA, hkerCard]
    exact hcard
  have hj2 : 2 ≤ j := by
    rw [hj] at hRge
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hRge
  have hp2r : p ^ 2 ∣ Nat.card ψ.range := by
    rw [hj]
    exact pow_dvd_pow p hj2
  have hAut : p ^ 2 ∣ Nat.card (MulAut (PSimple p K)) :=
    hp2r.trans (Subgroup.card_subgroup_dvd_card ψ.range)
  exact eq_three_of_sq_dvd hp hp2 (card_mulAut_small (S := PSimple p K) hsmall) hAut

end CFSG.LocalAnalysis.GLTheoremA
