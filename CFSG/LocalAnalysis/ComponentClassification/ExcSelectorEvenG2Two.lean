module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic
public import CFSG.LieType.Chevalley.G2SolvableNormalTrivial
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.Assembly.LowTwoRank

theorem eq_seven_of_dvd {r : ℕ} (hr : Odd r) (h5 : 5 ≤ r) (h : r * (r ^ 2 - 1) ∣ 24192) :
    r = 7 := by
  have hle : r * (r ^ 2 - 1) ≤ 24192 := Nat.le_of_dvd (by norm_num) h
  have hr30 : r < 30 := by
    by_contra hc
    push Not at hc
    have h1 : 899 ≤ r ^ 2 - 1 := by
      have : 30 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    have : 30 * 899 ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul hc h1
    omega
  obtain ⟨s, rfl⟩ := hr
  have hs : s < 15 := by omega
  interval_cases s <;> first | rfl | omega

theorem card_ringEquiv_le_one_of_card_seven {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 7) : Nat.card (F ≃+* F) ≤ 1 := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 7 := by rw [← Nat.card_eq_fintype_card, hF]
  set e₀ := ZMod.ringEquivOfPrime F (by norm_num : Nat.Prime 7) hF'
  have hsub : Subsingleton (F ≃+* F) := ⟨fun σ τ => by
    have h : e₀.trans σ = e₀.trans τ := Subsingleton.elim _ _
    ext x
    have := congrArg (fun φ : ZMod 7 ≃+* F => φ (e₀.symm x)) h
    simpa using this⟩
  have : Finite (F ≃+* F) := Finite.of_subsingleton
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_one_iff_subsingleton.mpr hsub

theorem card_mulAut_psl2_seven {F : Type} [Field F] [Finite F] (hF : Nat.card F = 7) :
    Nat.card (MulAut (GorensteinWalter.PSL2 F)) ≤ 2016 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hF]; norm_num⟩
  have hsurj := GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F (p := 7) (f := 1)
    (by rw [hF]; norm_num) hodd (by rw [hF]; norm_num)
  have : Finite (GorensteinWalter.PGL2 F) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have : Finite (F ≃+* F) := by
    have : Fintype F := Fintype.ofFinite F
    exact Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  have : Finite (GorensteinWalter.PGammaL2 F) :=
    Finite.of_equiv _ (SemidirectProduct.equivProd).symm
  calc Nat.card (MulAut (GorensteinWalter.PSL2 F)) ≤ Nat.card (GorensteinWalter.PGammaL2 F) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card (GorensteinWalter.PGL2 F) * Nat.card (F ≃+* F) := SemidirectProduct.card
    _ ≤ Nat.card (GL (Fin 2) F) * 1 := by
        refine Nat.mul_le_mul ?_ (card_ringEquiv_le_one_of_card_seven hF)
        exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    _ = 2016 := by
        have : Fintype F := Fintype.ofFinite F
        rw [mul_one, Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card.symm.trans
          hF]
        norm_num

variable {k : Type} [Field k] [Finite k]

theorem card_adjointGroup_G2_two (hk : Nat.card k = 2) : Nat.card (adjointGroup .G2 k) = 12096 := by
  rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  rfl

omit [Finite k] in
theorem center_eq_bot_of_normal_G2 (M : Subgroup (adjointGroup .G2 k)) [hM : M.Normal] :
    center M = ⊥ := by
  set Z := (center M).map M.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨z, hzc, rfl⟩ := Subgroup.mem_map.1 hz
    have hgz : g * (z : adjointGroup .G2 k) * g⁻¹ ∈ M := hM.conj_mem _ z.2 g
    refine ⟨⟨_, hgz⟩, ?_, rfl⟩
    show _ ∈ center M
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : g⁻¹ * (y : adjointGroup .G2 k) * g ∈ M := by
      have := hM.conj_mem _ y.2 g⁻¹
      simpa using this
    have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hzc) ⟨_, hy⟩)
    change g⁻¹ * (y : adjointGroup .G2 k) * g * z = z * (g⁻¹ * y * g) at h1
    change (y : adjointGroup .G2 k) * (g * z * g⁻¹) = g * z * g⁻¹ * y
    calc (y : adjointGroup .G2 k) * (g * z * g⁻¹) =
        g * (g⁻¹ * (y : adjointGroup .G2 k) * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * y := by group
  have hsolv : Group.IsSolvable Z := by
    have : IsMulCommutative Z := ⟨⟨fun a b => by
      obtain ⟨a', ha, ha'⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb, hb'⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : adjointGroup .G2 k) * b = b * a
      rw [← ha', ← hb']
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hb) a')⟩⟩
    infer_instance
  have h := G2_solvable_normal_subgroups_trivial k Z hsolv
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : adjointGroup .G2 k) ∈ Z := ⟨x, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (Subtype.ext hx')

theorem not_smallType_of_normal_G2_two (hk : Nat.card k = 2) (M : Subgroup (adjointGroup .G2 k))
    [hM : M.Normal] : ¬ SmallType M := by
  have hG := card_adjointGroup_G2_two hk
  have hZ := center_eq_bot_of_normal_G2 M
  have hc := card_centralQuotient_of_center_eq_bot hZ
  have hMdvd : Nat.card M ∣ 12096 := hG ▸ Subgroup.card_subgroup_dvd_card M
  rintro (⟨p, f, hp, hp2, hf, h5, hm, -⟩ | ⟨⟨e7⟩, -⟩ | h34)
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psl hm
    have hFodd : Odd (Nat.card F) := hF ▸ (hp.odd_of_ne_two hp2).pow
    have hg : Nat.gcd 2 (Nat.card F - 1) = 2 := by
      obtain ⟨j, hj⟩ := hFodd
      rw [hj, show 2 * j + 1 - 1 = 2 * j by omega]
      exact Nat.gcd_eq_left (dvd_mul_right 2 j)
    have h2 := UnbalancingLocal.card_psl_two_mul_gcd F
    rw [hg, ← Nat.card_congr e.toEquiv, hc] at h2
    have hF5 : 5 ≤ Nat.card F := hF ▸ h5
    have h7 : Nat.card F = 7 := eq_seven_of_dvd hFodd hF5 (by
      rw [← h2, show (24192 : ℕ) = 12096 * 2 by norm_num]
      exact Nat.mul_dvd_mul_right hMdvd 2)
    have hM168 : Nat.card M = 168 := by rw [h7] at h2; omega
    set C := centralizer (M : Set (adjointGroup .G2 k)) with hCdef
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hMC : M ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxZ : (⟨x, hx.1⟩ : M) ∈ center M := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hx.2) y y.2)
      rw [hZ, Subgroup.mem_bot] at hxZ
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hxZ)
    let φ : M × C →* adjointGroup .G2 k := MonoidHom.noncommCoprod M.subtype C.subtype fun m c =>
      (Subgroup.mem_centralizer_iff.1 c.2) m m.2
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨m, c⟩ h1
      change (m : adjointGroup .G2 k) * c = 1 at h1
      have hm : (m : adjointGroup .G2 k) = (c : adjointGroup .G2 k)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      have hmC : (m : adjointGroup .G2 k) ∈ M ⊓ C := ⟨m.2, hm ▸ C.inv_mem c.2⟩
      rw [hMC, Subgroup.mem_bot] at hmC
      have hc1 : (c : adjointGroup .G2 k) = 1 := by
        rw [← inv_inv (c : adjointGroup .G2 k), ← hm, hmC, inv_one]
      exact Prod.ext (Subtype.ext hmC) (Subtype.ext hc1)
    have hC72 : Nat.card C ∣ 72 := by
      have h1 : Nat.card (M × C) ∣ Nat.card (adjointGroup .G2 k) := by
        rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      rw [Nat.card_prod, hM168, hG, show (12096 : ℕ) = 168 * 72 by norm_num] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    have hCsolv : Group.IsSolvable C := by
      refine LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      have hsub : (Nat.card C).primeFactors ⊆ {2, 3} := by
        intro q hq
        have hq' := Nat.mem_primeFactors.1 hq
        have hq72 : q ∣ 72 := hq'.2.1.trans hC72
        have : q ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hq72
        rcases (Nat.Prime.dvd_mul hq'.1).1 this with h | h
        · simp [(Nat.prime_dvd_prime_iff_eq hq'.1 Nat.prime_two).1 (hq'.1.dvd_of_dvd_pow h)]
        · simp [(Nat.prime_dvd_prime_iff_eq hq'.1 Nat.prime_three).1 (hq'.1.dvd_of_dvd_pow h)]
      exact (Finset.card_le_card hsub).trans (by decide)
    have hC1 : C = ⊥ := G2_solvable_normal_subgroups_trivial k C hCsolv
    have hinj : Function.Injective
        (MulAut.conjNormal : adjointGroup .G2 k →* MulAut M) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hgC : g ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have := congrArg (fun φ : MulAut M => ((φ ⟨m, hm⟩ : M) : adjointGroup .G2 k)) hg
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
        calc m * g = g * m * g⁻¹ * g := by rw [this]
          _ = g * m := by group
      rw [hC1, Subgroup.mem_bot] at hgC
      exact hgC
    have heM : M ≃* GorensteinWalter.PSL2 F :=
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
        e).trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    have hle : Nat.card (adjointGroup .G2 k) ≤ Nat.card (MulAut M) :=
      Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_congr (MulAut.congr heM).toEquiv, hG] at hle
    have := card_mulAut_psl2_seven h7
    omega
  · have h2520 : Nat.card M = 2520 := by
      rw [← hc, Nat.card_congr e7.toEquiv]
      exact UnbalancingLocal.card_alternating_seven
    rw [h2520] at hMdvd
    norm_num at hMdvd
  · obtain ⟨hcard, -, -⟩ := PSL3Four.excludes_alternating_models_stated.{0} _
      (statedClassicalModel_of_lieModel_psl h34)
    rw [hc] at hcard
    rw [hcard] at hMdvd
    norm_num at hMdvd

end CFSG.ComponentClassification.ExcSelector
