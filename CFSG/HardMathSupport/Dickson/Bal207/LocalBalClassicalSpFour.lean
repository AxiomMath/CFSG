module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpEight
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThree
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Descent

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem outer_involution_conj_eta (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {a : MulAut (StatedProj (StatedSp 2 K))} (ha : orderOf a = 2)
    (haI : a ∉ inner (StatedProj (StatedSp 2 K))) :
    ∃ b ∈ inner (StatedProj (StatedSp 2 K)), a = b * exceptionalAut K ^ (2 * m + 1) * b⁻¹ := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨hγord, -, -, -, -, -, -, -, -, hinvol⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  obtain ⟨s, j, hj, hsj⟩ := hinvol a ha
  have hjf : j = 2 * m + 1 := hj.resolve_left fun h => haI (by
    rw [hsj, h, pow_zero, mul_one]
    exact spInner_mem_inner s)
  subst hjf
  set ηG : Subgroup.zpowers (minorAut K ^ (2 * m + 1)) :=
    ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩ with hηG
  set u := (antiSpEquiv K).symm s with hu
  set x : etaProduct K m := SemidirectProduct.inl u * SemidirectProduct.inr ηG with hx
  have hΘx : etaProductHom K m x = a := by
    rw [hx, map_mul, etaProductHom_inl, hηG, etaProductHom_inr_eta, hu,
      MulEquiv.apply_symm_apply, hsj]
  have hxr : x.right = ηG := by
    rw [hx, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul]
  have hγ2f : exceptionalAut K ^ (2 * (2 * m + 1)) = 1 := by rw [← hγord, pow_orderOf_eq_one]
  have hu1 : u * (minorAut K ^ (2 * m + 1)) u = 1 := by
    have hsq := pow_orderOf_eq_one a
    rw [ha] at hsq
    have hγ2 : exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1) = 1 := by
      rw [← pow_add, ← two_mul, hγ2f]
    have key : a * a = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) :=
      calc a * a = spInner 2 K s * (exceptionalAut K ^ (2 * m + 1) * spInner 2 K s) *
            exceptionalAut K ^ (2 * m + 1) := by rw [hsj]; simp only [mul_assoc]
        _ = spInner 2 K s * spInner 2 K ((exceptionalSpAut K ^ (2 * m + 1)) s) *
            (exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1)) := by
          rw [exceptionalAut_pow_mul_spInner]
          simp only [mul_assoc]
        _ = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) := by
          rw [hγ2, mul_one, map_mul]
    have h1 : s * (exceptionalSpAut K ^ (2 * m + 1)) s = 1 :=
      spInner_injective (by rw [← key, ← sq, hsq, map_one])
    have hs : s = antiSpEquiv K u := by rw [hu, MulEquiv.apply_symm_apply]
    rw [hs, exceptionalSpAut_pow_apply, ← map_mul] at h1
    exact (antiSpEquiv K).injective (h1.trans (map_one _).symm)
  have hxl : x.left = u := by
    simp only [hx, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inl, map_one, mul_one]
  have hx2 : x ^ 2 = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [sq, SemidirectProduct.mul_left, hxr, hxl, SemidirectProduct.one_left]
      exact hu1
    · rw [sq, SemidirectProduct.mul_right, hxr, SemidirectProduct.one_right]
      have h := pow_orderOf_eq_one (minorAut K ^ (2 * m + 1))
      rw [orderOf_eta m hK] at h
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, h]; rfl)
  obtain ⟨h, hh⟩ := eta_involution_conj m hK x hxr hx2
  have hconj := congrArg (etaProductHom K m) hh
  rw [map_mul, map_mul, map_inv, hΘx, etaProductHom_inl, etaProductHom_inr_eta] at hconj
  set b := spInner 2 K (antiSpEquiv K h)
  have hbH : b ∈ inner (StatedProj (StatedSp 2 K)) := spInner_mem_inner _
  refine ⟨b⁻¹, inv_mem hbH, ?_⟩
  rw [inv_inv, ← hconj]
  group

end Descent

section Moves

variable {K : Type} [Field K] [Finite K]

theorem not_three_dvd_card_suzukiGroup_eight
    (hK : Nat.card K = 8) : ¬ 3 ∣ Nat.card (suzukiGroup 1 K) := by
  have hK3 : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]; norm_num
  rw [CFSG.LieType.Ree.suzuki_order hK3]
  norm_num

theorem outer_involution_moves_order_three (hK : Nat.card K = 8)
    {σ : MulAut (StatedProj (StatedSp 2 K))} (hσ2 : σ ^ 2 = 1)
    (hσ : σ ∉ innerAut (StatedProj (StatedSp 2 K))) {s : StatedProj (StatedSp 2 K)}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) : σ s ≠ s := by
  intro hfix
  haveI : CharP K 2 := charP_two_of_card_eight hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]; norm_num
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective Nat.prime_two (by norm_num)
    hK' le_rfl (fun h => by omega)
  have hσ1 : σ ≠ 1 := fun h => hσ (h ▸ one_mem _)
  have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  obtain ⟨b, hb, hσb⟩ := outer_involution_conj_eta (m := 1) le_rfl hK3 hσord hσ
  obtain ⟨g, rfl⟩ := hb
  obtain ⟨φ, -, hφinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core (m := 1) le_rfl hK3 (exceptionalAut K)
      (fun x => exceptionalAut_proj x)
  set η : MulAut (StatedProj (StatedSp 2 K)) := exceptionalAut K ^ (2 * 1 + 1) with hη
  have hcs : σ * MulAut.conj s = MulAut.conj s * σ := by
    have h := SpChain.mulAut_mul_conj_mul_inv σ s
    rw [hfix] at h
    calc σ * MulAut.conj s = (σ * MulAut.conj s * σ⁻¹) * σ := by group
      _ = MulAut.conj s * σ := by rw [h]
  set s' : StatedProj (StatedSp 2 K) := g⁻¹ * s * g with hs'
  have hs'3 : s' ^ 3 = 1 := by
    have h := map_pow (MulAut.conj g⁻¹) s 3
    rw [hs3, map_one, MulAut.conj_apply, inv_inv] at h
    exact h.symm
  have hs'1 : s' ≠ 1 := fun h => hs1 (by
    have : s = g * s' * g⁻¹ := by rw [hs']; group
    rw [this, h]
    group)
  have hmem : MulAut.conj s' ∈ φ.range := by
    rw [hrange]
    refine ⟨⟨s', rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hconj : MulAut.conj s' = (MulAut.conj g)⁻¹ * MulAut.conj s * MulAut.conj g := by
      rw [hs', map_mul, map_mul, map_inv]
    have hη' : η = (MulAut.conj g)⁻¹ * σ * MulAut.conj g := by
      rw [hσb]
      group
    rw [hconj, hη']
    calc (MulAut.conj g)⁻¹ * MulAut.conj s * MulAut.conj g *
          ((MulAut.conj g)⁻¹ * σ * MulAut.conj g)
        = (MulAut.conj g)⁻¹ * (MulAut.conj s * σ) * MulAut.conj g := by group
      _ = (MulAut.conj g)⁻¹ * (σ * MulAut.conj s) * MulAut.conj g := by rw [hcs]
      _ = (MulAut.conj g)⁻¹ * σ * MulAut.conj g *
          ((MulAut.conj g)⁻¹ * MulAut.conj s * MulAut.conj g) := by group
  have hord : orderOf (MulAut.conj s') = 3 := by
    rw [orderOf_injective _ hinj s']
    exact orderOf_eq_prime hs'3 hs'1
  have hdvd : orderOf (MulAut.conj s') ∣ Nat.card φ.range :=
    Subgroup.orderOf_dvd_natCard φ.range hmem
  have hcard : Nat.card φ.range = Nat.card (suzukiGroup 1 K) :=
    Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm
  rw [hord, hcard] at hdvd
  exact not_three_dvd_card_suzukiGroup_eight hK hdvd

end Moves

section SpFour

variable {K : Type} [Field K] [Finite K]

theorem fieldCoreAt_fieldAut_sp_two_eight (hK : Nat.card K = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : FieldCoreAt 3 (fieldAut 2 K σ) := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, -, hS6, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) Nat.prime_two
      Nat.prime_three (by norm_num) (by norm_num) (by norm_num) le_rfl hK' σ hσ
  obtain ⟨⟨e⟩, -, -⟩ := hS6 ⟨rfl, by norm_num⟩
  have h3 : 3 ∣ Nat.card (Equiv.Perm (Fin 6)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Equiv.Perm (Fin 6)) 3 h3
  exact fieldCoreAt_fieldAut_sp_two_exc Nat.prime_two Nat.prime_three (by norm_num) (by norm_num)
    (by norm_num) hK' σ hσ (by norm_num)
    ⟨(e.symm g : StatedProj (StatedSp 2 K)), (e.symm g).2, by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg]⟩

theorem isLocallyBalancedAbs_one_psp_three_eight_two
    (hK : Nat.card K = 8) : IsLocallyBalancedAbs 3 1 (StatedProj (StatedSp 2 K)) := by
  classical
  haveI : CharP K 2 := charP_two_of_card_eight hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective Nat.prime_two (by norm_num)
    hK' le_rfl (fun h => by omega)
  have hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => hinj ?_
    rw [map_one]
    ext g
    have := Subgroup.mem_center_iff.1 hz g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← this]
    group
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by norm_num : 1 ≤ 3) hK'
  obtain ⟨-, -, -, -, -, hcard6, -⟩ :=
    exceptionalAut_structure (by norm_num : 1 ≤ 3) hFr hord hzp
  refine isLocallyBalancedAbs_one_of_inner_outer_good Nat.prime_three hcen
    (QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K)))) (fun α => QuotientGroup.eq_one_iff α)
    ?_ ?_ ?_
  · intro y hy
    have h1 : orderOf y ∣ 2 * 3 := by
      rw [← hcard6]
      exact orderOf_dvd_natCard y
    exact orderOf_dvd_iff_pow_eq_one.1 (Nat.Coprime.dvd_of_dvd_mul_right hy.symm h1)
  · intro s hs3 hs1
    refine ⟨?_, fun σ hσ2 hσ => ⟨s, rfl, outer_involution_moves_order_three hK hσ2 hσ hs3 hs1⟩⟩
    exact W2.core_eq_bot_of_noNormalPPrime Nat.prime_three
      (noNormalPPrime_three_centralizer_statedProj_eight hK (by omega)
        (orderOf_eq_prime hs3 hs1))
  · intro x hx hxin
    left
    obtain ⟨σ, h, hσ, hxh⟩ := outer_conj_fieldAut_eight le_rfl hK hx hxin
    exact fieldCoreAt_of_conj (fieldCoreAt_fieldAut_sp_two_eight hK hσ) h⁻¹ (by rw [hxh]; group)

theorem isLocallyBalancedAbs_three_one_B_two_eight
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) (hq : IsTwoPow q 3) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  have hq8 : q.card = 8 := by
    rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)) = 8 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using hq8
  exact IsLocallyBalancedAbs.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
    (isLocallyBalancedAbs_one_psp_three_eight_two hK)

end SpFour

section Row

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

theorem bal207LocalBalRow_sp : Bal207LocalBalRow FamSp := by
  rintro p ⟨d, hd⟩ ⟨hidx, hsp⟩
  cases d with
  | B r q =>
    obtain ⟨rfl, h⟩ := hidx
    rcases h with ⟨hq, hr⟩ | ⟨hq, hr⟩
    · exact isLocallyBalancedAbs_three_one_B_two hd hq hr
    · rcases Nat.lt_or_ge r 3 with h3 | h3
      · obtain rfl : r = 2 := by omega
        exact isLocallyBalancedAbs_three_one_B_two_eight hd hq
      · exact isLocallyBalancedAbs_three_one_B_eight_of_three_le hd hq h3
  | _ => exact hsp.elim

end Row

end CFSG.HardMathSupport.Dickson.Bal207

end
