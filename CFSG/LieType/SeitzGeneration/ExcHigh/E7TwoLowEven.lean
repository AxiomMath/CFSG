module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoLow
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameEven
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinSingularEven

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

section S3
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups

section Main

variable {K : Type} [Field K] [Finite K]

theorem e7_conj_into_frame_five_even (hev : Even (Nat.card K)) (hpq : 5 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5p : (5 : ℕ).Prime := Nat.prime_five
  have hord := orderOf_eq_two_of_dvd_add_one hp5p (by norm_num) hpq
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp5p hpq
  have hpq1 := not_dvd_pred_of_dvd_add_one hp5p (by norm_num) hpq
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hchar2 : ringChar K = 2 := by
    have heven : Even (Fintype.card K) := by
      rw [← Nat.card_eq_fintype_card]
      exact hev
    exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
  haveI : CharP K 2 := ringChar.of_eq hchar2
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hpl : 5 ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self 5 m.ne_zero
  have hpK0 : ((5 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp5p hpK
  have hn3 : 3 ≤ 6 := by norm_num
  obtain ⟨Ψ, hker, hrange, hrank, hweyl⟩ := exists_psi_D6_param K hn3
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K) isRoot_e7Theta
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (Spin.quadPlus 6 K)), Commute (ρ a) (Ψ t) :=
    fun a t => commute_rootPairE7_theta_of_mem_e7D6Group (hρr ▸ ⟨a, rfl⟩) (hrange ▸ ⟨t, rfl⟩)
  haveI : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  haveI : Finite (spinGroup (Spin.quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcen5 := not_dvd_card_center_spinPlus (K := K) hn3 (p := 5) (by norm_num) hpq1
  let ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hψker : ¬ 5 ∣ Nat.card ψ.ker :=
    not_dvd_card_ker_noncommCoprod (by norm_num) ρ hρi Ψ hcomm hker hcen5
  obtain ⟨g, hg⟩ := exists_conj_le_range_of_sylow_E7_five hpq ψ hψker E₀ hE₀p
  set E := E₀.map (MulAut.conj g).toMonoidHom with hE
  have hEp : ∀ x ∈ E, x ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hE₀p y hy]
    group
  have hEc : Nat.card E = 5 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ ψ.range := hg
  set ψ' : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* ψ.range := ψ.rangeRestrict with hψ'
  have hψ'surj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hψ'ker : ψ'.ker = ψ.ker := ψ.ker_rangeRestrict
  set E1 : Subgroup ψ.range := E.subgroupOf ψ.range with hE1def
  have hE1 : IsElemAbelian 5 E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker ψ' hψ'surj (hψ'ker ▸ hψker) hE1
  have hcardE1 : Nat.card E1 = 5 ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = 5 ^ 2 := by
    rw [← card_map_eq_of_disjoint_ker ψ' hdisE', hmapE', hcardE1]
  have hlift : ∀ ε ∈ E, ∃ e ∈ E', ψ e = ε := by
    intro ε hε
    have : (⟨ε, hE_le hε⟩ : ψ.range) ∈ E1 := hε
    rw [← hmapE'] at this
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, he, congrArg Subtype.val hee⟩
  set E₁ : Subgroup SL(2, K) := E'.map (MonoidHom.fst _ _) with hE₁def
  set E₂ : Subgroup (spinGroup (Spin.quadPlus 6 K)) := E'.map (MonoidHom.snd _ _) with hE₂def
  have hE₁ea : IsElemAbelian 5 E₁ := hE'ea.map _
  have hE₂ea : IsElemAbelian 5 E₂ := hE'ea.map _
  have hcard₁ : Nat.card E₁ ≤ 5 := card_le_of_isElemAbelian_specialLinear_two hpK0 hE₁ea
  have hE₂card : Nat.card E₂ = 5 ∨ Nat.card E₂ = 5 ^ 2 := by
    have hpg : IsPGroup 5 E₂ := fun x => ⟨1, Subtype.ext (by simpa using hE₂ea.2 x x.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
    have hle2 : Nat.card E₂ ≤ 5 ^ 2 := hcardE' ▸ card_map_le _ E'
    have hge : 5 ^ 2 ≤ 5 * Nat.card E₂ := by
      have := card_le_card_map_prod E'
      rw [hcardE'] at this
      exact this.trans (Nat.mul_le_mul_right _ hcard₁)
    rw [hn] at hle2 hge ⊢
    have hn2 : n ≤ 2 := by
      by_contra h
      have : 5 ^ 3 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hn1 : 1 ≤ n := by
      by_contra h
      have : n = 0 := by omega
      subst this
      norm_num at hge
    interval_cases n
    · left; norm_num
    · right; rfl
  have hNS : ∀ T : Submodule K (Fin 6 ⊕ Fin 6 → K),
      (∀ e ∈ E₂, ∀ v ∈ T, spinAction (Spin.quadPlus 6 K) e v ∈ T) →
      (∀ v ∈ T, Spin.quadPlus 6 K v = 0) → T = ⊥ := by
    intro T hTi hTs
    by_contra hT0
    obtain ⟨U, hU0, hUp, hUn⟩ :=
      exists_rGroup_normalized_of_invariant_singular_charTwo hn3 E₂ T hT0 hTs hTi
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    have hcenr : ¬ ringChar K ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 6 K))) := by
      rw [hchar2]
      exact not_dvd_card_center_spinPlus_charTwo hn3
    have hV0 := map_ne_bot_of_central_kernel Ψ hker hcenr hU0 hUp
    apply hN
    refine normalizesRGroup_of_map_conj g ⟨U.map Ψ, hV0, hUp.map Ψ, ?_⟩
    rintro ε hε
    obtain ⟨⟨a, s⟩, he, rfl⟩ := hlift ε hε
    have hs : s ∈ E₂ := ⟨(a, s), he, rfl⟩
    have hψe : ψ (a, s) = ρ a * Ψ s := rfl
    rw [hψe, map_conj_mul, ← map_conj_map Ψ s U, hUn s hs]
    exact map_conj_eq_of_commute _ _ (by
      rintro _ ⟨u, -, rfl⟩
      exact hcomm a u)
  have hfr : ∃ x : spinGroup (Spin.quadPlus 6 K), ∀ e ∈ E₂,
      x * e * x⁻¹ ∈ spinFrameGroup 6 K hn3 ι6 := by
    rcases hE₂card with h5 | h25
    ·
      haveI : Nontrivial E₂ := Finite.one_lt_card_iff_nontrivial.mp (by rw [h5]; norm_num)
      obtain ⟨b', hb'⟩ := exists_ne (1 : E₂)
      set b : spinGroup (Spin.quadPlus 6 K) := (b' : spinGroup (Spin.quadPlus 6 K)) with hbdef
      have hbE : b ∈ E₂ := b'.2
      have hb5 : b ^ 5 = 1 := hE₂ea.2 b hbE
      have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
      have hord5 : orderOf b = 5 := orderOf_eq_prime hb5 hb1
      have hzp : Subgroup.zpowers b = E₂ := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact hbE
        · rw [Nat.card_zpowers, hord5, h5]
      have hmem : ∀ e ∈ E₂, ∃ i : ℕ, b ^ i = e := fun e he => by
        rw [← hzp] at he
        exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr he)
      have hNSb : ∀ T : Submodule K (Fin 6 ⊕ Fin 6 → K),
          (∀ v ∈ T, spinAction (Spin.quadPlus 6 K) b v ∈ T) →
          (∀ v ∈ T, Spin.quadPlus 6 K v = 0) → T = ⊥ := by
        intro T hTb hTs
        refine hNS T (fun e he v hv => ?_) hTs
        obtain ⟨i, rfl⟩ := hmem e he
        rw [map_pow]
        exact OrthBlk.pow_apply_mem hTb i v hv
      obtain ⟨x, hx⟩ := exists_spin_conj_frameGroup_cyclic_charTwo hn3 (k := 3) (by norm_num) ι6
        hp5p (by norm_num) hpl hord b hb5 hNSb
      refine ⟨x, fun e he => ?_⟩
      obtain ⟨i, rfl⟩ := hmem e he
      rw [← conj_pow]
      exact pow_mem hx i
    · exact exists_spin_conj_frameGroup_charTwo hn3 (k := 3) (by norm_num) ι6 hp5p (by norm_num)
        hpl hord E₂ hE₂ea.2 h25 hNS
  obtain ⟨x, hx⟩ := hfr
  refine ⟨Ψ x * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨⟨a, s⟩, he, hee⟩ := hlift (g * z * g⁻¹) ⟨z, hz, rfl⟩
  have hs : s ∈ E₂ := ⟨(a, s), he, rfl⟩
  have h1 : Ψ (x * s * x⁻¹) ∈ e7FrameGroup K :=
    map_spinFrameGroup_le_e7 hn3 hrank hweyl ⟨_, hx s hs, rfl⟩
  have h2 : ρ a ∈ e7FrameGroup K := rootPairE7_theta_le_e7FrameGroup (hρr ▸ ⟨a, rfl⟩)
  have hee' : ρ a * Ψ s = g * z * g⁻¹ := hee
  have key : (Ψ x * g) * z * (Ψ x * g)⁻¹ = ρ a * Ψ (x * s * x⁻¹) := by
    have h3 : (Ψ x * g) * z * (Ψ x * g)⁻¹ = Ψ x * (g * z * g⁻¹) * (Ψ x)⁻¹ := by group
    rw [h3, ← hee', map_mul, map_mul, map_inv]
    have hc : Ψ x * ρ a = ρ a * Ψ x := (hcomm a x).symm.eq
    calc Ψ x * (ρ a * Ψ s) * (Ψ x)⁻¹ = (Ψ x * ρ a) * Ψ s * (Ψ x)⁻¹ := by group
      _ = ρ a * (Ψ x * Ψ s * (Ψ x)⁻¹) := by rw [hc]; group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [key]
  exact (e7FrameGroup K).mul_mem h2 h1

end Main

end S3

section S4
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups

section Glue

theorem e7TwoSylowFiveEven : E7TwoSylowFiveEven := fun K _ _ hev hpq E₀ hE₀p hE₀c hN =>
  e7_conj_into_frame_five_even hev hpq E₀ hE₀p hE₀c hN

theorem e7TwoSylowFive : E7TwoSylowFive := e7TwoSylowFive_of_even e7TwoSylowFiveEven

@[expose] def SeitzExcHighE7TwoSeven : Prop :=
  SeitzExcHighForAt IsE7Index fun d p => p = 7 ∧ ClassRange LieTypeIndex.E7 (fun _ => True) 2 d p

theorem seitzExcHighE7TwoFive : SeitzExcHighForAt IsE7Index fun d p => p = 5 ∧ ClassRange LieTypeIndex.E7 (fun _ => True) 2 d p := by
  refine seitzExcHighE7Two_of_native_for (R := fun p => p = 5) ?_
  intro K _ _ p hpF hp5 hR hpq E₀ hE₀p hE₀c hN
  subst hR
  exact closure_centralizers_eq_top_of_conj_frame
    (fun E hE hEp hEc => e7A1D6_le_closure_centralizers_two hpF.out hp5 hpq E hE hEp hEc)
    E₀ hE₀p hE₀c (e7TwoSylowFive K hpq E₀ hE₀p hE₀c hN)

theorem seitzExcHighE7TwoLtEleven_of_seven (h : SeitzExcHighE7TwoSeven) :
    SeitzExcHighE7TwoLtEleven :=
  SeitzExcHighForAt.union (fun d p hp _ hQ => by
    obtain ⟨hlt, hcr⟩ := hQ
    have hp5 : 5 ≤ p := hcr.1
    have h7 : p = 5 ∨ p = 7 := by
      interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)
    rcases h7 with rfl | rfl
    · exact Or.inl ⟨rfl, hcr⟩
    · exact Or.inr ⟨rfl, hcr⟩) seitzExcHighE7TwoFive h

theorem seitzExcHighE7Two_of_seven (h : SeitzExcHighE7TwoSeven) : SeitzExcHighE7Two :=
  seitzExcHighE7Two_of_ge_eleven_of_lt (seitzExcHighE7TwoLtEleven_of_seven h)

end Glue

end S4

end CFSG.LieType.SeitzGeneration.ExcHigh
