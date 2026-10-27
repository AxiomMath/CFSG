module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2Toral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh TauCeti
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes

section Transport

theorem normalizesRGroup_of_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {r : ℕ}
    {E₀ : Subgroup G} (h : NormalizesRGroup r (E₀.map e.toMonoidHom)) : NormalizesRGroup r E₀ := by
  obtain ⟨U, hU0, hUp, hUn⟩ := h
  refine ⟨U.map e.symm.toMonoidHom, ?_, hUp.map _, fun x hx => ?_⟩
  · intro hbot
    apply hU0
    have h1 := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) hbot
    simp only [Subgroup.map_map, Subgroup.map_bot] at h1
    have h2 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext y
      simp
    rw [h2, Subgroup.map_id] at h1
    exact h1
  · have hU := hUn (e x) ⟨x, hx, rfl⟩
    have h1 := congrArg (fun S : Subgroup H => S.map e.symm.toMonoidHom) hU
    simp only [Subgroup.map_map] at h1
    rw [Subgroup.map_map]
    rw [← h1]
    congr 1
    ext y
    simp [MulAut.conj_apply]

end Transport

section Classes

set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge CFSG.AGLEmbeddingD2

section E7Five

variable {K : Type} [Field K] [Finite K]

theorem e7_conj_into_frame_five_elem (hpq : 5 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀ : IsElemAbelian 5 E₀)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5p : (5 : ℕ).Prime := Nat.prime_five
  have hord := orderOf_eq_two_of_dvd_add_one hp5p (by norm_num) hpq
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp5p hpq
  have hpq1 := not_dvd_pred_of_dvd_add_one hp5p (by norm_num) hpq
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hpl : 5 ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self 5 m.ne_zero
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
  obtain ⟨g, hg⟩ := exists_conj_le_range_of_sylow_E7_five hpq ψ hψker E₀ hE₀.2
  set E := E₀.map (MulAut.conj g).toMonoidHom with hE
  have hEa : IsElemAbelian 5 E := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE₀ _
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE_le : E ≤ ψ.range := hg
  set ψ' : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* ψ.range := ψ.rangeRestrict with hψ'
  have hψ'surj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hψ'ker : ψ'.ker = ψ.ker := ψ.ker_rangeRestrict
  set E1 : Subgroup ψ.range := E.subgroupOf ψ.range with hE1def
  have hE1 : IsElemAbelian 5 E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEa.2 x hx)⟩
  obtain ⟨E', hmapE', -, hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker ψ' hψ'surj (hψ'ker ▸ hψker) hE1
  have hlift : ∀ ε ∈ E, ∃ e ∈ E', ψ e = ε := by
    intro ε hε
    have : (⟨ε, hE_le hε⟩ : ψ.range) ∈ E1 := hε
    rw [← hmapE'] at this
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, he, congrArg Subtype.val hee⟩
  set E₂ : Subgroup (spinGroup (Spin.quadPlus 6 K)) := E'.map (MonoidHom.snd _ _) with hE₂def
  have hE₂ea : IsElemAbelian 5 E₂ := hE'ea.map _
  have hE₂comm : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₂ea.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hNS : ∀ T : Submodule K (Fin 6 ⊕ Fin 6 → K),
      (∀ e ∈ E₂, ∀ v ∈ T, spinAction (Spin.quadPlus 6 K) e v ∈ T) →
      (∀ v ∈ T, Spin.quadPlus 6 K v = 0) → T = ⊥ := by
    intro T hTi hTs
    by_contra hT0
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    obtain ⟨U, hU0, hUp, hUn⟩ : ∃ U : Subgroup (spinGroup (Spin.quadPlus 6 K)), U ≠ ⊥ ∧
        IsPGroup (ringChar K) U ∧ ∀ e ∈ E₂, U.map (MulAut.conj e).toMonoidHom = U := by
      rcases Nat.even_or_odd (Nat.card K) with hev | hodd
      · have hchar2 : ringChar K = 2 := by
          have heven : Even (Fintype.card K) := by
            rw [← Nat.card_eq_fintype_card]
            exact hev
          exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
        haveI : CharP K 2 := ringChar.of_eq hchar2
        exact exists_rGroup_normalized_of_invariant_singular_charTwo hn3 E₂ T hT0 hTs hTi
      · exact exists_rGroup_normalized_of_invariant_singular hodd hn3 E₂ T hT0 hTs hTi
    have hcenr : ¬ ringChar K ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 6 K))) := by
      rcases Nat.even_or_odd (Nat.card K) with hev | hodd
      · have hchar2 : ringChar K = 2 := by
          have heven : Even (Fintype.card K) := by
            rw [← Nat.card_eq_fintype_card]
            exact hev
          exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
        haveI : CharP K 2 := ringChar.of_eq hchar2
        rw [hchar2]
        exact not_dvd_card_center_spinPlus_charTwo hn3
      · have hr2 : ringChar K ≠ 2 := by
          intro h2
          have : Even (Nat.card K) := by
            rw [hK, h2]
            exact (Nat.even_pow.mpr ⟨even_two, m.ne_zero⟩)
          exact (Nat.not_even_iff_odd.mpr hodd) this
        have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
          intro hd
          have hq1 : 1 ≤ Nat.card K := Nat.card_pos
          have h1 : ringChar K ∣ Nat.card K := by
            rw [hK]
            exact dvd_pow_self _ m.ne_zero
          have h2 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
          have e : Nat.card K - (Nat.card K - 1) = 1 := by omega
          rw [e] at h2
          exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
        exact not_dvd_card_center_spinPlus (K := K) hn3 hr2 hrq1
    have hV0 := map_ne_bot_of_central_kernel Ψ hker hcenr hU0 hUp
    apply hN
    refine normalizesRGroup_of_map_conj g ⟨U.map Ψ, hV0, hUp.map Ψ, ?_⟩
    rintro ε hε
    obtain ⟨⟨a, s⟩, he, rfl⟩ := hlift ε hε
    have hs : s ∈ E₂ := ⟨(a, s), he, rfl⟩
    have hψe : ψ (a, s) = ρ a * Ψ s := rfl
    rw [hψe, ExcHigh.map_conj_mul, ← map_conj_map Ψ s U, hUn s hs]
    exact map_conj_eq_of_commute _ _ (by
      rintro _ ⟨u, -, rfl⟩
      exact hcomm a u)
  have hfr : ∃ x : spinGroup (Spin.quadPlus 6 K), ∀ e ∈ E₂,
      x * e * x⁻¹ ∈ spinFrameGroup 6 K hn3 ι6 := by
    rcases Nat.even_or_odd (Nat.card K) with hev | hodd
    · have hchar2 : ringChar K = 2 := by
        have heven : Even (Fintype.card K) := by
          rw [← Nat.card_eq_fintype_card]
          exact hev
        exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
      haveI : CharP K 2 := ringChar.of_eq hchar2
      exact exists_spin_conj_frameGroup_elem_charTwo hn3 (k := 3) (by norm_num) ι6 hp5p le_rfl
        hpl hord E₂ hE₂comm hE₂ea.2 hNS
    · exact exists_spin_conj_frameGroup_elem hodd hn3 (k := 3) (by norm_num) ι6 hp5p le_rfl hpl
        hord E₂ hE₂comm hE₂ea.2 hNS
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

theorem hyperGen_adjoint_E7_two_five (K : Type) [Field K] [Finite K] (hpq : 5 ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian 5 E → Nat.card E = 5 ^ 3 → HyperGen 5 ⊤ E)
    {E₀ : Subgroup (adjointGroup .E7 K)} (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) : HyperGen 5 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact hyperGen_of_two_conj (e7A1D6 K) (e7FrameGroup K) (weylWordElt .E7 K e7Word)
    e7FrameGroup_le_e7A1D6 e7FrameGroup_le_conj_e7A1D6
    (fun M hX hn => eq_top_of_e7A1D6_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => e7A1D6_le_hyperClosure Nat.prime_five le_rfl hpq hcube E hE hEa hEc)
    hE₀ hc (e7_conj_into_frame_five_elem hpq E₀ hE₀ hN)

end E7Five

section E8Seven

variable {K : Type} [Field K] [Finite K]

theorem e8_conj_into_frame_seven_elem (hpq : 7 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀ : IsElemAbelian 7 E₀)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : (7 : ℕ).Prime := by norm_num
  have hodd := odd_card_of_seven_dvd_add_one hpq
  have hord := orderOf_eq_two_of_dvd_add_one hp7 (by norm_num) hpq
  have hpK : ¬ 7 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp7 hpq
  have hpq1 := not_dvd_pred_of_dvd_add_one hp7 (by norm_num) hpq
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hpl : 7 ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self 7 m.ne_zero
  have hn3 : 3 ≤ 8 := by norm_num
  obtain ⟨Ψ, hker, hrange, hrank, hweyl⟩ := exists_psi_D8_param K hn3
  obtain ⟨g, hg⟩ := exists_conj_le_range_of_sylow_E8_seven hpq Ψ hker E₀ hE₀.2
  set E := E₀.map (MulAut.conj g).toMonoidHom with hE
  have hEa : IsElemAbelian 7 E := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 7 hE₀ _
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  haveI : Finite (spinGroup (Spin.quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcen7 := not_dvd_card_center_spinPlus (K := K) hn3 (p := 7) (by norm_num) hpq1
  have hΨcop : ¬ 7 ∣ Nat.card Ψ.ker := fun hd => hcen7 (hd.trans (Subgroup.card_dvd_of_le hker))
  have hE_le : E ≤ Ψ.range := hg
  set Ψ' : spinGroup (Spin.quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian 7 E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEa.2 x hx)⟩
  obtain ⟨E', hmapE', -, hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE'ea.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hlift : ∀ ε ∈ E, ∃ e ∈ E', Ψ e = ε := by
    intro ε hε
    have : (⟨ε, hE_le hε⟩ : Ψ.range) ∈ E1 := hε
    rw [← hmapE'] at this
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, he, congrArg Subtype.val hee⟩
  have hNS : ∀ T : Submodule K (Fin 8 ⊕ Fin 8 → K),
      (∀ e ∈ E', ∀ v ∈ T, spinAction (Spin.quadPlus 8 K) e v ∈ T) →
      (∀ v ∈ T, Spin.quadPlus 8 K v = 0) → T = ⊥ := by
    intro T hTi hTs
    by_contra hT0
    obtain ⟨U, hU0, hUp, hUn⟩ :=
      exists_rGroup_normalized_of_invariant_singular hodd hn3 E' T hT0 hTs hTi
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    have hr2 : ringChar K ≠ 2 := by
      intro h2
      have : Even (Nat.card K) := by
        rw [hK, h2]
        exact (Nat.even_pow.mpr ⟨even_two, m.ne_zero⟩)
      exact (Nat.not_even_iff_odd.mpr hodd) this
    have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
      intro hd
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      have h1 : ringChar K ∣ Nat.card K := by
        rw [hK]
        exact dvd_pow_self _ m.ne_zero
      have h2 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
      have e : Nat.card K - (Nat.card K - 1) = 1 := by omega
      rw [e] at h2
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
    have hcenr := not_dvd_card_center_spinPlus (K := K) hn3 hr2 hrq1
    have hV0 := map_ne_bot_of_central_kernel Ψ hker hcenr hU0 hUp
    apply hN
    refine normalizesRGroup_of_map_conj g ⟨U.map Ψ, hV0, hUp.map Ψ, ?_⟩
    rintro ε hε
    obtain ⟨e, he, rfl⟩ := hlift ε hε
    rw [← map_conj_map Ψ e U, hUn e he]
  obtain ⟨x, hx⟩ := exists_spin_conj_frameGroup_elem hodd hn3 (k := 4) (by norm_num) ιstd hp7
    (by norm_num) hpl hord E' hE'comm hE'ea.2 hNS
  refine ⟨Ψ x * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨e, he, hee⟩ := hlift (g * z * g⁻¹) ⟨z, hz, rfl⟩
  have h1 : Ψ (x * e * x⁻¹) ∈ e8FrameGroup K :=
    map_spinFrameGroup_le hn3 hrank hweyl ⟨_, hx e he, rfl⟩
  have h2 : Ψ (x * e * x⁻¹) = Ψ x * (g * z * g⁻¹) * (Ψ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hee]
  rw [h2] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  simpa [mul_assoc] using h1

theorem hyperGen_adjoint_E8_two_seven (K : Type) [Field K] [Finite K] (hpq : 7 ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K))),
      IsElemAbelian 7 E → Nat.card E = 7 ^ 3 → HyperGen 7 ⊤ E)
    {E₀ : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian 7 E₀) (hc : Nat.card E₀ = 7 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) : HyperGen 7 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hpq1 : ¬ 7 ∣ Nat.card K - 1 := not_dvd_pred_of_dvd_add_one (by norm_num) (by norm_num) hpq
  exact hyperGen_of_two_conj (⨆ k, e8D8Chain K k) (e8FrameGroup K) (weylWordElt .E8 K e8Word)
    e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_d8Chain_le_hyperClosure (by norm_num) (by norm_num) hpq1 hcube Ψ
      hker hrange E hE hEa hEc)
    hE₀ hc (e8_conj_into_frame_seven_elem hpq E₀ hE₀ hN)

end E8Seven

section Cat

theorem hyperGen_E7_two_five {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid)
    (h2 : orderOf ((q.card : ℕ) : ZMod 5) = 2)
    {E₀ : Subgroup (Cat ⟨.E7 q, hv⟩)} (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3)
    (hN : ¬ NormalizesRSub ⟨.E7 q, hv⟩ E₀) : HyperGen 5 ⊤ E₀ := by
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpq : 5 ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two Nat.prime_five h2
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one Nat.prime_five hpq
  refine hyperGen_of_mulEquiv e ?_
  refine hyperGen_adjoint_E7_two_five K hpq (fun E hE hEc =>
    SeitzExcOpenRest.plusModel_cubes_of_orthTwo seitzGoodInnerOrthTwo_holds (by norm_num)
      Nat.prime_five le_rfl hpK E hE hEc)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc]) ?_
  intro hN'
  apply hN
  have h1 := normalizesRGroup_of_map_mulEquiv e hN'
  have hr : ringChar K = (LieTypeIndex.E7 q).characteristic := by
    rw [ringChar.eq K q.p, LieTypeIndex.characteristic_E7]
  rw [hr] at h1
  exact h1

theorem hyperGen_E8_two_seven {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid)
    (h2 : orderOf ((q.card : ℕ) : ZMod 7) = 2)
    {E₀ : Subgroup (Cat ⟨.E8 q, hv⟩)} (hE₀ : IsElemAbelian 7 E₀) (hc : Nat.card E₀ = 7 ^ 3)
    (hN : ¬ NormalizesRSub ⟨.E8 q, hv⟩ E₀) : HyperGen 7 ⊤ E₀ := by
  have hp7 : (7 : ℕ).Prime := by norm_num
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpq : 7 ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp7 h2
  have hpK : ¬ 7 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp7 hpq
  refine hyperGen_of_mulEquiv e ?_
  refine hyperGen_adjoint_E8_two_seven K hpq (fun E hE hEc =>
    SeitzExcOpenRest.plusModel_cubes_of_orthTwo seitzGoodInnerOrthTwo_holds (by norm_num)
      hp7 (by norm_num) hpK E hE hEc)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 7 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc]) ?_
  intro hN'
  apply hN
  have h1 := normalizesRGroup_of_map_mulEquiv e hN'
  have hr : ringChar K = (LieTypeIndex.E8 q).characteristic := by
    rw [ringChar.eq K q.p, LieTypeIndex.characteristic_E8]
  rw [hr] at h1
  exact h1

end Cat

end Classes

@[expose] def ExcCubeOpenRest2 (d : LieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∨ ∃ q : PrimePower,
    (d = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 2 ∧ p = 7) ∨
    (d = .E8 q ∧ p = 5 ∧ (orderOf ((q.card : ℕ) : ZMod p) = 2 ∨
      orderOf ((q.card : ℕ) : ZMod p) = 4 ∨ orderOf ((q.card : ℕ) : ZMod p) = 1))

@[expose] def SeitzGoodInnerExcOpenRest2 : Prop :=
  SeitzHyperLie fun d p E₀ => IsTopIndex d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    ExcCubeOpenRest2 d.1 p

section Assembly

set_option linter.unusedSectionVars false

theorem eq_five_or_seven_of_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hlt : p < 11) : p = 5 ∨ p = 7 := by
  have := hp.two_le
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

theorem seitzGoodInnerExcOpenRest_of_rest2 (hrest : SeitzGoodInnerExcOpenRest2) :
    SeitzExcOpenRest.SeitzGoodInnerExcOpenRest := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, hopen⟩
  by_cases hr : ExcCubeOpenRest2 d.1 p
  · exact hrest d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, hr⟩
  have hp3 : p ≠ 3 := fun h => hr (Or.inl h)
  obtain ⟨d, hv⟩ := d
  rcases hopen with h3 | ⟨q, ⟨hd, h2, hlt⟩ | ⟨hd, hcase⟩⟩
  · exact absurd h3 hp3
  · simp only at hd
    subst hd
    rcases eq_five_or_seven_of_lt hp hp2 hp3 hlt with rfl | rfl
    · exact hyperGen_E7_two_five hv h2 hE₀ hcard hN
    · exact absurd (Or.inr ⟨q, Or.inl ⟨rfl, h2, rfl⟩⟩) hr
  · simp only at hd
    subst hd
    rcases hcase with ⟨h2, hlt⟩ | ⟨h4, h5⟩ | ⟨h5, h1⟩
    · rcases eq_five_or_seven_of_lt hp hp2 hp3 hlt with rfl | rfl
      · exact absurd (Or.inr ⟨q, Or.inr ⟨rfl, rfl, Or.inl h2⟩⟩) hr
      · exact hyperGen_E8_two_seven hv h2 hE₀ hcard hN
    · exact absurd (Or.inr ⟨q, Or.inr ⟨rfl, h5, Or.inr (Or.inl h4)⟩⟩) hr
    · exact absurd (Or.inr ⟨q, Or.inr ⟨rfl, h5, Or.inr (Or.inr h1)⟩⟩) hr

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2
