module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311i
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveMain

public section

open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311i

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.Chevalley.E6GraphLevi TauCeti CFSG.Open
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen UniSeitzPlanes)

section SU6

theorem uniClosure_unitarySL_eq_top_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1) (F : Subgroup (unitarySL σ))
    (hF : IsElemAbelian p F) (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {g : unitarySL σ | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ n : ℕ, g ^ (2 ^ n) = 1} =
      ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  set e := TwSU6.unitarySLEquivStated (p := 2) hK hσ with he
  have hq : 2 ^ f ≠ 2 := by
    intro h2
    rw [h2] at hpq
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  have hcomm : ∀ x ∈ F.map e.toMonoidHom, ∀ y ∈ F.map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hexp : ∀ x ∈ F.map e.toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF.2 x hx, map_one]
  have hcard : Nat.card (F.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hc]
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d.uniClosure_unitarySU_of_dvd_add_one
    (n := 5) hU hp hpq hq (F.map e.toMonoidHom) hcomm hexp hcard
  rw [ringChar.eq K 2] at h
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective, MonoidHom.map_closure] at hmap
  rw [eq_top_iff, ← hmap, Subgroup.closure_le]
  rintro _ ⟨g, ⟨_, ⟨x, hx, rfl⟩, hx1, hgx, hg2⟩, rfl⟩
  refine Subgroup.subset_closure ⟨x, hx, fun h1 => hx1 (by rw [h1, map_one]), ?_, 1, ?_⟩
  · have h1 : e.symm g * e.symm (e x) = e.symm (e x) * e.symm g := by
      rw [← map_mul, ← map_mul]
      exact congrArg _ hgx
    show e.symm g * x = x * e.symm g
    simpa using h1
  · rw [pow_one]
    change e.symm g ^ 2 = 1
    rw [← map_pow, hg2, map_one]

end SU6

section TwE6Two

set_option linter.unusedSectionVars false

theorem twE6TwoUniNative_even (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} [hpF : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1) (E₀ : Subgroup ↥(twistedE6RootGroup K σ))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, hK'⟩
  haveI : CharP K 2 := hU.charP
  set σ' : K →+* K := σ.toRingHom with hσ'def
  have hσ' : ∀ c, σ' c = c ^ (2 ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) = 2 ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK hσ'
  have hq2 : 2 ≤ 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
  have hpk : ¬ p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) := by
    rw [hkcard]
    intro h
    have h1 : p ∣ 2 ^ f + 1 - 2 ^ f := Nat.dvd_sub hpq h
    rw [show 2 ^ f + 1 - 2 ^ f = 1 by omega] at h1
    exact hpF.out.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpk1 : ¬ p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) - 1 := by
    rw [hkcard]
    intro h
    have h1 : p ∣ 2 ^ f + 1 - (2 ^ f - 1) := Nat.dvd_sub hpq h
    rw [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hp3 : p ≠ 3 := by omega
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ψ₁, hk₁, -, hX₁⟩ := TwFive.twE6SU6Cover_five K σ 2 f Nat.prime_two hf hK hσ p hp5 hpq
  obtain ⟨Ψ, hΨker, hΨrange⟩ := exists_psi_d4 Nat.prime_two hf σ' hkcard
  haveI := finite_spinPlus_four (RingHom.eqLocusField σ' (RingHom.id K))
  have hcen := not_dvd_card_center_spinPlus_four hpF.out hp5 hpk1
  have hcomm : ∀ t x, Commute (torusG σ' t) (Ψ x) := fun t x => by
    have hmem : Ψ x ∈ d4Group σ' := by
      rw [d4Group, ← hΨrange]
      exact ⟨x, rfl⟩
    exact torusG_commute_d4Group σ' t (Ψ x) hmem
  set ψ₂ := MonoidHom.noncommCoprod (torusG σ') Ψ hcomm with hψ₂
  have hk₂ : ¬ p ∣ Nat.card ψ₂.ker :=
    not_dvd_card_ker_noncommCoprod_tw hpF.out _ _ hcomm (not_dvd_card_ker_torusG σ' hpF.out hp3) hΨker
      hcen
  have hdr : d4Group σ' ≤ ψ₂.range := by
    rw [d4Group, ← hΨrange]
    rintro _ ⟨x, rfl⟩
    refine ⟨(1, x), ?_⟩
    change torusG σ' 1 * Ψ x = Ψ x
    rw [map_one, one_mul]
  have htr : (torusG σ').range ≤ ψ₂.range := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(t, 1), ?_⟩
    change torusG σ' t * Ψ 1 = torusG σ' t
    rw [map_one, mul_one]
  have hP₂ : frameTorusGroup σ' ≤ ψ₂.range := by
    refine sup_le (iSup_le fun i => ?_) htr
    fin_cases i
    · exact (le_iSup (fun i => (d4Rho σ' i).range) 0).trans hdr
    · exact (le_iSup (fun i => (d4Rho σ' i).range) 2).trans hdr
    · exact (le_iSup (fun i => (d4Rho σ' i).range) 3).trans hdr
    · exact (frameHom_three_le_d4Group σ').trans hdr
  have hP₁ : frameTorusGroup σ' ≤ ψ₁.range := le_sup_left.trans hX₁
  obtain ⟨g, hg⟩ : ∃ g : ↥(twistedE6RootGroup K σ),
      E₀.map (MulAut.conj g).toMonoidHom ≤ frameTorusGroup σ' := by
    rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with rfl | rfl | hp7
    ·
      obtain ⟨e₂⟩ := TwFive.exists_mulEquiv_sl2_su2 (K := K) hK σ' hσ'
      let θ : SL(2, RingHom.eqLocusField σ' (RingHom.id K)) × unitarySL σ' ≃*
          CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K 2 ×
            CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K 6 :=
        e₂.prodCongr (TwSU6.unitarySLEquivStated hK hσ')
      obtain ⟨Ew, hEwe, hEwc, hEwle⟩ := TwFive.exists_elemAbelian_six Nat.prime_two hf K hK σ hσ hpq
      have hEwr : Ew ≤ ψ₁.range := hEwle.trans hP₁
      obtain ⟨Ew', hEw'e, hEw'm, hEw'c⟩ := TwFive.exists_lift_of_le_range ψ₁ hk₁ hEwr hEwe
      have hord := TwFive.five_hord Nat.prime_two hf hK σ hσ hpq
      have hcomm₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
        intro a ha b hb
        let _ : CommGroup E₀ := IsPGroup.commGroupOfCardEqPrimeSq hE₀c
        exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E₀) ⟨b, hb⟩)
      have hE₀e : IsElemAbelian 5 E₀ :=
        ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm₀ a a.2 b b.2), hE₀p⟩
      obtain ⟨g, E', hE'e, hE'm⟩ := TwFive.exists_conj_lift_elemAbelian ψ₁ hk₁ hord E₀ hE₀e
      obtain ⟨c, hc⟩ := TwFive.exists_conj_le_toral_of_equiv hU hpq θ Ew' hEw'e (hEw'c.trans hEwc) E'
        hE'e
      refine ⟨(ψ₁ c)⁻¹ * g, ?_⟩
      rintro y ⟨e, he, rfl⟩
      have h1 : g * e * g⁻¹ ∈ E₀.map (MulAut.conj g).toMonoidHom :=
        ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      rw [← hE'm] at h1
      obtain ⟨y', hy', hy'e⟩ := h1
      obtain ⟨z, hz, hzy⟩ := hc hy'
      have hzψ : ψ₁ z ∈ Ew := hEw'm ▸ ⟨z, hz, rfl⟩
      have hψ : g * e * g⁻¹ = ψ₁ c * ψ₁ z * (ψ₁ c)⁻¹ := by
        rw [← hy'e, ← hzy]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      have hconj : (MulAut.conj ((ψ₁ c)⁻¹ * g)).toMonoidHom e = ψ₁ z := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
        calc (ψ₁ c)⁻¹ * g * e * (g⁻¹ * ψ₁ c) = (ψ₁ c)⁻¹ * (g * e * g⁻¹) * ψ₁ c := by group
          _ = ψ₁ z := by rw [hψ]; group
      rw [hconj]
      exact hEwle hzψ
    · exact absurd hpF.out (by norm_num)
    · have hpq' : p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) + 1 := by
        rw [hkcard]
        exact hpq
      exact exists_conj_le_frame_torus (frameHom σ') (frameHom_injective σ')
        (fun i j hij A B => frameHom_commute σ' hij A B) (torusG σ').range
        (fun a ha i y => by
          obtain ⟨t, rfl⟩ := ha
          exact torusG_commute_frame _ (frameHom_mem_rootPair σ') t i y)
        hp5 hpq' (factorization_card_le_frame_torusG Nat.prime_two hf K hK σ hσ hpF.out hp7 hpq) E₀ hE₀p
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  set M := Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} with hM
  have hpk0 := natCast_ne_zero_of_not_dvd_card hpF.out hpk
  have hBr₁ : Subgroup.closure {b : unitarySL σ' | ∃ n : ℕ, b ^ (2 ^ n) = 1} = ⊤ := by
    haveI := TwSU6.isPerfect_unitarySL_gen (p := 2) hK hσ'
    exact closure_two_pow_eq_top_of_isPerfect
  have hH₁ : ∀ F : Subgroup (SL(2, RingHom.eqLocusField σ' (RingHom.id K)) × unitarySL σ'),
      IsElemAbelian p F → Nat.card F = p ^ 2 →
        Subgroup.closure {h | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (2 ^ n) = 1} = ⊤ :=
    fun F hF hc => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_uniCen_prod_of_plane
      (fun F' hF' => card_le_of_isElemAbelian_specialLinear_two hpk0 hF')
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_two_pow_SL_eq_top 2 _) hBr₁
      (fun F' hF' hc' => uniClosure_unitarySL_eq_top_even hf hK hσ' hpF.out hp5 hpq F' hF' hc') F hF hc
  have hM₁ : ψ₁.range ≤ M :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.range_le_uniClosure_of_cover ψ₁ hk₁ hH₁ E₁
      (hg.trans hP₁) hE₁p hE₁c
  have hBr₂ : Subgroup.closure {b : spinGroup (Spin.quadPlus 4 (RingHom.eqLocusField σ' (RingHom.id K))) |
      ∃ n : ℕ, b ^ (2 ^ n) = 1} = ⊤ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_two_pow_eq_top_of_isQuasisimple
      (isQuasisimple_spinGroup_quadPlus (by norm_num))
  have hM₂ := map_le_uniClosure_of_cover ψ₂ hk₂ _
    (fun F hF hc => range_inr_le_uniClosure_prod hBr₂
      (fun F' hF' hc' => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_uniCen_spinPlus_even
        (by norm_num) hpF.out hp5 hpk hpk1 F' hF' hc') F hF hc)
    E₁ (hg.trans hP₂) hE₁p hE₁c
  have hd4M : d4Group σ' ≤ M := by
    rw [d4Group, ← hΨrange]
    rintro _ ⟨x, rfl⟩
    have h1 : ψ₂ ((MonoidHom.inr _ _) x) = Ψ x := by
      change torusG σ' 1 * Ψ x = Ψ x
      rw [map_one, one_mul]
    rw [← h1]
    exact hM₂ ⟨(MonoidHom.inr _ _) x, ⟨x, rfl⟩, rfl⟩
  have hX₁' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ'),
      y ∈ leviRootGroups σ' → y ∈ ψ₁.range := fun y hy => hX₁ (Subgroup.mem_sup_right hy)
  refine eq_top_of_orbitRankOneGroup_le M fun a => ?_
  refine le_map_subtype_of_mem (orbitRankOneGroup_le_graphFixedRootGroup' _ _) fun y hy => ?_
  match a, hy with
  | ⟨0, _⟩, hy =>
    exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))))
  | ⟨1, _⟩, hy =>
    exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))))
  | ⟨2, _⟩, hy =>
    exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hy)))
  | ⟨3, _⟩, hy =>
    obtain ⟨A, hA⟩ := orbitRankOneGroup_le_range_rankOneFix σ' orbCenter orbCenter_card hy
    have hyeq : y = centerHom σ' A := Subtype.ext hA.symm
    rw [hyeq]
    exact hd4M (Subgroup.mem_iSup_of_mem 1 ⟨A, rfl⟩)
  | ⟨n + 4, h⟩, _ => exact absurd h (by change ¬ n + 4 < 4; omega)

end TwE6Two

section TwE6TwoCat

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_twE6Two_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ q : PrimePower, d.1 = .twistedE6 q ∧ q.p = 2 ∧ p ∣ q.card + 1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hn, q, hq, hq2, hpq⟩
  obtain rfl : d = .twistedE6 q := hq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  rw [hq2] at hK hσ
  have hpq' : p ∣ 2 ^ q.exponent + 1 := by
    rw [← hq2, ← PrimePower.card_def]
    exact hpq
  show UniPlaneGen (LieTypeIndex.twistedE6 q).characteristic E
  rw [LieTypeIndex.characteristic_twistedE6, hq2]
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := 2) e hinj (fun E₀ h1 h2 _ => twE6TwoUniNative_even K σ q.exponent_pos hK hσ hp5 hpq' E₀
      h1 h2) hE hc hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  exact hn ⟨R, hR1, by rw [LieTypeIndex.characteristic_twistedE6, hq2]; exact hRp, hRn⟩

end TwE6TwoCat

section TwE6ThreeFourCat

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_twE6ThreeFour_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ q : PrimePower, d.1 = .twistedE6 q ∧ q.p = 2 ∧
        (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 4) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hn, q, hq, hq2, hord⟩
  obtain rfl : d = .twistedE6 q := hq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  rw [hq2] at hK hσ
  have hf := q.exponent_pos
  have hord' : orderOf (((2 ^ q.exponent : ℕ)) : ZMod p) = 3 ∨
      orderOf (((2 ^ q.exponent : ℕ)) : ZMod p) = 4 := by
    rw [← hq2, ← PrimePower.card_def]
    exact hord
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2 * q.exponent) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hk : Nat.card (GaloisField 2 q.exponent) = 2 ^ q.exponent := GaloisField.card 2 _ hf.ne'
  obtain ⟨ι₀⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq (ℓ := 2) (f := q.exponent)
    hk hK
  letI : Algebra (GaloisField 2 q.exponent) K := ι₀.toAlgebra
  show UniPlaneGen (LieTypeIndex.twistedE6 q).characteristic E
  rw [LieTypeIndex.characteristic_twistedE6, hq2]
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := 2) e hinj (fun E₀ h1 h2 _ => ?_) hE hc hin ?_
  · rcases hord' with h3 | h4
    · exact twE6ThreeUniNative_of_subfield (k := GaloisField 2 q.exponent) σ hf hk hK hσ hp5 h3 E₀ h1 h2
    · exact twE6FourUniNative_of_subfield (k := GaloisField 2 q.exponent) σ hf hk hK hσ hp5 h4 E₀ h1 h2
  · rintro ⟨R, hR1, hRp, hRn⟩
    exact hn ⟨R, hR1, by rw [LieTypeIndex.characteristic_twistedE6, hq2]; exact hRp, hRn⟩

end TwE6ThreeFourCat

section Residual

open CFSG.LocalAnalysis.GLTheoremB.MovingAround

set_option linter.unusedSectionVars false

@[expose] def Input23_11TwoRest4 : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
    InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
    ((∃ q : PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 3) ∨
      (∃ q : PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∨
      (∃ q : PrimePower, d.1 = .E8 q ∧ (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
        orderOf ((q.card : ℕ) : ZMod p) = 6)) ∨
      (∃ q : PrimePower, d.1 = .twistedE6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∨
      (∃ q : PrimePower, d.1 = .trialityD4 q ∧
        (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1)) ∨
      (IsReeF4Index d.1 ∧ ¬ (p = 5 ∧ d.1 = LieTypeIndex.reeF4 2) ∧ ∃ m : ℕ, d.1 = .reeF4 m ∧
        (p ∣ 2 ^ (2 * m + 1) + 1 ∨ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)))

theorem orderOf_eq_six_of_degCountTw {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (h1 : ¬ p ∣ q - 1)
    (h2 : ¬ p ∣ q + 1) (h3 : orderOf ((q : ℕ) : ZMod p) ≠ 3) (h4 : orderOf ((q : ℕ) : ZMod p) ≠ 4)
    (hdeg : 2 ≤ CFSG.LieType.SeitzGeneration.degCountTw (orderOf ((q : ℕ) : ZMod p))) :
    orderOf ((q : ℕ) : ZMod p) = 6 := by
  have h60 := CFSG.LieType.SeitzGeneration.le_sixty_of_degCountTw_pos
    (e := orderOf ((q : ℕ) : ZMod p)) (by omega)
  have key : ∀ e ≤ 60, 2 ≤ CFSG.LieType.SeitzGeneration.degCountTw e →
      e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  rcases key _ h60 hdeg with he | he | he | he | he
  · exact absurd (Inputs2311h.dvd_sub_one_of_orderOf_eq_one_even hq he) h1
  · exact absurd (Inputs2311h.dvd_add_one_of_orderOf_eq_two_even hp he) h2
  · exact absurd he h3
  · exact absurd he h4
  · exact he

theorem input23_11TwoRest3_of_rest4 (h : Input23_11TwoRest4) : Inputs2311h.Input23_11TwoRest3 := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hch, hp5, hcpf, hin, hn, hcls⟩ := hs
  have hres := fun hcls => h d p hp hp2 hpd hex E hE hc ⟨hch, hp5, hcpf, hin, hn, hcls⟩
  rcases hcls with ⟨q, hq, hq2, hp57⟩ | hE6 | hE7 | hE8 | ⟨q, hq, h1, hdeg⟩ | hD4 | hR
  · exact uniSeitzPlanes_F4Two_fiveSeven_even d p hp hp2 hpd hex E hE hc ⟨hin, hn, q, hq, hq2, hp57⟩
  · exact hres (Or.inl hE6)
  · exact hres (Or.inr (Or.inl hE7))
  · exact hres (Or.inr (Or.inr (Or.inl hE8)))
  · have hq2 : q.p = 2 := by
      rw [hq, LieTypeIndex.characteristic_twistedE6] at hch
      exact hch
    by_cases hplus : p ∣ q.card + 1
    · exact uniSeitzPlanes_twE6Two_inner_even d p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, hn, q, hq, hq2, hplus⟩
    by_cases h34 : orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 4
    · exact uniSeitzPlanes_twE6ThreeFour_inner_even d p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, hn, q, hq, hq2, h34⟩
    · push Not at h34
      have hq1 : 1 ≤ q.card := by
        rw [PrimePower.card_def]
        exact Nat.one_le_pow _ _ q.prime_p.pos
      exact hres (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, orderOf_eq_six_of_degCountTw hp hq1 h1 hplus h34.1 h34.2 hdeg⟩))))
  · exact hres (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD4)))))
  · exact hres (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hR)))))

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311i
