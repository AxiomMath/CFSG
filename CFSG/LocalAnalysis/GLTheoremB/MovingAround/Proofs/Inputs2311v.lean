module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311u
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.NF

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311v

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartTwo.Sec19
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

section Abstract

variable {G : Type*} [Group G]

theorem map_fixedSubgroup_conj_inputs2311v (ψ α : MulAut G) :
    (CFSG.RankThree.PartOne.CTP.fixedSubgroup α).map ψ.toMonoidHom =
      CFSG.RankThree.PartOne.CTP.fixedSubgroup (ψ * α * ψ⁻¹) := by
  ext y
  rw [Subgroup.mem_map, CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    show ψ (α (ψ⁻¹ (ψ x))) = ψ x
    rw [MulAut.inv_apply_self, hx']
  · intro hy
    have hy' : ψ (α (ψ⁻¹ y)) = y := hy
    refine ⟨ψ⁻¹ y, ?_, MulAut.apply_inv_self G ψ y⟩
    show α (ψ⁻¹ y) = ψ⁻¹ y
    have h := congrArg (fun w => ψ⁻¹ w) hy'
    simp only [MulAut.inv_apply_self] at h
    exact h

theorem nonempty_fixedSubgroup_conj_inputs2311v (ψ α : MulAut G) :
    Nonempty (CFSG.RankThree.PartOne.CTP.fixedSubgroup α ≃*
      CFSG.RankThree.PartOne.CTP.fixedSubgroup (ψ * α * ψ⁻¹)) :=
  ⟨(MulEquiv.subgroupMap ψ (CFSG.RankThree.PartOne.CTP.fixedSubgroup α)).trans
    (MulEquiv.subgroupCongr (map_fixedSubgroup_conj_inputs2311v ψ α))⟩

theorem isPGLPiThree_of_equiv_inputs2311v {X Y : Type} [Group X] [Group Y] {q : ℕ}
    (e : X ≃* Y) (h : IsPGLPiThree Y q) : IsPGLPiThree X q := by
  obtain ⟨π, p, f, F, _, hF, hpf, hmod, ⟨e'⟩⟩ := h
  exact ⟨π, p, f, F, inferInstance, hF, hpf, hmod, ⟨e.trans e'⟩⟩

theorem card_of_isPGLPiThree_inputs2311v {X : Type} [Group X] {q : ℕ} (h : IsPGLPiThree X q)
    (hq : q % 3 = 2) : Nat.card X = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨π, p, f, F, _, hF, hpf, hmod, ⟨e⟩⟩ := h
  subst hpf
  cases π with
  | false =>
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two.card_projImage_glPi hF,
      CFSG.RankThree.PartTwo.Sec13.card_slPi_three hF]
    rfl
  | true =>
    have h1 : (p ^ f) % 3 = 1 := hmod
    omega

theorem nonempty_fixedSubgroup_of_conj_inputs2311v {β φ ψ γ : MulAut G} {X : Type*} [Group X]
    (hφβ : φ = β ∨ φ = β⁻¹) (hψ : ψ * φ * ψ⁻¹ = γ)
    (h : Nonempty (CFSG.RankThree.PartOne.CTP.fixedSubgroup γ ≃* X)) :
    Nonempty (CFSG.RankThree.PartOne.CTP.fixedSubgroup β ≃* X) := by
  have hβφ : CFSG.RankThree.PartOne.CTP.fixedSubgroup β =
      CFSG.RankThree.PartOne.CTP.fixedSubgroup φ := by
    rcases hφβ with rfl | rfl
    · rfl
    · exact (CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.fixedSubgroup_inv β).symm
  obtain ⟨e⟩ := nonempty_fixedSubgroup_conj_inputs2311v ψ φ
  rw [hψ] at e
  obtain ⟨e'⟩ := h
  exact ⟨((MulEquiv.subgroupCongr hβφ).trans e).trans e'⟩

theorem pgu_lt_ordG2_inputs2311v {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < CFSG.Open.ordG2 q := by
  unfold CFSG.Open.ordG2
  have hq2 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hq3 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have e6 : q ^ 6 = q ^ 3 * q ^ 3 := by ring
  rw [e6]
  generalize hQ : q ^ 3 = Q at hq3 ⊢
  generalize hA : q ^ 2 - 1 = A
  have hA1 : 1 ≤ A := by omega
  have hQQ : Q * 8 ≤ Q * Q := Nat.mul_le_mul_left Q hq3
  generalize hQQd : Q * Q = QQ at hQQ ⊢
  have hlt : Q < QQ := by omega
  have hle : Q + 1 ≤ QQ - 1 := by omega
  have key : Q * (Q + 1) < QQ * (QQ - 1) :=
    calc Q * (Q + 1) < QQ * (Q + 1) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
      _ ≤ QQ * (QQ - 1) := Nat.mul_le_mul_left QQ hle
  calc Q * A * (Q + 1) = (Q * (Q + 1)) * A := by ring
    _ < (QQ * (QQ - 1)) * A := Nat.mul_lt_mul_of_pos_right key (by omega)

theorem five_le_pow_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) : 5 ≤ ℓ ^ f := by
  have h4 : ℓ ≠ 4 := fun h => by
    rw [h] at hℓ
    norm_num at hℓ
  have h5 : 5 ≤ ℓ := by
    have := hℓ.two_le
    omega
  calc 5 ≤ ℓ := h5
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

theorem twist_lang_inputs2311v (Φ : G →* G) {g₀ h d z : G} (hg : Φ g₀ = g₀ * z)
    (hh : h * (z * Φ h * z⁻¹)⁻¹ = d) (hc : h * d = d * h) :
    Φ (g₀ * h * g₀⁻¹) = (g₀ * h * g₀⁻¹) * (g₀ * d * g₀⁻¹)⁻¹ := by
  have h1 : z * Φ h * z⁻¹ = d⁻¹ * h := by
    calc z * Φ h * z⁻¹ = (h⁻¹ * (h * (z * Φ h * z⁻¹)⁻¹))⁻¹ := by group
      _ = (h⁻¹ * d)⁻¹ := by rw [hh]
      _ = d⁻¹ * h := by group
  have hX : Φ h = z⁻¹ * (d⁻¹ * h) * z := by
    calc Φ h = z⁻¹ * (z * Φ h * z⁻¹) * z := by group
      _ = z⁻¹ * (d⁻¹ * h) * z := by rw [h1]
  have hc' : d⁻¹ * h = h * d⁻¹ := ((Commute.inv_right (hc : Commute h d)).eq).symm
  rw [map_mul, map_mul, map_inv, hg, hX, hc']
  group

theorem conj_eq_of_fixed_inputs2311v {S P m : G} (hm : (S⁻¹ * P) * m * (S⁻¹ * P)⁻¹ = m) :
    P * m * P⁻¹ = S * m * S⁻¹ := by
  calc P * m * P⁻¹ = S * ((S⁻¹ * P) * m * (S⁻¹ * P)⁻¹) * S⁻¹ := by group
    _ = S * m * S⁻¹ := by rw [hm]

theorem twist_conj_inputs2311v {S P m y : G} (hm : (S⁻¹ * P) * m * (S⁻¹ * P)⁻¹ = m) :
    (y * S⁻¹) * (P * m * P⁻¹) * (y * S⁻¹)⁻¹ = y * m * y⁻¹ := by
  rw [conj_eq_of_fixed_inputs2311v hm]
  group

theorem fixed_conj_inputs2311v {S P m y : G} (hyS : y * S = S * y) (hyP : y * P = P * y)
    (hSP : S * P = P * S) (hm : (S⁻¹ * P) * m * (S⁻¹ * P)⁻¹ = m) :
    S * (P⁻¹ * (y * m * y⁻¹) * P) * S⁻¹ = y * m * y⁻¹ := by
  set N := S⁻¹ * P with hNdef
  have hN : S * P⁻¹ = N⁻¹ := by
    rw [hNdef, mul_inv_rev, inv_inv]
    exact (Commute.inv_right (hSP : Commute S P)).eq
  have hyN : Commute y N := by
    rw [hNdef]
    exact (Commute.inv_right (hyS : Commute y S)).mul_right (hyP : Commute y P)
  have h1 : N⁻¹ * y = y * N⁻¹ := (hyN.inv_right).eq.symm
  have h2 : y⁻¹ * N = N * y⁻¹ := (hyN.inv_left).eq
  have hmN : N⁻¹ * m * N = m := by
    calc N⁻¹ * m * N = N⁻¹ * (N * m * N⁻¹) * N := by rw [hm]
      _ = m := by group
  calc S * (P⁻¹ * (y * m * y⁻¹) * P) * S⁻¹ = (S * P⁻¹) * (y * m * y⁻¹) * (S * P⁻¹)⁻¹ := by
        group
    _ = N⁻¹ * (y * m * y⁻¹) * N := by rw [hN, inv_inv]
    _ = (N⁻¹ * y) * m * (y⁻¹ * N) := by group
    _ = (y * N⁻¹) * m * (N * y⁻¹) := by rw [h1, h2]
    _ = y * (N⁻¹ * m * N) * y⁻¹ := by group
    _ = y * m * y⁻¹ := by rw [hmN]

end Abstract

section NormalForm


variable {K : Type} [Field K] [Finite K]

theorem not_conj_tau_inputs2311v {σ : K ≃+* K} {β φ : MulAut (C0 σ)} (hφβ : φ = β ∨ φ = β⁻¹)
    (hβG : ¬ TriOddIsGLine σ β) : ¬ ∃ ψ : MulAut (C0 σ), ψ * φ * ψ⁻¹ = tauAut σ := by
  rintro ⟨ψ, hψ⟩
  apply hβG
  rcases hφβ with rfl | rfl
  · exact ⟨ψ, Or.inl hψ⟩
  · refine ⟨ψ, Or.inr ?_⟩
    rw [← hψ]
    group

theorem exists_cocycle_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (β : MulAut (C0 σ)) (hβ3 : β ^ 3 = 1) (hβout : β ∉ innerAut (C0 σ)) :
    ∃ g : C0 σ, normSeq (tauAut σ) g 3 = 1 ∧
      (MulAut.conj g * tauAut σ = β ∨ MulAut.conj g * tauAut σ = β⁻¹) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
  have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨g, hg, hφ⟩ := d4_outer_three_normal_form hℓ hℓ2 hf K hK σ hσ β hord hβout
  exact ⟨g, hg, hφ.imp Eq.symm Eq.symm⟩

theorem normSeq_of_conj_inputs2311v {ℓ f : ℕ} (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {g n : C0 σ} (hg : normSeq (tauAut σ) g 3 = 1)
    {ψ : MulAut (C0 σ)} (hψ : ψ * (MulAut.conj g * tauAut σ) * ψ⁻¹ = MulAut.conj n * tauAut σ) :
    normSeq (tauAut σ) n 3 = 1 := by
  have hZ : Subgroup.center (C0 σ) = ⊥ := center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * tauAut σ) ^ 3 = 1 := by
    rw [← hψ, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  exact normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube

theorem exists_conj_toral_one_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut (C0 σ)) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ innerAut (C0 σ)) (hβG : ¬ TriOddIsGLine σ β) :
    ∃ (φ ψ : MulAut (C0 σ)) (s : C0 σ) (d : Kˣ), (φ = β ∨ φ = β⁻¹) ∧
      ψ * φ * ψ⁻¹ = MulAut.conj s * tauAut σ ∧ Units.map σ.toRingHom.toMonoidHom d = d ∧
      d ^ 3 = 1 ∧ d ≠ 1 ∧
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  classical
  obtain ⟨g, hg, hφβ⟩ := exists_cocycle_inputs2311v hℓ hℓ2 hf hK σ hσ β hβ3 hβout
  have hnot := not_conj_tau_inputs2311v (σ := σ) hφβ hβG
  obtain ⟨y₀, n₀, hn₀, hy₀⟩ := d4MonoNF ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ g hg
  have hN₀ := normSeq_of_conj_inputs2311v hK σ hσ hg hy₀
  by_cases htor : (n₀ : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨t, s, -, -, hts, d, hd, hd3, hsd⟩ := d4_toral_conj hℓ hℓ2 hf K hK σ hσ n₀ htor hN₀
    have hconj : MulAut.conj (t * y₀) * (MulAut.conj g * tauAut σ) *
        (MulAut.conj (t * y₀))⁻¹ = MulAut.conj s * tauAut σ := by
      rw [← hts, ← hy₀, map_mul]
      group
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hnot
      refine ⟨MulAut.conj (t * y₀), ?_⟩
      have hs1 : s = 1 := by
        apply Subtype.ext
        have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Kˣ) =
            (1 : Fin TwistTag.D4.tag.rank → Kˣ) :=
          funext fun i => by fin_cases i <;> rfl
        rw [hsd, h1, rootDiagUnit_one]
        rfl
      rw [hconj, hs1, map_one, one_mul]
    exact ⟨_, _, s, d, hφβ, hconj, hd, hd3, hd1, hsd⟩
  · obtain ⟨y₁, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.ellQ1_conj_toral
        CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds hℓ hℓ2 hℓ3 hf hq hK σ hσ n₀ hn₀ htor hN₀
    refine ⟨_, MulAut.conj (y₁ * y₀), s, d, hφβ, ?_, hd, hd3, hd1, hsd⟩
    rw [← hconj, ← hy₀, map_mul]
    group

theorem exists_conj_minusToral_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut (C0 σ)) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ innerAut (C0 σ)) (hβG : ¬ TriOddIsGLine σ β) :
    ∃ (φ ψ : MulAut (C0 σ)) (s : C0 σ), (φ = β ∨ φ = β⁻¹) ∧
      ψ * φ * ψ⁻¹ = MulAut.conj s * tauAut σ ∧ D4MinusToral ℓ f hℓ K σ s := by
  classical
  obtain ⟨g, hg, hφβ⟩ := exists_cocycle_inputs2311v hℓ hℓ2 hf hK σ hσ β hβ3 hβout
  have hnot := not_conj_tau_inputs2311v (σ := σ) hφβ hβG
  rcases d4MinusNF ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ g hg with
    ⟨y, hy⟩ | ⟨y, s, hs, hy⟩ | ⟨y, n, hn, hy⟩
  · exact absurd ⟨MulAut.conj y, hy⟩ hnot
  · exact ⟨_, _, s, hφβ, hy, hs⟩
  · have hN := normSeq_of_conj_inputs2311v hK σ hσ hg hy
    obtain ⟨y₀, s, hs, hy₀⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.minusEll_conj_toral
        CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds hℓ hℓ2 hℓ3 hf hq hK σ hσ n hn hN
    refine ⟨_, MulAut.conj (y₀ * y), s, hφβ, ?_, hs⟩
    rw [← hy₀, ← hy, map_mul]
    group

end NormalForm

section ToralOne


variable {K : Type} [Field K] [Finite K]

theorem isPGLPiThree_toral_one_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hq : (ℓ ^ f) % 3 = 1) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {d : Kˣ} (hd : Units.map σ.toRingHom.toMonoidHom d = d)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {s : C0 σ}
    (hsd : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    IsPGLPiThree ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ))
      (ℓ ^ f) := by
  have hA := a2Std_of_class hℓ hℓ2 hf hq hK hσ hd hd3 hd1
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.nonempty_fixSub_mulEquiv_projImage
    hA hℓ hf rfl _ (a2_hφ_of_class (σ := σ) (d := d) hsd)
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hcard : Nat.card (CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hK hσ
  refine ⟨true, ℓ, f, CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom, inferInstance,
    ⟨hℓ, hf, hcard⟩, rfl, hq, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans e

end ToralOne


section Minus


variable {K : Type} [Field K] [Finite K]

theorem exists_fixed_embedding_minusToral_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {s : C0 σ} (hs : D4MinusToral ℓ f hℓ K σ s) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = ℓ ^ f ∧
      ∃ α : MulAut (adjointGroup Tag.D4 F), α ^ 3 = 1 ∧
        (D4ElemType α fun ε δ => ε ≠ 0 ∧ δ = 1) ∧
        ∃ Θ : CFSG.RankThree.PartOne.CTP.fixedSubgroup α →*
            CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ),
          Function.Injective Θ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hs3, hsτ⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.toral_pow_three_and_fixed
      hℓ σ hσ hs
  obtain ⟨L, _, _, _, _, g₀, b, ⟨hg₀C, hg₀P, hg₀F⟩, -, -, hsL⟩ := hs
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  set F := CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom with hFdef
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hFcard : Nat.card F = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hK hσ
  have hsmem := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom s.2
  have hsC : (s : ModGL TwistTag.D4.tag K) ∈ adjointGroup TwistTag.D4.tag K :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hsmem).1
  have hsF : Units.map (entrywiseHom σ.toRingHom) (s : ModGL TwistTag.D4.tag K) = s := by
    have h := congrArg Subtype.val hsτ
    rwa [coe_fieldActor] at h
  have hsP : (s : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K =
      diagramMap TwistTag.D4 K * s := by
    have htw := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hsmem).2
    rw [twistHom_apply, hsF] at htw
    calc (s : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K =
        (diagramMap TwistTag.D4 K * s * (diagramMap TwistTag.D4 K)⁻¹) *
          diagramMap TwistTag.D4 K := by rw [htw]
      _ = diagramMap TwistTag.D4 K * s := by group
  obtain ⟨a, u, ⟨u₀, hu₀, rfl⟩, hsd⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed
    Tag.D4 (K := F) (L := K) σ.toRingHom (fun c => by rw [hFcard]; exact hσ c) hsC hsF
  obtain ⟨Sq, hSqdef⟩ : ∃ Sq : ModGL Tag.D4 F, Sq = rootDiagUnit Tag.D4 a * u₀ := ⟨_, rfl⟩
  obtain ⟨sT, hsT⟩ : ∃ sT : ModGL Tag.D4 K, sT = (s : ModGL TwistTag.D4.tag K) := ⟨_, rfl⟩
  have hSq : baseChangeGL (algebraMap F K) Sq = sT := by
    rw [hsT, hSqdef, map_mul, hsd]
  have hSqP : Sq * CFSG.HardMathSupport.Lang.D4Three.d4P F =
      CFSG.HardMathSupport.Lang.D4Three.d4P F * Sq := by
    apply baseChangeGL_injective (algebraMap F K)
    rw [map_mul, map_mul, hSq,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphType_baseChangeGL_d4P, hsT]
    exact hsP
  have hSq3 : Sq ^ 3 = 1 := by
    apply baseChangeGL_injective (algebraMap F K)
    rw [map_pow, hSq, map_one, hsT]
    have h := congrArg Subtype.val hs3
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hP3 : CFSG.HardMathSupport.Lang.D4Three.d4P F ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 F
  have hu₀' : u₀⁻¹ ∈ adjointGroup Tag.D4 F := inv_mem hu₀
  set g : adjointGroup Tag.D4 F := ⟨u₀⁻¹, hu₀'⟩ with hgdef
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (adjointGroup Tag.D4 F), α = MulAut.conj g *
      (exactNormalAut Tag.D4 F a⁻¹ 1 0 * CFSG.HardMathSupport.Lang.D4Three.d4Graph F 1) :=
    ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ModGL Tag.D4 F, M = Sq⁻¹ * CFSG.HardMathSupport.Lang.D4Three.d4P F :=
    ⟨_, rfl⟩
  have hαcoe : ∀ j : adjointGroup Tag.D4 F, (α j : ModGL Tag.D4 F) = M * j * M⁻¹ := by
    intro j
    rw [hαdef,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphType_coe_normalForm]
    have hgM : (g : ModGL Tag.D4 F) * rootDiagUnit Tag.D4 a⁻¹ *
        CFSG.HardMathSupport.Lang.D4Three.d4P F ^ 1 = M := by
      rw [pow_one, ← rootDiagUnit_inv, hMdef, hSqdef, mul_inv_rev]
    rw [hgM]
  have hM3 : M * M * M = 1 := by
    have hc : Commute Sq⁻¹ (CFSG.HardMathSupport.Lang.D4Three.d4P F) :=
      Commute.inv_left (hSqP : Commute _ _)
    rw [← pow_three', hMdef, hc.mul_pow, inv_pow, hSq3, inv_one, one_mul, hP3]
  have hα3 : α ^ 3 = 1 := by
    refine MulEquiv.ext fun j => Subtype.ext ?_
    have h3 : (α ^ 3) j = α (α (α j)) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [h3, hαcoe, hαcoe, hαcoe, MulAut.one_apply]
    calc M * (M * (M * (j : ModGL Tag.D4 F) * M⁻¹) * M⁻¹) * M⁻¹ =
        (M * M * M) * j * (M * M * M)⁻¹ := by group
      _ = j := by rw [hM3]; group
  have hαT : D4ElemType α fun ε δ => ε ≠ 0 ∧ δ = 1 :=
    ⟨g, a⁻¹, 1, 1, by norm_num, one_pow 3, ⟨one_ne_zero, rfl⟩, hαdef⟩
  have hbcM : baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap F K) M) =
      (baseChangeGL (algebraMap K L) sT)⁻¹ * CFSG.HardMathSupport.Lang.D4Three.d4P L := by
    rw [hMdef]
    simp only [map_mul, map_inv, hSq,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphType_baseChangeGL_d4P]
  have hmN₀ : ∀ j : CFSG.RankThree.PartOne.CTP.fixedSubgroup α,
      ((baseChangeGL (algebraMap K L) sT)⁻¹ * CFSG.HardMathSupport.Lang.D4Three.d4P L) *
        baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap F K)
          ((j : adjointGroup Tag.D4 F) : ModGL Tag.D4 F)) *
          ((baseChangeGL (algebraMap K L) sT)⁻¹ * CFSG.HardMathSupport.Lang.D4Three.d4P L)⁻¹ =
      baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap F K)
        ((j : adjointGroup Tag.D4 F) : ModGL Tag.D4 F)) := by
    intro j
    have hj : α j = j := j.2
    have h1 : baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap F K)
        ((α j : adjointGroup Tag.D4 F) : ModGL Tag.D4 F)) =
        baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap F K)
          ((j : adjointGroup Tag.D4 F) : ModGL Tag.D4 F)) := by rw [hj]
    rw [hαcoe] at h1
    simp only [map_mul, map_inv] at h1
    rw [hbcM] at h1
    exact h1
  set bb : Fin TwistTag.D4.tag.rank → Lˣ := ![1, 1, b, 1] with hbbdef
  obtain ⟨db, hdbdef⟩ : ∃ db : ModGL TwistTag.D4.tag L, db = rootDiagUnit TwistTag.D4.tag bb :=
    ⟨_, rfl⟩
  have hsL' : triEmb K σ L s = g₀ * db * g₀⁻¹ := by
    rw [hdbdef]
    exact hsL
  have hdbT : db ∈ torusGroup TwistTag.D4.tag L := by
    rw [hdbdef]
    exact rootDiagUnit_mem_torusGroup _
  have hdbP : diagramMap TwistTag.D4 L * db = db * diagramMap TwistTag.D4 L := by
    rw [hdbdef, diagramMap_mul_rootDiagUnit]
    congr 2
    funext i
    fin_cases i <;> rfl
  obtain ⟨h, hhT, hhP, hhe⟩ := d4Minus_torus_lang Fr hFr hdbT hdbP
  have hhdb : h * db = db * h := by
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    rw [hc, hdbdef, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm c]
  have hFy₀ : twistHom TwistTag.D4 L Fr (g₀ * h * g₀⁻¹) =
      (g₀ * h * g₀⁻¹) * (triEmb K σ L s)⁻¹ := by
    rw [hsL']
    exact twist_lang_inputs2311v _ hg₀F hhe hhdb
  obtain ⟨y, hydef⟩ : ∃ y : ModGL TwistTag.D4.tag L, y = g₀ * h * g₀⁻¹ := ⟨_, rfl⟩
  have hFy : twistHom TwistTag.D4 L Fr y = y * (triEmb K σ L s)⁻¹ := by
    rw [hydef]
    exact hFy₀
  have hyS : y * triEmb K σ L s = triEmb K σ L s * y := by
    rw [hydef, hsL']
    calc g₀ * h * g₀⁻¹ * (g₀ * db * g₀⁻¹) = g₀ * (h * db) * g₀⁻¹ := by group
      _ = g₀ * (db * h) * g₀⁻¹ := by rw [hhdb]
      _ = g₀ * db * g₀⁻¹ * (g₀ * h * g₀⁻¹) := by group
  have hg₀P' : g₀⁻¹ * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * g₀⁻¹ :=
    ((Commute.inv_right (hg₀P : Commute (diagramMap TwistTag.D4 L) g₀)).eq).symm
  have hyP : y * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * y := by
    rw [hydef]
    calc g₀ * h * g₀⁻¹ * diagramMap TwistTag.D4 L =
        g₀ * h * (g₀⁻¹ * diagramMap TwistTag.D4 L) := by group
      _ = g₀ * h * (diagramMap TwistTag.D4 L * g₀⁻¹) := by rw [hg₀P']
      _ = g₀ * (h * diagramMap TwistTag.D4 L) * g₀⁻¹ := by group
      _ = g₀ * (diagramMap TwistTag.D4 L * h) * g₀⁻¹ := by rw [hhP]
      _ = (g₀ * diagramMap TwistTag.D4 L) * h * g₀⁻¹ := by group
      _ = (diagramMap TwistTag.D4 L * g₀) * h * g₀⁻¹ := by rw [hg₀P]
      _ = diagramMap TwistTag.D4 L * (g₀ * h * g₀⁻¹) := by group
  have hSLP : triEmb K σ L s * diagramMap TwistTag.D4 L =
      diagramMap TwistTag.D4 L * triEmb K σ L s := by
    rw [triEmb_apply, ← baseChangeGL_diagramMap (algebraMap K L) TwistTag.D4, ← map_mul, ← map_mul,
      hsP]
  have hyN : ∀ m ∈ adjointGroup TwistTag.D4.tag L,
      y * m * y⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
    intro m hm
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    have h1 : g₀⁻¹ * m * g₀ ∈ adjointGroup TwistTag.D4.tag L :=
      mul_mem (mul_mem (inv_mem hg₀C) hm) hg₀C
    have h3 := mul_mem (mul_mem hg₀C (conj_rootDiagUnit_mem_adjointGroup c h1)) (inv_mem hg₀C)
    rw [← hc] at h3
    have e : y * m * y⁻¹ = g₀ * (h * (g₀⁻¹ * m * g₀) * h⁻¹) * g₀⁻¹ := by
      rw [hydef]
      group
    rw [e]
    exact h3
  have hσF : σ.toRingHom.comp (algebraMap F K) = algebraMap F K := RingHom.ext fun c => c.2
  have hjK : ∀ x : ModGL TwistTag.D4.tag F, Units.map (entrywiseHom σ.toRingHom)
      (baseChangeGL (algebraMap F K) x) = baseChangeGL (algebraMap F K) x := by
    intro x
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hσF]
  let ι₀ : adjointGroup Tag.D4 F →* ModGL TwistTag.D4.tag F := (adjointGroup TwistTag.D4.tag F).subtype
  obtain ⟨mT, hmTdef⟩ : ∃ mT : CFSG.RankThree.PartOne.CTP.fixedSubgroup α →
      ModGL TwistTag.D4.tag L, ∀ j, mT j = baseChangeGL (algebraMap K L)
        (baseChangeGL (algebraMap F K) (ι₀ (j : adjointGroup Tag.D4 F))) := ⟨_, fun _ => rfl⟩
  have hmN : ∀ j, ((triEmb K σ L s)⁻¹ * diagramMap TwistTag.D4 L) * mT j *
      ((triEmb K σ L s)⁻¹ * diagramMap TwistTag.D4 L)⁻¹ = mT j := by
    intro j
    have h := hmN₀ j
    rw [hsT] at h
    rw [hmTdef]
    exact h
  have hmF : ∀ j, twistHom TwistTag.D4 L Fr (mT j) =
      diagramMap TwistTag.D4 L * mT j * (diagramMap TwistTag.D4 L)⁻¹ := by
    intro j
    rw [hmTdef, twistHom_baseChangeGL (algebraMap K L) (d4Minus_hcomm hσ Fr hFr), twistHom_apply,
      hjK, map_mul, map_mul, map_inv, baseChangeGL_diagramMap]
  have hXr : ∀ j, y * mT j * y⁻¹ ∈ (triEmb K σ L).range := by
    intro j
    rw [triEmb_range hℓ hf hK hσ Fr hFr]
    refine Subgroup.mem_inf.2 ⟨hyN _ ?_, ?_⟩
    · rw [hmTdef]
      exact baseChangeGL_mem_adjointGroup _
        (baseChangeGL_mem_adjointGroup _ (show ι₀ (j : adjointGroup Tag.D4 F) ∈
          adjointGroup TwistTag.D4.tag F from (j : adjointGroup Tag.D4 F).2))
    · show twistHom TwistTag.D4 L Fr (y * mT j * y⁻¹) = y * mT j * y⁻¹
      rw [map_mul, map_mul, map_inv, hFy, hmF j]
      exact twist_conj_inputs2311v (hmN j)
  let θ : CFSG.RankThree.PartOne.CTP.fixedSubgroup α →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj y).toMonoidHom.comp ((baseChangeGL (algebraMap K L)).comp
      ((baseChangeGL (algebraMap F K)).comp
        (ι₀.comp (CFSG.RankThree.PartOne.CTP.fixedSubgroup α).subtype)))
  have hθ : ∀ j, θ j = y * mT j * y⁻¹ := fun j => by
    rw [hmTdef]
    rfl
  have hθr : ∀ j, θ j ∈ (triEmb K σ L).range := fun j => by
    rw [hθ]
    exact hXr j
  let θ' : CFSG.RankThree.PartOne.CTP.fixedSubgroup α →* (triEmb K σ L).range :=
    θ.codRestrict _ hθr
  let Θ₀ : CFSG.RankThree.PartOne.CTP.fixedSubgroup α →* C0 σ :=
    (MonoidHom.ofInjective (triEmb_injective (K := K) (σ := σ) (L := L))).symm.toMonoidHom.comp θ'
  have hΘ₀ : ∀ j, triEmb K σ L (Θ₀ j) = θ j := fun j =>
    MonoidHom.apply_ofInjective_symm triEmb_injective (θ' j)
  have hΘfix : ∀ j, Θ₀ j ∈
      CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ) := by
    intro j
    show (MulAut.conj s * tauAut σ) (Θ₀ j) = Θ₀ j
    apply triEmb_injective (K := K) (σ := σ) (L := L)
    have hxmem := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom (Θ₀ j).2
    have hxtw := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxmem).2
    rw [twistHom_apply] at hxtw
    have hτx : Units.map (entrywiseHom σ.toRingHom) ((Θ₀ j : C0 σ) : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * (Θ₀ j : C0 σ) * diagramMap TwistTag.D4 K := by
      calc _ = (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
            Units.map (entrywiseHom σ.toRingHom) ((Θ₀ j : C0 σ) : ModGL TwistTag.D4.tag K) *
              (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
        _ = _ := by rw [hxtw]
    have e2 : triEmb K σ L (tauAut σ (Θ₀ j)) =
        (diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L (Θ₀ j) * diagramMap TwistTag.D4 L := by
      rw [triEmb_apply, triEmb_apply, coe_fieldActor, hτx, map_mul, map_mul, map_inv,
        baseChangeGL_diagramMap]
    rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, e2, hΘ₀, hθ]
    exact fixed_conj_inputs2311v hyS hyP hSLP (hmN j)
  refine ⟨↥F, inferInstance, inferInstance, hFcard, α, hα3, hαT, Θ₀.codRestrict _ hΘfix, ?_⟩
  intro j₁ j₂ h12
  have h1 : Θ₀ j₁ = Θ₀ j₂ := congrArg Subtype.val h12
  have h2 : θ j₁ = θ j₂ := by rw [← hΘ₀, ← hΘ₀, h1]
  rw [hθ, hθ, hmTdef, hmTdef] at h2
  have h3 : baseChangeGL (algebraMap K L) (baseChangeGL (algebraMap F K)
      (ι₀ (j₁ : adjointGroup Tag.D4 F))) = baseChangeGL (algebraMap K L)
        (baseChangeGL (algebraMap F K) (ι₀ (j₂ : adjointGroup Tag.D4 F))) :=
    mul_left_cancel (mul_right_cancel h2)
  have h4 := baseChangeGL_injective (algebraMap F K) (baseChangeGL_injective (algebraMap K L) h3)
  exact Subtype.ext (Subtype.ext h4)

theorem isPGLPiThree_minusToral_inputs2311v {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {s : C0 σ} (hs : D4MinusToral ℓ f hℓ K σ s) :
    IsPGLPiThree ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ))
      (ℓ ^ f) := by
  classical
  obtain ⟨F, _, _, hF, α, hα3, hαT, Θ, hΘ⟩ :=
    exists_fixed_embedding_minusToral_inputs2311v hℓ hf hK σ hσ hs
  obtain ⟨m, hm, hcard⟩ := CFSG.HardMathSupport.Lang.E6Descent.card_fixSub_minusToral hℓ hℓ2 hf hq hK hσ hs
  have hq5 : 5 ≤ ℓ ^ f := five_le_pow_inputs2311v hℓ hℓ2 hℓ3 hf
  have hC : Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ)) =
      (ℓ ^ f) ^ 3 * m * (1 + (ℓ ^ f) ^ 3) := by
    rw [← hcard]
    exact Nat.card_congr (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).toEquiv
  have h25 : 5 ^ 2 ≤ (ℓ ^ f) ^ 2 := Nat.pow_le_pow_left hq5 2
  have hm' : m ≤ (ℓ ^ f) ^ 2 - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) h25)) hm
  have hCle : Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ)) ≤
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
    rw [hC, add_comm 1 ((ℓ ^ f) ^ 3)]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm')
  have hle : Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup α) ≤
      Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * tauAut σ)) :=
    Nat.card_le_card_of_injective Θ hΘ
  have : CharP F ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hF
  have hchar : ringChar F = ℓ := ringChar.eq F ℓ
  have hF3 : ringChar F ≠ 3 := by rw [hchar]; exact hℓ3
  have hF2 : ringChar F ≠ 2 := by rw [hchar]; exact hℓ2
  have hF5 : 5 ≤ Nat.card F := by rw [hF]; exact hq5
  rcases CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.isG2Type_or_isA2Type hF3 hα3 hαT
    with hG | hA
  ·
    exfalso
    obtain ⟨ψ, hψ⟩ := hG
    have hfix : CFSG.RankThree.PartOne.CTP.fixedSubgroup (ψ * α * ψ⁻¹) =
        CFSG.RankThree.PartOne.CTP.fixedSubgroup (CFSG.HardMathSupport.Lang.D4Three.d4Graph F 1) := by
      rcases hψ with h | h
      · rw [h]
      · rw [h, CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.fixedSubgroup_d4Graph_two]
    obtain ⟨e₁⟩ := nonempty_fixedSubgroup_conj_inputs2311v ψ α
    have e₂ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2 F
      (by omega : 3 ≤ Nat.card F)
    have hfix' : CFSG.RankThree.PartOne.CTP.fixedSubgroup
        (CFSG.HardMathSupport.Lang.D4Three.d4Graph F 1) =
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (CFSG.HardMathSupport.Lang.D4Three.d4Graph F 1) := Subgroup.ext fun _ => Iff.rfl
    have hJ : Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup α) = CFSG.Open.ordG2 (ℓ ^ f) := by
      rw [Nat.card_congr e₁.toEquiv, hfix, hfix', Nat.card_congr e₂.toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    have hlt := pgu_lt_ordG2_inputs2311v (q := ℓ ^ f) (le_trans (by norm_num) hq5)
    have h1 := hle.trans hCle
    rw [hJ] at h1
    exact absurd (lt_of_lt_of_le hlt h1) (lt_irrefl _)
  ·
    obtain ⟨ψ, B, hB3, hB1, hψ⟩ := hA
    have hfix : CFSG.RankThree.PartOne.CTP.fixedSubgroup (ψ * α * ψ⁻¹) =
        CFSG.RankThree.PartOne.CTP.fixedSubgroup
          (CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.gammaP F B) := by
      rcases hψ with h | h
      · rw [h]
      · rw [h, CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.fixedSubgroup_inv]
    obtain ⟨e₁⟩ := nonempty_fixedSubgroup_conj_inputs2311v ψ α
    have hP := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds
      F hF2 hF3 hF5 B hB3 hB1
    rw [hF] at hP
    have hJ : IsPGLPiThree (CFSG.RankThree.PartOne.CTP.fixedSubgroup α) (ℓ ^ f) :=
      isPGLPiThree_of_equiv_inputs2311v (e₁.trans (MulEquiv.subgroupCongr hfix)) hP
    have hJcard := card_of_isPGLPiThree_inputs2311v hJ hq
    have hbij : Function.Bijective Θ := hΘ.bijective_of_nat_card_le (by rw [hJcard]; exact hCle)
    exact isPGLPiThree_of_equiv_inputs2311v (MulEquiv.ofBijective Θ hbij).symm hJ

end Minus

section Main


theorem triOddA2FixPGL_holds : Inputs2311u.TriOddA2FixPGL := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ β hβ3 hβout hβG
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq12 : (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 := by omega
  rcases hq12 with hq | hq
  · obtain ⟨φ, ψ, s, d, hφβ, hψ, hd, hd3, hd1, hsd⟩ :=
      exists_conj_toral_one_inputs2311v hℓ hℓ2 hℓ3 hf hq hK σ hσ β hβ3 hβout hβG
    obtain ⟨π, p, f', F, _, hF, hpf, hmod, ⟨e⟩⟩ :=
      isPGLPiThree_toral_one_inputs2311v hℓ hℓ2 hf hq hK σ hσ hd hd3 hd1 hsd
    obtain ⟨e'⟩ := nonempty_fixedSubgroup_of_conj_inputs2311v hφβ hψ ⟨e⟩
    exact ⟨π, p, f', F, inferInstance, hF, hpf, hmod, ⟨e'⟩⟩
  · obtain ⟨φ, ψ, s, hφβ, hψ, hs⟩ :=
      exists_conj_minusToral_inputs2311v hℓ hℓ2 hℓ3 hf hq hK σ hσ β hβ3 hβout hβG
    obtain ⟨π, p, f', F, _, hF, hpf, hmod, ⟨e⟩⟩ :=
      isPGLPiThree_minusToral_inputs2311v hℓ hℓ2 hℓ3 hf hq hK σ hσ hs
    obtain ⟨e'⟩ := nonempty_fixedSubgroup_of_conj_inputs2311v hφβ hψ ⟨e⟩
    exact ⟨π, p, f', F, inferInstance, hF, hpf, hmod, ⟨e'⟩⟩

end Main

section Escape


theorem triOddA2Escape_holds : Inputs2311u.TriOddA2Escape :=
  Inputs2311u.triOddA2Escape_of_fixPGL triOddA2FixPGL_holds

end Escape

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311v
