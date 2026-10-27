module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I164
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Census Matrix

theorem rk2_le_twoLocal {Y : Type} [Group Y] [Finite Y] {p k : ℕ} (hp : p.Prime) {A Q : Subgroup Y}
    (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ k) (hQ : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set Y)) : k ≤ GLATwoLocalRank p Y := by
  have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (Q : Set Y)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hAQ hA hcard
  refine h1.trans ?_
  show _ ≤ sSup {k | ∃ H : Subgroup Y, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}
  exact le_csSup (bddAbove_twoLocalPRanks hp.one_lt) ⟨_, ⟨Q, hQ, hQ2, rfl⟩, rfl⟩

theorem rk2_twoLocal_equiv_le {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (e : X ≃* Y) : GLATwoLocalRank p X ≤ GLATwoLocalRank p Y := by
  rcases Nat.eq_zero_or_pos (GLATwoLocalRank p X) with h0 | h1
  · rw [h0]; exact Nat.zero_le _
  obtain ⟨A, Q, hA, hQ1, hQ2, hAQ, hAcard⟩ := rk2_exists_realizer hp h1
  refine rk2_le_twoLocal hp (A := A.map e.toMonoidHom) (Q := Q.map e.toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hA e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hAcard]) ?_ ?_ ?_
  · intro hbot
    exact hQ1 ((Subgroup.map_eq_bot_iff_of_injective Q e.injective).1 hbot)
  · exact hQ2.map e.toMonoidHom
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hAQ

@[expose] def rk2V (r : ℕ) : (Fin 3 → ZMod r) →+ (Fin 5 → ZMod r) where
  toFun u := ![u 0, u 0, u 1, u 2, -(2 * u 0 + u 1 + u 2)]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' u u' := by ext i; fin_cases i <;> simp <;> ring

theorem rk2_twoLocal_SU_five {F : Type} [Field F] [Finite F] {n r : ℕ} (hFD : UnitaryFieldData 2 n F)
    [CharP F 2] (hr : r.Prime) (hrQ : r ∣ 2 ^ n + 1) :
    3 ≤ GLATwoLocalRank r ↥(StatedSU 5 (2 ^ n) F) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hn1 : 1 ≤ n := hFD.one_le
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hrK : r ∣ Nat.card F - 1 := by
    rw [hFD.card, show 2 * n = n * 2 from mul_comm 2 n, pow_mul, sq_sub_one_eq hq1]
    exact Dvd.dvd.mul_right hrQ _
  obtain ⟨ζ, hζr⟩ := exists_zeta (K := F) (r := r) hrK
  have hζ : ζ ^ r = 1 := by rw [← hζr]; exact pow_orderOf_eq_one ζ
  have hζu : ζ ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζr ▸ hrQ)
  have hv : ∀ u, ∑ i, rk2V r u i = 0 := by
    intro u
    simp [rk2V, Fin.sum_univ_five]
    ring
  have hmem : ∀ u, torusWit ζ hζ (rk2V r) u ∈ StatedSU 5 (2 ^ n) F := fun u =>
    torusWit_mem_SU (by positivity) hζ hζu (rk2V r) hv u
  set φ' : Multiplicative (Fin 3 → ZMod r) →* StatedSU 5 (2 ^ n) F :=
    (torusWit ζ hζ (rk2V r)).codRestrict _ hmem with hφ'
  have hinj : Function.Injective φ' := by
    intro u u' h
    have := torusWit_injective (K := F) hζ hζr (rk2V r) (fun u hu0 => by
      funext i
      fin_cases i
      · simpa [rk2V] using hu0 0
      · simpa [rk2V] using hu0 2
      · simpa [rk2V] using hu0 3) (congrArg Subtype.val h)
    exact this
  set E : Subgroup (StatedSU 5 (2 ^ n) F) := φ'.range with hE
  have hEel : IsElemAbelian r E :=
    isElemAbelian_range (fun a => multiplicative_zmod_pow_eq_one a) φ'
  have hEcard : Nat.card E = r ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans (card_multiplicative_zmod 3)
  have hn2 : 2 ≤ 5 := by norm_num
  set t : StatedSU 5 (2 ^ n) F := ⟨swapGL hn2, swapGL_mem_statedSU hFD hn2⟩ with ht
  have ht2 : t ^ 2 = 1 := Subtype.ext (Units.ext (by
    rw [pow_two]
    exact one_add_mul_one_add (swapBlock_mul_self hn2)))
  have ht1 : t ≠ 1 := by
    intro h1
    have := congrArg (fun A : StatedSU 5 (2 ^ n) F =>
      ((A : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) 0 1) h1
    simp [ht, coe_swapGL, swapBlock, Matrix.one_apply] at this
  have hEt : ∀ x ∈ E, x * t = t * x := by
    rintro _ ⟨u, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    change ((torusWit ζ hζ (rk2V r) u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
      (1 + swapBlock 5 F) = (1 + swapBlock 5 F) *
        ((torusWit ζ hζ (rk2V r) u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
    rw [torusWit_apply, coe_diagHom]
    refine diagonal_mul_swap fun i j hi hj => ?_
    have key : ∀ l : Fin 5, l.val < 2 → rk2V r u.toAdd l = u.toAdd 0 := by
      intro l hl
      fin_cases l <;> simp [rk2V] at hl ⊢
    rw [key i hi, key j hj]
  exact le_localRank_of_commute_involution hr (orderOf_eq_prime ht2 ht1) hEel hEcard hEt

theorem rk2_pRank_bot {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q (⊥ : Subgroup Y) = 0 := by
  have := CFSG.SectionRank.pRank_le hq.one_lt (H := (⊥ : Subgroup Y)) (k := 0) (fun E hE _ => by
    have : E = ⊥ := le_bot_iff.1 hE
    subst this
    simp)
  omega

theorem rk2_pRank_le_of_card_le {Y : Type} [Group Y] [Finite Y] {q k : ℕ} (hq : q.Prime)
    {H : Subgroup Y} (hH : Nat.card H ≤ q ^ k) : CFSG.Open.pRank q H ≤ k :=
  CFSG.SectionRank.pRank_le hq.one_lt fun E hE _ => (Subgroup.card_le_of_le hE).trans hH

section Main


theorem rk2_twA4_family {K₀ : Type} [Group K₀] [Finite K₀] {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : q ∣ 2 ^ n + 1) (hK₀ : Rk2IsLabel K₀ ⟨.twA, 4, n⟩) :
    5 + CFSG.Open.pRank q (Subgroup.center K₀) ≤
      GLATwoLocalRank q K₀ + CFSG.Open.pRank q (⊤ : Subgroup K₀) := by
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK₀
  have hM' : CFSG.Blueprint.LieModel (K₀ ⧸ Subgroup.center K₀) .PSU 5 2 n := hM
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  have hn1 : 1 ≤ n := hl.1
  have hFD : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn1, by rw [hcard, ← pow_mul, mul_comm]⟩
  haveI : CharP F 2 := hFD.charP
  haveI : Fact q.Prime := ⟨hq⟩
  have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 5 2 n = (1, 1) := rfl
  have hZg : Nat.card (Subgroup.center K₀) ∣ Nat.gcd 5 (2 ^ n + 1) :=
    rk2_card_center_dvd_twA (ℓ := 4) hK₀ hex
  have hZ5 : Nat.card (Subgroup.center K₀) ∣ 5 := hZg.trans (Nat.gcd_dvd_left _ _)
  set H : Subgroup (GL (Fin 5) F) := StatedSU 5 (2 ^ n) F with hH
  set D : Subgroup H := (StatedScalars (Fin 5) F).subgroupOf H with hD
  have hHK : (Nat.card F = 2 ^ n ∧ H = StatedSL 5 F ∧ q ∣ 2 ^ n - 1) ∨
      (Nat.card F = (2 ^ n) ^ 2 ∧ H = StatedSU 5 (2 ^ n) F ∧ q ∣ 2 ^ n + 1) :=
    Or.inr ⟨hcard, rfl, hqn⟩
  have hTor := fun (C : Subgroup H) [C.Normal] (hC : C ≤ D) =>
    scalar_quotient_diagonal_torus_rank (K := F) (p := 2) (f := n) (n := 5) (r := q)
      Nat.prime_two (by norm_num) hq2 hHK C hC
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hZ5 with h1 | h5
  ·
    have hbot : Subgroup.center K₀ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    let e' : K₀ ≃* StatedProj H :=
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans e
    have hz : CFSG.Open.pRank q (Subgroup.center K₀) = 0 := by rw [hbot]; exact rk2_pRank_bot hq
    have hmq : 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup K₀) := by
      have := (hTor D le_rfl).1
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt e']
      simpa using this
    have hm2 : 2 ≤ GLATwoLocalRank q K₀ := by
      have h2 : 1 + 1 ≤ CFSG.Assembly.RankThreeEven.localRank q (StatedProj H) :=
        le_localRank_statedSU_torus hFD hq hqn (by norm_num) (Or.inl (by norm_num))
      exact h2.trans (rk2_twoLocal_equiv_le hq e'.symm)
    omega
  ·
    have hdvd5 : 5 ∣ Nat.gcd 5 (2 ^ n + 1) := by
      have := hZg
      rwa [h5] at this
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hadm : StatedLieAdmissible .PSU 5 2 n := hM'.admissible
    have hmm : CFSG.Models.LieModel (StatedProj H) .PSU 5 2 n :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
        ⟨hadm, F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hfin, hcardM⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hmm
    have hq0 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have hga : (CFSG.Blueprint.Multiplier.genericOrders .PSU 5 2 n).1 = Nat.gcd 5 (2 ^ n + 1) := rfl
    have hdv : (CFSG.Blueprint.Multiplier.genericOrders .PSU 5 2 n).1 ∣ Nat.card D :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := 2 ^ n) (by norm_num)
        hq0 (Or.inr ⟨hcard, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
    have hM : (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj H))).factorization 5 ≤
        (Nat.card D).factorization 5 := by
      rw [hcardM]
      refine (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.factorization_card_table (by norm_num)
        (by norm_num) hadm (Or.inr rfl) (hga ▸ hdvd5)).trans ?_
      exact (Nat.factorization_le_iff_dvd
        (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hadm).ne'
        Nat.card_pos.ne').2 hdv 5
    let α : H →* StatedProj H := QuotientGroup.mk' D
    have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
    have hαk : α.ker = D := QuotientGroup.ker_mk' D
    have hαc : α.ker ≤ Subgroup.center H := hαk ▸ CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center H
    let β : K₀ →* StatedProj H := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K₀))
    have hβ : Function.Surjective β := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hβk : β.ker = Subgroup.center K₀ := by
      ext x
      rw [MonoidHom.mem_ker]
      exact (MulEquiv.map_eq_one_iff e).trans (QuotientGroup.eq_one_iff x)
    have hβp : IsPGroup 5 β.ker := IsPGroup.of_card (n := 1) (by rw [hβk, h5, pow_one])
    have hHperf : Group.IsPerfect H :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.isPerfect_linUni (K := F) (p := 2) (f := n)
        Nat.prime_two (by norm_num) (Or.inr ⟨hcard, rfl⟩)
    have hLperf : Group.IsPerfect K₀ := ⟨hQ.1⟩
    haveI := hfin
    obtain ⟨ψ, hψs, hβψ⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_hom_of_cover
      (X := StatedProj H) hHperf hLperf α hα hαc β hβ hβk.le (p := 5) (by norm_num) hβp
      (by rw [hαk]; exact hM)
    have hDdvd : Nat.card D ∣ 5 := card_scalars_dvd (by norm_num) H fun x c hc => by
      have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU x.1.2
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    have hHD : Nat.card H = Nat.card (StatedProj H) * Nat.card D :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup D
    have hKZ : Nat.card K₀ = Nat.card (K₀ ⧸ Subgroup.center K₀) * Nat.card (Subgroup.center K₀) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hKS : Nat.card (K₀ ⧸ Subgroup.center K₀) = Nat.card (StatedProj H) :=
      Nat.card_congr e.toEquiv
    have hkerψ : Nat.card ψ.ker * Nat.card K₀ = Nat.card H := by
      have := Subgroup.card_ker_mul_card_range ψ
      rwa [MonoidHom.range_eq_top.2 hψs, Subgroup.card_top] at this
    have hS0 : 0 < Nat.card (StatedProj H) := Nat.card_pos
    have h5D : Nat.card ψ.ker * 5 = Nat.card D := by
      have : Nat.card (StatedProj H) * (Nat.card ψ.ker * 5) =
          Nat.card (StatedProj H) * Nat.card D := by
        rw [← hHD, ← hkerψ, hKZ, hKS, h5]
        ring
      exact Nat.eq_of_mul_eq_mul_left hS0 this
    have hDle : Nat.card D ≤ 5 := Nat.le_of_dvd (by norm_num) hDdvd
    have hker1 : Nat.card ψ.ker = 1 := by
      have : 0 < Nat.card ψ.ker := Nat.card_pos
      omega
    have hinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).1 (Subgroup.eq_bot_of_card_eq _ hker1)
    let χ : H ≃* K₀ := MulEquiv.ofBijective ψ ⟨hinj, hψs⟩
    have hmq : 4 ≤ CFSG.Open.pRank q (⊤ : Subgroup K₀) := by
      have h4 := (hTor ⊥ bot_le).2 (by rw [Subgroup.card_bot]; exact hq.not_dvd_one)
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt
        (χ.symm.trans QuotientGroup.quotientBot.symm)]
      simpa using h4
    have hm2 : 3 ≤ GLATwoLocalRank q K₀ :=
      (rk2_twoLocal_SU_five hFD hq hqn).trans (rk2_twoLocal_equiv_le hq χ)
    have hz : CFSG.Open.pRank q (Subgroup.center K₀) ≤ 2 := by
      refine rk2_pRank_le_of_card_le hq ?_
      rw [h5]
      have h3 : 3 ≤ q := by have := hq.two_le; omega
      nlinarith
    omega

end Main

end CFSG.LocalAnalysis.GLTheoremA
