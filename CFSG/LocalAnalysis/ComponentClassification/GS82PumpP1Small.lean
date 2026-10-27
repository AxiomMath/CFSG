module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.GH74.KGroups.L27
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (allTags mem_allTags lieSylowExponent_bounds
  prod_pos_of_prime factorization_prod_of_mem)
open CFSG.ComponentClassification.GSThmB.QPUSpor (exists_eq_of_prime_dvd_prod)

theorem inChev2_of_lieModel_psl_two_five {Y : Type} [Group Y]
    (h : Blueprint.LieModel Y .PSL 2 5 1) : GH74.GLS.InChev2 Y := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    obtain ⟨e5⟩ := ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (.inr (by rw [hK]; norm_num))
    exact Or.inl ⟨.PSL, 2, 2, ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩,
      StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five (e.trans e5)⟩
  all_goals exact absurd h0 (by norm_num)

theorem lieModel_statedProj_sl_three_two :
    Blueprint.LieModel (StatedProj (StatedSL 3 (ZMod 2))) .PSL 3 2 1 :=
  .inl ⟨by simp [Blueprint.classicalTags], ⟨Nat.prime_two, le_rfl, by norm_num, by decide,
    by decide⟩, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num,
    ⟨MulEquiv.refl _⟩⟩

theorem inChev2_of_lieModel_psl_two_seven {Y : Type} [Group Y]
    (h : Blueprint.LieModel Y .PSL 2 7 1) : GH74.GLS.InChev2 Y := by
  obtain ⟨e1⟩ := GH74.KGroups.L27.equiv_of_lieModel h
  obtain ⟨e2⟩ := GH74.KGroups.L27.equiv_of_lieModel3 lieModel_statedProj_sl_three_two
  exact Or.inl ⟨.PSL, 3, 1, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩,
    Blueprint.LieModel.of_mulEquiv (e2.trans e1.symm) lieModel_statedProj_sl_three_two⟩

@[expose] def admB : StatedLieTag → ℕ → ℕ → ℕ → Bool
  | .PSL, n, p, f => decide (2 ≤ n) && !(n == 2 && p ^ f == 2) && !(n == 2 && p ^ f == 3)
  | .PSU, n, p, f => decide (3 ≤ n) && !(n == 3 && p ^ f == 2)
  | .PSp, n, p, f => decide (2 ≤ n) && !(n == 2 && p ^ f == 2)
  | .POmegaOdd, n, p, _ => decide (3 ≤ n) && p != 2
  | .POmegaPlus, n, _, _ => decide (4 ≤ n)
  | .POmegaMinus, n, _, _ => decide (4 ≤ n)
  | .G2, n, p, f => n == 0 && decide (3 ≤ p ^ f)
  | .F4, n, _, _ => n == 0
  | .E6, n, _, _ => n == 0
  | .E7, n, _, _ => n == 0
  | .E8, n, _, _ => n == 0
  | .twistedE6, n, _, _ => n == 0
  | .trialityD4, n, _, _ => n == 0
  | .twistedB2, n, p, f => n == 0 && p == 2 && f % 2 == 1 && decide (3 ≤ f)
  | .twistedF4, n, p, f => n == 0 && p == 2 && f % 2 == 1 && decide (3 ≤ f)
  | .twistedG2, n, p, f => n == 0 && p == 3 && f % 2 == 1 && decide (3 ≤ f)
  | .Tits, n, p, f => n == 0 && p == 2 && f == 1

theorem admB_of_admissible {τ : StatedLieTag} {n p f : ℕ} (h : StatedLieAdmissible τ n p f) :
    admB τ n p f = true := by
  obtain ⟨-, -, h⟩ := h
  cases τ <;> simp_all [admB, Prod.ext_iff, Nat.odd_iff] <;> tauto

@[expose] def lieDvdCand (M p e : ℕ) (τ : StatedLieTag) (n f : ℕ) : Bool :=
  f == 0 || !admB τ n p f || decide (e < lieSylowExponent τ n * f) ||
    lieOrderNumerator τ n (p ^ f) % lieOrderDivisor τ n (p ^ f) != 0 ||
    M % (lieOrderNumerator τ n (p ^ f) / lieOrderDivisor τ n (p ^ f)) != 0 ||
    decide (M ≤ lieOrderNumerator τ n (p ^ f) / lieOrderDivisor τ n (p ^ f))

@[expose] def oddLieDvdCheck (M : ℕ) (l : List (ℕ × ℕ))
    (ok : StatedLieTag → ℕ → ℕ → ℕ → Bool) : Bool :=
  l.all fun x => x.1 == 2 || allTags.all fun τ => (List.range (x.2 + 2)).all fun n =>
    (List.range (x.2 + 1)).all fun f => lieDvdCand M x.1 x.2 τ n f || ok τ n x.1 f

theorem allowed_of_oddLieDvdCheck (hO : LieOrderFormulasInput) {M : ℕ} {l : List (ℕ × ℕ)}
    {ok : StatedLieTag → ℕ → ℕ → ℕ → Bool}
    (hl : (l.map fun x => x.1 ^ x.2).prod = M) (hpr : ∀ x ∈ l, x.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hc : oddLieDvdCheck M l ok = true) {Y : Type} [Group Y]
    {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hY : Blueprint.LieModel Y τ n p f)
    (hdvd : Nat.card Y ∣ M) (hlt : Nat.card Y < M) : ok τ n p f = true := by
  have ha := Blueprint.LieModel.admissible hY
  obtain ⟨hfin, hord, hfac⟩ := hO Y τ n p f ha hY
  have hp : p.Prime := ha.1
  obtain ⟨hN1, hnN⟩ := lieSylowExponent_bounds ha
  have hf1 : 1 ≤ f := ha.2.1
  have hNf : lieSylowExponent τ n ≤ lieSylowExponent τ n * f := Nat.le_mul_of_pos_right _ hf1
  have hfN : f ≤ lieSylowExponent τ n * f := Nat.le_mul_of_pos_left _ hN1
  have hM : 0 < M := hl ▸ prod_pos_of_prime hpr
  have hY0 : 0 < Nat.card Y := Nat.pos_of_dvd_of_pos hdvd hM
  have hpY : p ∣ Nat.card Y := Nat.dvd_of_factorization_pos (by rw [hfac]; omega)
  obtain ⟨x, hx, rfl⟩ := exists_eq_of_prime_dvd_prod hp hpr (hl ▸ hpY.trans hdvd)
  have he : M.factorization x.1 = x.2 := hl ▸ factorization_prod_of_mem hpr hnd x hx
  have hle : lieSylowExponent τ n * f ≤ x.2 := by
    rw [← hfac, ← he]
    exact (Nat.factorization_le_iff_dvd hY0.ne' hM.ne').2 hdvd x.1
  rw [oddLieDvdCheck, List.all_eq_true] at hc
  have h1 := hc x hx
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1
  rcases h1 with h2 | h1
  · exact absurd h2 hp2
  have h3 := h1 τ (mem_allTags τ) n (by omega) f (by omega)
  rcases h3 with h3 | h3
  swap
  · exact h3
  exfalso
  have hd : 0 < lieOrderDivisor τ n (x.1 ^ f) :=
    Nat.pos_of_ne_zero (CatLeafProof.lieOrderDivisor_ne_zero ha)
  have hq : lieOrderNumerator τ n (x.1 ^ f) / lieOrderDivisor τ n (x.1 ^ f) = Nat.card Y := by
    rw [← hord, Nat.mul_div_cancel _ hd]
  have hmod : lieOrderNumerator τ n (x.1 ^ f) % lieOrderDivisor τ n (x.1 ^ f) = 0 := by
    rw [← hord, Nat.mul_mod_left]
  simp only [lieDvdCand, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
    bne_iff_ne, ne_eq, hq, hmod, not_true_eq_false, or_false] at h3
  rcases h3 with (((h0 | hadm) | hgt) | hM') | hle'
  · omega
  · rw [admB_of_admissible ha] at hadm
    exact Bool.noConfusion hadm
  · omega
  · exact hM' (Nat.mod_eq_zero_of_dvd hdvd)
  · omega

theorem lieModel_psl_two_five_of_dvd_360 (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hY : Blueprint.LieModel Y τ n p f)
    (hdvd : Nat.card Y ∣ 360) (hlt : Nat.card Y < 360) :
    τ = .PSL ∧ n = 2 ∧ p = 5 ∧ f = 1 := by
  have h := allowed_of_oddLieDvdCheck hO (l := [(2, 3), (3, 2), (5, 1)])
    (ok := fun τ n p f => τ == .PSL && n == 2 && p == 5 && f == 1) (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel) hp2 hY hdvd
    hlt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem lieModel_psl_two_seven_of_dvd_6048 (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hY : Blueprint.LieModel Y τ n p f)
    (hdvd : Nat.card Y ∣ 6048) (hlt : Nat.card Y < 6048) :
    τ = .PSL ∧ n = 2 ∧ p = 7 ∧ f = 1 := by
  have h := allowed_of_oddLieDvdCheck hO (l := [(2, 5), (3, 3), (7, 1)])
    (ok := fun τ n p f => τ == .PSL && n == 2 && p == 7 && f == 1) (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel) hp2 hY hdvd
    hlt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end CFSG.ComponentClassification.GS82PumpInputs
