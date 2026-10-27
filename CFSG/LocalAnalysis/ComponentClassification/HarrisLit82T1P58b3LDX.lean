module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDPc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDBlk

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open P58b3 (tBlockP OddGen)
open scoped MatrixGroups

namespace P58b3L

theorem facts_map_solvable_two {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {S : Type*} [Group S] (π : X →* S) (hπ : Function.Surjective π) (hker : π.ker = center X)
    {c : X} (hcZ : c ∈ center X) (hc2 : orderOf c = 2) {t : X} {Q : Subgroup X}
    (hQ : IsSolvableTwoComponentIn Q (centralizer {t})) (hcQ : c ∈ Q) :
    Q.map π ≤ centralizer {π t} ∧ ((Q.map π).subgroupOf (centralizer {π t})).IsSubnormal ∧
      Group.IsSolvable ↥(Q.map π) ∧ OddGen ↥(Q.map π) ∧
      (∃ r ∈ Q.map π, r ^ 3 = 1 ∧ r ≠ 1) ∧
      ∀ s ∈ Q.map π, (∀ h ∈ Q.map π, s * h = h * s) → s * s = 1 → s = 1 := by
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  obtain ⟨h₁, h₂, h₃, h₄⟩ := P58b3.facts_map_solvable' π hπ hker hQ
  obtain ⟨-, -, -, hQiso⟩ := hQ
  refine ⟨h₁, h₂, h₃, h₄, ?_, fun s hs hsc hs2 =>
    P58b3.eq_one_of_mem_center_map π hker hcZ hc2 hcQ hQiso hs hsc hs2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 3
    (P58b3.three_dvd_card_of_coreQuot hQiso)
  refine ⟨π y, ⟨y, y.2, rfl⟩, ?_, fun h1 => ?_⟩
  · rw [← map_pow, ← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
  · have hyZ : (y : X) ∈ center X := hπZ.1 h1
    obtain ⟨k, hk⟩ := Sol78.center_isPGroup_two hO ⟨y, hyZ⟩
    have hdvd : orderOf (⟨y, hyZ⟩ : center X) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

section Diag

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem false_of_sign_of_quasisimple (hK3 : Nat.card K = 3) (hker : OKer (oQ (diagGL hw)))
    {J : Finset (Fin d)} (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty)
    (hJc : Jᶜ.Nonempty) (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (h3I : 3 ≤ I.card)
    (hqI : IsQuasisimple (blockP K hw I)) (hIcev : Even Iᶜ.card)
    {R₁ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hR₁x : R₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR₁s : (R₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hR₁solv : Group.IsSolvable ↥R₁) (hR₁odd : OddGen ↥R₁) {r} (hr : r ∈ R₁) (hr3 : r ^ 3 = 1)
    (hr1 : r ≠ 1) (hnc : ∀ s ∈ R₁, (∀ h ∈ R₁, s * h = h * s) → s * s = 1 → s = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hro : Odd (orderOf r) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hr3)
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJc
    · rwa [compl_compl]
  have hIcc : Iᶜᶜ.Nonempty := by
    rw [compl_compl]
    rcases hI with rfl | rfl
    · exact hJne
    · exact hJc
  have hI' : Iᶜ = J ∨ Iᶜ = Jᶜ := by
    rcases hI with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (compl_compl J)
  have hR₁c := le_tBlockP_compl_of_isSubnormal' hw hK hker hJ hI hIc (hNF I hI h3I) hqI hR₁x hR₁s
    hR₁solv hR₁odd.le_closure
  have hboth : 3 ≤ Iᶜ.card → IsQuasisimple (blockP K hw Iᶜ) → False := by
    intro h3 hq'
    have hR₁I := le_tBlockP_compl_of_isSubnormal' hw hK hker hJ hI' hIcc (hNF Iᶜ hI' h3) hq'
      hR₁x hR₁s hR₁solv hR₁odd.le_closure
    exact hr1 (eq_one_of_mem_tBlockP_inf_of_odd hw (I := Iᶜ) (hR₁c hr) (hR₁I hr) hro)
  obtain ⟨b, hb⟩ := hIcev
  rcases (show Iᶜ.card ≤ 2 ∨ Iᶜ.card = 4 ∨ 5 ≤ Iᶜ.card by omega) with h | h | h
  · exact hr1 (P58b3.eq_one_of_mem_tBlockP_of_card_le_two hw hK3 h (hR₁c hr) hro)
  · by_cases hq' : IsQuasisimple (blockP K hw Iᶜ)
    · exact hboth (by omega) hq'
    · have hR₁sI : (R₁.subgroupOf (tBlockP hw Iᶜ)).IsSubnormal :=
        CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
          (P58b3.tBlockP_le_centralizer hw J Iᶜ hI' hJ) hR₁s
      obtain ⟨s, hs, hsc, hs2⟩ := exists_central_involution_of_le_tBlockP' hw hK3 h hIcc hq'
        hR₁c hR₁sI hR₁odd hr hr3 hr1
      have hs1 := hnc s hs hsc (by rw [← pow_two, ← hs2, pow_orderOf_eq_one])
      rw [hs1, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
  · exact hboth (by omega) (P58b3.isQuasisimple_blockP_of_five_le hw hK h hIcc)

end Diag

theorem exists_pc_model {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {n : ℕ}
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    {T : GL (Fin (2 * n)) K} (hT : T ∈ matrixDerived (oQ R))
    (hT2 : (T : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * T = -1) :
    ∃ (R₁ : GL (Fin (2 * n)) K) (A : matrixDerived (oQ R₁))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ R₁))),
      (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) ∧
      ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        blkDiag n (jMat (-1 : K)) ∧
      θ (projH _ ⟨T, hT⟩) = projH _ A := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  set Tm := (T : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hTm
  set Rm := (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hRm
  have hiso : Tmᵀ * Rm * Tm = Rm := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  have hTT' : Tm * (-Tm) = 1 := by rw [Matrix.mul_neg, hT2, neg_neg]
  have hε : Tmᵀ * Rm = (-1 : K) • (Rm * Tm) := by
    calc Tmᵀ * Rm = Tmᵀ * Rm * (Tm * (-Tm)) := by rw [hTT', Matrix.mul_one]
      _ = Tmᵀ * Rm * Tm * (-Tm) := by rw [Matrix.mul_assoc (Tmᵀ * Rm)]
      _ = Rm * (-Tm) := by rw [hiso]
      _ = (-1 : K) • (Rm * Tm) := by rw [Matrix.mul_neg, neg_one_smul]
  have hS2 : Tm * Tm = (-1 : K) • 1 := by rw [neg_one_smul]; exact hT2
  have hc0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hS2 hε (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgramR₁ (g := linPair T hTiso)
    (linPair_right T hTiso)
  set A := derivedTransport H₁⁻¹ 1 hS ⟨T, hT⟩ with hAdef
  have hAm : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)) := by
    rw [hAdef, coe_derivedTransport, Units.val_mul, Units.val_mul, inv_inv]
    calc ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * Tm * H₁ =
        ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * (Tm * H₁) := by
          rw [Matrix.mul_assoc]
      _ = ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat (-1 : K))) := by
          rw [hAH₁]
      _ = blkDiag n (jMat (-1 : K)) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]
  exact ⟨R₁, A, oTransport H₁⁻¹ 1 hS, hR₁m, hAm, oTransport_proj _ _ _ _⟩

theorem false_of_typeD_three {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) {n : ℕ} (hn5 : 5 ≤ n)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R))) {c t : X}
    (hcZ : c ∈ center X) (hc2 : orderOf c = 2) (ht2 : orderOf t = 2) (htZ : t ∉ center X)
    {Q₁ : Subgroup X} (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set π₀ : X →* StatedProj (matrixDerived (oQ R)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (center X)) with hπ₀
  have hπ₀s : Function.Surjective π₀ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ₀k : π₀.ker = center X := by
    ext y
    rw [MonoidHom.mem_ker, hπ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hxx : π₀ t * π₀ t = 1 := by rw [← map_mul, htt, map_one]
  have hx1 : π₀ t ≠ 1 := fun h => htZ (hπ₀k ▸ MonoidHom.mem_ker.mpr h)
  obtain ⟨T, hT, hxT, hT2 | hT2⟩ := P51e.Orth.exists_lift_sq h2 (by omega) hR hxx
  ·
    obtain ⟨w, hw, J, hJ, θ', hker', hJne, hJc, hNF, hθ'T, -⟩ :=
      P58b3.exists_sign_frame_rank_ker hK hR hker hT hT2 (by rw [← hxT]; exact hx1)
    set π : X →* StatedProj (matrixDerived (oQ (diagGL hw))) := θ'.toMonoidHom.comp π₀ with hπ
    have hπs : Function.Surjective π := θ'.surjective.comp hπ₀s
    have hπk : π.ker = center X := by
      ext y
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hπ₀k]
    have hπt : π t = projH _ ⟨signGL K J, hJ⟩ := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxT, hθ'T]
    obtain ⟨hR₁x, hR₁s, hR₁solv, hR₁odd, ⟨r, hr, hr3, hr1⟩, hnc⟩ :=
      facts_map_solvable_two hO π hπs hπk hcZ hc2 hQ₁ hcQ₁
    rw [hπt] at hR₁x hR₁s
    have hJev := P58b.OLie.even_card_of_signGL_mem hK hJ
    have hsum : J.card + Jᶜ.card = 2 * n := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ J
      rw [Fintype.card_fin] at this
      omega
    have hJcev : Even Jᶜ.card := by
      obtain ⟨a, ha⟩ := hJev
      exact ⟨n - a, by omega⟩
    obtain ⟨I, hI, h5I, hIcev⟩ : ∃ I : Finset (Fin (2 * n)), (I = J ∨ I = Jᶜ) ∧ 5 ≤ I.card ∧
        Even Iᶜ.card := by
      by_cases h5 : 5 ≤ J.card
      · exact ⟨J, Or.inl rfl, h5, hJcev⟩
      · exact ⟨Jᶜ, Or.inr rfl, by omega, by rw [compl_compl]; exact hJev⟩
    have hIc : Iᶜ.Nonempty := by
      rcases hI with rfl | rfl
      · exact hJc
      · rwa [compl_compl]
    exact false_of_sign_of_quasisimple hw hK3 hker' hJ hJne hJc hNF hI (by omega)
      (P58b3.isQuasisimple_blockP_of_five_le hw hK h5I hIc) hIcev hR₁x hR₁s hR₁solv hR₁odd hr hr3
      hr1 hnc
  ·
    obtain ⟨R₁, A, θ₂, hR₁m, hAm, hθ₂T⟩ := exists_pc_model hK hR hT hT2
    set π : X →* StatedProj (matrixDerived (oQ R₁)) := θ₂.toMonoidHom.comp π₀ with hπ
    have hπs : Function.Surjective π := θ₂.surjective.comp hπ₀s
    have hπk : π.ker = center X := by
      ext y
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hπ₀k]
    have hπt : π t = projH _ A := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxT, hθ₂T]
    obtain ⟨hR₁x, hR₁s, hR₁solv, -, ⟨r, hr, hr3, hr1⟩, -⟩ :=
      facts_map_solvable_two hO π hπs hπk hcZ hc2 hQ₁ hcQ₁
    rw [hπt] at hR₁x hR₁s
    exact hr1 (eq_one_of_odd_of_pc hK3 (by omega) hR₁m hAm hR₁x hR₁s hR₁solv hr
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hr3)))

end P58b3L

end CFSG.ComponentClassification.HarrisLit.T1
