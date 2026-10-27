module

public import CFSG.LocalAnalysis.RankThreeUC.K518HANode

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

theorem two_le_pRank_of_commuting {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) (hao : orderOf a = p)
    (hbo : orderOf b = p) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    2 ≤ CFSG.Open.pRank p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E : Subgroup G := Subgroup.closure {a, b} with hE
  have hEH : E ≤ H := (Subgroup.closure_le H).2 (by
    rintro x (rfl | rfl)
    · exact ha
    · exact hb)
  have hS : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy
  have hpow : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.AGLEmbedding.ParabHub.pow_eq_one_of_mem_closure hS (fun s hs => by
      rcases hs with rfl | rfl
      · rw [← hao]; exact pow_orderOf_eq_one _
      · rw [← hbo]; exact pow_orderOf_eq_one _) hx
  have hcomm : IsMulCommutative E := Subgroup.isMulCommutative_closure hS
  have hEa : CFSG.Open.IsElemAbelian p E := ⟨hcomm, hpow⟩
  have hEp : IsPGroup p E := by
    refine (IsPGroup.iff_orderOf).2 fun x => ?_
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hpow x.1 x.2)
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (by simpa using h1 : orderOf x ∣ p ^ 1)
    exact ⟨j, hj⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hEp
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hkle : k ≤ 1 := by omega
    have hzE : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have hcz : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hao]
    have hcle : Nat.card E ≤ p := by
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hkle
        _ = p := pow_one p
    have heq : Subgroup.zpowers a = E :=
      Subgroup.eq_of_le_of_card_ge hzE (by rw [hcz]; exact hcle)
    exact hnot (heq ▸ Subgroup.subset_closure (by simp : b ∈ ({a, b} : Set G)))
  exact hk2.trans (CFSG.SectionRank.le_pRank hp.one_lt hEH hEa hk)

section Elements

variable {F : Type} [Field F] [CharP F 2]

private theorem su3_one_add_one : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1

private def su3GM : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 1]

private def su3UM : Matrix (Fin 3) (Fin 3) F := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

private theorem det_su3GM : (su3GM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h2 := su3_one_add_one (F := F)
  simp [su3GM, Matrix.det_fin_three]
  linear_combination -h2

private theorem det_su3UM : (su3UM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [su3UM, Matrix.det_fin_three]

variable (σ : F ≃+* F)

private theorem su3GM_unitary :
    conjTr σ (su3GM : Matrix (Fin 3) (Fin 3) F) * antidiag 3 * su3GM = antidiag 3 := by
  have h2 := su3_one_add_one (F := F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, su3GM, antidiag, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, h2]

private theorem su3UM_unitary :
    conjTr σ (su3UM : Matrix (Fin 3) (Fin 3) F) * antidiag 3 * su3UM = antidiag 3 := by
  have h2 := su3_one_add_one (F := F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, su3UM, antidiag, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, h2]

variable {σ}

private theorem su3GM_cube : (su3GM : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
  have h2 := su3_one_add_one (F := F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su3GM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h2]

private theorem su3GM_su3UM_ne : (su3GM : Matrix (Fin 3) (Fin 3) F) * su3UM ≠ su3UM * su3GM := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [su3GM, su3UM, Matrix.mul_apply, Fin.sum_univ_three] at this

private def su3G : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero su3GM (by rw [det_su3GM]; exact one_ne_zero)

private def su3U : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero su3UM (by rw [det_su3UM]; exact one_ne_zero)

private theorem su3G_mem : su3G ∈ SU σ 3 := by
  refine ⟨?_, ?_⟩
  · simpa [su3G] using det_su3GM (F := F)
  · simpa [su3G] using su3GM_unitary σ

private theorem su3U_mem : su3U ∈ SU σ 3 := by
  refine ⟨?_, ?_⟩
  · simpa [su3U] using det_su3UM (F := F)
  · simpa [su3U] using su3UM_unitary σ

private theorem exists_su3_order_three :
    ∃ g u : SU σ 3, orderOf g = 3 ∧ g * u ≠ u * g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨su3G, su3G_mem⟩, ⟨su3U, su3U_mem⟩, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      apply Units.ext
      change (su3GM : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
      exact su3GM_cube
    · intro h
      have h' := congrArg (fun x : SU σ 3 => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
      have := congrFun (congrFun h' 0) 0
      simp [su3G, su3GM] at this
  · intro h
    have h' := congrArg (fun x : SU σ 3 => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    exact su3GM_su3UM_ne h'

end Elements

section Four

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem su3_two_le_pRank (hF : Nat.card F = (2 ^ 1) ^ 2) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (SU (unitaryInvolution F 2 1) 3)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨ω, -, hω⟩ : ∃ ω ∈ (Finset.univ : Finset F), ω ∉ ({0, 1} : Finset F) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      rw [Finset.card_univ, hcard]
      exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num))
  have hω0 : ω ≠ 0 := fun h => hω (by simp [h])
  have hω1 : ω ≠ 1 := fun h => hω (by simp [h])
  have hω3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hcard] at this
  have hσω : unitaryInvolution F 2 1 ω * ω = 1 := by
    rw [unitaryInvolution_apply, pow_one, ← pow_succ, show 2 + 1 = 3 from rfl, hω3]
  set σ := unitaryInvolution F 2 1 with hσ
  set sM : Matrix (Fin 3) (Fin 3) F := ω • (1 : Matrix (Fin 3) (Fin 3) F) with hsM
  have hdet : sM.det = 1 := by
    rw [hsM, Matrix.det_smul, Matrix.det_one, mul_one]
    simpa using hω3
  have hsunit : conjTr σ sM * antidiag 3 * sM = antidiag 3 := by
    have h1 : conjTr σ sM = σ ω • (1 : Matrix (Fin 3) (Fin 3) F) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [conjTr, hsM]
      · simp [conjTr, hsM, Matrix.one_apply, hij, Ne.symm hij]
    rw [h1, hsM, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, smul_smul,
      mul_comm ω (σ ω), hσω, one_smul]
  let s : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero sM (by rw [hdet]; exact one_ne_zero)
  have hsmem : s ∈ SU σ 3 := ⟨by simpa [s] using hdet, by simpa [s] using hsunit⟩
  have hcomm : ∀ x : GL (Fin 3) F, s * x = x * s := by
    intro x
    apply Units.ext
    change sM * (x : Matrix (Fin 3) (Fin 3) F) = (x : Matrix (Fin 3) (Fin 3) F) * sM
    rw [hsM, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]
  obtain ⟨g, u, hg3, hgu⟩ := exists_su3_order_three (σ := σ)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : orderOf (⟨s, hsmem⟩ : SU σ 3) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      apply Units.ext
      change sM ^ 3 = 1
      rw [hsM, smul_pow, one_pow, hω3, one_smul]
    · intro h
      have h' := congrArg (fun x : SU σ 3 => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
      have := congrFun (congrFun h' 0) 0
      simp [s, hsM] at this
      exact hω1 this
  refine two_le_pRank_of_commuting Nat.prime_three (H := ⊤) (a := ⟨s, hsmem⟩) (b := g)
    trivial trivial hs3 hg3 ?_ ?_
  · exact Subtype.ext (hcomm _)
  · rintro ⟨m, hm⟩
    apply hgu
    have hc : Commute (⟨s, hsmem⟩ : SU σ 3) u := Subtype.ext (hcomm _)
    rw [← hm]
    exact (hc.zpow_left m).eq

end Four

section NodeGoodSU3

open CFSG.AGLEmbedding.ParabPrime

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

private theorem su3_dvd_card_inn (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpΛ : p ∣ Nat.card (SU (unitaryInvolution F 2 f) 3)) :
    p ∣ Nat.card (MulAut.conj : SU (unitaryInvolution F 2 f) 3 →*
      MulAut (SU (unitaryInvolution F 2 f) 3)).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hex : ∃ x : SU (unitaryInvolution F 2 f) 3, orderOf x = p ∧
      ∃ u : SU (unitaryInvolution F 2 f) 3, x * u ≠ u * x := by
    by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨g, u, hg, hgu⟩ := exists_su3_order_three (σ := unitaryInvolution F 2 f)
      exact ⟨g, hg, u, hgu⟩
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpΛ
      refine ⟨x, hx, ?_⟩
      by_contra hcomm
      push Not at hcomm
      have hz : x ∈ Subgroup.center (SU (unitaryInvolution F 2 f) 3) :=
        Subgroup.mem_center_iff.2 fun u => (hcomm u).symm
      have h3 : x ^ 3 = 1 := su_three_center_pow_three hF hq hz
      have : p ∣ 3 := hx ▸ orderOf_dvd_of_pow_eq_one h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
  obtain ⟨x, hx, u, hxu⟩ := hex
  have hne : (MulAut.conj x : MulAut (SU (unitaryInvolution F 2 f) 3)) ≠ 1 := by
    intro h
    apply hxu
    have := congrArg (fun a : MulAut (SU (unitaryInvolution F 2 f) 3) => a u) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [this]
  have hpow : (MulAut.conj x : MulAut (SU (unitaryInvolution F 2 f) 3)) ^ p = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hord : orderOf (MulAut.conj x : MulAut (SU (unitaryInvolution F 2 f) 3)) = p :=
    orderOf_eq_prime hpow hne
  have := Subgroup.orderOf_dvd_natCard (MulAut.conj : SU (unitaryInvolution F 2 f) 3 →*
    MulAut (SU (unitaryInvolution F 2 f) 3)).range
    (⟨x, rfl⟩ : (MulAut.conj x : MulAut (SU (unitaryInvolution F 2 f) 3)) ∈
      (MulAut.conj : SU (unitaryInvolution F 2 f) 3 →*
        MulAut (SU (unitaryInvolution F 2 f) 3)).range)
  rwa [hord] at this

theorem nodeGood_su3 (h2 : K518RkSU3) (hf : 1 ≤ f) (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpΛ : p ∣ Nat.card (SU (unitaryInvolution F 2 f) 3)) :
    NodeGood (SU (unitaryInvolution F 2 f) 3) p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hf1 : f = 1
  · subst hf1
    right
    have hc := CFSG.LieType.Steinberg.card_SU_three (p := 2) (f := 1) hF
    rw [hc] at hpΛ
    have h216 : p ∣ 2 ^ 3 * 3 ^ 3 := by
      have : (2 ^ 1) ^ 3 * ((2 ^ 1) ^ 2 - 1) * ((2 ^ 1) ^ 3 + 1) = 2 ^ 3 * 3 ^ 3 := by norm_num
      rwa [this] at hpΛ
    have hp3 : p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).1 h216 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
    subst hp3
    exact su3_two_le_pRank hF
  · left
    have hq : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := fun h => by
      have := (Prod.mk.inj h).2
      omega
    have hqs' := CFSG.LieType.Universal.Unitary.isQuasisimple_SU (p := 2) (f := f) hF (le_refl 3) hnq
    have hqs : CFSG.Open.IsQuasisimple (SU (unitaryInvolution F 2 f) 3) :=
      ⟨hqs'.1.commutator_eq_top, hqs'.2.1⟩
    refine ⟨fun N hN hN2 => ?_, fun ψ hψ hnot => ?_, su3_dvd_card_inn hF hq hp hp2 hpΛ⟩
    · haveI := hN
      exact normal_two_eq_bot_of_quasisimple hqs
        (fun z hz => ⟨3, by decide, su_three_center_pow_three hF hq hz⟩) N hN2
    · exact h2 F f hf hF p hp hp2 hpΛ ψ hψ hnot

end NodeGoodSU3

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
