module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaPi
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaWreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaParams

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module QuadraticMap

@[expose] def NoncommSylowData {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) : Prop :=
  ∃ (G : Type) (_ : Group G) (ψ : G →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q)),
    Function.Injective ψ ∧ IsPGroup p G ∧ ∃ x y : G, x * y ≠ y * x

@[expose] def OSylowData {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p a r : ℕ) (μ₀ : ℤ) : Prop :=
  (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
      a * r + r.factorial.factorization p ∧
    (1 ≤ r → r < p → OmegaFrameData Q p a r μ₀) ∧ (p ≤ r → NoncommSylowData Q p)

section Blocks

variable {K : Type} [Field K] [Fintype K] {p : ℕ} [hp : Fact p.Prime]

theorem exists_split_block (hpK : ¬ p ∣ Fintype.card K) :
    ∃ (S₀ : FormSpace K K) (ρ : Multiplicative (ZMod (p ^ weirA p K)) →* S₀.isom)
      (J₀ φ₀ : S₀.isom), IsPlusQuadSpace S₀ ∧ finrank K S₀.V = 2 * weirE p K ∧
      Function.Injective ρ ∧ (∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹) ∧
      ∀ c, φ₀ * ρ c * φ₀⁻¹ = ρ (c ^ (Fintype.card K : ℤ)) := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  haveI : NeZero (weirE p K) := ⟨(weirE_pos hpK).ne'⟩
  haveI : NeZero (p ^ weirA p K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let L := FiniteField.Extension K (ringChar K) (weirE p K)
  have hLcard : Nat.card L = Fintype.card K ^ weirE p K := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  have hLdim : finrank K L = weirE p K := FiniteField.finrank_extension K _ _
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim, hρ, hJ, hφ⟩ :=
    exists_orthBlock_split K (L := L) (m := p ^ weirA p K) (by rw [hLcard]; exact pow_weirA_dvd)
  exact ⟨S₀, ρ, J₀, φ₀, hS₀, by rw [hdim, hLdim], hρ, hJ, hφ⟩

theorem exists_aniso_block (hpK : ¬ p ∣ Fintype.card K) {f : ℕ} (hf : weirE p K = 2 * f) :
    ∃ (S₀ : FormSpace K K) (ρ : Multiplicative (ZMod (p ^ weirA p K)) →* S₀.isom)
      (J₀ φ₀ : S₀.isom), IsQuadSpace S₀ ∧ finrank K S₀.V = 2 * f ∧
      Function.Injective ρ ∧ (∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹) ∧
      ∀ c, φ₀ * ρ c * φ₀⁻¹ = ρ (c ^ (Fintype.card K : ℤ)) := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  haveI : NeZero (weirE p K) := ⟨(weirE_pos hpK).ne'⟩
  haveI : NeZero (p ^ weirA p K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hf0 : 0 < f := by have := weirE_pos hpK; omega
  let L := FiniteField.Extension K (ringChar K) (weirE p K)
  have hLdim : finrank K L = weirE p K := FiniteField.finrank_extension K _ _
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim, hρ, hJ, hφ⟩ :=
    exists_orthBlock_aniso K (L := L) hf0 (hLdim.trans hf) (m := p ^ weirA p K)
      (pow_weirA_dvd_pow_add_one hpK hf)
  exact ⟨S₀, ρ, J₀, φ₀, hS₀, by rw [hdim, hLdim, hf], hρ, hJ, hφ⟩

end Blocks

section Frames

variable {K : Type} [Field K] [Fintype K] {p : ℕ} [hp : Fact p.Prime] {V : Type}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem omegaFrameData_split_even (hpK : ¬ p ∣ Fintype.card K) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {n : ℕ}
    (hdim : finrank K V = 2 * n) {r : ℕ} (hrn : weirE p K * r ≤ n)
    (htype : weirE p K * r = n → IsPlusType Q) :
    OmegaFrameData Q p (weirA p K) r (Fintype.card K : ℤ) := by
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim₀, hρ, hJ, hφ⟩ := exists_split_block (K := K) (p := p) hpK
  have hS₀q : IsQuadSpace S₀ := by
    obtain ⟨Q₀, hQ₀F, hnd, -⟩ := hS₀
    exact ⟨Q₀, hQ₀F, hnd⟩
  obtain ⟨QS, hSF, hQS, hplusS⟩ := isPlusQuadSpace_pi (fun _ : Fin r => S₀) (fun _ => hS₀)
  have hSdim : finrank K (FormSpace.pi fun _ : Fin r => S₀).V = 2 * (weirE p K * r) := by
    rw [FormSpace.finrank_pi]
    simp only [hdim₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  obtain ⟨ψ, hψ, hψD⟩ := exists_orthogonal_embedding_dickson
    (FormSpace.pi fun _ : Fin r => S₀) hSF hQS hSdim (MonoidHom.id _) Function.injective_id hQ hT
    hdim hrn (fun h => iff_of_true hplusS (htype h))
  exact omegaFrameData_of_embedding S₀ hS₀q (d := weirE p K) hdim₀ ρ hρ J₀ φ₀ hJ hφ ψ hψ
    fun h2 g hev => hψD h2 g hev

theorem omegaFrameData_split_odd (hpK : ¬ p ∣ Fintype.card K) (h2 : ringChar K ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n + 1) {r : ℕ}
    (hrn : weirE p K * r ≤ n) : OmegaFrameData Q p (weirA p K) r (Fintype.card K : ℤ) := by
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim₀, hρ, hJ, hφ⟩ := exists_split_block (K := K) (p := p) hpK
  have hS₀q : IsQuadSpace S₀ := by
    obtain ⟨Q₀, hQ₀F, hnd, -⟩ := hS₀
    exact ⟨Q₀, hQ₀F, hnd⟩
  obtain ⟨QS, hSF, hQS, -⟩ := isPlusQuadSpace_pi (fun _ : Fin r => S₀) (fun _ => hS₀)
  have hSdim : finrank K (FormSpace.pi fun _ : Fin r => S₀).V = 2 * (weirE p K * r) := by
    rw [FormSpace.finrank_pi]
    simp only [hdim₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  obtain ⟨ψ, hψ⟩ := exists_injective_orthogonal_of_model_odd h2 (FormSpace.pi fun _ : Fin r => S₀)
    hSF hQS hSdim (MonoidHom.id _) Function.injective_id hQ hdim hrn
  exact omegaFrameData_of_embedding S₀ hS₀q (d := weirE p K) hdim₀ ρ hρ J₀ φ₀ hJ hφ ψ hψ
    fun h => absurd (ringChar.eq K 2) h2

theorem omegaFrameData_aniso_even (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {f : ℕ}
    (hf : weirE p K = 2 * f) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {n : ℕ}
    (hdim : finrank K V = 2 * n) {r : ℕ} (hr1 : 1 ≤ r) (hrp : r < p) (hrn : f * r ≤ n)
    (htype : f * r = n → (IsPlusType Q ↔ Even r)) :
    OmegaFrameData Q p (weirA p K) r (Fintype.card K : ℤ) := by
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim₀, hρ, hJ, hφ⟩ := exists_aniso_block (K := K) (p := p) hpK hf
  obtain ⟨QS, hSF, hQS⟩ := isQuadSpace_pi (fun _ : Fin r => S₀) (fun _ => hS₀)
  have hSdim : finrank K (FormSpace.pi fun _ : Fin r => S₀).V = 2 * (f * r) := by
    rw [FormSpace.finrank_pi]
    simp only [hdim₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have htypeS : IsPlusType QS ↔ Even r := by
    haveI : NeZero (p ^ weirA p K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    refine isPlusType_iff_even hp1 hpK hf hQS hr1 hSdim
      ((isomEquivOrthogonal _ hSF).toMonoidHom.comp (piTorus S₀ ρ r))
      ((isomEquivOrthogonal _ hSF).injective.comp (piTorus_injective S₀ hρ r)) ?_
    have hv : padicValNat p r.factorial = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => by
        have := (Nat.Prime.dvd_factorial hp.out).1 h
        omega
    rw [hv, add_zero, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, ← pow_mul]
  obtain ⟨ψ, hψ, hψD⟩ := exists_orthogonal_embedding_dickson
    (FormSpace.pi fun _ : Fin r => S₀) hSF hQS hSdim (MonoidHom.id _) Function.injective_id hQ hT
    hdim hrn (fun h => htypeS.trans (htype h).symm)
  exact omegaFrameData_of_embedding S₀ hS₀ (d := f) hdim₀ ρ hρ J₀ φ₀ hJ hφ ψ hψ
    fun h2 g hev => hψD h2 g hev

theorem omegaFrameData_aniso_odd (hpK : ¬ p ∣ Fintype.card K) {f : ℕ} (hf : weirE p K = 2 * f)
    (h2 : ringChar K ≠ 2) (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank K V = 2 * n + 1) {r : ℕ} (hrn : f * r ≤ n) :
    OmegaFrameData Q p (weirA p K) r (Fintype.card K : ℤ) := by
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim₀, hρ, hJ, hφ⟩ := exists_aniso_block (K := K) (p := p) hpK hf
  obtain ⟨QS, hSF, hQS⟩ := isQuadSpace_pi (fun _ : Fin r => S₀) (fun _ => hS₀)
  have hSdim : finrank K (FormSpace.pi fun _ : Fin r => S₀).V = 2 * (f * r) := by
    rw [FormSpace.finrank_pi]
    simp only [hdim₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  obtain ⟨ψ, hψ⟩ := exists_injective_orthogonal_of_model_odd h2 (FormSpace.pi fun _ : Fin r => S₀)
    hSF hQS hSdim (MonoidHom.id _) Function.injective_id hQ hdim hrn
  exact omegaFrameData_of_embedding S₀ hS₀ (d := f) hdim₀ ρ hρ J₀ φ₀ hJ hφ ψ hψ
    fun h => absurd (ringChar.eq K 2) h2

end Frames

section Sylow

variable {K : Type} [Field K] [Fintype K] {p : ℕ} [hp : Fact p.Prime] {V : Type}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem not_dvd_sq_sub_one_of_rank_two {k : ℕ} (hk : 3 ≤ k)
    (hr : (if Even (weirE p K) then 2 * k else k) / weirE p K = 2) :
    ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 2 - 1 := by
  intro hd
  have he : weirE p K ∣ 2 := (dvd_pow_sub_one_iff_weirE 2).1 hd
  rcases (Nat.dvd_prime Nat.prime_two).1 he with h1 | h2
  · rw [h1] at hr
    simp at hr
    omega
  · rw [h2] at hr
    simp at hr
    omega

theorem noncommSylowData_of_embedding (hpK : ¬ p ∣ Fintype.card K) {N : ℕ}
    (hN : p ≤ N / weirE p K)
    (ψ : sigmaModel p (weirE p K) (weirA p K) N →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (hψ : Function.Injective ψ) : NoncommSylowData Q p :=
  ⟨_, inferInstance, ψ, hψ, isPGroup_sigmaModel p _ _ N,
    exists_noncomm_sigmaModel p (one_le_weirA hpK) hN⟩

theorem osylowData_odd (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) (h2 : ringChar K ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) (hdim : finrank K V = 2 * n + 1) (hQ : (polarBilin Q).Nondegenerate) :
    ∃ r : ℕ, OSylowData Q p (weirA p K) r (Fintype.card K : ℤ) ∧
      (r = 2 → ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 2 - 1) := by
  refine ⟨(if Even (weirE p K) then 2 * n else n) / weirE p K, ⟨?_, ?_, ?_⟩,
    fun hr2 => not_dvd_sq_sub_one_of_rank_two hn hr2⟩
  · rw [odd_dim_params hp1 hpK h2 hdim hQ, Nat.factorization_def _ hp.out]
  · intro hr1 hrp
    by_cases hev : Even (weirE p K)
    · obtain ⟨f, hf⟩ := hev
      have hf' : weirE p K = 2 * f := by omega
      have hr : (if Even (weirE p K) then 2 * n else n) / weirE p K = n / f := by
        rw [if_pos ⟨f, hf⟩, hf', Nat.mul_div_mul_left n f two_pos]
      rw [hr]
      exact omegaFrameData_aniso_odd hpK hf' h2 hQ hdim (Nat.mul_div_le n f)
    · rw [if_neg hev]
      exact omegaFrameData_split_odd hpK h2 hQ hdim (Nat.mul_div_le n _)
  · intro hpr
    by_cases hev : Even (weirE p K)
    · obtain ⟨f, hf⟩ := hev
      have hf' : weirE p K = 2 * f := by omega
      rw [if_pos ⟨f, hf⟩] at hpr
      obtain ⟨ψ, hψ⟩ := exists_injective_sigmaModel_aniso_odd h2 hpK hf' hQ hdim (le_refl n)
      exact noncommSylowData_of_embedding hpK hpr ψ hψ
    · rw [if_neg hev] at hpr
      obtain ⟨ψ, hψ⟩ := exists_injective_sigmaModel_split_odd h2 hpK hQ hdim (le_refl n)
      exact noncommSylowData_of_embedding hpK hpr ψ hψ

theorem osylowData_even (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {n : ℕ} (hn : 4 ≤ n)
    (hdim : finrank K V = 2 * n) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q)) :
    ∃ r : ℕ, OSylowData Q p (weirA p K) r (Fintype.card K : ℤ) ∧
      (r = 2 → ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 2 - 1) := by
  obtain ⟨k, hk3, hkn, hcard, hts, hta⟩ := even_dim_params hp1 hpK hn hdim hQ hε
  refine ⟨(if Even (weirE p K) then 2 * k else k) / weirE p K, ⟨?_, ?_, ?_⟩,
    fun hr2 => not_dvd_sq_sub_one_of_rank_two hk3 hr2⟩
  · rw [hcard, Nat.factorization_def _ hp.out]
  · intro hr1 hrp
    by_cases hev : Even (weirE p K)
    · obtain ⟨f, hf⟩ := hev
      have hf' : weirE p K = 2 * f := by omega
      have hr : (if Even (weirE p K) then 2 * k else k) / weirE p K = k / f := by
        rw [if_pos ⟨f, hf⟩, hf', Nat.mul_div_mul_left k f two_pos]
      rw [hr] at hr1 hrp ⊢
      exact omegaFrameData_aniso_even hp1 hpK hf' hQ hT hdim hr1 hrp
        ((Nat.mul_div_le k f).trans hkn) (hta f hf')
    · have hr : (if Even (weirE p K) then 2 * k else k) / weirE p K = k / weirE p K := by
        rw [if_neg hev]
      rw [hr]
      exact omegaFrameData_split_even hpK hQ hT hdim ((Nat.mul_div_le k _).trans hkn) (hts hev)
  · intro hpr
    by_cases hev : Even (weirE p K)
    · obtain ⟨f, hf⟩ := hev
      have hf' : weirE p K = 2 * f := by omega
      rw [if_pos ⟨f, hf⟩] at hpr
      obtain ⟨ψ, hψ⟩ := exists_injective_sigmaModel_aniso hp1 hpK hf' hQ hdim hkn (hta f hf')
      exact noncommSylowData_of_embedding hpK hpr ψ hψ
    · rw [if_neg hev] at hpr
      obtain ⟨ψ, hψ⟩ := exists_injective_sigmaModel_split hpK hQ hdim hkn (hts hev)
      exact noncommSylowData_of_embedding hpK hpr ψ hψ

end Sylow

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
