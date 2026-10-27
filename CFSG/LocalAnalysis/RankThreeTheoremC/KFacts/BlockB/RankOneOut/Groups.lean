module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycLie
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.RankOneOut

open CFSG.AGLEmbedding.BlockCyc CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.QuasithinUnique

section Groups

theorem not_dvd_card_of_perfect {Q : Type*} [Group Q] [Finite Q] (hQ : commutator Q = ⊤)
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card (Q ⧸ Subgroup.center Q)) :
    ¬ p ∣ Nat.card Q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow : x ^ (Subgroup.center Q).index = 1 := by
    have hker : x ∈ (MonoidHom.transferCenterPow Q).ker :=
      Abelianization.commutator_subset_ker _ (hQ ▸ Subgroup.mem_top x)
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hker)
    rwa [MonoidHom.transferCenterPow_apply] at h1
  have h2 := orderOf_dvd_of_pow_eq_one hpow
  rw [hx, Subgroup.index_eq_card] at h2
  exact h h2

theorem commutator_mem_sup_centralizer {A : Type*} [Group A] {Q : Subgroup A}
    (hQ : commutator Q = ⊤)
    (hOut : ∀ α β : MulAut (↥Q ⧸ Subgroup.center ↥Q), α * β * α⁻¹ * β⁻¹ ∈
      (MulAut.conj : (↥Q ⧸ Subgroup.center ↥Q) →* MulAut (↥Q ⧸ Subgroup.center ↥Q)).range)
    {x y : A} (hx : x ∈ Subgroup.normalizer (Q : Set A))
    (hy : y ∈ Subgroup.normalizer (Q : Set A)) :
    x * y * x⁻¹ * y⁻¹ ∈ Q ⊔ Subgroup.centralizer (Q : Set A) := by
  have : Group.IsPerfect ↥Q := ⟨hQ⟩
  let N := Subgroup.normalizer (Q : Set A)
  let xn : ↥N := ⟨x, hx⟩
  let yn : ↥N := ⟨y, hy⟩
  let c : ↥N := xn * yn * xn⁻¹ * yn⁻¹
  have hcx : (c : A) = x * y * x⁻¹ * y⁻¹ := rfl
  let ρ : ↥N →* MulAut (↥Q ⧸ Subgroup.center ↥Q) :=
    (centerQuotientHom ↥Q).comp (Subgroup.normalizerMonoidHom Q)
  have h1 : ρ c ∈ (MulAut.conj : (↥Q ⧸ Subgroup.center ↥Q) →*
      MulAut (↥Q ⧸ Subgroup.center ↥Q)).range := by
    have : ρ c = ρ xn * ρ yn * (ρ xn)⁻¹ * (ρ yn)⁻¹ := by
      simp only [c, map_mul, map_inv]
    rw [this]
    exact hOut _ _
  obtain ⟨w, hw⟩ := h1
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Q) w
  have hconj : centerQuotientHom ↥Q (MulAut.conj q) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥Q) q) := by
    ext z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Q) z
    change onCenterQuotient (MulAut.conj q) (QuotientGroup.mk' _ z) = _
    rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
      map_inv]
  have heq : Subgroup.normalizerMonoidHom Q c = MulAut.conj q :=
    centerQuotientHom_injective ↥Q (hw.symm.trans hconj.symm)
  have hcent : (q : A)⁻¹ * (x * y * x⁻¹ * y⁻¹) ∈ Subgroup.centralizer (Q : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 := congrArg (fun φ : MulAut ↥Q => ((φ ⟨z, hz⟩ : ↥Q) : A)) heq
    change (c : A) * z * (c : A)⁻¹ = (q : A) * z * (q : A)⁻¹ at h2
    rw [← hcx]
    calc z * ((q : A)⁻¹ * c) = (q : A)⁻¹ * ((q : A) * z * (q : A)⁻¹) * c := by group
      _ = (q : A)⁻¹ * ((c : A) * z * (c : A)⁻¹) * c := by rw [h2]
      _ = (q : A)⁻¹ * c * z := by group
  have hdecomp : x * y * x⁻¹ * y⁻¹ = (q : A) * ((q : A)⁻¹ * (x * y * x⁻¹ * y⁻¹)) := by group
  rw [hdecomp]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left q.2) (Subgroup.mem_sup_right hcent)

theorem commutator_mem_range_conj_of_mulEquiv {J P : Type*} [Group J] [Group P] (e : J ≃* P)
    (hP : ∀ α β : MulAut P, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : P →* MulAut P).range)
    (α β : MulAut J) : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : J →* MulAut J).range := by
  have h1 := hP (MulAut.congr e α) (MulAut.congr e β)
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
  obtain ⟨p, hp⟩ := h1
  refine ⟨e.symm p, ?_⟩
  ext j
  have h2 := congrArg (fun φ : MulAut P => e.symm (φ (e j))) hp
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h2
  rw [MulAut.conj_apply, ← h2, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem not_three_dvd_two_pow_sub_one {f : ℕ} (hf : Odd f) : ¬ 3 ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  omega

theorem commutator_mem_range_conj_projectiveSL_three {K : Type} [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K - 1) (α β : MulAut (projectiveSL 3 K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp
    (OuterDerived.commutator_mem_linearAutGroup (K := K) le_rfl α β)
  have hc : Nat.Coprime (Nat.card Kˣ) 3 := by
    rw [Nat.card_units, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact h3
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ^ 3 = Matrix.GeneralLinearGroup.det A :=
    (powCoprime hc).surjective _
  rw [← hA]
  exact conjAut_mem_range_conj_of_det_eq_pow hμ.symm

theorem not_five_dvd_card_of_psl_three {Y : Type} [Group Y] {f : ℕ} (hf : Odd f)
    (hm : StatedClassicalModel Y .PSL 3 2 f) : ¬ 5 ∣ Nat.card Y := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_projectiveSL hm
  have hdvd : Nat.card Y ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.index_dvd_card (scalars 3 K)
  exact fun h5 => not_five_dvd_card_SL_three hK hf (h5.trans hdvd)

theorem rankOneOut_of_psl_three {A : Type} [Group A] {Q : Subgroup A} [Finite Q]
    (hQ : commutator Q = ⊤) {f : ℕ} (hf : Odd f)
    (hm : StatedClassicalModel (↥Q ⧸ Subgroup.center ↥Q) .PSL 3 2 f) :
    ¬ 5 ∣ Nat.card Q ∧ ∀ x ∈ Subgroup.normalizer (Q : Set A),
      ∀ y ∈ Subgroup.normalizer (Q : Set A),
        x * y * x⁻¹ * y⁻¹ ∈ Q ⊔ Subgroup.centralizer (Q : Set A) := by
  refine ⟨not_dvd_card_of_perfect hQ Nat.prime_five (not_five_dvd_card_of_psl_three hf hm), ?_⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_projectiveSL hm
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact not_three_dvd_two_pow_sub_one hf
  intro x hx y hy
  exact commutator_mem_sup_centralizer hQ
    (commutator_mem_range_conj_of_mulEquiv e (commutator_mem_range_conj_projectiveSL_three h3))
    hx hy

end Groups

section AltFive


theorem false_of_alternating_five_parabolic {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 5)) (T J : Subgroup Y) (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJ : J ≠ Subgroup.normalizer (T : Set Y))
    (hJtop : J ≠ ⊤) : False := by
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hcard)
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 2) ≃* Y :=
    ((projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)).trans e5).trans e.symm
  obtain ⟨i, j, hij⟩ := (borelQuotient_sl ePSL).exists_two_nodes T' J hNJ hJ hJtop
  have hi : i.val < 1 := i.isLt
  have hj : j.val < 1 := j.isLt
  exact hij (Fin.ext (by omega))

end AltFive

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.RankOneOut
