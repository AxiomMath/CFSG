module

public import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open

theorem pRank_top_statedSp_eq {p : ℕ} [Fact p.Prime] (hp : Odd p) {K : Type} [Field K]
    [Finite K] (hpK : ¬ p ∣ Nat.card K) (n : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedSp n K)) =
      (if Even (orderOf (Nat.card K : ZMod p)) then 2 * n else n) /
        orderOf (Nat.card K : ZMod p) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card]
  exact CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel p
    (one_le_weirA hpK') fun P => sylow_Sp hp K hpK' n P

private theorem not_dvd_of_dvd_sq_sub_one {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q ^ 2 - 1)
    (hp1 : p ≠ 1) : ¬ p ∣ q := by
  intro hd
  have h2 : p ∣ q ^ 2 := hd.trans (dvd_pow_self q two_ne_zero)
  have h3 : p ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h2 h
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have : q ^ 2 - (q ^ 2 - 1) = 1 := by omega
  rw [this] at h3
  exact hp1 (Nat.dvd_one.1 h3)

private theorem orderOf_natCast_dvd_two {p q : ℕ} [Fact p.Prime] (hq : 1 ≤ q)
    (h : p ∣ q ^ 2 - 1) : orderOf (q : ZMod p) ∣ 2 := by
  apply orderOf_dvd_of_pow_eq_one
  have := (ZMod.natCast_eq_zero_iff (q ^ 2 - 1) p).2 h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
  exact this

theorem pRank_top_statedSp_eq_of_dvd {p : ℕ} [Fact p.Prime] (hp : Odd p) {K : Type} [Field K]
    [Finite K] (hpK : p ∣ Nat.card K ^ 2 - 1) (n : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedSp n K)) = n := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hpK' : ¬ p ∣ Nat.card K := not_dvd_of_dvd_sq_sub_one hq hpK (Fact.out : p.Prime).ne_one
  rw [pRank_top_statedSp_eq hp hpK' n]
  have hdvd := orderOf_natCast_dvd_two (p := p) hq hpK
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · rw [h1]; simp
  · rw [h1]; simp

private theorem pRank_top_eq_of_sylow_mulEquiv {p : ℕ} [hp : Fact p.Prime] {G G' : Type}
    [Group G] [Finite G] [Group G'] [Finite G'] (P : Sylow p G) (P' : Sylow p G')
    (φ : P ≃* P') :
    CFSG.Open.pRank p (⊤ : Subgroup G) = CFSG.Open.pRank p (⊤ : Subgroup G') := by
  calc CFSG.Open.pRank p (⊤ : Subgroup G) = CFSG.Open.pRank p (P : Subgroup G) :=
        ((CFSG.SectionRank.pRank_sylow P).1).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup P) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P : Subgroup G)
    _ = CFSG.Open.pRank p (⊤ : Subgroup P') :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt φ
    _ = CFSG.Open.pRank p (P' : Subgroup G') :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P' : Subgroup G')).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup G') := (CFSG.SectionRank.pRank_sylow P').1

theorem pRank_top_orthogonalGroup_odd_eq {p : ℕ} [Fact p.Prime] (hp : Odd p) {K : Type}
    [Field K] [Finite K] (hK : Odd (Nat.card K)) (hpK : ¬ p ∣ Nat.card K) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ}
    (hdim : Module.finrank K V = 2 * n + 1) (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    [Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q)] :
    CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSp n K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Odd (Fintype.card K) := by rwa [← Nat.card_eq_fintype_card]
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨P⟩ : Nonempty (Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q)) := inferInstance
  obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
  obtain ⟨φ⟩ := sylow_orthogonal_odd hp hK' hpK' hdim Q hQ P P'
  exact pRank_top_eq_of_sylow_mulEquiv P P' φ

theorem pRank_top_statedOmega_quadOdd_le {p : ℕ} [Fact p.Prime] (hp : Odd p) {K : Type}
    [Field K] [Finite K] (hK : Odd (Nat.card K)) (hpK : ¬ p ∣ Nat.card K) (n : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedOmega (StatedQuadOdd n K))) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSp n K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Odd (Fintype.card K) := by rwa [← Nat.card_eq_fintype_card]
  set Q := CFSG.LieType.Universal.Spin.quadOdd n K with hQdef
  have hQ : ⇑Q = StatedQuadOdd n K := CFSG.LieType.Universal.Spin.coe_quadOdd n K
  have h2 : ringChar K ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    exact Nat.not_even_iff_odd.2 hK' (Nat.even_iff.2 this)
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K (Ring.two_ne_zero h2)
  have hdim : Module.finrank K (Fin n ⊕ Fin n ⊕ Unit → K) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  haveI : Finite ((Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K)) :=
    Finite.of_injective (fun g => (g : (Fin n ⊕ Fin n ⊕ Unit → K) → (Fin n ⊕ Fin n ⊕ Unit → K)))
      fun g h hgh => LinearEquiv.ext (congrFun hgh)
  have hmem : ∀ x : StatedOmega (StatedQuadOdd n K),
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ K x.1 ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := fun x =>
    Subgroup.commutator_le_of_le le_rfl le_rfl (Subgroup.mem_comap.1
      ((CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ).le x.2))
  let f : StatedOmega (StatedQuadOdd n K) →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ K).toMonoidHom.comp
      (StatedOmega (StatedQuadOdd n K)).subtype).codRestrict _ hmem
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ K).injective
      (congrArg Subtype.val hxy))
  have h := CFSG.SectionRank.pRank_top_le_of_injective (Fact.out : p.Prime).one_lt f hf
  rwa [pRank_top_orthogonalGroup_odd_eq hp hK hpK hdim Q hnd] at h

theorem sq_eq_one_of_scalar_mem_statedOmega_quadOdd {n : ℕ} {K : Type} [Field K] (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n ⊕ Unit) c ∈
      StatedOmega (StatedQuadOdd n K)) : c ^ 2 = 1 := by
  have hQ := CFSG.LieType.Universal.Spin.coe_quadOdd n K
  have h1 := (CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ).le h
  have h2 := Subgroup.commutator_le_of_le le_rfl le_rfl (Subgroup.mem_comap.1 h1)
  have h3 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 h2 (Pi.single (.inr (.inr ())) 1)
  rw [MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] at h3
  simp [CFSG.LieType.Universal.Spin.quadOdd_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mulVec_diagonal] at h3
  rcases h3 with rfl | rfl <;> simp

private theorem not_dvd_two_of_odd {p : ℕ} (hp : p.Prime) (hodd : Odd p) : ¬ p ∣ 2 := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
  subst this
  exact absurd hodd (by decide)

theorem pRank_top_statedProj_statedSp_eq_of_dvd {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {K : Type} [Field K] [Finite K] (hpK : p ∣ Nat.card K ^ 2 - 1) {n : ℕ} (hn : 1 ≤ n) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n K))) = n := by
  rw [pRank_top_statedProj_eq (not_dvd_two_of_odd (Fact.out) hp)
    fun c hc => (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c).1 hc]
  exact pRank_top_statedSp_eq_of_dvd hp hpK n

theorem pRank_top_statedProj_statedOmega_quadOdd_le_of_dvd {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (n : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K)))) ≤ n := by
  have hpK' : ¬ p ∣ Nat.card K :=
    not_dvd_of_dvd_sq_sub_one Nat.card_pos hpK (Fact.out : p.Prime).ne_one
  rw [pRank_top_statedProj_eq (not_dvd_two_of_odd (Fact.out) hp)
    fun c hc => sq_eq_one_of_scalar_mem_statedOmega_quadOdd c hc]
  exact (pRank_top_statedOmega_quadOdd_le hp hK hpK' n).trans
    (pRank_top_statedSp_eq_of_dvd hp hpK n).le

end CFSG.GroupTheory.WeirSylow
