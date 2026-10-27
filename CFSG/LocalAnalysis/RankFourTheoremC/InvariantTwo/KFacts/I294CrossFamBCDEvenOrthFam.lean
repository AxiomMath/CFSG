module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenOrthRank
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial

section Rank

variable {p : ℕ} [hp : Fact p.Prime]

theorem crossAt_of_rank {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (hrank : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H))
    (hbig : ∀ y₀ : H, y₀ ^ p = 1 → 3 ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set H))) :
    (CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) = 2 →
      ∀ R : Sylow p (H ⧸ N), IsMulCommutative (R : Subgroup (H ⧸ N))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) → ∀ y : H ⧸ N, y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (H ⧸ N)))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hHL : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) = CFSG.Open.pRank p (⊤ : Subgroup H) :=
    CFSG.SectionRank.pRank_quotient_eq N hN
  refine ⟨fun h2 R => ?_, fun h3 y hy => ?_⟩
  · exfalso
    omega
  · obtain ⟨z, hzp, rfl⟩ := exists_pow_eq_one_lift N hN y hy
    have h3H : 3 ≤ CFSG.Open.pRank p (centralizer ({z} : Set H)) := hbig z hzp
    obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1
      (centralizer ({z} : Set H))
    have hFy : ∀ f ∈ E, f * z = z * f := fun f hf => by
      have := hEle hf
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    have := le_pRank_centralizer_quotient N hN hE hEcard hFy
    omega

end Rank

section Omega

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {p : ℕ} [hp : Fact p.Prime] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def isoGL (Q : QuadraticForm K (ι → K)) : Subgroup (GL ι K) :=
  (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom

theorem mem_isoGL_iff (hQ : ⇑Q = Q₀) {g : GL ι K} :
    g ∈ isoGL Q ↔ ∀ v, Q₀ ((g : Matrix ι ι K) *ᵥ v) = Q₀ v := by
  rw [isoGL, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  refine forall_congr' fun v => ?_
  rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ]

@[expose] noncomputable def isoGLEquiv (Q : QuadraticForm K (ι → K)) :
    isoGL Q ≃* TauCeti.QuadraticMap.orthogonalGroup Q :=
  ((isoGL Q).equivMapOfInjective (toLinEquiv ι K).toMonoidHom (toLinEquiv ι K).injective).trans
    (MulEquiv.subgroupCongr
      (Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

theorem not_dvd_card_scalars_omega (hp2 : p ≠ 2) (hQ : ⇑Q = Q₀)
    (hhom : ∀ (c : K) (w : ι → K), Q₀ (c • w) = c ^ 2 * Q₀ w) {w₀ : ι → K} (hw₀ : Q₀ w₀ = 1) :
    ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)) := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨c, hc⟩ : ((z : StatedOmega Q₀) : GL ι K) ∈ StatedScalars ι K := z.2
  have hiso' : ∀ v, Q₀ (((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ v) =
      Q₀ v := by
    rw [hc]
    exact isometry_of_mem_statedOmega hQ (z : StatedOmega Q₀).2
  have hc2 := sq_eq_one_of_scalar_isometry hhom hw₀ c hiso'
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((z : StatedOmega Q₀) : GL ι K) ^ 2 = 1
    rw [← hc, ← map_pow, hc2, map_one]
  have := Nat.le_of_dvd two_pos (hz ▸ orderOf_dvd_of_pow_eq_one hz2)
  have hp2' : 2 ≤ p := hp.out.two_le
  omega

theorem crossAt_statedProj_omega_even (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hee : Even e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hab : CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)))
    (hhom : ∀ (c : K) (w : ι → K), Q₀ (c • w) = c ^ 2 * Q₀ w) {w₀ : ι → K} (hw₀ : Q₀ w₀ = 1)
    (hlarge : p * e ≤ Fintype.card ι) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedOmega Q₀)),
        IsMulCommutative (R : Subgroup (StatedProj (StatedOmega Q₀)))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) →
      ∀ y : StatedProj (StatedOmega Q₀), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedOmega Q₀))))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hp2 : p ≠ 2 := by omega
  have hp2' : Odd p := hp.out.odd_of_ne_two hp2
  have hpe1 : p ∣ Nat.card K ^ e - 1 := (hpe e).2 dvd_rfl
  have h5e : 5 * e ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    have : 5 * e ≤ p * e := Nat.mul_le_mul_right e hp5
    omega
  set Ω := StatedOmega Q₀ with hΩ
  have hΩle : Ω ≤ isoGL Q := fun g hg => (mem_isoGL_iff hQ).2 (isometry_of_mem_statedOmega hQ hg)
  let M' : Subgroup (isoGL Q) := Ω.subgroupOf (isoGL Q)
  have hcont : ∀ g : isoGL Q, g ^ p = 1 → g ∈ M' := by
    intro g hg
    have hg1 : ((g : isoGL Q) : GL ι K) ^ p = 1 := by simpa using congrArg Subtype.val hg
    exact mem_statedOmega_of_pow_eq_one hQ hab hp2' ((mem_isoGL_iff hQ).1 g.2)
      (k := 1) (by simpa using hg1)
  have hrankO : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (isoGL Q)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 (isoGLEquiv Q)]
    exact BCDEven.three_le_pRank_orthogonal hp5 hpK he hee hpe1 Q hnd h5e
  have hbigO : ∀ y₀ : isoGL Q, y₀ ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set (isoGL Q))) := by
    intro y₀ hy₀
    have h := BCDEven.three_le_pRank_centralizer_orthogonal hp5 hpK he hee hpe Q hnd h5e
      (isoGLEquiv Q y₀) (by rw [← map_pow, hy₀, map_one])
    exact h.trans (pRank_centralizer_of_mulEquiv (isoGLEquiv Q) y₀)
  have hrankM : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup M') := restrict_le_pRank M' hcont hrankO
  have hbigM := restrict_centralizer M' hcont hbigO
  let ε : M' ≃* Ω := Subgroup.subgroupOfEquivOfLe hΩle
  have hrankΩ : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Ω) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 ε]
    exact hrankM
  have hbigΩ : ∀ y₀ : Ω, y₀ ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set Ω)) := by
    intro y₀ hy₀
    have h := hbigM (ε.symm y₀) (by rw [← map_pow, hy₀, map_one])
    exact h.trans (pRank_centralizer_of_mulEquiv (p := p) ε.symm y₀)
  exact crossAt_of_rank (p := p) ((StatedScalars ι K).subgroupOf Ω)
    (not_dvd_card_scalars_omega hp2 hQ hhom hw₀) hrankΩ hbigΩ

end Omega

end CFSG.LocalAnalysis.RankFourTheoremC
