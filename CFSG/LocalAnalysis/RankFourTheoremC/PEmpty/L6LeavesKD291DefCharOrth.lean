module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharTail
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.Open CFSG.Assembly.LowTwoRank Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin

theorem rankThreeCent_of_tailEquiv {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Finite K]
    [CharP K p] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Type} [AddCommGroup A]
    [Module K A] [FiniteDimensional K A] {r : ℕ} (hr : 3 ≤ r) {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : Module.finrank K A = 1 ∨ Module.finrank K A = 2) {Q0 : (ι → K) → K}
    (e₁ : StatedOmega Q0 ≃* orthElementaryGroup (quadTail r qA)) {G : Type} [Group G]
    [Finite G] (θ : G ≃* StatedProj (StatedOmega Q0)) : RankThreeCent p G := by
  let π : ↥(orthElementaryGroup (quadTail r qA)) →* G :=
    θ.symm.toMonoidHom.comp ((QuotientGroup.mk' ((StatedScalars ι K).subgroupOf
      (StatedOmega Q0))).comp e₁.symm.toMonoidHom)
  have hπ : Function.Surjective π :=
    θ.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp e₁.symm.surjective)
  refine rankThreeCent_of_tail hr hani hreg hm π hπ ?_
  intro u hu hπu
  obtain ⟨k, hk⟩ := isPGroup_tailUnipotent (p := p) hani
    (⟨u, hu⟩ : ↥((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))))
  have hu1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨z, hz⟩ : ∃ z : StatedOmega Q0, z = e₁.symm u := ⟨_, rfl⟩
  have hz1 : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q0)) z = 1 := by
    rw [hz]
    exact θ.symm.injective (hπu.trans (map_one θ.symm).symm)
  have hzmem : z ∈ (StatedScalars ι K).subgroupOf (StatedOmega Q0) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
    exact hz1
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hzmem
  obtain ⟨c, hc⟩ := hzmem
  obtain ⟨a⟩ := ‹Nonempty ι›
  have hzpow : z ^ p ^ k = 1 := by rw [hz, ← map_pow, hu1, map_one]
  have hc1 : (c : K) ^ p ^ k = 1 := by
    have h1 : ((z : GL ι K) : Matrix ι ι K) = Matrix.scalar ι (c : K) := by
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
    have h2 : ((z : GL ι K) : Matrix ι ι K) ^ p ^ k = 1 := by
      have := congrArg (fun w : StatedOmega Q0 => ((w : GL ι K) : Matrix ι ι K)) hzpow
      simpa using this
    rw [h1, ← map_pow] at h2
    have h3 := congrFun (congrFun h2 a) a
    simpa [Matrix.scalar_apply] using h3
  have hc2 : (c : K) = 1 := by
    have h0 : ((c : K) - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, hc1, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_pos hp.out.pos k).ne').1 h0)
  have hcu : c = 1 := Units.ext hc2
  have hz' : z = 1 := Subtype.ext (by rw [← hc, hcu, map_one]; rfl)
  calc u = e₁ z := by rw [hz, MulEquiv.apply_symm_apply]
    _ = 1 := by rw [hz', map_one]

theorem rankThreeCent_pomegaOdd {p n f : ℕ} [hp : Fact p.Prime] (hn : 3 ≤ n) {G : Type}
    [Group G] [Finite G] (h : StatedClassicalModel G .POmegaOdd n p f) : RankThreeCent p G := by
  obtain ⟨⟨-, hf, -, hp2⟩, K, hKf, hKfin, hK, ⟨θ⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  haveI : Nonempty (Fin n ⊕ Fin n ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
  exact rankThreeCent_of_tailEquiv (p := p) hn anisotropic_oddTailForm
    (nondegenerate_oddTailForm h2) (Or.inl finrank_unit_fun)
    (tailOmegaEquiv (oddTailIsometry n K) (coe_quadOdd n K)
      (commutator_orthogonalGroup_quadOdd h2 hn)) θ

theorem rankThreeCent_pomegaMinus {p n f : ℕ} [hp : Fact p.Prime] (hn : 4 ≤ n) {G : Type}
    [Group G] [Finite G] (h : StatedClassicalModel G .POmegaMinus n p f) :
    RankThreeCent p G := by
  obtain ⟨⟨-, hf, -⟩, K, hKf, hKfin, hK, b, c, hirr, ⟨θ⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  haveI : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  exact rankThreeCent_of_tailEquiv (p := p) (r := n - 1) (by omega)
    (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
    (Or.inr finrank_fin_two_fun)
    (tailOmegaEquiv (minusTailIsometry n K b c) (coe_quadMinus n K b c)
      (commutator_orthogonalGroup_quadMinus hn hirr)) θ

theorem inOmegaOdd : InOmegaOdd := fun p n f hp _ hn G _ _ hm => by
  haveI : Fact p.Prime := ⟨hp⟩
  exact rankThreeCent_pomegaOdd hn hm

theorem inOmegaMinus : InOmegaMinus := fun p n f hp _ hn G _ _ hm => by
  haveI : Fact p.Prime := ⟨hp⟩
  exact rankThreeCent_pomegaMinus hn hm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
