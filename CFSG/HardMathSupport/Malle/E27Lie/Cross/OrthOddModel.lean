module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddCentralizer
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.MapPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.AGLEmbedding.ToralCensus Subgroup QuadraticMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem scalars_subgroupOf_le_center (H : Subgroup (GL ι K)) :
    (StatedScalars ι K).subgroupOf H ≤ center H :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

variable [Finite K]

theorem exists_perfect_three_dvd_centralizer_pomega
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0) (h3 : ((3 : ℕ) : K) ≠ 0)
    (hn : 7 ≤ Fintype.card ι) (hK : 4 ≤ Nat.card K)
    {a : StatedProj (StatedOmega Q₀)} (ha : orderOf a = 3) :
    ∃ B : Subgroup (StatedProj (StatedOmega Q₀)),
      B ≤ Subgroup.centralizer ({a} : Set (StatedProj (StatedOmega Q₀))) ∧ ⁅B, B⁆ = B ∧
        3 ∣ Nat.card B := by
  classical
  have hΩ := statedOmega_eq_comap hQ0
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hdim : 7 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]; exact hn
  let π : StatedOmega Q₀ →* StatedProj (StatedOmega Q₀) := QuotientGroup.mk' _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have ha' : orderOf (π g) = 3 := ha
  have hker : π.ker ≤ center (StatedOmega Q₀) := by
    rw [QuotientGroup.ker_mk']
    exact scalars_subgroupOf_le_center _
  have hO : ∀ u : StatedOmega Q₀, toLinEquiv ι K (u : GL ι K) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun u => by
    have h : (u : GL ι K) ∈ (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap (toLinEquiv ι K).toMonoidHom := by
      rw [← hΩ]; exact u.2
    exact Subgroup.commutator_le_self _ (Subgroup.mem_comap.mp h)
  have hg3 : (g ^ 3 : StatedOmega Q₀) ∈ π.ker := by
    have h1 : π g ^ 3 = 1 := by
      have := pow_orderOf_eq_one (π g)
      rwa [ha'] at this
    rw [MonoidHom.mem_ker, map_pow]
    exact h1
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hg3
  obtain ⟨c, hc⟩ := hg3
  have hsq : (c : K) * c = 1 := by
    obtain ⟨v, hv⟩ := exists_quadratic_ne_zero (K := K) (Q := Q) hQ
    have hcv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hO (g ^ 3)) v
    rw [toLinEquiv_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hcv
    have hsmul : Matrix.mulVec (Matrix.diagonal fun _ => (c : K)) v = (c : K) • v := by
      funext i
      simp [Matrix.mulVec_diagonal]
    rw [hsmul, QuadraticMap.map_smul, smul_eq_mul] at hcv
    have h1 : ((c : K) * c - 1) * Q v = 0 := by rw [sub_mul, hcv, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hv)
  have hcc : c * c = 1 := Units.ext hsq
  have hg6 : (g : GL ι K) ^ 6 = 1 := by
    have h3' : (g : GL ι K) ^ 3 = Matrix.GeneralLinearGroup.scalar ι c := by
      rw [hc]; rfl
    have h6 : (g : GL ι K) ^ 6 = ((g : GL ι K) ^ 3) ^ 2 := by rw [← pow_mul]
    rw [h6, h3', ← map_pow, _root_.sq, hcc, map_one]
  set w : StatedOmega Q₀ := g ^ 4 with hw
  have hw3 : w ^ 3 = 1 := by
    apply Subtype.ext
    show ((g : GL ι K) ^ 4) ^ 3 = 1
    have h12 : ((g : GL ι K) ^ 4) ^ 3 = ((g : GL ι K) ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
    rw [h12, hg6, one_pow]
  have hπ3 : π g ^ 3 = 1 := by
    have := pow_orderOf_eq_one (π g)
    rwa [ha'] at this
  have hπw : π w = π g := by
    rw [hw, map_pow, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hπ3, one_mul]
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, map_one] at hπw
    have h1 : π g = 1 := hπw.symm
    rw [h1, orderOf_one] at ha'
    omega
  have hx : OddOrderIsometry Q 3 (toLinEquiv ι K (w : GL ι K)) := by
    refine ⟨hO w, ?_, h3, fun v hv => hQ.1 v fun w' => ?_⟩
    · rw [← map_pow]
      have : (w : GL ι K) ^ 3 = 1 := congrArg Subtype.val hw3
      rw [this, map_one]
    · simpa [polarBilin_apply_apply] using hv w'
  have hx1 : toLinEquiv ι K (w : GL ι K) ≠ 1 := fun h =>
    hw1 (Subtype.ext ((toLinEquiv ι K).injective (h.trans (map_one _).symm)))
  obtain ⟨V, hVC, hVp, y, hyV, hy3, hy1⟩ :=
    perfectThreeIn_isometryCentralizer_odd hx hx1 h2 hdim hK
  have hVO : V ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hVC.trans inf_le_left
  have hVD : V ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    calc V = ⁅V, V⁆ := hVp.symm
      _ ≤ _ := Subgroup.commutator_mono hVO hVO
  set e := toLinEquiv ι K with he
  set V' : Subgroup (GL ι K) := V.comap e.toMonoidHom with hV'
  have hV'G : V' ≤ StatedOmega Q₀ := by
    rw [hΩ]
    exact Subgroup.comap_mono hVD
  have hmapV' : V' = V.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e V
  have hperf' : ⁅V', V'⁆ = V' := by
    rw [hmapV', ← Subgroup.map_commutator, hVp]
  set B : Subgroup (StatedOmega Q₀) := V'.subgroupOf (StatedOmega Q₀) with hB
  have hBperf : ⁅B, B⁆ = B := by
    apply Subgroup.map_injective (StatedOmega Q₀).subtype_injective
    rw [Subgroup.map_commutator, hB, Subgroup.map_subgroupOf_eq_of_le hV'G, hperf']
  have hy'V : e.symm y ∈ V' := by
    rw [hV', Subgroup.mem_comap]
    simpa using hyV
  have hB3 : 3 ∣ Nat.card B := by
    let yb : B := ⟨⟨e.symm y, hV'G hy'V⟩, Subgroup.mem_subgroupOf.2 hy'V⟩
    have hyb3 : yb ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      show (e.symm y) ^ 3 = 1
      rw [← map_pow, hy3, map_one]
    have hyb1 : yb ≠ 1 := fun h => by
      apply hy1
      have := congrArg (fun t : B => (t : StatedOmega Q₀).1) h
      have h' : e.symm y = 1 := this
      simpa using congrArg e h'
    rw [← orderOf_eq_prime hyb3 hyb1]
    exact orderOf_dvd_natCard yb
  have hBc : ∀ b ∈ B, b * w = w * b := by
    intro b hb
    have hb' : e (b : GL ι K) ∈ V := Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp hb)
    have hcomm := (mem_isometryCentralizer.mp (hVC hb')).2
    apply Subtype.ext
    apply e.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact LinearEquiv.ext fun v => hcomm v
  refine ⟨B.map π, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change π b * π g = π g * π b
    rw [← hπw, ← map_mul, ← map_mul, hBc b hb]
  · rw [← Subgroup.map_commutator, hBperf]
  · exact three_dvd_card_map_of_perfect π hker hBperf hB3

end CFSG.HardMathSupport.Malle.E27Lie
