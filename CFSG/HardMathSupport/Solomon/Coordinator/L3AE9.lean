module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
import CFSG.Quasithin.Vol2.KGFact1297Rank
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

section Elements

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem coe_diagTau_pow {τ : K} (hτ : τ ^ 3 = 1) (n : ℕ) :
    (((diagTau hτ ^ n : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal hτ, Matrix.diagonal_pow,
    Matrix.diagonal_apply_eq]
  simp

theorem exists_elemAbelian_nine_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ E : Subgroup ↥(slPi π 3 (p ^ f) K), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  let u : Kˣ := Units.mk0 τ hτ0
  have hu : (u : K) ^ 3 = 1 := hτ
  have hu3 : u ^ 3 = 1 := Units.ext hu
  let a : ↥(slPi π 3 (p ^ f) K) := ⟨diagTau hτ, diagTau_mem_slPi hπ hq' hτ⟩
  let b : ↥(slPi π 3 (p ^ f) K) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_slPi_of_cube hK hq hu⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext (diagTau_pow_three hτ)
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.scalar (Fin 3) u) ^ 3 = 1
    rw [← map_pow, hu3, map_one]
  have hab : a * b = b * a := by
    apply Subtype.ext
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u (diagTau hτ)).eq
  have ha1 : a ≠ 1 := by
    intro h
    have h1 := congrArg (fun m : ↥(slPi π 3 (p ^ f) K) =>
      ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [a, coe_diagTau_eq_diagonal hτ, Matrix.diagonal_apply_eq] at h1
    exact hτ1 (by simpa using h1)
  have hba : b ∉ Subgroup.zpowers a := by
    intro h
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at h
    obtain ⟨n, hn⟩ := h
    have h1 := congrArg (fun m : ↥(slPi π 3 (p ^ f) K) =>
      ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2) hn
    simp only [Subgroup.coe_pow] at h1
    have h2 := coe_diagTau_pow hτ n
    change (((diagTau hτ ^ n : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = _ at h1
    rw [h2] at h1
    change _ = ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2
      at h1
    rw [coe_scalar_eq_smul] at h1
    simp at h1
    exact hτ1 h1.symm
  obtain ⟨E, -, hcomm, hexp, hcard⟩ :=
    CFSG.Quasithin.H13.KG1297.exists_elemAbelian_nine ha3 hb3 hab ha1 hba
  exact ⟨E, ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, hexp⟩, hcard⟩

theorem exists_elemAbelian_nine_slPi_quot (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ E : Subgroup (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  let u : Kˣ := Units.mk0 τ hτ0
  let a : ↥(slPi π 3 (p ^ f) K) := ⟨diagTau hτ, diagTau_mem_slPi hπ hq' hτ⟩
  let c : ↥(slPi π 3 (p ^ f) K) := ⟨cycThree, cycThree_mem_slPi hπ⟩
  let s : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) (u ^ 2)
  have hs1 : s ≠ 1 := by
    intro h
    have h1 := congrArg (fun m : GL (Fin 3) K => (m : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [s] at h1
    rw [coe_scalar_eq_smul] at h1
    have h2 : τ ^ 2 = 1 := by simpa [u] using h1
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hτ, h2]; simp
  have hca : (cycThree : GL (Fin 3) K) * diagTau hτ = s * (diagTau hτ * cycThree) := by
    have h1 : (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ = s * diagTau hτ := by
      apply Units.ext
      rw [cycThree_conj_diagTau hτ, Units.val_mul, coe_scalar_eq_smul]
      simp [u]
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [h1, mul_assoc]
  have hsc : ∀ g : GL (Fin 3) K, s * g = g * s := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (u ^ 2) g).eq.symm
  have hnc : ¬ (diagTau hτ * cycThree : GL (Fin 3) K) = cycThree * diagTau hτ := by
    intro h
    rw [hca] at h
    exact hs1 (mul_eq_right.mp h.symm)
  have hnc' : ¬ a * c = c * a := fun h => hnc (congrArg Subtype.val h)
  have hz : (a * c)⁻¹ * (c * a) ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
    rw [center_slPi_eq hK hq, Subgroup.mem_subgroupOf]
    refine ⟨u ^ 2, ?_⟩
    change s = (diagTau hτ * cycThree)⁻¹ * (cycThree * diagTau hτ)
    rw [hca, hsc (diagTau hτ * cycThree), inv_mul_cancel_left]
  have hmk : (QuotientGroup.mk a : ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) *
      QuotientGroup.mk c = QuotientGroup.mk c * QuotientGroup.mk a := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact hz
  have ha3 : (QuotientGroup.mk a : ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ^ 3
      = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext (diagTau_pow_three hτ)
  have hc3 : (QuotientGroup.mk c : ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ^ 3
      = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext cycThree_pow_three
  have ha1 : (QuotientGroup.mk a : ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))
      ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    exact hnc' (Subgroup.mem_center_iff.mp h c).symm
  have hba : (QuotientGroup.mk c : ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))
      ∉ Subgroup.zpowers (QuotientGroup.mk a) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
    have h1 := Subgroup.mem_center_iff.mp hk a
    have h2 : Commute a ((a ^ k)⁻¹) := ((Commute.refl a).zpow_right k).inv_right
    apply hnc'
    have h3 : (a ^ k)⁻¹ * (a * c) = (a ^ k)⁻¹ * (c * a) := by
      calc (a ^ k)⁻¹ * (a * c) = ((a ^ k)⁻¹ * a) * c := by rw [mul_assoc]
        _ = (a * (a ^ k)⁻¹) * c := by rw [h2.eq]
        _ = a * ((a ^ k)⁻¹ * c) := by rw [mul_assoc]
        _ = ((a ^ k)⁻¹ * c) * a := h1
        _ = (a ^ k)⁻¹ * (c * a) := by rw [mul_assoc]
    exact mul_left_cancel h3
  obtain ⟨E, -, hcomm, hexp, hcard⟩ :=
    CFSG.Quasithin.H13.KG1297.exists_elemAbelian_nine ha3 hc3 hmk ha1 hba
  exact ⟨E, ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, hexp⟩, hcard⟩

theorem exists_elemAbelian_nine_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ∃ E : Subgroup X', CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, ⟨⟨hc⟩, hx⟩, hcard⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    change e.symm a * e.symm b = e.symm b * e.symm a
    rw [← map_mul, ← map_mul]
    exact congrArg e.symm (congrArg Subtype.val (hc.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    change e.symm a ^ 3 = 1
    rw [← map_pow, hx a ha, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hcard

theorem exists_elemAbelian_nine_of_isL3Type {X : Type} [Group X] (h : IsL3Type X) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  rcases h with ⟨K, hKf, hFin, hc, (⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)⟩ | ⟨K, hKf, hFin, q, hcard, hq3, (⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)⟩
  · obtain ⟨p, f, hK, hmod, -⟩ := exists_true_data K hc
    exact exists_elemAbelian_nine_of_mulEquiv
      (e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm)
      (exists_elemAbelian_nine_slPi_quot hK hmod)
  · obtain ⟨p, f, hK, hmod, -⟩ := exists_true_data K hc
    exact exists_elemAbelian_nine_of_mulEquiv e (exists_elemAbelian_nine_slPi hK hmod)
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f K := ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hq3
    exact exists_elemAbelian_nine_of_mulEquiv
      (e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm)
      (exists_elemAbelian_nine_slPi_quot hK hmod)
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f K := ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hq3
    exact exists_elemAbelian_nine_of_mulEquiv e (exists_elemAbelian_nine_slPi hK hmod)

end Elements

end CFSG.HardMathSupport.Solomon.Coordinator
