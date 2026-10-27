module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalTools

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools Matrix
open scoped Pointwise MatrixGroups

section SL2

variable {F : Type} [Field F] [Finite F]

theorem exists_ne_zero_sq_ne_one (hF : 4 ≤ Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

theorem sl2_normal_eq_top_or_le_center (hF : 4 ≤ Nat.card F) (N : Subgroup SL(2, F))
    (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center SL(2, F) := by
  obtain ⟨a, ha, ha2⟩ := exists_ne_zero_sq_ne_one hF
  have hsimple : IsSimpleGroup PSL(2, F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  set π := QuotientGroup.mk' (Subgroup.center SL(2, F))
  have hNπ : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases (haveI := hNπ; hsimple.eq_bot_or_eq_top_of_normal (N.map π)) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    rw [eq_top_iff, ← SL2.commutator_eq_top ha ha2, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨n₁, hn₁, he⟩ : π g₁ ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
    have hz : n₁⁻¹ * g₁ ∈ Subgroup.center SL(2, F) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center SL(2, F)), MonoidHom.mem_ker, map_mul,
        map_inv, he, inv_mul_cancel]
    set z := n₁⁻¹ * g₁ with hzdef
    have hg₁ : g₁ = n₁ * z := by rw [hzdef]; group
    have hzc : z * g₂ * z⁻¹ = g₂ := by
      rw [(Subgroup.mem_center_iff.mp hz g₂).symm, mul_inv_cancel_right]
    have e : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = n₁ * (g₂ * n₁⁻¹ * g₂⁻¹) := by
      rw [hg₁]
      calc n₁ * z * g₂ * (n₁ * z)⁻¹ * g₂⁻¹ = n₁ * (z * g₂ * z⁻¹) * n₁⁻¹ * g₂⁻¹ := by group
        _ = n₁ * (g₂ * n₁⁻¹ * g₂⁻¹) := by rw [hzc]; group
    rw [commutatorElement_def, e]
    exact N.mul_mem hn₁ (hN.conj_mem _ (N.inv_mem hn₁) g₂)

omit [Finite F] in
theorem sl2_eq_one_or_neg_one_of_mem_center {A : SL(2, F)}
    (hA : A ∈ Subgroup.center SL(2, F)) : A = 1 ∨ A = -1 := by
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin, pow_two, mul_self_eq_one_iff] at hc
  rcases hc with rfl | rfl
  · left
    ext i j
    rw [← hcA, map_one]
    rfl
  · right
    ext i j
    rw [← hcA, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]

def sl2S : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem sl2S_sq : (sl2S : SL(2, F)) ^ 2 = -1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [sl2S, Matrix.mul_apply, Fin.sum_univ_two]

omit [Finite F] in
theorem sl2_neg_one_ne_one (hF : Odd (Nat.card F)) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h2 : (2 : F) = 0 := by
    have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h'
    linear_combination -h'
  have hdvd : 2 ∣ Nat.card F := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : addOrderOf (1 : F) = 2 :=
      addOrderOf_eq_prime (by rw [two_nsmul, one_add_one_eq_two, h2]) one_ne_zero
    rw [← h1]
    exact addOrderOf_dvd_natCard 1
  exact (Nat.not_even_iff_odd.mpr hF) (even_iff_two_dvd.mpr hdvd)

omit [Finite F] in
theorem orderOf_sl2S (hF : Odd (Nat.card F)) : orderOf (sl2S : SL(2, F)) = 4 := by
  have h4 : (sl2S : SL(2, F)) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, sl2S_sq, neg_one_sq]
  have hdvd := orderOf_dvd_of_pow_eq_one h4
  have hne : ¬ orderOf (sl2S : SL(2, F)) ∣ 2 := by
    intro h
    exact sl2_neg_one_ne_one hF (by rw [← sl2S_sq]; exact orderOf_dvd_iff_pow_eq_one.mp h)
  have : orderOf (sl2S : SL(2, F)) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 4 = {1, 2, 4} from rfl] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h
  · rw [h] at hne
    exact absurd (one_dvd 2) hne
  · rw [h] at hne
    exact absurd (dvd_refl 2) hne
  · exact h

end SL2

section J

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem J_le_N (hσ : σ.IsValid) (Δ : Data σ r) : Δ.J ≤ σ.N := Δ.J_le.trans hσ.L₀_le_N

theorem J_inf_ON_of_deltaEps (Δ : Data σ r) (hδ : σ.DeltaEpsMinus) : Δ.J ⊓ σ.ON = ⊥ := by
  rcases Δ.J_inf with h | ⟨hq, hh, -⟩
  · exact h
  · exfalso
    rcases hδ with ⟨_, h3⟩ | ⟨h1, _⟩
    · rw [hq] at h3
      norm_num at h3
    · exact h1 hh

theorem odd_q (hσ : σ.IsValid) : Odd σ.q := (hσ.p_prime.odd_of_ne_two hσ.p_ne_two).pow

theorem isSylowOf_S_N (hσ : σ.IsValid) : IsSylowOf 2 (σ.S : Subgroup G) σ.N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨σ.S_le_N hσ, σ.S.isPGroup', fun h => σ.S.not_dvd_index (h.trans ?_)⟩
  exact Subgroup.relIndex_dvd_index_of_le (σ.S_le_N hσ)

theorem J_structure (hσ : σ.IsValid) (Δ : Data σ r) (hJ : Δ.J ⊓ σ.ON = ⊥) :
    σ.x ∈ Δ.J ∧
      (∀ N₀ : Subgroup G, N₀ ≤ Δ.J → Δ.J ≤ Subgroup.normalizer (N₀ : Set G) →
        N₀ = Δ.J ∨ ∀ g ∈ N₀, g = 1 ∨ g = σ.x) ∧
      ∃ w ∈ Δ.J, orderOf w = 4 := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := Δ.J_sl2 hJ
  have hFodd : Odd (Nat.card F) := hcard ▸ odd_q hσ
  have hF4 : 4 ≤ Nat.card F := by have := hσ.five_lt_q; omega
  have hneg : orderOf (-1 : SL(2, F)) = 2 :=
    orderOf_eq_prime (by rw [neg_one_sq]) (sl2_neg_one_ne_one hFodd)
  have h2J : 2 ∣ Nat.card Δ.J := by
    rw [← hneg, ← orderOf_injective φ.symm.toMonoidHom φ.symm.injective (-1)]
    exact orderOf_dvd_natCard _
  have hxJ : σ.x ∈ Δ.J := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSJ : IsSylowOf 2 ((σ.S : Subgroup G) ⊓ Δ.J) Δ.J :=
      (isSylowOf_S_N hσ).inf_of_le_normalizer (J_le_N hσ Δ) Δ.J_normal
    have hne : (σ.S : Subgroup G) ⊓ Δ.J ≠ ⊥ := by
      intro h
      have hc := hSJ.card_eq
      rw [h, Subgroup.card_bot] at hc
      have hpos : 0 < (Nat.card Δ.J).factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2J
      have : 2 ^ (Nat.card Δ.J).factorization 2 ≠ 1 :=
        (Nat.one_lt_pow hpos.ne' (by norm_num)).ne'
      exact this hc.symm
    set W : Subgroup σ.S := ((σ.S : Subgroup G) ⊓ Δ.J).subgroupOf σ.S with hW
    have hWn : W.Normal := by
      rw [hW, Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      exact fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, ((σ.S_le_N hσ).trans Δ.J_normal) hg⟩
    have hW1 : W ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro g hg
      have : (⟨g, hg.1⟩ : σ.S) ∈ W := hg
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hnil : Group.IsNilpotent σ.S := σ.S.isPGroup'.isNilpotent
    have hWZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hW1
    have hWZp : IsPGroup 2 (W ⊓ Subgroup.center σ.S : Subgroup σ.S) :=
      σ.S.isPGroup'.to_subgroup _
    have hdvd : 2 ∣ Nat.card (W ⊓ Subgroup.center σ.S : Subgroup σ.S) := by
      obtain ⟨k, hk⟩ := hWZp.exists_card_eq
      rcases k with _ | k
      · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hWZ
      · rw [hk, pow_succ]
        exact Dvd.intro_left _ rfl
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := (W ⊓ Subgroup.center σ.S :
      Subgroup σ.S)) 2 hdvd
    have hgG : orderOf ((g : σ.S) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
    have hgZ : ((g : σ.S) : G) ∈ CFSG.QuasiDihedralFusion.centerOf (σ.S : Subgroup G) := by
      refine ⟨(g : σ.S).2, ?_⟩
      show ((g : σ.S) : G) ∈ Subgroup.centralizer ((σ.S : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := Subgroup.mem_center_iff.mp g.2.2 ⟨h, hh⟩
      exact congrArg Subtype.val this
    have hgx := hσ.center_involution _ hgZ hgG
    rw [← hgx]
    exact g.2.1.2
  have hxc : ∀ j ∈ Δ.J, j * σ.x = σ.x * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (J_le_N hσ Δ hj)
  have hcen : ∀ g : Δ.J, (∀ j : Δ.J, g * j = j * g) → φ g = 1 ∨ φ g = -1 := by
    intro g hg
    apply sl2_eq_one_or_neg_one_of_mem_center
    rw [Subgroup.mem_center_iff]
    intro A
    obtain ⟨j, rfl⟩ := φ.surjective A
    rw [← map_mul, ← map_mul, hg j]
  have hφx : φ ⟨σ.x, hxJ⟩ = -1 := by
    rcases hcen ⟨σ.x, hxJ⟩ (fun j => Subtype.ext (hxc j j.2).symm) with h | h
    · exfalso
      have : (⟨σ.x, hxJ⟩ : Δ.J) = 1 := φ.injective (by rw [h, map_one])
      exact x_ne_one hσ (congrArg Subtype.val this)
    · exact h
  refine ⟨hxJ, ?_, ?_⟩
  · intro N₀ hN₀ hnorm
    have hWn : (N₀.subgroupOf Δ.J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀).mpr hnorm
    set N₁ : Subgroup SL(2, F) := (N₀.subgroupOf Δ.J).map φ.toMonoidHom with hN₁
    have hN₁n : N₁.Normal := hWn.map _ φ.surjective
    rcases sl2_normal_eq_top_or_le_center hF4 N₁ hN₁n with h | h
    · left
      apply le_antisymm hN₀
      intro j hj
      have hm : φ ⟨j, hj⟩ ∈ N₁ := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨j', hj', he⟩ := hm
      have : j' = ⟨j, hj⟩ := φ.injective he
      rw [this] at hj'
      exact hj'
    · right
      intro g hg
      have hm : φ ⟨g, hN₀ hg⟩ ∈ N₁ := ⟨⟨g, hN₀ hg⟩, hg, rfl⟩
      rcases sl2_eq_one_or_neg_one_of_mem_center (h hm) with h1 | h1
      · left
        have : (⟨g, hN₀ hg⟩ : Δ.J) = 1 := φ.injective (by rw [h1, map_one])
        exact congrArg Subtype.val this
      · right
        have : (⟨g, hN₀ hg⟩ : Δ.J) = ⟨σ.x, hxJ⟩ := φ.injective (by rw [h1, hφx])
        exact congrArg Subtype.val this
  · refine ⟨((φ.symm sl2S : Δ.J) : G), (φ.symm sl2S).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_sl2S hFodd]

theorem x_mem_J (hσ : σ.IsValid) (Δ : Data σ r) (hJ : Δ.J ⊓ σ.ON = ⊥) : σ.x ∈ Δ.J :=
  (J_structure hσ Δ hJ).1

theorem normal_eq_or_le (hσ : σ.IsValid) (Δ : Data σ r) (hJ : Δ.J ⊓ σ.ON = ⊥)
    {N₀ : Subgroup G} (hN₀ : N₀ ≤ Δ.J) (hnorm : Δ.J ≤ Subgroup.normalizer (N₀ : Set G)) :
    N₀ = Δ.J ∨ ∀ g ∈ N₀, g = 1 ∨ g = σ.x :=
  (J_structure hσ Δ hJ).2.1 N₀ hN₀ hnorm

theorem four_dvd_card_J (hσ : σ.IsValid) (Δ : Data σ r) (hJ : Δ.J ⊓ σ.ON = ⊥) :
    4 ∣ Nat.card Δ.J := by
  obtain ⟨w, hw, hw4⟩ := (J_structure hσ Δ hJ).2.2
  rw [← hw4]
  exact Subgroup.orderOf_dvd_natCard Δ.J hw

theorem J_le_of_covers (hσ : σ.IsValid) (Δ : Data σ r) (hJ : Δ.J ⊓ σ.ON = ⊥)
    {Y : Subgroup G} (hYN : Y ≤ σ.N) (hcov : (σ.L₀ : Set G) ⊆ (Y : Set G) * σ.ON) :
    Δ.J ≤ Y := by
  set W : Subgroup G := Y ⊓ Δ.J with hW
  have hJN := J_le_N hσ Δ
  have hWnorm : Δ.J ≤ Subgroup.normalizer (W : Set G) := by
    intro j hj
    apply mem_normalizer_of_conj_mem
    intro w hw
    obtain ⟨y, hy, o, ho, rfl⟩ := hcov (Δ.J_le hj)
    have hwo : o * w * o⁻¹ = w := by
      have := (Subgroup.mem_centralizer_iff.mp (Δ.J_centralizes hw.2)) o ho
      rw [this, mul_inv_cancel_right]
    refine ⟨?_, Δ.J.mul_mem (Δ.J.mul_mem hj hw.2) (Δ.J.inv_mem hj)⟩
    have e : y * o * w * (y * o)⁻¹ = y * (o * w * o⁻¹) * y⁻¹ := by group
    rw [e, hwo]
    exact Y.mul_mem (Y.mul_mem hy hw.1) (Y.inv_mem hy)
  have hYJ : Y ≤ Subgroup.normalizer (Δ.J : Set G) := hYN.trans Δ.J_normal
  have hYO : Y ≤ Subgroup.normalizer (σ.ON : Set G) := hYN.trans σ.N_le_normalizer_ON
  have h1 := card_sup_mul_card_inf hYJ
  have h2 := card_sup_mul_card_inf hYO
  have hle : Y ⊔ Δ.J ≤ Y ⊔ σ.ON := by
    refine sup_le le_sup_left ?_
    intro j hj
    obtain ⟨y, hy, o, ho, rfl⟩ := hcov (Δ.J_le hj)
    exact Subgroup.mul_mem_sup hy ho
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : Y ≤ Y ⊔ Δ.J)
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hJk : Nat.card Δ.J = Nat.card (Y ⊓ Δ.J : Subgroup G) * k := by
    rw [hk] at h1
    have : Nat.card Y * (k * Nat.card (Y ⊓ Δ.J : Subgroup G)) = Nat.card Y * Nat.card Δ.J := by
      rw [← h1]; ring
    have := Nat.eq_of_mul_eq_mul_left hYpos this
    rw [← this, mul_comm]
  have hkO : k ∣ Nat.card σ.ON := by
    rw [hm, hk] at h2
    refine ⟨m * Nat.card (Y ⊓ σ.ON : Subgroup G), Nat.eq_of_mul_eq_mul_left hYpos ?_⟩
    rw [← h2]
    ring
  have hkodd : Odd k := (σ.odd_card_ON).of_dvd_nat hkO
  rcases normal_eq_or_le hσ Δ hJ inf_le_right hWnorm with h | h
  · rw [← h]
    exact inf_le_left
  · exfalso
    have hW2 : Nat.card W ≤ 2 := by
      have hsub : (W : Set G) ⊆ {1, σ.x} := fun g hg => by
        rcases h g hg with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      calc Nat.card W = Nat.card (W : Set G) := rfl
        _ ≤ Nat.card ({1, σ.x} : Set G) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h4 := four_dvd_card_J hσ Δ hJ
    rw [hJk] at h4
    have hcop : Nat.Coprime 4 k := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_left.mpr hkodd).pow_left 2
    have h4W : 4 ∣ Nat.card W := hcop.dvd_of_dvd_mul_right h4
    have := Nat.le_of_dvd Nat.card_pos h4W
    omega

end J

end CFSG.ABGTheoremB.TotallyInverted.Sec11
