module

public import CFSG.LocalAnalysis.AGLEmbedding.TimmesfeldRouteAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Center

theorem center_quotient_center_eq_bot_of_isPerfect {D : Type*} [Group D]
    (h : Group.IsPerfect (D ⧸ Subgroup.center D)) :
    Subgroup.center (D ⧸ Subgroup.center D) = ⊥ := by
  have hsup : commutator D ⊔ Subgroup.center D = ⊤ := by
    have h1 : (commutator D).map (QuotientGroup.mk' (Subgroup.center D)) = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def]
      exact h.commutator_eq_top
    have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center D))) h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center D) q
  have hc : ∀ y : D, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center D := by
    intro y
    have h1 := Subgroup.mem_center_iff.mp hq (QuotientGroup.mk' (Subgroup.center D) y)
    rw [← QuotientGroup.ker_mk' (Subgroup.center D), MonoidHom.mem_ker]
    simp only [map_mul, map_inv, ← h1, mul_inv_cancel_right, mul_inv_cancel]
  let f : D →* Subgroup.center D :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hc y⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        have hb := Subgroup.mem_center_iff.mp (hc b) a
        simp only [Subgroup.coe_mul]
        calc x * (a * b) * x⁻¹ * (a * b)⁻¹
            = x * a * x⁻¹ * a⁻¹ * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
          _ = x * a * x⁻¹ * a⁻¹ * (x * b * x⁻¹ * b⁻¹) := by
            rw [hb, mul_inv_cancel_right] }
  have hker : commutator D ⊔ Subgroup.center D ≤ f.ker := by
    refine sup_le (Abelianization.commutator_subset_ker f) fun z hz => ?_
    rw [MonoidHom.mem_ker]
    ext
    change x * z * x⁻¹ * z⁻¹ = 1
    rw [Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right, mul_inv_cancel]
  have hx : x ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : f y = 1 := hker (hsup ▸ Subgroup.mem_top y)
    have hy' : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hy
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hy'
    exact hy'.symm
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem center_eq_bot_of_mulEquiv_lie {Λ : Type*} [Group Λ] (hΛ : Group.IsPerfect Λ)
    {d : TauCeti.ValidLieTypeIndex} (φ : Λ ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Subgroup.center Λ = ⊥ := by
  have hQ : Group.IsPerfect (TauCeti.CFSGIndex.lie d).Group :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
  exact center_eq_bot_of_mulEquiv φ (center_quotient_center_eq_bot_of_isPerfect hQ)

private theorem mul_comm_of_card_le_three {X : Type*} [Group X] [Finite X]
    (h3 : Nat.card X ≤ 3) (a b : X) : a * b = b * a := by
  have hpos := Nat.card_pos (α := X)
  rcases (show Nat.card X = 1 ∨ Nat.card X = 2 ∨ Nat.card X = 3 by omega) with h1 | h2 | h3
  · have : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp h1.le
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime (Nat.card X)) := ⟨h2 ▸ Nat.prime_two⟩
    let _ : CommGroup X := (isCyclic_of_prime_card rfl).commGroup
    exact mul_comm a b
  · have : Fact (Nat.Prime (Nat.card X)) := ⟨h3 ▸ Nat.prime_three⟩
    let _ : CommGroup X := (isCyclic_of_prime_card rfl).commGroup
    exact mul_comm a b

theorem center_eq_bot_of_mulEquiv_alternating {Λ : Type*} [Group Λ]
    (hnab : ∃ a b : Λ, a * b ≠ b * a) {n : ℕ} (φ : Λ ≃* alternatingGroup (Fin n)) :
    Subgroup.center Λ = ⊥ := by
  have h4 : 4 ≤ n := by
    by_contra! hn
    obtain ⟨a, b, hab⟩ := hnab
    refine hab (φ.injective ?_)
    rw [map_mul, map_mul]
    refine mul_comm_of_card_le_three ?_ _ _
    rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with hn1 | hn2
    · rw [alternatingGroup.eq_bot_of_card_le_two (by rw [Nat.card_fin]; omega),
        Subgroup.card_bot]
      omega
    · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
      rw [nat_card_alternatingGroup, Nat.card_fin]
      interval_cases n <;> decide
  exact center_eq_bot_of_mulEquiv φ (alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega))

theorem center_eq_bot_of_isOrthogonalTwo {Λ : Type} [Group Λ] (hΛ : Group.IsPerfect Λ)
    (hnab : ∃ a b : Λ, a * b ≠ b * a) (hO : IsOrthogonalTwo Λ) : Subgroup.center Λ = ⊥ := by
  rcases hO with ⟨d, -, ⟨φ⟩⟩ | ⟨n, -, ⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv_lie hΛ φ
  · exact center_eq_bot_of_mulEquiv_alternating hnab φ

theorem IsOrthogonalTwo.of_mulEquiv {Λ Y : Type} [Group Λ] [Group Y] (e : Y ≃* Λ)
    (hO : IsOrthogonalTwo Λ) : IsOrthogonalTwo Y := by
  rcases hO with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans φ⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.trans φ⟩⟩

end Center

section Blocks

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_nineThreeTwo (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hL28 : KFactL28Parabolic) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (h2 : NineThreeTwo M (pCoreOf 2 H) L)
    (hY : IsCaseTwoGroup 3 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) : False := by
  have hnot := (h.nineThree_not_one h85 hD2 hL).2 h2
  obtain ⟨-, ⟨hPL, T₂, hT₂, hN⟩, hS⟩ := h2
  obtain ⟨-, hK7⟩ := hL28 _ hL.component.2.2 hY
  have hJ : (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)).subgroupOf (barM M L) ≠ ⊤ := by
    intro htop
    apply hL.not_le_normalizer
    intro l hl
    have h1 : (⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hL.le hl⟩, ⟨⟨l, hL.le hl⟩, hl, rfl⟩⟩ :
        ↥(barM M L)) ∈ (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)).subgroupOf
          (barM M L) := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyl⟩ := Subgroup.mem_subgroupOf.mp h1
    have hq : ((y⁻¹ * ⟨l, hL.le hl⟩ : ↥M) : G) ∈ pCoreOf 2 M :=
      (mk_eq_one_iff_coe_mem_pCoreOf _).mp (by rw [map_mul, map_inv, hyl, inv_mul_cancel])
    have hqS := h.twoCore_M_le h.twoCore_inf hq
    have hyN : (y : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      (Subgroup.mem_subgroupOf.mp hy).1
    have hl' : l = (y : G) * ((y⁻¹ * ⟨l, hL.le hl⟩ : ↥M) : G) := by simp
    rw [hl']
    exact Subgroup.mul_mem _ hyN (Subgroup.le_normalizer hqS)
  have hP := hK7 _ _ (isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT₂)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hN ⟨x.2, coe_mem_normalizer_of_subgroupOf hT₂.1 hx⟩))
    hJ
  have hcore := congrArg (Subgroup.map (barM M L).subtype) hP
  rw [pCoreOf_map_subtype, Subgroup.map_subgroupOf_eq_of_le hPL,
    Subgroup.map_subgroupOf_eq_of_le hT₂.1] at hcore
  exact hnot (by rw [hS, hcore]; exact hT₂)

theorem D1PhaseThree.false_of_block_section (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hL28 : KFactL28Parabolic) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hK : (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∨
        IsOrthogonalTwo (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∨
        ∃ n : ℕ, Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
          alternatingGroup (Fin n))) →
      IsCaseTwoGroup 3 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        ¬ IsOrthogonalTwo (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        ¬ ∃ n : ℕ, Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
          alternatingGroup (Fin n))) :
    False := by
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) b
    exact ⟨a', b', fun h' => hab (by rw [← map_mul, ← map_mul, h'])⟩
  have e₀ : Subgroup.center ↥(barM M L) = ⊥ →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* ↥(barM M L)) := fun hZ =>
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩
  have halt : ∀ n : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin n)) → False := by
    rintro n ⟨φ⟩
    obtain ⟨e⟩ := e₀ (center_eq_bot_of_mulEquiv_alternating hnab φ)
    have hA : ∃ n : ℕ, Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
        alternatingGroup (Fin n)) := ⟨n, ⟨e.trans φ⟩⟩
    exact (hK (Or.inr (Or.inr hA))).2.2 hA
  have haltq : ∀ n : ℕ, Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
      alternatingGroup (Fin n)) → False := fun n hn =>
    (hK (Or.inr (Or.inr ⟨n, hn⟩))).2.2 ⟨n, hn⟩
  rcases h.nineThree h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (h.nineThree_not_one h85 hD2 hL).1 h1
  · exact h.false_of_nineThreeTwo h85 hD2 hL28 hL h2 (hK (Or.inl h2.1)).1
  · obtain ⟨e⟩ := e₀ (center_eq_bot_of_isOrthogonalTwo hperf hnab h3.2.1)
    have hO := IsOrthogonalTwo.of_mulEquiv e h3.2.1
    exact (hK (Or.inr (Or.inl hO))).2.1 hO
  · exact haltq 6 h4.2.2.1
  · exact halt 7 h5.2.1
  · obtain ⟨-, n, hn, -⟩ := h6
    exact haltq (2 * n) hn
  · obtain ⟨-, n, hn, -⟩ := h7
    exact halt (4 * n) hn
  · obtain ⟨-, N, r, -, -, -, -, -, hN, -⟩ := h8
    exact halt N hN

end Blocks

end CFSG.AGLEmbedding
