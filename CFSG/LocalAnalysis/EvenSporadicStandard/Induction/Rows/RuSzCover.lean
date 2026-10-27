module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzCoverModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLink
public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
public import CFSG.Quasithin.Background.KnownMultOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift

theorem exists_elementary_lift {J X : Type} [Group J] [Finite J] [Group X] {φ : J →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J) {E : Subgroup X} {n : X}
    (h : E8Normalized E n) {z : J} (hzk : φ z = 1) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) {x : X}
    (hx : x ∈ E) :
    ∃ B : Subgroup J, (∀ y ∈ B, y * y = 1) ∧ (∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y) ∧
      16 ≤ Nat.card B ∧ ∃ b ∈ B, φ b = x := by
  obtain ⟨a₁, a₂, a₃, m, hd, hdesc⟩ :=
    exists_e8Datum_of_normalizer h.sq h.card h.normalizes h.pow_seven h.fixed
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ := hd.exists_lift hφ hker
  have hzc : ∀ y : J, Commute y z := fun y => Subgroup.mem_center_iff.mp (hker hzk) y
  have hsq : ∀ i, (![b₁, b₂, b₃, z] : Fin 4 → J) i ^ 2 = 1 := by
    intro i
    fin_cases i <;> simpa
  have hcomm : ∀ i j, Commute ((![b₁, b₂, b₃, z] : Fin 4 → J) i)
      ((![b₁, b₂, b₃, z] : Fin 4 → J) j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
      first
        | exact Commute.refl _ | exact c₁₂ | exact c₁₂.symm | exact c₁₃ | exact c₁₃.symm
        | exact c₂₃ | exact c₂₃.symm | exact hzc _ | exact (hzc _).symm
  have hind : ∀ v : Fin 4 → Fin 2, v ≠ 0 →
      (List.ofFn fun i => (![b₁, b₂, b₃, z] : Fin 4 → J) i ^ (v i : ℕ)).prod ≠ 1 := by
    intro v hv hprod
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two] at hprod
    have himg := congrArg φ hprod
    simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃, hzk, one_pow, mul_one] at himg
    by_cases h0 : (v 0, v 1, v 2) = (0, 0, 0)
    · simp only [Prod.mk.injEq] at h0
      obtain ⟨h0, h1, h2⟩ := h0
      have h3 : v 3 ≠ 0 := by
        intro h3
        apply hv
        funext i
        fin_cases i
        exacts [h0, h1, h2, h3]
      have h3' : v 3 = 1 := by
        revert h3; generalize v 3 = w; revert w; decide
      rw [h0, h1, h2, show (Fin.succ 2 : Fin 4) = 3 from rfl, h3'] at hprod
      simp only [Fin.isValue, Fin.val_zero, pow_zero, Fin.val_one, pow_one, one_mul] at hprod
      exact hz1 hprod
    · exact hd.prod_ne_one _ _ _ h0 (by rw [← himg]; group)
  obtain ⟨ψ, hψinj, hψ⟩ := exists_prodHom (![b₁, b₂, b₃, z] : Fin 4 → J) hsq hcomm hind
  set B : Subgroup J := Subgroup.closure (Set.range (![b₁, b₂, b₃, z] : Fin 4 → J)) with hB
  have hBcomm : IsMulCommutative B := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  have hcommB : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hBcomm.is_comm.comm (⟨y, hy⟩ : B) ⟨y', hy'⟩)
  have hmem : ∀ i : Fin 4, (![b₁, b₂, b₃, z] : Fin 4 → J) i ∈ B := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  refine ⟨B, ?_, hcommB, ?_, ?_⟩
  · intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← pow_two]
      exact hsq i
    | one => simp
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcommB y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ihx, inv_one]
  · have hrange : ψ.range ≤ B := by
      rintro _ ⟨v, rfl⟩
      rw [hψ]
      refine Subgroup.list_prod_mem _ fun y hy => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact Subgroup.pow_mem _ (hmem i) _
    have hcard : Nat.card ψ.range = 2 ^ 4 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
      simp [Nat.card_eq_fintype_card]
    have := Subgroup.card_le_of_le hrange
    rw [hcard] at this
    omega
  · obtain ⟨i, j, k, hijk⟩ := hdesc x hx
    refine ⟨b₁ ^ (i : ℕ) * b₂ ^ (j : ℕ) * b₃ ^ (k : ℕ), ?_, ?_⟩
    · exact B.mul_mem (B.mul_mem (Subgroup.pow_mem _ (hmem 0) _) (Subgroup.pow_mem _ (hmem 1) _))
        (Subgroup.pow_mem _ (hmem 2) _)
    · rw [map_mul, map_mul, map_pow, map_pow, map_pow, hb₁, hb₂, hb₃, ← hijk]

section Cover


theorem mem_inner_of_odd_outer {J : Type} [Group J] (hodd : Odd (Nat.card (Outer J)))
    {α : MulAut J} (h2 : α * α = 1) : α ∈ inner J := by
  have hα : orderOf (QuotientGroup.mk (s := inner J) α) ∣ 2 :=
    (orderOf_map_dvd (QuotientGroup.mk' (inner J)) α).trans
      (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2))
  have hcard : orderOf (QuotientGroup.mk (s := inner J) α) ∣ Nat.card (Outer J) :=
    orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk (s := inner J) α) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hα (Nat.coprime_two_left.2 hodd))
      hcard
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem exists_conj_eq_of_involutory_cover {J : Type} [Group J] [Group.IsPerfect J]
    (hK : SuzukiModel (J ⧸ center J) 2 3) {α : MulAut J} (h2 : α * α = 1) :
    ∃ a : J, α = MulAut.conj a := by
  have hodd := ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0}
    (J ⧸ center J) 2 3 hK).2 J ⟨MulEquiv.refl _⟩).2.2
  obtain ⟨a, ha⟩ := mem_inner_of_odd_outer hodd h2
  exact ⟨a, ha.symm⟩

theorem isPGroup_two_center_of_suzukiModel {J : Type} [Group J] [Finite J] [Group.IsPerfect J]
    (hK : SuzukiModel (J ⧸ center J) 2 3) : IsPGroup 2 (center J) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hK
  exact CFSG.Quasithin.isPGroup_two_of_mulEquiv_cyclic_odd_sylow (center J) le_rfl e
    fun _ _ hr2 _ Q => CFSG.SectionRank.suzuki_sylow_isCyclic a ha hr2 Q

theorem szCoverFacts_proved : SzCoverFacts := by
  intro J _ _ hperf hmodel α hα1 hα2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := exists_conj_eq_of_involutory_cover hmodel hα2
  by_cases hZ : center J = ⊥
  · right
    have e1 : (J ⧸ center J) ≃* J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact not_twoSubgroupsAbelian_fix (suzukiModel_of_mulEquiv' e1 hmodel) hα1 hα2
  · left
    set φ : J →* J ⧸ center J := QuotientGroup.mk' (center J) with hφ
    have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
    have hker : φ.ker ≤ center J := by rw [hφ, QuotientGroup.ker_mk']
    have hZ2 := isPGroup_two_center_of_suzukiModel hmodel
    have : Nontrivial (center J) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 : 1 < Nat.card (center J) := Finite.one_lt_card
      rw [hk, pow_zero] at h1
      exact lt_irrefl _ h1
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center J) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hz2 : (z : J) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
    have hz1 : (z : J) ≠ 1 := by
      intro h
      have h' : z = 1 := Subtype.ext h
      rw [h', orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hzk : φ (z : J) = 1 := (QuotientGroup.eq_one_iff (z : J)).2 z.2
    have haa : a * a ∈ center J := mem_center_of_conj_eq_one (by rw [map_mul]; exact hα2)
    have hx2 : φ a * φ a = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff (a * a)).2 haa
    have hx1 : φ a ≠ 1 := by
      intro h
      apply hα1
      have hac : a ∈ center J := (QuotientGroup.eq_one_iff a).1 h
      ext y
      show a * y * a⁻¹ = y
      rw [(Subgroup.mem_center_iff.1 hac y).symm]
      group
    have hxo : orderOf (φ a) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := suzukiModel_data hmodel
    have hz' : orderOf (e (φ a)) = 2 := by rw [MulEquiv.orderOf_eq]; exact hxo
    obtain ⟨E, n, hxE, hEn⟩ := exists_E8Normalized hF hz'
    have hxE' : φ a ∈ E.map e.symm.toMonoidHom := ⟨e (φ a), hxE, by simp⟩
    obtain ⟨B, hBsq, hBcomm, hBcard, b, hbB, hbx⟩ :=
      exists_elementary_lift hφs hker (hEn.map e.symm) hzk hz2 hz1 hxE'
    refine ⟨B, fun y hy => ?_, hBsq, hBcomm, hBcard⟩
    have hc : b⁻¹ * a ∈ center J := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbx, inv_mul_cancel])
    obtain ⟨c, hcc, hac⟩ : ∃ c ∈ center J, a = b * c := ⟨b⁻¹ * a, hc, by group⟩
    have hcy : c * y = y * c := (Subgroup.mem_center_iff.1 hcc y).symm
    have hb : b * y = y * b := hBcomm b hbB y hy
    show a * y * a⁻¹ = y
    rw [hac]
    calc b * c * y * (b * c)⁻¹ = b * (c * y) * c⁻¹ * b⁻¹ := by group
      _ = b * (y * c) * c⁻¹ * b⁻¹ := by rw [hcy]
      _ = b * y * b⁻¹ := by group
      _ = y := by rw [hb]; group

end Cover

end CFSG.EvenSporadicStandard.Induction
