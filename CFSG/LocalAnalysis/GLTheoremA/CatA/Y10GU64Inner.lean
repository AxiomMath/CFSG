module

public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Arith
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Normalize
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Structure
public import CFSG.LieType.SemisimpleCentralizers.PComponentProduct
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.Assembly.LargeEvenGLABridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

open CFSG.LieType.SemisimpleCentralizers.OrderThree
  (nonempty_quotientCenter_equiv_statedProj_statedSU
    nonempty_quotientCenter_mulEquiv_of_surjective)

theorem nonempty_quotientCenter_model_twA {S : Type} [Group S] {lab : GLALabel}
    (hl : HasLabel S (fun l : GLALabel => l = lab)) (ht : lab.tag = .twA) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ lab.n) ^ 2 ∧
      Nonempty (S ⧸ Subgroup.center S ≃* StatedProj (StatedSU (lab.rank + 1) (2 ^ lab.n) K)) := by
  obtain ⟨_, lab', _, hraw⟩ := hl
  obtain ⟨_, _, _, _, _, _, _, hEq⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hEq' : lab' = lab := hEq
  rw [hEq'] at hraw
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [ht] at hraw
  dsimp only at hraw
  unfold CFSG.Assembly.LargeEvenRecipeUnitary at hraw
  obtain ⟨K, hK, hKf, hcard, hQ⟩ := hraw
  obtain ⟨_, _, θ, -⟩ := hQ
  exact ⟨K, hK, hKf, hcard, ⟨θ⟩⟩

theorem u64InnerPiece_holds : U64InnerPiece := by
  intro d n K _ _ hK hd5 hd hn β hβ hβ3 J hJ hJl
  have hn0 : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hne : Even n := by
    rw [even_iff_two_dvd]
    omega
  have hd3 : 3 ≤ d := by omega
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.unitaryFieldData_of_card hn1 hK
  haveI : CharP K 2 := h.charP
  obtain ⟨A, hA, hβA⟩ := hβ
  obtain ⟨B, hB, hB3, hβB⟩ :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.exists_mem_statedSU_pow_three_eq_one
      hK hne hn0 hd3 hA hβA hβ3
  let S : Subgroup (GL (Fin d) K) := StatedSU d (2 ^ n) K
  let N : Subgroup S := (StatedScalars (Fin d) K).subgroupOf S
  let π : S →* StatedProj S := QuotientGroup.mk' N
  let b : S := ⟨B, hB⟩
  let α : MulAut S := MulAut.conj b
  have hkerπ : π.ker ≤ Subgroup.center S := by
    rw [show π.ker = N from QuotientGroup.ker_mk' N]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp hx
    simpa only [Subgroup.coe_mul] using Subgroup.mem_center_iff.mp hx' (y : GL (Fin d) K)
  have hαβ : ∀ g : S, π (α g) = β (π g) := by
    intro g
    have hg : ((α g : S) : GL (Fin d) K) = B * (g : GL (Fin d) K) * B⁻¹ := by
      dsimp only [α]
      rw [MulAut.conj_apply]
      rfl
    show QuotientGroup.mk' N (α g) = β (QuotientGroup.mk' N g)
    exact (hβB g (α g) hg).symm
  obtain ⟨Jt, hJt, hJtmap⟩ :=
    exists_glaPComponent_map_fixSubgroup π hkerπ α β hαβ
      (show Function.Surjective π from QuotientGroup.mk'_surjective N) Nat.prime_three hJ
  have memY : ∀ y : S, y ∈ fixSubgroup α ↔ Commute (y : GL (Fin d) K) B := by
    intro y
    rw [mem_fixSubgroup, MulAut.conj_apply]
    constructor
    · intro hy
      have hb : (b : S) * y = y * b := by
        calc b * y = b * y * b⁻¹ * b := by group
          _ = y * b := by rw [hy]
      have hb' : (b : GL (Fin d) K) * (y : GL (Fin d) K) =
          (y : GL (Fin d) K) * (b : GL (Fin d) K) :=
        congrArg (fun z : S => (z : GL (Fin d) K)) hb
      exact hb'.symm
    · intro hy
      have hb' : (b : S) * y = y * b := by
        apply Subtype.ext
        exact hy.symm
      calc b * y * b⁻¹ = y * b * b⁻¹ := by rw [hb']
        _ = y := by group
  obtain ⟨k, a, L₁, L₂, hL1B, hL2B, hL12, hcommut, e₁, e₂⟩ :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.exists_centralizer_factors h hne hB hB3
  have hL1Y : L₁ ≤ fixSubgroup α := fun x hx => (memY x).2 (hL1B x hx)
  have hL2Y : L₂ ≤ fixSubgroup α := fun x hx => (memY x).2 (hL2B x hx)
  have hEY : L₁ ⊔ L₂ ≤ fixSubgroup α := sup_le hL1Y hL2Y
  have hEn : ((L₁ ⊔ L₂).subgroupOf (fixSubgroup α)).Normal := by
    refine ⟨fun e he y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    have hyB : Commute (((y : ↥(fixSubgroup α)) : S) : GL (Fin d) K) B :=
      (memY (y : S)).1 y.2
    have heB : Commute (((e : ↥(fixSubgroup α)) : S) : GL (Fin d) K) B :=
      (memY (e : S)).1 (hEY he)
    have hconj : ((y : ↥(fixSubgroup α)) : S) * ((e : ↥(fixSubgroup α)) : S) *
        ((y : ↥(fixSubgroup α)) : S)⁻¹ =
        ⁅((y : ↥(fixSubgroup α)) : S), ((e : ↥(fixSubgroup α)) : S)⁆ *
          ((e : ↥(fixSubgroup α)) : S) := by
      rw [commutatorElement_def]; group
    show ((y : ↥(fixSubgroup α)) : S) * ((e : ↥(fixSubgroup α)) : S) *
        ((y : ↥(fixSubgroup α)) : S)⁻¹ ∈ L₁ ⊔ L₂
    rw [hconj]
    exact mul_mem (hcommut _ _ hyB heB) he
  have hsolv : IsSolvable (↥(fixSubgroup α) ⧸ (L₁ ⊔ L₂).subgroupOf (fixSubgroup α)) := by
    apply Group.isSolvable_of_comm
    intro p q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hxB : Commute (((x : ↥(fixSubgroup α)) : S) : GL (Fin d) K) B :=
      (memY (x : S)).1 x.2
    have hyB : Commute (((y : ↥(fixSubgroup α)) : S) : GL (Fin d) K) B :=
      (memY (y : S)).1 y.2
    have hcom : ⁅(((y : ↥(fixSubgroup α)) : S))⁻¹, (((x : ↥(fixSubgroup α)) : S))⁻¹⁆ ∈ L₁ ⊔ L₂ :=
      hcommut _ _ hyB.inv_left hxB.inv_left
    convert hcom using 1
    rw [commutatorElement_def]; group
  have hSUq :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.isQuasisimple_or_isSolvable_statedSU hK hn2 k
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    nlinarith [h2n, Nat.zero_le (2 ^ n)]
  have hSLq :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.isQuasisimple_or_isSolvable_statedSL hK4 a
  have hLfun : ∀ i : Fin 2, CFSG.Assembly.IsQuasisimple ↥(![L₁, L₂] i) ∨
      IsSolvable ↥(![L₁, L₂] i) := by
    intro i
    fin_cases i
    · change CFSG.Assembly.IsQuasisimple ↥L₁ ∨ IsSolvable ↥L₁
      rcases e₁ with ⟨e₁'⟩
      rcases hSUq with hq | hs
      · exact Or.inl (CFSG.Assembly.IsQuasisimple.of_mulEquiv e₁' hq)
      · haveI : Group.IsSolvable (StatedSU k (2 ^ n) K) := hs
        exact Or.inr (Group.isSolvable_of_isSolvable_injective
          (f := (e₁' : ↥L₁ →* StatedSU k (2 ^ n) K)) e₁'.injective)
    · change CFSG.Assembly.IsQuasisimple ↥L₂ ∨ IsSolvable ↥L₂
      rcases e₂ with ⟨e₂'⟩
      rcases hSLq with hq | hs
      · exact Or.inl (CFSG.Assembly.IsQuasisimple.of_mulEquiv e₂' hq)
      · haveI : Group.IsSolvable (StatedSL a K) := hs
        exact Or.inr (Group.isSolvable_of_isSolvable_injective
          (f := (e₂' : ↥L₂ →* StatedSL a K)) e₂'.injective)
  have hE : L₁ ⊔ L₂ = ⨆ i : Fin 2, ![L₁, L₂] i := by
    apply le_antisymm
    · apply sup_le
      · exact le_iSup (fun i : Fin 2 => ![L₁, L₂] i) 0
      · exact le_iSup (fun i : Fin 2 => ![L₁, L₂] i) 1
    · apply iSup_le
      intro i
      fin_cases i <;> simp
  have hcomm : ∀ i j : Fin 2, i ≠ j → ∀ x ∈ ![L₁, L₂] i, ∀ y ∈ ![L₁, L₂] j,
      Commute x y := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hL12 x hx y hy
    · exact (hL12 y hy x hx).symm
    · exact absurd rfl hij
  obtain ⟨i, hJt_eq, hJt_q⟩ :=
    CFSG.LieType.SemisimpleCentralizers.largeEvenPComponent_eq_of_commuting_product
      (p := 3) (fun i : Fin 2 => ![L₁, L₂] i) hEY hEn hsolv hE hcomm hLfun
      ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 (fixSubgroup α) Jt).mpr hJt)
  have hcardJt : ∀ (hq : Group.IsPerfect Jt),
      Nat.card (Jt ⧸ Subgroup.center Jt) = Nat.card (J ⧸ Subgroup.center J) := by
    intro hq
    have hkerf : (π.subgroupMap Jt).ker ≤ Subgroup.center Jt := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hx1 : π (x : S) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        simpa using this
      have hx2 : (x : S) ∈ π.ker := MonoidHom.mem_ker.mpr hx1
      have hx3 : (x : S) ∈ Subgroup.center S := hkerπ hx2
      simpa only [Subgroup.coe_mul] using Subgroup.mem_center_iff.mp hx3 (y : S)
    obtain ⟨eJtJ⟩ : Nonempty (Jt ⧸ Subgroup.center Jt ≃* J ⧸ Subgroup.center J) := by
      rw [← hJtmap]
      exact nonempty_quotientCenter_mulEquiv_of_surjective
        hq (π.subgroupMap Jt) (π.subgroupMap_surjective Jt) hkerf
    exact Nat.card_congr eJtJ.toEquiv
  obtain ⟨K₅, hK₅f, hK₅fin, hK₅card, hK₅eq⟩ :=
    nonempty_quotientCenter_model_twA (lab := ⟨.twA, 4, 2⟩) hJl rfl
  letI : Field K₅ := hK₅f
  haveI : Finite K₅ := hK₅fin
  have hK₅card' : Nat.card K₅ = (2 ^ 2) ^ 2 := hK₅card
  have hcard_model : Nat.card (J ⧸ Subgroup.center J) =
      Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K₅)) :=
    Nat.card_congr (Classical.choice hK₅eq).toEquiv
  fin_cases i
  ·
    change Jt = L₁ at hJt_eq
    change CFSG.Assembly.IsQuasisimple ↥L₁ at hJt_q
    have hq : Group.IsPerfect Jt := by rw [hJt_eq]; exact ⟨hJt_q.1⟩
    have hcardJtJ := hcardJt hq
    rcases e₁ with ⟨e₁'⟩
    have hqsSU : CFSG.Assembly.IsQuasisimple (StatedSU k (2 ^ n) K) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv e₁'.symm hJt_q
    have hk2 : 2 ≤ k :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSU hqsSU
    have hquot : Nat.card (L₁ ⧸ Subgroup.center L₁) =
        Nat.card (StatedProj (StatedSU k (2 ^ n) K)) :=
      Nat.card_congr (Classical.choice
        (nonempty_quotientCenter_equiv_statedProj_statedSU
          (f := n) hK hn2 hk2 e₁')).toEquiv
    have hSUeq : Nat.card (StatedProj (StatedSU k (2 ^ n) K)) =
        Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K₅)) := by
      have h1 : Nat.card (L₁ ⧸ Subgroup.center L₁) = Nat.card (J ⧸ Subgroup.center J) := by
        rw [← hJt_eq]
        exact hcardJtJ
      exact hquot.symm.trans (h1.trans hcard_model)
    have hpadic := congrArg (fun m => padicValNat 2 m) hSUeq
    rw [CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_psu (K := K) (a := n) (d := k)
        hn1 (by omega : 1 ≤ k) hK,
      CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_psu (K := K₅) (a := 2) (d := 5)
        (by norm_num) (by norm_num) hK₅card'] at hpadic
    have h20 : n * (k * (k - 1) / 2) = 20 := by
      norm_num at hpadic
      exact hpadic
    exact (CFSG.LieType.SemisimpleCentralizers.OrderThree.eq_two_of_mul_eq_twenty hn h20).1
  ·
    change Jt = L₂ at hJt_eq
    change CFSG.Assembly.IsQuasisimple ↥L₂ at hJt_q
    have hq : Group.IsPerfect Jt := by rw [hJt_eq]; exact ⟨hJt_q.1⟩
    have hcardJtJ := hcardJt hq
    rcases e₂ with ⟨e₂'⟩
    have hqsSL : CFSG.Assembly.IsQuasisimple (StatedSL a K) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv e₂'.symm hJt_q
    have ha2 : 2 ≤ a :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSL hqsSL
    have hquot : Nat.card (L₂ ⧸ Subgroup.center L₂) =
        Nat.card (StatedProj (StatedSL a K)) :=
      Nat.card_congr (Classical.choice
        (CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj
          e₂')).toEquiv
    have hSLeq : Nat.card (StatedProj (StatedSL a K)) =
        Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K₅)) := by
      have h1 : Nat.card (L₂ ⧸ Subgroup.center L₂) = Nat.card (J ⧸ Subgroup.center J) := by
        rw [← hJt_eq]
        exact hcardJtJ
      exact hquot.symm.trans (h1.trans hcard_model)
    have hpadic := congrArg (fun m => padicValNat 2 m) hSLeq
    have hK2n : Nat.card K = 2 ^ (2 * n) := by
      rw [hK, ← pow_mul, Nat.mul_comm]
    rw [CFSG.LieType.SemisimpleCentralizers.OrderThree.padicValNat_card_statedProj_statedSL
        (K := K) (p := 2) (m := 2 * n) (a := a) Nat.prime_two (by omega : 1 ≤ 2 * n) hK2n
        (by omega : 1 ≤ a),
      CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_psu (K := K₅) (a := 2) (d := 5)
        (by norm_num) (by norm_num) hK₅card'] at hpadic
    have h20 : (2 * n) * (a * (a - 1) / 2) = 20 := by
      norm_num at hpadic
      exact hpadic
    obtain ⟨hn10, ha2'⟩ :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.eq_ten_of_mul_eq_twenty hn h20
    exfalso
    have hK20 : Nat.card K = 2 ^ 20 := by
      rw [hK, hn10]; norm_num
    rw [ha2'] at hSLeq
    exact (CFSG.LieType.SemisimpleCentralizers.OrderThree.card_statedProj_statedSL_two_ne
      (K := K) (K₅ := K₅) hK20 hK₅card') hSLeq

end CFSG.LocalAnalysis.GLTheoremA.Y10F
