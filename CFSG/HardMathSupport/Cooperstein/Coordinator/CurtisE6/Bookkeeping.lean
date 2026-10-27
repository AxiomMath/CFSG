module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Interfaces
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule


section Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mulAut_mul_conj' {G : Type*} [Group G] (φ : MulAut G) (x : G) :
    φ * MulAut.conj x = MulAut.conj (φ x) * φ :=
  MulEquiv.ext fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem rootDiagUnit_pow_card (a : Fin Tag.E6.rank → Kˣ) (j : ℕ) :
    ((CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 a :
      ModGL .E6 K) ^ j : ModGL .E6 K) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 (a ^ j) := by
  induction j with
  | zero =>
    refine Units.ext ?_
    simp [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiag_one]
  | succ j ih =>
    refine Units.ext ?_
    rw [pow_succ, Units.val_mul, ih]
    simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit]
    rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiag_mul_rootDiag, pow_succ]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem e6InnerOfSqOne_core (α : MulAut ↥(adjointGroup .E6 K)) (hα : α * α = 1)
    (g : ↥(adjointGroup .E6 K)) (a : Fin Tag.E6.rank → Kˣ)
    (hex : ∀ h : ↥(adjointGroup .E6 K), (α h : ModGL .E6 K) =
      (g : ModGL .E6 K) * rootDiagUnit .E6 a * (h : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹ *
        (g : ModGL .E6 K)⁻¹) :
    α ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range := by
  set d : ModGL .E6 K := rootDiagUnit .E6 a with hd
  set δ : MulAut ↥(adjointGroup .E6 K) := (MulAut.conj g)⁻¹ * α with hδdef
  have hδ : ∀ x : ↥(adjointGroup .E6 K), (δ x : ModGL .E6 K) = d * (x : ModGL .E6 K) * d⁻¹ := by
    intro x
    have h1 : δ x = g⁻¹ * α x * g := by
      rw [hδdef, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hex x]
    group
  have hpow : ∀ (j : ℕ) (x : ↥(adjointGroup .E6 K)),
      ((δ ^ j) x : ModGL .E6 K) = d ^ j * (x : ModGL .E6 K) * (d ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hδ, ih, pow_succ']
      group
  have hN : δ ^ Nat.card Kˣ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hpow, hd, rootDiagUnit_pow_card]
    have : a ^ Nat.card Kˣ = 1 := funext fun i => by
      simp only [Pi.pow_apply, Pi.one_apply]
      exact pow_card_eq_one'
    have h1 : rootDiagUnit .E6 (1 : Fin Tag.E6.rank → Kˣ) = (1 : ModGL .E6 K) :=
      Units.ext CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiag_one
    rw [this, h1, one_mul, inv_one, mul_one]
    rfl
  have hsq : δ * δ ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →*
      MulAut ↥(adjointGroup .E6 K)).range := by
    have e : MulAut.conj (g * δ g) * (δ * δ) = 1 := by
      calc MulAut.conj (g * δ g) * (δ * δ) = MulAut.conj g * (MulAut.conj (δ g) * δ) * δ := by
            rw [map_mul]; simp only [mul_assoc]
        _ = MulAut.conj g * (δ * MulAut.conj g) * δ := by rw [mulAut_mul_conj']
        _ = α * α := by
            rw [hδdef]; simp only [mul_assoc, mul_inv_cancel_left]
        _ = 1 := hα
    refine ⟨(g * δ g)⁻¹, ?_⟩
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right e
  have hq : Even (Nat.card Kˣ + 1) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    have h1 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
    rw [Nat.sub_add_cancel h1]
    exact (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
  obtain ⟨m, hm⟩ := hq
  have hδm : δ = (δ * δ) ^ m := by
    have : δ ^ (Nat.card Kˣ + 1) = δ := by rw [pow_succ, hN, one_mul]
    calc δ = δ ^ (Nat.card Kˣ + 1) := this.symm
      _ = (δ * δ) ^ m := by rw [hm, ← two_mul, pow_mul, pow_two]
  have hδr : δ ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range := by
    rw [hδm]
    exact pow_mem hsq m
  have : α = MulAut.conj g * δ := (mul_inv_cancel_left (MulAut.conj g) α).symm
  rw [this]
  exact mul_mem ⟨g, rfl⟩ hδr

end Inner

theorem e6InnerOfSqOne_holds : E6InnerOfSqOne := by
  intro K _ _ _ α hα hex
  obtain ⟨g, a, h⟩ := hex
  exact e6InnerOfSqOne_core α hα g a h

section Out

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_sq_one_ringAut_le :
    Nat.card {σ : K ≃+* K // σ ^ 2 = 1} ≤ 2 ∧
      (Nat.card K = 2 → Nat.card {σ : K ≃+* K // σ ^ 2 = 1} ≤ 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨-, -, -, -, -, hinv⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6
    (Or.inl rfl) K
  have hne : ∀ σ : K ≃+* K, σ ^ 2 = 1 → σ ≠ 1 → ∀ c, σ c = c ^ (2 ^ ((n : ℕ) / 2)) :=
    fun σ h1 h2 => (hinv 2 n Nat.prime_two n.pos hK σ h1 h2).2.1
  refine ⟨?_, fun h2 => ?_⟩
  · have hinj : Function.Injective
        (fun σ : {σ : K ≃+* K // σ ^ 2 = 1} => decide (σ.1 = 1)) := by
      intro σ τ h
      by_cases hσ : σ.1 = 1
      · have hτ : τ.1 = 1 := by
          by_contra hτ
          simp [hσ, hτ] at h
        exact Subtype.ext (hσ.trans hτ.symm)
      · have hτ : τ.1 ≠ 1 := by
          intro hτ
          simp [hσ, hτ] at h
        exact Subtype.ext (RingEquiv.ext fun c => (hne σ.1 σ.2 hσ c).trans (hne τ.1 τ.2 hτ c).symm)
    simpa using Nat.card_le_card_of_injective _ hinj
  · have hK1 : Nat.card K = 2 ^ 1 := by rw [h2]; rfl
    have hinj : Function.Injective (fun _ : {σ : K ≃+* K // σ ^ 2 = 1} => ()) := by
      intro σ τ _
      have h1 : ∀ σ : K ≃+* K, σ ^ 2 = 1 → σ = 1 := fun σ hσ => by
        by_contra hne'
        have := (hinv 2 1 Nat.prime_two le_rfl hK1 σ hσ hne').1
        exact absurd this (by decide)
      exact Subtype.ext ((h1 σ.1 σ.2).trans (h1 τ.1 τ.2).symm)
    simpa using Nat.card_le_card_of_injective _ hinj

theorem e6OutBound_core (B : Subgroup (MulAut ↥(adjointGroup .E6 K)))
    (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ Nat.card {σ : K ≃+* K // σ ^ 2 = 1} * 2 *
      Nat.card ↥(B ⊓ (MulAut.conj : ↥(adjointGroup .E6 K) →*
        MulAut ↥(adjointGroup .E6 K)).range) := by
  obtain ⟨Θ, -, -, hker, hsig, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6
    (Or.inl rfl) K
  let Φ : ↥B →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)) := Θ.comp B.subtype
  have hfinA : Finite ↥(adjointGroup .E6 K) := by
    have := finite_modGL (τ := Tag.E6) (K := K)
    infer_instance
  have hfinM : Finite (MulAut ↥(adjointGroup .E6 K)) :=
    Finite.of_injective (fun f : MulAut ↥(adjointGroup .E6 K) => (f : ↥(adjointGroup .E6 K) →
      ↥(adjointGroup .E6 K))) DFunLike.coe_injective
  have hfinI : Finite ↥(B ⊓ (MulAut.conj : ↥(adjointGroup .E6 K) →*
      MulAut ↥(adjointGroup .E6 K)).range) := inferInstance
  have hcard : Nat.card B = Nat.card Φ.range * Nat.card Φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv]
  haveI : NeZero (exactE Tag.E6) := ⟨by decide⟩
  have hZ : Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 2 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (exactE Tag.E6)) ≃ _)).trans
      (Nat.card_zmod _)
  have hrange : Nat.card Φ.range ≤ Nat.card {σ : K ≃+* K // σ ^ 2 = 1} * 2 := by
    let F : ↥Φ.range → {σ : K ≃+* K // σ ^ 2 = 1} × Multiplicative (ZMod (exactE Tag.E6)) :=
      fun y => (⟨(y.1 : RingAut K × Multiplicative (ZMod (exactE Tag.E6))).1, by
        obtain ⟨x, hx⟩ := y.2
        have h1 : Φ x * Φ x = 1 := by
          have hx2 : x * x = 1 := Subtype.ext (hsq x.1 x.2)
          rw [← map_mul, hx2, map_one]
        rw [hx] at h1
        have h2 := congrArg Prod.fst h1
        simpa [pow_two] using h2⟩, (y.1 : RingAut K × Multiplicative (ZMod (exactE Tag.E6))).2)
    have hFi : Function.Injective F := by
      intro y z h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Subtype.ext (Prod.ext (congrArg Subtype.val h1) h2)
    have := Nat.card_le_card_of_injective F hFi
    rwa [Nat.card_prod, hZ] at this
  have hker' : Nat.card Φ.ker ≤ Nat.card ↥(B ⊓ (MulAut.conj : ↥(adjointGroup .E6 K) →*
      MulAut ↥(adjointGroup .E6 K)).range) := by
    let G : ↥Φ.ker → ↥(B ⊓ (MulAut.conj : ↥(adjointGroup .E6 K) →*
        MulAut ↥(adjointGroup .E6 K)).range) := fun x =>
      ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, by
        have hx : Θ x.1.1 = 1 := x.2
        obtain ⟨g, a, hga⟩ := (hker _).1 (MonoidHom.mem_ker.2 hx)
        exact e6InnerOfSqOne_core x.1.1 (hsq _ x.1.2) g a hga⟩⟩
    have hGi : Function.Injective G := fun x y h => by
      have h1 : x.1.1 = y.1.1 := congrArg (fun z => z.1) h
      exact Subtype.ext (Subtype.ext h1)
    exact Nat.card_le_card_of_injective G hGi
  rw [hcard]
  exact Nat.mul_le_mul hrange hker'

theorem e6OutBound_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (B : Subgroup (MulAut ↥(adjointGroup .E6 K))),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 4 * Nat.card ↥(B ⊓ (MulAut.conj : ↥(adjointGroup .E6 K) →*
        MulAut ↥(adjointGroup .E6 K)).range) ∧
      (Nat.card K = 2 → Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : ↥(adjointGroup .E6 K) →*
        MulAut ↥(adjointGroup .E6 K)).range)) := by
  intro K _ _ _ B _ hsq
  have h := e6OutBound_core B hsq
  obtain ⟨h1, h2⟩ := card_sq_one_ringAut_le (K := K)
  refine ⟨?_, fun hK => ?_⟩
  · calc Nat.card B ≤ _ := h
      _ ≤ 2 * 2 * _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 2 h1)
  · calc Nat.card B ≤ _ := h
      _ ≤ 1 * 2 * _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 2 (h2 hK))
      _ = 2 * _ := by rw [one_mul]

end Out

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_minGroup_E6 :
    Nat.card ↥(e6Data_valid.minGroup K) =
      Nat.card ↥(adjointGroup .E6 K) * Nat.gcd 3 (Nat.card K - 1) := by
  have hsurj := Isogeny.e6Isogeny_surjective K
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Isogeny.e6Isogeny K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    CentralExt.FieldFour.e6Isogeny_ker_eq_center, (CentralExt.MinusculeClosed.card_center_e6 (k := K)).1] at h1
  exact h1

theorem prod_lt_pow78 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) <
      q ^ 78 := by
  have hpos : ∀ a : ℕ, 0 < q ^ a := fun a => pow_pos (by omega) a
  have hlt : ∀ a : ℕ, q ^ a - 1 < q ^ a := fun a => Nat.sub_lt (hpos a) one_pos
  have h1 : q ^ 36 * (q ^ 12 - 1) < q ^ 36 * q ^ 12 :=
    Nat.mul_lt_mul_of_pos_left (hlt 12) (hpos 36)
  have h2 := Nat.mul_lt_mul'' h1 (hlt 9)
  have h3 := Nat.mul_lt_mul'' h2 (hlt 8)
  have h4 := Nat.mul_lt_mul'' h3 (hlt 6)
  have h5 := Nat.mul_lt_mul'' h4 (hlt 5)
  have h6 := Nat.mul_lt_mul'' h5 (hlt 2)
  refine h6.trans_le (le_of_eq ?_)
  ring

theorem e6CardBound_core (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(e6Data_valid.minGroup K) < 2 ^ (78 * n) ∧
      (n = 1 → 2 * Nat.card ↥(e6Data_valid.minGroup K) < 2 ^ 79) := by
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard := card_minGroup_E6 (K := K)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, CFSG.Open.ordE6] at hcard
  have hle : Nat.card ↥(e6Data_valid.minGroup K) ≤ Nat.card K ^ 36 * (Nat.card K ^ 12 - 1) *
      (Nat.card K ^ 9 - 1) * (Nat.card K ^ 8 - 1) * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 5 - 1) *
        (Nat.card K ^ 2 - 1) := by
    rw [hcard]
    exact Nat.div_mul_le_self _ _
  refine ⟨?_, fun h1 => ?_⟩
  · calc _ ≤ _ := hle
      _ < Nat.card K ^ 78 := prod_lt_pow78 hq
      _ = 2 ^ (78 * n) := by rw [hK, ← pow_mul]; ring_nf
  · subst h1
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    rw [hK2] at hle
    have : 2 * (2 ^ 36 * (2 ^ 12 - 1) * (2 ^ 9 - 1) * (2 ^ 8 - 1) * (2 ^ 6 - 1) * (2 ^ 5 - 1) *
        (2 ^ 2 - 1)) < 2 ^ 79 := by norm_num
    omega

end Card

theorem e6CardBound_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      Nat.card ↥(e6Data_valid.minGroup K) < 2 ^ (78 * n) ∧
        (n = 1 → 2 * Nat.card ↥(e6Data_valid.minGroup K) < 2 ^ 79) := by
  intro K _ _ _ n hn hK
  exact e6CardBound_core n hn hK

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
