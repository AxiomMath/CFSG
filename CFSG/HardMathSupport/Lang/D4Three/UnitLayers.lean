module

public import CFSG.HardMathSupport.Lang.E27Lie.CocycleCount
public import CFSG.HardMathSupport.Lang.D4Three.CharThreeCount
public import CFSG.HardMathSupport.Lang.Triality.HeightCoord

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie


variable (τ : Tag) {K : Type} [Field K] [Finite K]

@[expose] def unitN (K : Type) [Field K] [Finite K] (k : ℕ) : Subgroup ↥(adjointGroup τ K) :=
  (heightSeries τ K (((k + 1 : ℕ) : ℤ))).comap (adjointGroup τ K).subtype

theorem mem_unitN {k : ℕ} {x : ↥(adjointGroup τ K)} :
    x ∈ unitN τ K k ↔ (x : ModGL τ K) ∈ heightSeries τ K (((k + 1 : ℕ) : ℤ)) := Iff.rfl

@[expose] def UnitRoots (k : ℕ) : Type :=
  ↥{α : Fin τ.rank → ℤ | IsRoot τ α ∧ height α = ((k + 1 : ℕ) : ℤ)}

instance (k : ℕ) : Finite (UnitRoots τ k) :=
  ((finite_setOf_isRoot τ).subset fun _ h => h.1).to_subtype

abbrev UnitCoord (K : Type) (k : ℕ) : Type := Multiplicative (UnitRoots τ k → K)

theorem UnitRoots.pos {k : ℕ} (δ : UnitRoots τ k) : IsRoot τ δ.1 ∧ 0 < height δ.1 :=
  ⟨δ.2.1, by rw [δ.2.2]; positivity⟩

@[expose] def unitPhi (K : Type) [Field K] [Finite K] (k : ℕ) : unitN τ K k →* UnitCoord τ K k where
  toFun x := Multiplicative.ofAdd (fun δ => rootCoord (UnitRoots.pos τ δ) (x.1 : ModGL τ K))
  map_one' := by
    refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
    exact rootCoord_one _
  map_mul' x y := by
    refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
    have hx : (x.1 : ModGL τ K) ∈ heightSeries τ K (height δ.1) := by
      rw [δ.2.2]; exact x.2
    have hy : (y.1 : ModGL τ K) ∈ heightSeries τ K (height δ.1) := by
      rw [δ.2.2]; exact y.2
    exact rootCoord_mul _ hx hy

theorem unitN_chain (k : ℕ) : unitN τ K (k + 1) ≤ unitN τ K k := by
  intro x hx
  rw [mem_unitN] at hx ⊢
  unfold heightSeries at hx ⊢
  refine rootSpan_mono (S := {γ | IsRoot τ γ ∧ 0 < height γ ∧
      ((k + 1 + 1 : ℕ) : ℤ) ≤ height γ}) (T := {γ | IsRoot τ γ ∧ 0 < height γ ∧
      ((k + 1 : ℕ) : ℤ) ≤ height γ}) ?_ hx
  intro γ hγ
  refine ⟨hγ.1, hγ.2.1, ?_⟩
  have := hγ.2.2
  push_cast at this ⊢
  linarith

theorem unitN_bot :
    unitN τ K (maxHeight τ).toNat = ⊥ := by
  have hdz : (((maxHeight τ).toNat : ℕ) : ℤ) = maxHeight τ :=
    Int.toNat_of_nonneg (by linarith [one_le_maxHeight (τ := τ)])
  have h1 : heightSeries τ K ((((maxHeight τ).toNat + 1 : ℕ) : ℤ)) = ⊥ := by
    have := heightSeries_maxHeight_add_one (τ := τ) (R := K)
    push_cast
    rw [hdz]
    exact this
  rw [unitN, h1]
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_bot, Subgroup.mem_bot]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem unitN_zero_mem {g : ↥(adjointGroup τ K)} (hg : g ∈ unitN τ K 0) :
    (g : ModGL τ K) ∈ posUnipotent τ K := by
  rw [mem_unitN] at hg
  have : (((0 + 1 : ℕ) : ℤ)) = 1 := by norm_num
  rw [this, heightSeries_one] at hg
  exact hg

theorem unitPhi_conj {k : ℕ} {g : ↥(adjointGroup τ K)} (hg : g ∈ unitN τ K 0) (x : unitN τ K k) :
    ∃ hx : g * (x : ↥(adjointGroup τ K)) * g⁻¹ ∈ unitN τ K k,
      unitPhi τ K k ⟨g * (x : ↥(adjointGroup τ K)) * g⁻¹, hx⟩ = unitPhi τ K k x := by
  have hgU := unitN_zero_mem τ hg
  have hx := x.2
  rw [mem_unitN] at hx
  have hmem : g * (x : ↥(adjointGroup τ K)) * g⁻¹ ∈ unitN τ K k := by
    rw [mem_unitN]
    exact (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hgU) _).1 hx
  refine ⟨hmem, ?_⟩
  refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
  have hx' : ((x : ↥(adjointGroup τ K)) : ModGL τ K) ∈ heightSeries τ K (height δ.1) := by
    rw [δ.2.2]; exact hx
  exact rootCoord_conj (UnitRoots.pos τ δ) hgU hx'

theorem unitPhi_triv {k : ℕ} (x : unitN τ K k) (hx : (x : ↥(adjointGroup τ K)) ∈ unitN τ K (k + 1)) :
    unitPhi τ K k x = 1 := by
  refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
  rw [mem_unitN] at hx
  have hker : ((x : ↥(adjointGroup τ K)) : ModGL τ K) ∈ rootSpan τ K (coordKerRoots δ.1) := by
    refine heightSeries_succ_le_coordKer _ ?_
    rw [δ.2.2]
    simpa using hx
  exact rootCoord_of_mem_coordKer (UnitRoots.pos τ δ) hker

theorem unitPhi_ker {k : ℕ} (x : unitN τ K k) (hx : unitPhi τ K k x = 1) :
    (x : ↥(adjointGroup τ K)) ∈ unitN τ K (k + 1) := by
  have hcoord : ∀ (α : Fin τ.rank → ℤ) (hα : IsRoot τ α ∧ 0 < height α),
      height α = ((k + 1 : ℕ) : ℤ) → rootCoord hα ((x : ↥(adjointGroup τ K)) : ModGL τ K) = 0 := by
    intro α hα hαh
    have := congrArg Multiplicative.toAdd hx
    exact congrFun this ⟨α, hα.1, hαh⟩
  have := mem_heightSeries_succ_of_coord_eq_zero x.2 hcoord
  rw [mem_unitN]
  exact_mod_cast this

structure LayerAct (β : MulAut ↥(adjointGroup τ K)) (σ : K ≃+* K) where
  r : ∀ k, UnitRoots τ k → UnitRoots τ k
  f : ∀ k, UnitRoots τ k → K
  stable : ∀ k, ∀ x ∈ unitN τ K k, β x ∈ unitN τ K k
  coord : ∀ k (δ : UnitRoots τ k) (x : ↥(adjointGroup τ K)), x ∈ unitN τ K k →
    rootCoord (UnitRoots.pos τ δ) ((β x : ↥(adjointGroup τ K)) : ModGL τ K) =
      f k δ * σ (rootCoord (UnitRoots.pos τ (r k δ)) (x : ModGL τ K))

variable {τ}

@[expose] def LayerAct.tau {β : MulAut ↥(adjointGroup τ K)} {σ : K ≃+* K} (la : LayerAct τ β σ)
    (k : ℕ) : UnitCoord τ K k →* UnitCoord τ K k :=
  AddMonoidHom.toMultiplicative (monoTauAdd (la.r k) (la.f k) σ)

theorem LayerAct.act {β : MulAut ↥(adjointGroup τ K)} {σ : K ≃+* K} (la : LayerAct τ β σ) (k : ℕ)
    (x : unitN τ K k) :
    unitPhi τ K k ⟨β x, la.stable k x x.2⟩ = la.tau k (unitPhi τ K k x) := by
  refine congrArg Multiplicative.ofAdd (funext fun δ => ?_)
  exact la.coord k δ x x.2

theorem LayerAct.cocycleData {β : MulAut ↥(adjointGroup τ K)} {σ : K ≃+* K} (la : LayerAct τ β σ)
    (b : ℕ → ℕ)
    (hb : ∀ k, k < (maxHeight τ).toNat →
      Nat.card {a : UnitCoord τ K k // a ∈ (unitPhi τ K k).range ∧
        a * la.tau k a * la.tau k (la.tau k a) = 1} ≤ b k) :
    CocycleData β (unitN τ K) (maxHeight τ).toNat (unitPhi τ K) la.tau b where
  chain := unitN_chain τ
  bot := unitN_bot τ
  stable := la.stable
  conj := fun k _ g hg x => unitPhi_conj τ hg x
  act := fun k _ x => la.act k x
  triv := fun k _ x hx => unitPhi_triv τ x hx
  ker := fun k _ x hx => unitPhi_ker τ x hx
  bound := hb

theorem sum_card_unitRoots_le (d : ℕ) :
    ∑ k ∈ Finset.range d, Nat.card (UnitRoots τ k) ≤
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  classical
  have hfin : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.Finite :=
    (finite_setOf_isRoot τ).subset fun _ h => h.1
  have hcard : ∀ k, Nat.card (UnitRoots τ k) =
      (hfin.toFinset.filter fun α => height α = ((k + 1 : ℕ) : ℤ)).card := by
    intro k
    rw [UnitRoots, Nat.card_coe_set_eq]
    rw [← Set.ncard_coe_finset]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by rw [h2]; positivity⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  simp_rw [hcard]
  rw [← Finset.card_biUnion]
  · rw [Set.ncard_eq_toFinset_card _ hfin]
    refine Finset.card_le_card fun α hα => ?_
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hα
    exact (Finset.mem_filter.1 hk).1
  · intro i _ j _ hij
    refine Finset.disjoint_left.2 fun α hαi hαj => hij ?_
    have h1 := (Finset.mem_filter.1 hαi).2
    have h2 := (Finset.mem_filter.1 hαj).2
    have : ((i + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) := by rw [← h1, ← h2]
    omega

variable [CharP K 3]

theorem card_tau_cocycle_le {β : MulAut ↥(adjointGroup τ K)} {σ : K ≃+* K}
    (la : LayerAct τ β σ) (k : ℕ) :
    Nat.card {a : UnitCoord τ K k // a ∈ (unitPhi τ K k).range ∧
        a * la.tau k a * la.tau k (la.tau k a) = 1} ≤ Nat.card K ^ Nat.card (UnitRoots τ k) := by
  calc _ ≤ Nat.card (UnitCoord τ K k) := Nat.card_le_card_of_injective
          (fun a => a.1) (fun a b h => Subtype.ext h)
    _ = _ := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]

theorem card_tau_cocycle_le_div {β : MulAut ↥(adjointGroup τ K)} {σ : K ≃+* K}
    (la : LayerAct τ β σ) (k : ℕ) (j₀ : UnitRoots τ k)
    (hj₀ : ∃ a, monoN (la.r k) (la.f k) σ a j₀ ≠ 0) :
    Nat.card {a : UnitCoord τ K k // a ∈ (unitPhi τ K k).range ∧
        a * la.tau k a * la.tau k (la.tau k a) = 1} ≤
      Nat.card K ^ Nat.card (UnitRoots τ k) / 3 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  refine le_trans (Nat.mul_le_mul_right 3 ?_) (card_ker_mul_three_le _ j₀ hj₀)
  refine Nat.card_le_card_of_injective (fun a => ⟨Multiplicative.toAdd a.1, ?_⟩) ?_
  · have h := a.2.2
    have : (Multiplicative.ofAdd (monoN (la.r k) (la.f k) σ (Multiplicative.toAdd a.1)) :
        UnitCoord τ K k) = 1 := h
    simpa [ofAdd_eq_one] using this
  · intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Multiplicative.toAdd.injective this)

theorem card_fixed_unitN_zero_ge {β : MulAut ↥(adjointGroup τ K)} {σ : K ≃+* K}
    (la : LayerAct τ β σ) (hβ3 : β ^ 3 = 1) (S : Finset ℕ)
    (hS : ∀ k ∈ S, k < (maxHeight τ).toNat ∧ ∃ j₀ : UnitRoots τ k,
      ∃ a, monoN (la.r k) (la.f k) σ a j₀ ≠ 0) :
    3 ^ S.card ≤ Nat.card {x : ↥(adjointGroup τ K) // x ∈ unitN τ K 0 ∧ β x = x} := by
  classical
  have : Fintype ↥(adjointGroup τ K) := Fintype.ofFinite _
  set d := (maxHeight τ).toNat with hd
  set q := Nat.card K with hq
  have hqpos : 0 < q := Nat.card_pos
  set b : ℕ → ℕ := fun k =>
    if k ∈ S then q ^ Nat.card (UnitRoots τ k) / 3 else q ^ Nat.card (UnitRoots τ k) with hb
  have hbd : ∀ k, k < d → Nat.card {a : UnitCoord τ K k // a ∈ (unitPhi τ K k).range ∧
      a * la.tau k a * la.tau k (la.tau k a) = 1} ≤ b k := by
    intro k hk
    by_cases hkS : k ∈ S
    · obtain ⟨-, j₀, hj₀⟩ := hS k hkS
      simp only [hb, if_pos hkS]
      exact card_tau_cocycle_le_div la k j₀ hj₀
    · simp only [hb, if_neg hkS]
      exact card_tau_cocycle_le la k
  have hcd := (la.cocycleData b hbd).card_cocycle_le
  have hH : ∀ x ∈ unitN τ K 0, β x ∈ unitN τ K 0 := la.stable 0
  have hmain := card_le_card_cocycle_mul_card_fixed β hβ3 (unitN τ K 0) hH
  have hN0 : Nat.card (unitN τ K 0) =
      q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
    have hsub : unitN τ K 0 = (posUnipotent τ K).subgroupOf (adjointGroup τ K) := by
      ext x
      rw [mem_unitN, Subgroup.mem_subgroupOf]
      have : (((0 + 1 : ℕ) : ℤ)) = 1 := by norm_num
      rw [this, heightSeries_one]
    rw [hsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (posUnipotent_le_adjointGroup (τ := τ) (K := K))).toEquiv, card_posUnipotent]
  have hsum : (∏ k ∈ Finset.range d, q ^ Nat.card (UnitRoots τ k)) ≤
      q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right hqpos (sum_card_unitRoots_le (τ := τ) d)
  have hSsub : S ⊆ Finset.range d := fun k hk => Finset.mem_range.2 (hS k hk).1
  have h3 : 3 ^ S.card * ∏ k ∈ Finset.range d, b k ≤ ∏ k ∈ Finset.range d, q ^ Nat.card (UnitRoots τ k) := by
    have h1 : 3 ^ S.card = ∏ k ∈ Finset.range d, (if k ∈ S then 3 else 1) := by
      rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 hSsub, Finset.prod_const]
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun k _ => ?_
    by_cases hkS : k ∈ S
    · simp only [hb, if_pos hkS]
      exact Nat.mul_div_le _ _
    · simp only [hb, if_neg hkS, one_mul, le_refl]
  have hZpos : 0 < Nat.card {y : ↥(adjointGroup τ K) // y ∈ unitN τ K 0 ∧
      y * β y * β (β y) = 1} := by
    have : Nonempty {y : ↥(adjointGroup τ K) // y ∈ unitN τ K 0 ∧ y * β y * β (β y) = 1} :=
      ⟨⟨1, one_mem _, by simp⟩⟩
    exact Nat.card_pos
  rw [hN0] at hmain
  have hchain : 3 ^ S.card * Nat.card {y : ↥(adjointGroup τ K) // y ∈ unitN τ K 0 ∧
      y * β y * β (β y) = 1} ≤ Nat.card {y : ↥(adjointGroup τ K) // y ∈ unitN τ K 0 ∧
      y * β y * β (β y) = 1} * Nat.card {x : ↥(adjointGroup τ K) // x ∈ unitN τ K 0 ∧ β x = x} := by
    calc 3 ^ S.card * Nat.card {y : ↥(adjointGroup τ K) // y ∈ unitN τ K 0 ∧
          y * β y * β (β y) = 1}
        ≤ 3 ^ S.card * ∏ k ∈ Finset.range d, b k := Nat.mul_le_mul_left _ hcd
      _ ≤ ∏ k ∈ Finset.range d, q ^ Nat.card (UnitRoots τ k) := h3
      _ ≤ _ := hsum
      _ ≤ _ := hmain
  exact Nat.le_of_mul_le_mul_left (by rwa [mul_comm] at hchain) hZpos

end CFSG.HardMathSupport.Lang.D4Three
