module

public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.LieType.Ree.SuzukiMatrixIdentities

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint
open scoped commutatorElement

variable (a : ℕ) (K : Type) [Field K]

@[expose] noncomputable def suzukiZ0 : Subgroup (suzukiGroup a K) :=
  Subgroup.closure (Set.range fun v : K => suzukiSElt a K 0 v)

variable {a K}

theorem suzukiSElt_ext {g h : suzukiGroup a K}
    (e : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : g = h :=
  Subtype.ext (Units.ext e)

theorem suzukiSElt_mul
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v c d : K) :
    suzukiSElt a K u v * suzukiSElt a K c d =
      suzukiSElt a K (u + c) (v + d + u ^ 2 ^ (a + 1) * c) :=
  suzukiSElt_ext ((suzuki_unipotent_product a hK).1 u v c d)

theorem suzukiSElt_inv
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    (suzukiSElt a K u v)⁻¹ = suzukiSElt a K u (v + u ^ (2 ^ (a + 1) + 1)) := by
  rw [inv_eq_iff_mul_eq_one, suzukiSElt_mul hK]
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  refine suzukiSElt_ext ?_
  rw [coe_suzukiSElt, Subgroup.coe_one, Units.val_one, ← (suzuki_unipotent_product a hK).2.2.2.2.1]
  congr 1
  · linear_combination u * h2
  · linear_combination (v + u ^ (2 ^ (a + 1) + 1)) * h2

theorem suzukiSElt_zero_zero
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiSElt a K 0 0 = 1 :=
  suzukiSElt_ext (suzuki_unipotent_product a hK).2.2.2.2.1

theorem suzukiSElt_inj {u v c d : K} :
    suzukiSElt a K u v = suzukiSElt a K c d ↔ u = c ∧ v = d := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have h' := congrArg (fun g : suzukiGroup a K =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  simp only [coe_suzukiSElt] at h'
  have h10 := congrFun (congrFun h' 1) 0
  have h20 := congrFun (congrFun h' 2) 0
  simp [suzukiS] at h10 h20
  exact ⟨h10, h20⟩

theorem coe_suzukiU [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiU a K : Set (suzukiGroup a K)) = Set.range fun p : K × K => suzukiSElt a K p.1 p.2 := by
  let H : Subgroup (suzukiGroup a K) :=
    { carrier := Set.range fun p : K × K => suzukiSElt a K p.1 p.2
      mul_mem' := by
        rintro _ _ ⟨⟨u, v⟩, rfl⟩ ⟨⟨c, d⟩, rfl⟩
        exact ⟨(u + c, v + d + u ^ 2 ^ (a + 1) * c), (suzukiSElt_mul hK u v c d).symm⟩
      one_mem' := ⟨(0, 0), suzukiSElt_zero_zero hK⟩
      inv_mem' := by
        rintro _ ⟨⟨u, v⟩, rfl⟩
        exact ⟨(u, v + u ^ (2 ^ (a + 1) + 1)), (suzukiSElt_inv hK u v).symm⟩ }
  refine Set.Subset.antisymm ?_ Subgroup.subset_closure
  exact (Subgroup.closure_le H).2 subset_rfl

theorem coe_suzukiZ0 [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiZ0 a K : Set (suzukiGroup a K)) = Set.range fun v : K => suzukiSElt a K 0 v := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  let H : Subgroup (suzukiGroup a K) :=
    { carrier := Set.range fun v : K => suzukiSElt a K 0 v
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨d, rfl⟩
        refine ⟨v + d, ?_⟩
        rw [suzukiSElt_mul hK]
        simp
      one_mem' := ⟨0, suzukiSElt_zero_zero hK⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        rw [suzukiSElt_inv hK]
        simp }
  refine Set.Subset.antisymm ?_ Subgroup.subset_closure
  exact (Subgroup.closure_le H).2 subset_rfl

theorem suzukiZ0_le_suzukiU : suzukiZ0 a K ≤ suzukiU a K :=
  Subgroup.closure_mono (Set.range_subset_iff.2 fun v => ⟨(0, v), rfl⟩)

theorem mem_suzukiU_iff
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K} :
    g ∈ suzukiU a K ↔ ∃ u v : K, suzukiSElt a K u v = g := by
  rw [← SetLike.mem_coe, coe_suzukiU hK]
  exact ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨u, v, h⟩ => ⟨(u, v), h⟩⟩

theorem mem_suzukiZ0_iff
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K} :
    g ∈ suzukiZ0 a K ↔ ∃ v : K, suzukiSElt a K 0 v = g := by
  rw [← SetLike.mem_coe, coe_suzukiZ0 hK]
  rfl

theorem suzukiSElt_zero_commute
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (d u v : K) :
    suzukiSElt a K 0 d * suzukiSElt a K u v = suzukiSElt a K u v * suzukiSElt a K 0 d := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [suzukiSElt_mul hK, suzukiSElt_mul hK]
  congr 1 <;> simp [zero_pow hθ0, add_comm]

theorem commutatorElement_mem_suzukiZ0
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : suzukiGroup a K} (hx : x ∈ suzukiU a K) (hy : y ∈ suzukiU a K) :
    ⁅x, y⁆ ∈ suzukiZ0 a K := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
  rw [commutatorElement_def, suzukiSElt_inv hK, suzukiSElt_inv hK, suzukiSElt_mul hK,
    suzukiSElt_mul hK, suzukiSElt_mul hK, mem_suzukiZ0_iff hK]
  refine ⟨_, congrArg₂ (suzukiSElt a K) ?_ rfl⟩
  linear_combination (-(u + c)) * h2

theorem suzuki_unipotent_structure
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiU a K : Set (suzukiGroup a K)) =
      Set.range (fun p : K × K => suzukiSElt a K p.1 p.2) ∧
    Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 ∧
    (suzukiZ0 a K : Set (suzukiGroup a K)) = Set.range (fun v : K => suzukiSElt a K 0 v) ∧
    suzukiZ0 a K ≤ suzukiU a K ∧
    (∀ x ∈ suzukiZ0 a K, ∀ y ∈ suzukiZ0 a K, x * y = y * x) ∧
    (∀ z ∈ suzukiZ0 a K, ∀ g ∈ suzukiU a K, z * g = g * z) ∧
    (∃ _ : ((suzukiZ0 a K).subgroupOf (suzukiU a K)).Normal,
      ∀ x y : suzukiU a K ⧸ (suzukiZ0 a K).subgroupOf (suzukiU a K), x * y = y * x) ∧
    Group.IsSolvable (suzukiU a K) ∧ derivedSeries (suzukiU a K) 2 = ⊥ := by
  have hcent : ∀ z ∈ suzukiZ0 a K, ∀ g ∈ suzukiU a K, z * g = g * z := by
    intro z hz g hg
    obtain ⟨d, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    exact suzukiSElt_zero_commute hK d u v
  have hnorm : ((suzukiZ0 a K).subgroupOf (suzukiU a K)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := hcent _ hn _ g.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, ← h, mul_inv_cancel_right]
      exact hn⟩
  have hder1 : derivedSeries (suzukiU a K) 1 ≤ (suzukiZ0 a K).subgroupOf (suzukiU a K) := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact commutatorElement_mem_suzukiZ0 hK x.2 y.2
  have hder2 : derivedSeries (suzukiU a K) 2 = ⊥ := by
    rw [eq_bot_iff, show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ]
    refine (Subgroup.commutator_mono hder1 hder1).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hcent _ hx _ y.2)
  refine ⟨coe_suzukiU hK, ?_, coe_suzukiZ0 hK, suzukiZ0_le_suzukiU,
    fun x hx y hy => hcent x hx y (suzukiZ0_le_suzukiU hy), hcent, ⟨hnorm, fun x y => ?_⟩,
    ⟨⟨2, hder2⟩⟩, hder2⟩
  · rw [← SetLike.coe_sort_coe, coe_suzukiU hK, Nat.card_range_of_injective
      (fun p q h => Prod.ext (suzukiSElt_inj.1 h).1 (suzukiSElt_inj.1 h).2), Nat.card_prod, hK, sq]
  · induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by group
    rw [h]
    exact hder1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

end CFSG.LieType.Ree
