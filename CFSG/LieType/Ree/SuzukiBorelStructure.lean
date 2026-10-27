module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure
public import CFSG.LieType.Ree.SuzukiTorusIdentities

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiDElt_mul (l m : Kˣ) :
    suzukiDElt a K l * suzukiDElt a K m = suzukiDElt a K (l * m) :=
  suzukiSElt_ext (suzukiD_mul a l m)

theorem suzukiDElt_one : suzukiDElt a K 1 = 1 :=
  suzukiSElt_ext (suzukiD_one a)

theorem suzukiDElt_inv
    (l : Kˣ) : (suzukiDElt a K l)⁻¹ = suzukiDElt a K l⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, suzukiDElt_mul, mul_inv_cancel, suzukiDElt_one]

theorem suzukiDElt_inj
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l m : Kˣ} :
    suzukiDElt a K l = suzukiDElt a K m ↔ l = m := by
  refine ⟨fun h => (suzuki_torus_identities a hK).2.2.1 l m ?_, fun h => h ▸ rfl⟩
  have h' := congrArg (fun g : suzukiGroup a K =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  simpa only [coe_suzukiDElt] using h'

theorem suzukiDElt_conj
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) (u v : K) :
    (suzukiDElt a K l)⁻¹ * suzukiSElt a K u v * suzukiDElt a K l =
      suzukiSElt a K ((l : K) * u) ((l : K) ^ (2 ^ (a + 1) + 1) * v) := by
  refine suzukiSElt_ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul, Units.val_mul,
    Matrix.coe_units_inv, coe_suzukiDElt, coe_suzukiSElt, coe_suzukiSElt]
  exact (suzuki_torus_identities a hK).2.2.2.1 l u v

theorem suzukiDElt_conj'
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) (u v : K) :
    suzukiDElt a K l * suzukiSElt a K u v * (suzukiDElt a K l)⁻¹ =
      suzukiSElt a K ((l⁻¹ : Kˣ) * u) (((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * v) := by
  rw [← suzukiDElt_conj hK, suzukiDElt_inv l⁻¹, inv_inv, suzukiDElt_inv l]

theorem coe_suzukiT
    : (suzukiT a K : Set (suzukiGroup a K)) = Set.range (suzukiDElt a K) := by
  let H : Subgroup (suzukiGroup a K) :=
    { carrier := Set.range (suzukiDElt a K)
      mul_mem' := by
        rintro _ _ ⟨l, rfl⟩ ⟨m, rfl⟩
        exact ⟨l * m, (suzukiDElt_mul l m).symm⟩
      one_mem' := ⟨1, suzukiDElt_one⟩
      inv_mem' := by
        rintro _ ⟨l, rfl⟩
        exact ⟨l⁻¹, (suzukiDElt_inv l).symm⟩ }
  exact Set.Subset.antisymm ((Subgroup.closure_le H).2 subset_rfl) Subgroup.subset_closure

theorem mem_suzukiT_iff {g : suzukiGroup a K} :
    g ∈ suzukiT a K ↔ ∃ l : Kˣ, suzukiDElt a K l = g := by
  rw [← SetLike.mem_coe, coe_suzukiT]
  rfl

theorem suzukiT_le_normalizer
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiT a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
  intro g hg
  obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hg
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hh
    rw [suzukiDElt_conj' hK]
    exact suzukiSElt_mem_suzukiU a K _ _
  · obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).1 hh
    have : h = (suzukiDElt a K l)⁻¹ * suzukiSElt a K u v * suzukiDElt a K l := by
      rw [huv]
      group
    rw [this, suzukiDElt_conj hK]
    exact suzukiSElt_mem_suzukiU a K _ _

theorem suzukiU_inf_suzukiT
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiU a K ⊓ suzukiT a K = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hU, hT⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hU
  obtain ⟨l, hl⟩ := mem_suzukiT_iff.1 hT
  have h' := congrArg (fun g : suzukiGroup a K =>
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hl
  simp only [coe_suzukiDElt, coe_suzukiSElt, suzukiD_eq] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp [suzukiS] at h0 h1
  have hl1 : l = 1 := by
    apply Units.ext
    rw [h1, mul_one] at h0
    exact h0
  rw [← hl, hl1, suzukiDElt_one]
  exact Subgroup.one_mem _

theorem suzuki_borel_structure
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiT a K : Set (suzukiGroup a K)) = Set.range (suzukiDElt a K) ∧
    (∀ x ∈ suzukiT a K, ∀ y ∈ suzukiT a K, x * y = y * x) ∧
    Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 ∧
    suzukiT a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) ∧
    suzukiU a K ⊓ suzukiT a K = ⊥ ∧
    (suzukiB a K : Set (suzukiGroup a K)) =
      (suzukiU a K : Set (suzukiGroup a K)) * (suzukiT a K : Set (suzukiGroup a K)) ∧
    (∀ g ∈ suzukiB a K, ∃! p : (K × K) × Kˣ,
      g = suzukiSElt a K p.1.1 p.1.2 * suzukiDElt a K p.2) ∧
    Nat.card (suzukiB a K) = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  have hBUT : (suzukiB a K : Set (suzukiGroup a K)) =
      (suzukiU a K : Set (suzukiGroup a K)) * (suzukiT a K : Set (suzukiGroup a K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (suzukiT_le_normalizer hK)
  have hinj : Function.Injective fun p : (K × K) × Kˣ =>
      suzukiSElt a K p.1.1 p.1.2 * suzukiDElt a K p.2 := by
    rintro ⟨⟨u, v⟩, l⟩ ⟨⟨u', v'⟩, l'⟩ h
    simp only at h
    have hmem : (suzukiSElt a K u' v')⁻¹ * suzukiSElt a K u v ∈ suzukiU a K ⊓ suzukiT a K := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (suzukiSElt_mem_suzukiU a K _ _))
        (suzukiSElt_mem_suzukiU a K _ _), ?_⟩
      have : (suzukiSElt a K u' v')⁻¹ * suzukiSElt a K u v =
          suzukiDElt a K l' * (suzukiDElt a K l)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]
      exact mul_mem (suzukiDElt_mem_suzukiT a K _) (inv_mem (suzukiDElt_mem_suzukiT a K _))
    rw [suzukiU_inf_suzukiT hK, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    obtain ⟨rfl, rfl⟩ := suzukiSElt_inj.1 hmem.symm
    rw [mul_right_inj, suzukiDElt_inj hK] at h
    rw [h]
  have hrange : (suzukiB a K : Set (suzukiGroup a K)) =
      Set.range fun p : (K × K) × Kˣ => suzukiSElt a K p.1.1 p.1.2 * suzukiDElt a K p.2 := by
    rw [hBUT, coe_suzukiU hK, coe_suzukiT]
    ext g
    simp only [Set.mem_mul, Set.mem_range, Prod.exists]
    constructor
    · rintro ⟨_, ⟨u, v, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
      exact ⟨u, v, l, rfl⟩
    · rintro ⟨u, v, l, rfl⟩
      exact ⟨_, ⟨u, v, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
  refine ⟨coe_suzukiT, fun x hx y hy => ?_, ?_, suzukiT_le_normalizer hK, suzukiU_inf_suzukiT hK,
    hBUT, fun g hg => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hx
    obtain ⟨m, rfl⟩ := mem_suzukiT_iff.1 hy
    rw [suzukiDElt_mul, suzukiDElt_mul, mul_comm]
  · rw [← SetLike.coe_sort_coe, coe_suzukiT, Nat.card_range_of_injective
      (fun l m h => (suzukiDElt_inj hK).1 h), Nat.card_units, hK]
  · rw [← SetLike.mem_coe, hrange] at hg
    obtain ⟨p, rfl⟩ := hg
    exact ⟨p, rfl, fun q hq => hinj hq.symm⟩
  · rw [← SetLike.coe_sort_coe, hrange, Nat.card_range_of_injective hinj, Nat.card_prod,
      Nat.card_prod, Nat.card_units, hK, sq]

theorem commutatorElement_mem_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : suzukiGroup a K} (hx : x ∈ suzukiB a K) (hy : y ∈ suzukiB a K) :
    ⁅x, y⁆ ∈ suzukiU a K := by
  have hBUT := (suzuki_borel_structure hK).2.2.2.2.2.1
  have hN := suzukiT_le_normalizer hK
  rw [← SetLike.mem_coe, hBUT] at hx hy
  obtain ⟨s, hs, t, ht, rfl⟩ := hx
  obtain ⟨s', hs', t', ht', rfl⟩ := hy
  have hcomm : t * t' = t' * t := (suzuki_borel_structure hK).2.1 t ht t' ht'
  have hid : ⁅s * t, s' * t'⁆ =
      s * (t * s' * t⁻¹) * (t * t' * t⁻¹ * t'⁻¹) * (t' * s⁻¹ * t'⁻¹) * s'⁻¹ := by
    rw [commutatorElement_def]
    group
  have h1 : t * t' * t⁻¹ * t'⁻¹ = 1 := by
    rw [hcomm]
    group
  rw [hid, h1, mul_one]
  refine mul_mem (mul_mem (mul_mem hs ?_) ?_) (inv_mem hs')
  · exact (Subgroup.mem_normalizer_iff.1 (hN ht) s').1 hs'
  · exact (Subgroup.mem_normalizer_iff.1 (hN ht') s⁻¹).1 (inv_mem hs)

theorem suzuki_borel_solvable
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Group.IsSolvable (suzukiB a K) ∧ derivedSeries (suzukiB a K) 3 = ⊥ := by
  obtain ⟨-, -, -, -, hZ0ab, -⟩ := suzuki_unipotent_structure hK
  have h1 : derivedSeries (suzukiB a K) 1 ≤ (suzukiU a K).subgroupOf (suzukiB a K) := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact commutatorElement_mem_suzukiU hK x.2 y.2
  have h2 : derivedSeries (suzukiB a K) 2 ≤ (suzukiZ0 a K).subgroupOf (suzukiB a K) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy ⊢
    exact commutatorElement_mem_suzukiZ0 hK hx hy
  have h3 : derivedSeries (suzukiB a K) 3 = ⊥ := by
    rw [eq_bot_iff, show (3 : ℕ) = 2 + 1 from rfl, derivedSeries_succ]
    refine (Subgroup.commutator_mono h2 h2).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hZ0ab _ hx _ hy)
  exact ⟨⟨⟨3, h3⟩⟩, h3⟩

end CFSG.LieType.Ree
