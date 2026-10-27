module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface
public import CFSG.LocalAnalysis.ComponentInitial.EvenPairingCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBound

open CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable {a : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))

include hK in
theorem commutatorElement_suzukiSElt (u v c d : K) :
    ⁅suzukiSElt a K u v, suzukiSElt a K c d⁆ =
      suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * c + c ^ 2 ^ (a + 1) * u) := by
  obtain ⟨h2, hadd, -⟩ := suzuki_frob_data a hK
  rw [commutatorElement_def, suzukiSElt_inv hK, suzukiSElt_inv hK, suzukiSElt_mul hK,
    suzukiSElt_mul hK, suzukiSElt_mul hK]
  refine congrArg₂ (suzukiSElt a K) (by linear_combination (u + c) * h2) ?_
  have e1 : u + c + u = c := by linear_combination u * h2
  rw [e1, hadd, pow_succ, pow_succ]
  linear_combination (v + d + u ^ 2 ^ (a + 1) * u + c ^ 2 ^ (a + 1) * c) * h2

include hK in
theorem suzukiSElt_zero_mul (v d : K) :
    suzukiSElt a K 0 v * suzukiSElt a K 0 d = suzukiSElt a K 0 (v + d) := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [suzukiSElt_mul hK]
  congr 1 <;> simp [zero_pow hθ0]

include hK in
theorem suzukiSElt_eq_mul (u v : K) :
    suzukiSElt a K u v = suzukiSElt a K u 0 * suzukiSElt a K 0 v := by
  rw [suzukiSElt_mul hK]
  congr 1 <;> simp

include hK in
theorem suzukiSElt_add_zero (u c : K) :
    suzukiSElt a K (u + c) 0 =
      suzukiSElt a K u 0 * suzukiSElt a K c 0 *
        (suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * c))⁻¹ := by
  rw [suzukiSElt_mul hK, eq_mul_inv_iff_mul_eq, suzukiSElt_mul hK]
  congr 1 <;> simp

include hK in
theorem suzukiDElt_inv_conj (l : Kˣ) (u v : K) :
    (suzukiDElt a K l)⁻¹ * suzukiSElt a K u v * ((suzukiDElt a K l)⁻¹)⁻¹ =
      suzukiSElt a K ((l : K) * u) ((l : K) ^ (2 ^ (a + 1) + 1) * v) := by
  rw [inv_inv, suzukiDElt_conj hK]

include hK in
theorem exists_pow_theta_ne (ha : 1 ≤ a) : ∃ c : K, c ^ 2 ^ (a + 1) ≠ c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : 2 ≤ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have : 4 ≤ 2 ^ (2 * a + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y, hy⟩ := exists_ne (1 : Kˣ)
  obtain ⟨s, hs⟩ := hbij.2 y
  refine ⟨s, fun h => hy ?_⟩
  rw [← hs]
  have e : ((2 ^ (a + 1) - 1 : ℕ) : ℤ) = (2 ^ (a + 1) - 1 : ℤ) := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  change s ^ (2 ^ (a + 1) - 1 : ℤ) = 1
  rw [← e, zpow_natCast]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h' : (s : K) ^ (2 ^ (a + 1) - 1 : ℕ) * s = 1 * s := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul]
    exact h
  exact mul_right_cancel₀ s.ne_zero h'

include hK in
theorem suzukiSElt_zero_mem_commutator (ha : 1 ≤ a) (v : K) :
    suzukiSElt a K 0 v ∈ ⁅suzukiU a K, suzukiU a K⁆ := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  obtain ⟨c, hc⟩ := exists_pow_theta_ne hK ha
  set w₀ : K := (1 : K) ^ 2 ^ (a + 1) * c + c ^ 2 ^ (a + 1) * 1 with hw₀def
  have hw₀ : w₀ ≠ 0 := by
    intro h0
    apply hc
    rw [hw₀def, one_pow, one_mul, mul_one] at h0
    linear_combination h0 - c * h2
  have hmem₀ : suzukiSElt a K 0 w₀ ∈ ⁅suzukiU a K, suzukiU a K⁆ := by
    rw [← commutatorElement_suzukiSElt hK 1 0 c 0]
    exact Subgroup.commutator_mem_commutator (suzukiSElt_mem_suzukiU a K _ _)
      (suzukiSElt_mem_suzukiU a K _ _)
  by_cases hv : v = 0
  · rw [hv, suzukiSElt_zero_zero hK]
    exact one_mem _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
  obtain ⟨l, hl⟩ := hbij.2 (Units.mk0 (v / w₀) (div_ne_zero hv hw₀))
  have hlK : (l : K) ^ (2 ^ (a + 1) + 1) * w₀ = v := by
    have e : ((2 ^ (a + 1) + 1 : ℕ) : ℤ) = (2 ^ (a + 1) + 1 : ℤ) := by push_cast; ring
    have hl' : l ^ (2 ^ (a + 1) + 1 : ℕ) = Units.mk0 (v / w₀) (div_ne_zero hv hw₀) := by
      rw [← zpow_natCast, e]
      exact hl
    have := congrArg Units.val hl'
    rw [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    rw [this, div_mul_cancel₀ v hw₀]
  have hconj : (suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 w₀ * ((suzukiDElt a K l)⁻¹)⁻¹ =
      suzukiSElt a K 0 v := by
    rw [suzukiDElt_inv_conj hK, mul_zero, hlK]
  have hnorm : ∀ x ∈ suzukiU a K, (suzukiDElt a K l)⁻¹ * x * ((suzukiDElt a K l)⁻¹)⁻¹ ∈
      suzukiU a K := fun x hx => by
    have ht : (suzukiDElt a K l)⁻¹ ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
      inv_mem (suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K l))
    exact (Subgroup.mem_normalizer_iff.mp ht x).mp hx
  rw [← hconj]
  exact EvenCoverPairing.conj_mem_commutator hnorm hnorm hmem₀

include hK in
theorem commutator_suzukiU_le : ⁅suzukiU a K, suzukiU a K⁆ ≤ suzukiZ0 a K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact commutatorElement_mem_suzukiZ0 hK hx hy

include hK in
theorem mem_commutator_suzukiU_iff (ha : 1 ≤ a) {g : suzukiGroup a K} :
    g ∈ ⁅suzukiU a K, suzukiU a K⁆ ↔ ∃ w : K, suzukiSElt a K 0 w = g := by
  constructor
  · intro hg
    exact (mem_suzukiZ0_iff hK).mp (commutator_suzukiU_le hK hg)
  · rintro ⟨w, rfl⟩
    exact suzukiSElt_zero_mem_commutator hK ha w

theorem mem_commutator_subtype_iff {G : Type*} [Group G] {Q : Subgroup G} {x : Q} :
    x ∈ _root_.commutator Q ↔ (x : G) ∈ ⁅Q, Q⁆ := by
  rw [← Subgroup.map_subtype_commutator]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

include hK in
theorem suzukiSElt_sq (u v : K) :
    suzukiSElt a K u v * suzukiSElt a K u v = suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  rw [suzukiSElt_mul hK]
  refine congrArg₂ (suzukiSElt a K) (by linear_combination u * h2) ?_
  rw [pow_succ]
  linear_combination v * h2

include hK in
theorem nilpotencyClass_suzukiU_le : Group.nilpotencyClass (suzukiU a K) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (suzukiU a K) := (suzukiU_isPGroup_index hK).1.isNilpotent
  refine (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le).mp ?_
  refine Subgroup.lowerCentralSeries_succ_eq_bot _ ?_
  rw [Subgroup.top_lowerCentralSeries_one]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx' := commutator_suzukiU_le hK (mem_commutator_subtype_iff.mp hx)
  obtain ⟨d, hd⟩ := (mem_suzukiZ0_iff hK).mp hx'
  obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).mp y.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hd, ← huv]
  exact (suzukiSElt_zero_commute hK d u v).symm

include hK in
theorem isElemAbelian_commutator_suzukiU (ha : 1 ≤ a) :
    CFSG.Assembly.IsElemAbelian 2 ⁅suzukiU a K, suzukiU a K⁆ := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨w, hw⟩ := (mem_commutator_suzukiU_iff hK ha).mp x.2
    obtain ⟨w', hw'⟩ := (mem_commutator_suzukiU_iff hK ha).mp y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hw, ← hw', suzukiSElt_zero_mul hK,
      suzukiSElt_zero_mul hK, add_comm]
  · obtain ⟨w, rfl⟩ := (mem_commutator_suzukiU_iff hK ha).mp hx
    rw [pow_two, suzukiSElt_zero_mul hK, ← suzukiSElt_zero_zero hK]
    exact congrArg (suzukiSElt a K 0) (by linear_combination w * h2)

include hK in
theorem isElemAbelian_abelianization_suzukiU (ha : 1 ≤ a) :
    CFSG.Assembly.IsElemAbelian 2 (⊤ : Subgroup (Abelianization (suzukiU a K))) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, Abelianization.of y = x := QuotientGroup.mk_surjective x
  obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).mp y.2
  rw [← map_pow, ← MonoidHom.mem_ker, Abelianization.ker_of, mem_commutator_subtype_iff,
    Subgroup.coe_pow, ← huv, pow_two, suzukiSElt_sq hK]
  exact suzukiSElt_zero_mem_commutator hK ha _

@[expose] def sU (u : K) : suzukiU a K :=
  ⟨suzukiSElt a K u 0, suzukiSElt_mem_suzukiU a K u 0⟩

include hK in
theorem of_sU_add (ha : 1 ≤ a) (u c : K) :
    Abelianization.of (sU (a := a) (u + c)) =
      Abelianization.of (sU (a := a) u) * Abelianization.of (sU (a := a) c) := by
  rw [← map_mul, EvenCoverPairing.abelianization_of_eq_iff]
  change (suzukiSElt a K (u + c) 0)⁻¹ * (suzukiSElt a K u 0 * suzukiSElt a K c 0) ∈ _
  rw [suzukiSElt_add_zero hK, show ∀ x y z : suzukiGroup a K, (x * y * z⁻¹)⁻¹ * (x * y) = z by
    intro x y z; group]
  exact suzukiSElt_zero_mem_commutator hK ha _

include hK in
theorem exists_of_eq_of_sU (ha : 1 ≤ a) (x : Abelianization (suzukiU a K)) :
    ∃ u : K, Abelianization.of (sU (a := a) u) = x := by
  obtain ⟨y, rfl⟩ : ∃ y, Abelianization.of y = x := QuotientGroup.mk_surjective x
  obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff hK).mp y.2
  refine ⟨u, (EvenCoverPairing.abelianization_of_eq_iff _ _).mpr ?_⟩
  change (suzukiSElt a K u 0)⁻¹ * (y : suzukiGroup a K) ∈ _
  rw [← huv, suzukiSElt_eq_mul hK u v, inv_mul_cancel_left]
  exact suzukiSElt_zero_mem_commutator hK ha _

include hK in
theorem conj_sU (l : Kˣ) (u : K) :
    (suzukiDElt a K l)⁻¹ * suzukiSElt a K u 0 * ((suzukiDElt a K l)⁻¹)⁻¹ =
      suzukiSElt a K ((l : K) * u) 0 := by
  rw [suzukiDElt_inv_conj hK, mul_zero]

include hK in
theorem suzukiU_pairing_eq_zero (ha : 1 ≤ a)
    (f : Abelianization (suzukiU a K) → Abelianization (suzukiU a K) → ZMod 2)
    (hf₁ : ∀ x x' y, f (x * x') y = f x y + f x' y)
    (hf₂ : ∀ x y y', f x (y * y') = f x y + f x y')
    (hfT : ∀ t ∈ suzukiT a K, ∀ (b c : suzukiGroup a K) (hb : b ∈ suzukiU a K)
      (hc : c ∈ suzukiU a K) (htb : t * b * t⁻¹ ∈ suzukiU a K) (htc : t * c * t⁻¹ ∈ suzukiU a K),
      f (Abelianization.of ⟨t * b * t⁻¹, htb⟩) (Abelianization.of ⟨t * c * t⁻¹, htc⟩) =
        f (Abelianization.of ⟨b, hb⟩) (Abelianization.of ⟨c, hc⟩)) : f = 0 := by
  obtain ⟨hchar, -⟩ := suzuki_frobenius_exponents a K hK
  have hK4 : 4 < Nat.card K := by
    rw [hK]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set F : K → K → ZMod 2 := fun u c =>
    f (Abelianization.of (sU (a := a) u)) (Abelianization.of (sU (a := a) c)) with hF
  have hF0 := LinearCover.binary_scalar_invariant_biadditive_map_zero hK4 F
    (fun u u' c => by
      change f (Abelianization.of (sU (u + u'))) _ = f (Abelianization.of (sU u)) _ +
        f (Abelianization.of (sU u')) _
      rw [of_sU_add hK ha, hf₁])
    (fun u c c' => by
      change f _ (Abelianization.of (sU (c + c'))) = f _ (Abelianization.of (sU c)) +
        f _ (Abelianization.of (sU c'))
      rw [of_sU_add hK ha, hf₂])
    (fun l hl u c => by
      simp only [hF]
      have hT : (suzukiDElt a K (Units.mk0 l hl))⁻¹ ∈ suzukiT a K :=
        inv_mem (suzukiDElt_mem_suzukiT a K _)
      have h := hfT _ hT (suzukiSElt a K u 0) (suzukiSElt a K c 0)
        (suzukiSElt_mem_suzukiU a K _ _) (suzukiSElt_mem_suzukiU a K _ _)
        (by rw [conj_sU hK]; exact suzukiSElt_mem_suzukiU a K _ _)
        (by rw [conj_sU hK]; exact suzukiSElt_mem_suzukiU a K _ _)
      have e1 : (⟨(suzukiDElt a K (Units.mk0 l hl))⁻¹ * suzukiSElt a K u 0 *
          ((suzukiDElt a K (Units.mk0 l hl))⁻¹)⁻¹, by
            rw [conj_sU hK]; exact suzukiSElt_mem_suzukiU a K _ _⟩ : suzukiU a K) =
          sU (l * u) := Subtype.ext (conj_sU hK _ _)
      have e2 : (⟨(suzukiDElt a K (Units.mk0 l hl))⁻¹ * suzukiSElt a K c 0 *
          ((suzukiDElt a K (Units.mk0 l hl))⁻¹)⁻¹, by
            rw [conj_sU hK]; exact suzukiSElt_mem_suzukiU a K _ _⟩ : suzukiU a K) =
          sU (l * c) := Subtype.ext (conj_sU hK _ _)
      rw [e1, e2] at h
      exact h)
  funext x y
  obtain ⟨u, rfl⟩ := exists_of_eq_of_sU hK ha x
  obtain ⟨c, rfl⟩ := exists_of_eq_of_sU hK ha y
  exact hF0 u c

end CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBound
