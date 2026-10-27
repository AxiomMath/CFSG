module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerActionBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI.SuzukiModel

variable {a : ℕ} {K : Type} [Field K] [Finite K]

@[expose] def suzukiCenterHom (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Multiplicative K →* suzukiGroup a K where
  toFun v := suzukiSElt a K 0 (Multiplicative.toAdd v)
  map_one' := suzukiSElt_zero_zero hK
  map_mul' v w := by
    rw [suzukiSElt_mul hK]
    congr 1 <;> simp

theorem suzukiCenterHom_injective
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (suzukiCenterHom hK) := fun _ _ h =>
  Multiplicative.toAdd.injective (suzukiSElt_inj.1 h).2

theorem mem_range_suzukiCenterHom
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : suzukiGroup a K} :
    g ∈ (suzukiCenterHom hK).range ↔ ∃ v : K, suzukiSElt a K 0 v = g :=
  ⟨fun ⟨v, hv⟩ => ⟨Multiplicative.toAdd v, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem involutionSubgroup_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    involutionSubgroup (suzukiU a K) = (suzukiCenterHom hK).range := by
  refine involutionSubgroup_eq fun x => ?_
  rw [mem_range_suzukiCenterHom]
  constructor
  · rintro ⟨hx, h2⟩
    obtain ⟨v, hv, rfl⟩ :=
      (mem_suzukiB_and_orderOf_eq_two_iff hK).1 ⟨suzukiU_le_suzukiB a K hx, h2⟩
    refine ⟨⟨v, rfl⟩, ?_⟩
    rw [← suzukiSElt_zero_zero hK, Ne, suzukiSElt_inj]
    exact fun h => hv h.2
  · rintro ⟨⟨v, rfl⟩, h1⟩
    have hv : v ≠ 0 := by
      rintro rfl
      exact h1 (suzukiSElt_zero_zero hK)
    exact ⟨suzukiSElt_mem_suzukiU a K 0 v, orderOf_suzukiSElt_zero hK hv⟩

theorem suzukiB_le_rootScalarSubgroup
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ rootScalarSubgroup (suzukiCenterHom hK) := by
  refine sup_le (fun u hu => ?_) (fun t ht => ?_)
  · obtain ⟨x, y, rfl⟩ := (mem_suzukiU_iff hK).1 hu
    refine ⟨1, fun b => ?_⟩
    change suzukiSElt a K x y * suzukiSElt a K 0 b * (suzukiSElt a K x y)⁻¹ =
      suzukiSElt a K 0 ((1 : Kˣ) * b)
    rw [← suzukiSElt_zero_commute hK b x y, mul_inv_cancel_right, Units.val_one, one_mul]
  · obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
    refine ⟨l⁻¹ ^ (2 ^ (a + 1) + 1), fun b => ?_⟩
    change suzukiDElt a K l * suzukiSElt a K 0 b * (suzukiDElt a K l)⁻¹ =
      suzukiSElt a K 0 ((l⁻¹ ^ (2 ^ (a + 1) + 1) : Kˣ) * b)
    rw [suzukiDElt_conj' hK, mul_zero, Units.val_pow_eq_pow_val]

theorem normalizer_range_suzukiCenterHom_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.normalizer ((suzukiCenterHom hK).range : Set (suzukiGroup a K)) ≤ suzukiB a K := by
  have h := suzukiPointAction_suzukiGroup hK
  let ρ := MulAction.toPermHom (suzukiGroup a K) (suzukiOmegaSub hK)
  have hZU : (suzukiCenterHom hK).range ≤ suzukiU a K := by
    rintro _ ⟨v, rfl⟩
    exact suzukiSElt_mem_suzukiU a K 0 _
  have hne : (suzukiCenterHom hK).range ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, Multiplicative.ofAdd 1, rfl⟩, fun h1 => ?_⟩
    have h2 := suzukiCenterHom_injective hK (congrArg Subtype.val h1 |>.trans (map_one _).symm)
    exact one_ne_zero (Multiplicative.ofAdd.injective h2)
  intro g hg
  rw [← (suzuki_ovoid_stabilizer hK).2, MulAction.mem_stabilizer_iff]
  refine fixes_of_mem_normalizer ρ (fun x hx => h.le_stabilizer_left (hZU hx))
    (fun x hx y hxy hyα => eq_one_of_regular ρ h.regular (hZU hx) hxy hyα) hne hg

omit [Finite K] in
theorem coprime_card_units_suzuki (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (Nat.card Kˣ).Coprime (2 ^ (a + 1) + 1) := by
  rw [Nat.card_units, hK, ← Nat.isCoprime_iff_coprime]
  refine ⟨-2, 2 ^ (a + 1) - 1, ?_⟩
  push_cast [Nat.one_le_two_pow]
  ring

theorem exists_conj_suzukiCenterHom
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : Kˣ) :
    ∃ g : suzukiGroup a K, ∀ b : K,
      g * suzukiCenterHom hK (Multiplicative.ofAdd b) * g⁻¹ =
        suzukiCenterHom hK (Multiplicative.ofAdd (c * b)) := by
  obtain ⟨m, hm⟩ := (Nat.Coprime.pow_left_bijective (coprime_card_units_suzuki hK)).2 c
  have hm' : m ^ (2 ^ (a + 1) + 1) = c := hm
  refine ⟨suzukiDElt a K m⁻¹, fun b => ?_⟩
  change suzukiDElt a K m⁻¹ * suzukiSElt a K 0 b * (suzukiDElt a K m⁻¹)⁻¹ =
    suzukiSElt a K 0 (c * b)
  rw [suzukiDElt_conj' hK, mul_zero, inv_inv, ← hm', Units.val_pow_eq_pow_val]

theorem isSingerAction_suzukiGroup (hK : Nat.card K = 2 ^ (2 * a + 1))
    (Q : Sylow 2 (suzukiGroup a K)) :
    IsSingerAction (involutionSubgroup (Q : Subgroup (suzukiGroup a K))) (2 ^ (2 * a + 1)) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_eq_suzukiU hK
  rw [← hK]
  exact isSingerAction_sylow_of_range (suzukiCenterHom hK) (suzukiCenterHom_injective hK) Q₀
    (by rw [hQ₀]; exact involutionSubgroup_suzukiU hK)
    ((normalizer_range_suzukiCenterHom_le hK).trans (suzukiB_le_rootScalarSubgroup hK))
    (exists_conj_suzukiCenterHom hK) Q

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
