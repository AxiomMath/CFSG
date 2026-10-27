module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

variable {k : Type} [Field k] [Finite k]

theorem card_sl2_of_card_four (hk : Nat.card k = 4) :
    Nat.card (SpecialLinearGroup (Fin 2) k) = 60 := by
  have : Fintype k := Fintype.ofFinite k
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hk]
  norm_num

theorem charP_two_of_card_four (hk : Nat.card k = 4) : CharP k 2 := by
  have : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [← Nat.card_eq_fintype_card, hk]; rfl)

omit [Finite k] in
theorem center_sl2_eq_bot_of_charP_two [CharP k 2] :
    center (SpecialLinearGroup (Fin 2) k) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := CharTwo.sq_inj.1 (by rw [hr, one_pow])
  refine mem_bot.2 (Subtype.ext ?_)
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem isPerfect_sl2_of_card_four (hk : Nat.card k = 4) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) k) := by
  have : Fintype k := Fintype.ofFinite k
  exact LinearGroups.special_linear_dimension_two_perfect
    ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk]⟩

theorem isCyclic_sylow_of_card_sixty {H : Type*} [Group H] (hH : Nat.card H = 60) {r : ℕ}
    [hr : Fact r.Prime] (hr2 : r ≠ 2) (S : Sylow r H) : IsCyclic S := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 S.isPGroup'
  have hdvd : r ^ n ∣ 60 := hn ▸ hH ▸ Subgroup.card_subgroup_dvd_card (S : Subgroup H)
  have hn1 : n ≤ 1 := by
    by_contra hn2
    have h2 : r ^ 2 ∣ 60 := (pow_dvd_pow r (by omega)).trans hdvd
    have hr7 : r ≤ 7 := by
      have := Nat.le_of_dvd (by norm_num) h2
      nlinarith
    have hrp := hr.out
    interval_cases r <;> revert hr2 h2 hrp <;> decide
  interval_cases n
  · rw [pow_zero] at hn
    have : Subsingleton S := (Nat.card_eq_one_iff_unique.1 hn).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hn
    exact isCyclic_of_prime_card hn

theorem ker_eq_bot_of_sl2_four (hk : Nat.card k = 4) {C : Type*} [Group C] [Finite C]
    [Group.IsPerfect C] (ρ : C →* SpecialLinearGroup (Fin 2) k) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center C) (hodd : Odd (Nat.card ρ.ker)) : ρ.ker = ⊥ := by
  have : CharP k 2 := charP_two_of_card_four hk
  have hZ : ρ.ker = center C := by
    refine le_antisymm hker fun z hz => ?_
    have hzc : ρ z ∈ center (SpecialLinearGroup (Fin 2) k) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨c, rfl⟩ := hρ g
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz c]
    rw [center_sl2_eq_bot_of_charP_two, mem_bot] at hzc
    exact hzc
  refine GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes
    Group.IsPerfect.commutator_eq_top ρ.ker hZ hodd fun r _ _ hr2 S => ?_
  have hcard : Nat.card (C ⧸ ρ.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv,
      card_sl2_of_card_four hk]
  exact isCyclic_sylow_of_card_sixty hcard hr2 S

theorem commutator_inf_ker_eq_bot_of_card_four (hk : Nat.card k = 4) {X : Type*} [Group X]
    [Finite X] (π : X →* SpecialLinearGroup (Fin 2) k) {Y : Subgroup X} (hY : Y.map π = ⊤)
    (hYk : Y ⊓ π.ker ≤ center X) (hodd : Odd (Nat.card (center X))) :
    ⁅Y, Y⁆ ⊓ π.ker = ⊥ := by
  have := isPerfect_sl2_of_card_four hk
  set C : Subgroup X := ⁅Y, Y⁆ with hCdef
  have hCY : C ≤ Y := commutator_le_self Y
  have hC : C.map π = ⊤ := by
    rw [map_commutator, hY]
    exact Group.IsPerfect.commutator_eq_top
  have hdec : ∀ y ∈ Y, ∃ c ∈ C, c⁻¹ * y ∈ Y ⊓ π.ker := by
    intro y hy
    obtain ⟨c, hc, hcy⟩ : π y ∈ C.map π := hC ▸ mem_top _
    refine ⟨c, hc, mem_inf.2 ⟨mul_mem (inv_mem (hCY hc)) hy, ?_⟩⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
  have hperf : ⁅C, C⁆ = C := by
    refine le_antisymm (commutator_le_self C) (commutator_le.2 fun a ha b hb => ?_)
    obtain ⟨c, hc, hz⟩ := hdec a ha
    obtain ⟨d, hd, hw⟩ := hdec b hb
    have e : ⁅a, b⁆ = ⁅c, d⁆ := by
      have ha' : a = c * (c⁻¹ * a) := by group
      have hb' : b = d * (d⁻¹ * b) := by group
      rw [ha', hb', TorusLift.commutatorElement_mul_central_left (hYk hz),
        TorusLift.commutatorElement_mul_central_right (hYk hw)]
    rw [e]
    exact commutator_mem_commutator hc hd
  have : Group.IsPerfect C := Subgroup.isPerfect_iff.2 hperf
  let ρ : C →* SpecialLinearGroup (Fin 2) k := π.comp C.subtype
  have hρ : Function.Surjective ρ := by
    intro g
    obtain ⟨c, hc, rfl⟩ : g ∈ C.map π := hC ▸ mem_top _
    exact ⟨⟨c, hc⟩, rfl⟩
  have hρX : ∀ c : C, c ∈ ρ.ker → (c : X) ∈ center X := fun c hc =>
    hYk (mem_inf.2 ⟨hCY c.2, hc⟩)
  have hρker : ρ.ker ≤ Subgroup.center C := by
    intro c hc
    rw [mem_center_iff]
    intro d
    exact Subtype.ext (mem_center_iff.1 (hρX c hc) d)
  have hρodd : Odd (Nat.card ρ.ker) := by
    have hle : ρ.ker.map C.subtype ≤ center X := by
      rintro _ ⟨c, hc, rfl⟩
      exact hρX c hc
    rw [← card_map_of_injective C.subtype_injective]
    exact Odd.of_dvd_nat hodd (card_dvd_of_le hle)
  have hbot := ker_eq_bot_of_sl2_four hk ρ hρ hρker hρodd
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxC, hxk⟩ := mem_inf.1 hx
  have : (⟨x, hxC⟩ : C) ∈ ρ.ker := hxk
  rw [hbot, mem_bot] at this
  exact mem_bot.2 (congrArg Subtype.val this)

theorem center_eq_bot_of_sl2_four_prod (hk : Nat.card k = 4) {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (hodd : Odd (Nat.card (center X)))
    (ψ : X ⧸ center X ≃* SpecialLinearGroup (Fin 2) k × SpecialLinearGroup (Fin 2) k) :
    center X = ⊥ := by
  have := isPerfect_sl2_of_card_four hk
  set π := ψ.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hπ : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker := ker_comp_mk'_center ψ
  set π₁ := (MonoidHom.fst _ _).comp π
  set π₂ := (MonoidHom.snd _ _).comp π
  have hπ12 : ∀ x : X, π x = (π₁ x, π₂ x) := fun x => rfl
  have hk1 : ∀ x : X, π₁ x = 1 → π₂ x = 1 → x ∈ center X := fun x h1 h2 => by
    rw [← hker, MonoidHom.mem_ker, hπ12, h1, h2, Prod.mk_one_one]
  have hX1 : π₂.ker.map π₁ = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨x, hx⟩ := hπ (a, 1)
    exact ⟨x, MonoidHom.mem_ker.2 (congrArg Prod.snd hx), congrArg Prod.fst hx⟩
  have hX2 : π₁.ker.map π₂ = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    obtain ⟨x, hx⟩ := hπ (1, b)
    exact ⟨x, MonoidHom.mem_ker.2 (congrArg Prod.fst hx), congrArg Prod.snd hx⟩
  have hY1 := commutator_inf_ker_eq_bot_of_card_four hk π₁ hX1 (fun x hx => hk1 x hx.2 hx.1)
    hodd
  have hY2 := commutator_inf_ker_eq_bot_of_card_four hk π₂ hX2 (fun x hx => hk1 x hx.1 hx.2)
    hodd
  have hY2n : (⁅π₁.ker, π₁.ker⁆ : Subgroup X).Normal := inferInstance
  set Y₁ : Subgroup X := ⁅π₂.ker, π₂.ker⁆
  set Y₂ : Subgroup X := ⁅π₁.ker, π₁.ker⁆
  have hY1m : Y₁.map π₁ = ⊤ := by
    rw [map_commutator, hX1]
    exact Group.IsPerfect.commutator_eq_top
  have hY2m : Y₂.map π₂ = ⊤ := by
    rw [map_commutator, hX2]
    exact Group.IsPerfect.commutator_eq_top
  have hY1k : Y₁ ≤ π₂.ker := commutator_le_self _
  have hY2k : Y₂ ≤ π₁.ker := commutator_le_self _
  have hdec : ∀ x : X, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, (y₁ * y₂)⁻¹ * x ∈ center X := by
    intro x
    obtain ⟨y₁, hy₁, e₁⟩ : π₁ x ∈ Y₁.map π₁ := hY1m ▸ mem_top _
    obtain ⟨y₂, hy₂, e₂⟩ : π₂ x ∈ Y₂.map π₂ := hY2m ▸ mem_top _
    refine ⟨y₁, hy₁, y₂, hy₂, hk1 _ ?_ ?_⟩
    · rw [map_mul, map_inv, map_mul, MonoidHom.mem_ker.1 (hY2k hy₂), mul_one, e₁,
        inv_mul_cancel]
    · rw [map_mul, map_inv, map_mul, MonoidHom.mem_ker.1 (hY1k hy₁), one_mul, e₂,
        inv_mul_cancel]
  have htop : (⊤ : Subgroup X) ≤ Y₁ ⊔ Y₂ := by
    rw [← Group.IsPerfect.commutator_eq_top (G := X), _root_.commutator_def]
    refine commutator_le.2 fun a _ b _ => ?_
    obtain ⟨y₁, hy₁, y₂, hy₂, hz⟩ := hdec a
    obtain ⟨y₁', hy₁', y₂', hy₂', hw⟩ := hdec b
    set u := y₁ * y₂
    set v := y₁' * y₂'
    have hu : u ∈ Y₁ ⊔ Y₂ := mul_mem (mem_sup_left hy₁) (mem_sup_right hy₂)
    have hv : v ∈ Y₁ ⊔ Y₂ := mul_mem (mem_sup_left hy₁') (mem_sup_right hy₂')
    have ha : a = u * (u⁻¹ * a) := by group
    have hb : b = v * (v⁻¹ * b) := by group
    rw [ha, hb]
    generalize u⁻¹ * a = z at hz
    generalize v⁻¹ * b = w at hw
    have e : ⁅u * z, v * w⁆ = ⁅u, v⁆ := by
      rw [TorusLift.commutatorElement_mul_central_left hz,
        TorusLift.commutatorElement_mul_central_right hw]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
  refine eq_bot_iff.2 fun z hz => ?_
  have hzk : π z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup_of_normal_right.1 (htop (mem_top z))
  have h1 : π₁ (y₁ * y₂) = 1 := congrArg Prod.fst hzk
  have h2 : π₂ (y₁ * y₂) = 1 := congrArg Prod.snd hzk
  rw [map_mul, MonoidHom.mem_ker.1 (hY2k hy₂), mul_one] at h1
  have hy1 : y₁ = 1 := mem_bot.1 (hY1 ▸ mem_inf.2 ⟨hy₁, h1⟩)
  rw [hy1, one_mul] at h2 ⊢
  exact hY2 ▸ mem_inf.2 ⟨hy₂, h2⟩

end CFSG.LocalAnalysis.EvenBN.Common
