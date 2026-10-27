module

public import CFSG.GH74.Uniqueness.Section15HeringSetup
public import CFSG.GH74.Uniqueness.Section15HeringSolv
public import CFSG.GH74.Uniqueness.Section15HeringCaseA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PermutationRegular
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulAction G F] {m : ℕ}

theorem Hyp.one_lt_card_mulSubgroup [Finite F] (hG : Hyp G F m) :
    1 < Nat.card (mulSubgroup G F) := by
  rw [card_mulSubgroup hG]
  have := hG.two_le
  have : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem CE.solvable_eq_bot [Finite G] [Finite F] (hC : CE G F m) (N : Subgroup G) (hN : N.Normal)
    (hs : Group.IsSolvable N) : N = ⊥ := by
  have := hC.faithful
  by_contra hne
  obtain ⟨E, q, hEn, -, -, -, hEtr, hEst⟩ :=
    CFSG.BenderSuzuki.exists_regular_elementaryAbelian_normal_of_solvable_normal hC.twoTrans N
      hN hne hs
  apply hC.noReg
  refine ⟨E, hEn, fun x y => ?_⟩
  obtain ⟨n, hn⟩ := hEtr.exists_smul_eq x y
  refine ⟨n, hn, fun n' hn' => ?_⟩
  have h1 : n⁻¹ * n' ∈ stabilizer E x := by
    rw [mem_stabilizer_iff, mul_smul]
    change (n⁻¹ : E) • ((n' : G) • x) = x
    rw [hn', ← hn, inv_smul_smul]
  rw [hEst x, mem_bot] at h1
  exact (inv_mul_eq_one.mp h1).symm

theorem CE.not_isSolvable [Finite G] [Finite F] (hC : CE G F m) : ¬ Group.IsSolvable G := by
  intro hsol
  have h1 := hC.solvable_eq_bot ⊤ inferInstance inferInstance
  have h2 : Nat.card (mulSubgroup G F) ≤ 1 := by
    have := Subgroup.card_le_of_le (le_top : mulSubgroup G F ≤ ⊤)
    rwa [h1, Subgroup.card_bot] at this
  have := hC.toHyp.one_lt_card_mulSubgroup
  omega

theorem CE.exists_odd_prime_dvd_card_stab01 [Finite G] [Finite F] (hC : CE G F m) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (stab01 G F) := by
  by_contra hcon
  push Not at hcon
  have h0 : Nat.card (stab01 G F) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨j, hj⟩ : ∃ j, Nat.card (stab01 G F) = 2 ^ j :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd h0 (fun {d} hd hdvd =>
      by_contra fun hne => hcon d hd hne hdvd)⟩
  have hidx : (mulSubgroup G F).index = 2 ^ (m + j) := by
    have h1 := (mulSubgroup G F).card_mul_index
    rw [hC.card_group, hC.card_stabilizer, card_mulSubgroup hC.toHyp, hj] at h1
    have hpos : 0 < 2 ^ m - 1 := by
      have := hC.toHyp.one_lt_card_mulSubgroup
      rw [card_mulSubgroup hC.toHyp] at this
      omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, pow_add]
    ring
  exact hC.not_isSolvable (isSolvable_of_abelian_of_index_eq_two_pow (mulSubgroup G F)
    (fun a ha b hb => mulSubgroup_comm hC.toHyp ha hb) hidx)

theorem CE.normalClosure_eq_top [Finite G] [Finite F] (hC : CE G F m) :
    normalClosure (mulSubgroup G F : Set G) = ⊤ := by
  have := hC.faithful
  by_contra hne
  set X₀ := normalClosure (mulSubgroup G F : Set G) with hX₀
  have hKX : mulSubgroup G F ≤ X₀ := Subgroup.le_normalClosure
  have hX₀n : X₀.Normal := normalClosure_normal
  have hX₀ne : X₀ ≠ ⊥ := by
    intro hb
    have := Subgroup.card_le_of_le hKX
    rw [hb, Subgroup.card_bot] at this
    have := hC.toHyp.one_lt_card_mulSubgroup
    omega
  have hpre := isPretransitive_of_normal hC.twoTrans X₀ hX₀ne
  have hmove : ∃ g ∈ X₀, g • (0 : F) ≠ 0 := by
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq (0 : F) 1
    exact ⟨g, g.2, by rw [show (g : G) • (0 : F) = 1 from hg]; exact one_ne_zero⟩
  have h2 := hC.isMultiplyPretransitive_of_le X₀ hKX hmove
  rcases hC.ih X₀ hne (hC.ofSubgroup X₀ h2 hKX) with hreg | ⟨hm3, ⟨φ⟩⟩
  ·
    obtain ⟨N₀, hN₀n, hN₀reg⟩ := hreg
    have hbij : Function.Bijective (fun n : N₀ => ((n : X₀) : G) • (0 : F)) := by
      constructor
      · intro a b hab
        obtain ⟨n, -, hn⟩ := hN₀reg 0 (((a : X₀) : G) • (0 : F))
        exact (hn a rfl).trans (hn b hab.symm).symm
      · intro y
        obtain ⟨n, hn, -⟩ := hN₀reg 0 y
        exact ⟨n, hn⟩
    have hcard : Nat.card N₀ = 2 ^ m := by
      rw [← hC.card]
      exact Nat.card_congr (Equiv.ofBijective _ hbij)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN₀p : IsPGroup 2 N₀ := IsPGroup.of_card hcard
    have hle : N₀ ≤ CFSG.pCore 2 X₀ := le_sSup ⟨hN₀n, hN₀p⟩
    set M := (CFSG.pCore 2 X₀).map X₀.subtype with hM
    have hMn : M.Normal := inferInstance
    have hMs : Group.IsSolvable M := by
      have := ((CFSG.pCore_isPGroup (p := 2) (G := X₀)).map X₀.subtype).isNilpotent
      infer_instance
    have hMb := hC.solvable_eq_bot M hMn hMs
    have h1 : Nat.card N₀ ≤ Nat.card M := by
      rw [hM, Subgroup.card_map_of_injective X₀.subtype_injective]
      exact Subgroup.card_le_of_le hle
    rw [hMb, Subgroup.card_bot, hcard] at h1
    have : 1 < 2 ^ m := Nat.one_lt_two_pow (by have := hC.two_le; omega)
    omega
  ·
    subst hm3
    have hcard : Nat.card X₀ = 168 := by
      rw [Nat.card_congr φ.toEquiv]
      exact CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two
    have hstab : Nat.card (stabilizer X₀ (0 : F)) = 21 := by
      have h1 := (stabilizer X₀ (0 : F)).card_mul_index
      rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ, hC.card, hcard] at h1
      omega
    have hH : Nat.card (stabilizer G (0 : F)) ≤ 21 := by
      rw [hC.card_stabilizer]
      have := card_stab01_le hC.toHyp
      have : (2 ^ 3 - 1) * Nat.card (stab01 G F) ≤ 7 * 3 := Nat.mul_le_mul_left _ this
      omega
    have hHX : stabilizer G (0 : F) ≤ X₀ := by
      have h1 : Nat.card (stabilizer X₀ (0 : F)) = Nat.card (X₀ ⊓ stabilizer G (0 : F) : Subgroup G) := by
        rw [← stabilizer_subgroupOf, ← inf_subgroupOf_left]
        exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
      have heq : X₀ ⊓ stabilizer G (0 : F) = stabilizer G (0 : F) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [← h1, hstab]; exact hH)
      rw [← heq]
      exact inf_le_left
    apply hne
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx⟩ := hpre.exists_smul_eq (0 : F) (g • (0 : F))
    have hxg : (x : G)⁻¹ * g ∈ stabilizer G (0 : F) := by
      rw [mem_stabilizer_iff, mul_smul, ← show (x : G) • (0 : F) = g • (0 : F) from hx,
        inv_smul_smul]
    have : g = (x : G) * ((x : G)⁻¹ * g) := by group
    rw [this]
    exact X₀.mul_mem x.2 (hHX hxg)

theorem CE.not_dvd_card_mulSubgroup [Finite G] [Finite F] (hC : CE G F m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpΓ : p ∣ Nat.card (stab01 G F)) :
    ¬ p ∣ Nat.card (mulSubgroup G F) := by
  intro hpK
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := stab01 G F) p hpΓ
  have hγ1 : (γ : G) ≠ 1 := by
    intro h1
    have : γ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hγ
    exact hp.one_lt.ne hγ
  refine caseA_false (0 : F) (mulSubgroup G F) mulSubgroup_le_stabilizer
    (fun h hh k hk => conj_mem_mulSubgroup hC.toHyp hh hk)
    (fun a ha b hb => mulSubgroup_comm hC.toHyp ha hb)
    (fun k hk hk1 x hx => eq_zero_of_mem_mulSubgroup hC.toHyp hk hk1 hx)
    (commutator_stabilizer_le hC.toHyp) hpK ?_ (stab01_le_stabilizer γ.2) ?_ ?_
    hC.normalClosure_eq_top
  ·
    have h1 := (stabilizer G (0 : F)).card_mul_index
    rw [hC.card_group, mul_comm] at h1
    have hidx : (stabilizer G (0 : F)).index = 2 ^ m :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [hidx]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  ·
    intro hγK
    have : (γ : G) ∈ stab01 G F ⊓ mulSubgroup G F := ⟨γ.2, hγK⟩
    rw [stab01_inf_mulSubgroup hC.toHyp, mem_bot] at this
    exact hγ1 this
  ·
    rw [← hγ, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _

end CFSG.GH74.Uniqueness.Hering
