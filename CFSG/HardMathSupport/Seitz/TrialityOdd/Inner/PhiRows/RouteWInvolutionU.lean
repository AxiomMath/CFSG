module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public section

open Subgroup
open scoped Pointwise

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

lemma exists_fixed_involution_of_sylow {C : Type*} [Group C] [Finite C] (hC : Even (Nat.card C))
    (α : MulAut C) (hα : α * α = 1) :
    ∃ u : C, u ≠ 1 ∧ u * u = 1 ∧ α u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype C := Fintype.ofFinite C
  have : Fintype (Sylow 2 C) := Fintype.ofFinite _
  let f : Function.End (Sylow 2 C) := fun S => α • S
  have hf : f ^ 2 ^ 1 = 1 := by
    funext S
    change α • (α • S) = S
    rw [← mul_smul, hα, one_smul]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hodd : Nat.card (Sylow 2 C) ≡ 1 [MOD 2] := card_sylow_modEq_one 2 C
  have hfix : Fintype.card f.fixedPoints ≠ 0 := by
    intro h0
    rw [h0, ← Nat.card_eq_fintype_card] at hmod
    have := hodd.symm.trans hmod
    simp [Nat.ModEq] at this
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 C, α • S = S := by
    obtain ⟨⟨S, hS⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hfix)
    exact ⟨S, hS⟩
  have hmem : ∀ s ∈ (S : Subgroup C), α s ∈ (S : Subgroup C) := by
    intro s hs
    have : α s ∈ α • (S : Subgroup C) := Subgroup.smul_mem_pointwise_smul _ _ _ hs
    have h3 : ((α • S : Sylow 2 C) : Subgroup C) = α • (S : Subgroup C) := rfl
    have h2 : (α • S : Sylow 2 C) = S := hS
    rw [← h3, h2] at this
    exact this
  have hScard : Nat.card S = 2 ^ (Nat.card C).factorization 2 := by
    rw [Sylow.card_eq_multiplicity]
  have hpos : 1 ≤ (Nat.card C).factorization 2 := by
    have h0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
    exact (Nat.prime_two.factorization_pos_of_dvd h0 (even_iff_two_dvd.1 hC))
  let g : Function.End S := fun s => ⟨α s, hmem s s.2⟩
  have hg : g ^ 2 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    change α (α s) = s
    have := congrArg (fun β : MulAut C => β (s : C)) hα
    simpa using this
  have : Fintype S := Fintype.ofFinite S
  have hmod2 := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hg
  rw [← Nat.card_eq_fintype_card, hScard] at hmod2
  have hev : 2 ∣ Fintype.card g.fixedPoints := by
    have h2 : 2 ∣ 2 ^ (Nat.card C).factorization 2 := dvd_pow_self 2 (by omega)
    exact Nat.modEq_zero_iff_dvd.1 (hmod2.symm.trans (Nat.modEq_zero_iff_dvd.2 h2))
  have h1fix : (1 : S) ∈ Function.fixedPoints g := by
    apply Subtype.ext
    change α 1 = 1
    exact map_one α
  have hgt : 1 < Fintype.card g.fixedPoints := by
    have hp : 0 < Fintype.card g.fixedPoints :=
      Fintype.card_pos_iff.2 ⟨⟨1, h1fix⟩⟩
    obtain ⟨c, hc⟩ := hev
    omega
  obtain ⟨⟨u, hu⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hgt ⟨1, h1fix⟩
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have huα : α (u : C) = u := congrArg Subtype.val hu
  have hord : orderOf (u : C) ∣ 2 ^ (Nat.card C).factorization 2 := by
    rw [← hScard, Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard u
  obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hj1 : 1 ≤ j := by
    by_contra h
    have : j = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hj2
    exact hu1 (Subtype.ext hj2)
  refine ⟨(u : C) ^ 2 ^ (j - 1), ?_, ?_, ?_⟩
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hj2] at this
    have h3 := Nat.le_of_dvd (by positivity) this
    have : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_add, ← two_mul, ← pow_succ']
    rw [show j - 1 + 1 = j by omega]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hj2])
  · rw [map_pow, huα]

theorem exists_involution_commuting_of_inverted {G : Type*} [Group G] [Finite G] {x w : G}
    (hw : w * w = 1) (hwx : w * x * w⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer ({x} : Set G)))) :
    ∃ u : G, u ≠ 1 ∧ u * u = 1 ∧ u * x = x * u ∧ u * w = w * u := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hwx' : w * x⁻¹ * w⁻¹ = x := by
    have := congrArg (fun z => z⁻¹) hwx
    simpa [mul_assoc] using this
  have hmem : ∀ c : G, c * x = x * c → (w * c * w⁻¹) * x = x * (w * c * w⁻¹) := by
    intro c hc
    have hx : w⁻¹ * x * w = x⁻¹ := by rw [hwi]; rw [hwi] at hwx; exact hwx
    have hxc : c * x⁻¹ = x⁻¹ * c := by
      have := congrArg (fun z => x⁻¹ * z * x⁻¹) hc
      simpa [mul_assoc] using this.symm
    calc (w * c * w⁻¹) * x = w * c * (w⁻¹ * x * w) * w⁻¹ := by group
      _ = w * (x⁻¹ * c) * w⁻¹ := by rw [hx, mul_assoc w c, hxc, ← mul_assoc]
      _ = (w * x⁻¹ * w⁻¹) * (w * c * w⁻¹) := by group
      _ = x * (w * c * w⁻¹) := by rw [hwx']
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hCmem : ∀ c : G, c ∈ C ↔ c * x = x * c := fun c => by
    simp only [C, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hmemC : ∀ c : C, w * (c : G) * w⁻¹ ∈ C := fun c => (hCmem _).2 (hmem c ((hCmem _).1 c.2))
  let α : MulAut C :=
    { toFun := fun c => ⟨w * c * w⁻¹, hmemC c⟩
      invFun := fun c => ⟨w * c * w⁻¹, hmemC c⟩
      left_inv := fun c => by
        apply Subtype.ext
        change w * (w * c * w⁻¹) * w⁻¹ = c
        rw [hwi]
        calc w * (w * c * w) * w = (w * w) * c * (w * w) := by group
          _ = c := by rw [hw]; group
      right_inv := fun c => by
        apply Subtype.ext
        change w * (w * c * w⁻¹) * w⁻¹ = c
        rw [hwi]
        calc w * (w * c * w) * w = (w * w) * c * (w * w) := by group
          _ = c := by rw [hw]; group
      map_mul' := fun a b => by
        apply Subtype.ext
        change w * ((a : G) * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹)
        group }
  have hαα : α * α = 1 := by
    ext c
    change w * (w * (c : G) * w⁻¹) * w⁻¹ = c
    rw [hwi]
    calc w * (w * (c : G) * w) * w = (w * w) * c * (w * w) := by group
      _ = c := by rw [hw]; group
  obtain ⟨u, hu1, huu, huα⟩ := exists_fixed_involution_of_sylow hC α hαα
  refine ⟨(u : G), fun h => hu1 (Subtype.ext h), congrArg Subtype.val huu, ?_, ?_⟩
  · exact ((hCmem _).1 u.2)
  · have h := congrArg Subtype.val huα
    change w * (u : G) * w⁻¹ = u at h
    calc (u : G) * w = (w * (u : G) * w⁻¹) * w := by rw [h]
      _ = w * u := by group

theorem even_card_of_quasisimple_commutator {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (hq : CFSG.IsQuasisimple (⁅C, C⁆ : Subgroup G)) : Even (Nat.card C) := by
  obtain ⟨hperf, hsimp, -⟩ := hq
  have hRC : (⁅C, C⁆ : Subgroup G) ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hReven : Even (Nat.card (⁅C, C⁆ : Subgroup G)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard (⁅C, C⁆ : Subgroup G) hodd
    have := hsimp.toNontrivial
    have : Nontrivial (⁅C, C⁆ : Subgroup G) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (⁅C, C⁆ : Subgroup G))).nontrivial
    exact (Group.IsPerfect.not_isSolvable (⁅C, C⁆ : Subgroup G)) hsolv
  have hcard : Nat.card (⁅C, C⁆ : Subgroup G) ∣ Nat.card C :=
    Subgroup.card_dvd_of_le hRC
  obtain ⟨k, hk⟩ := hcard
  rw [hk]
  exact hReven.mul_right k

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

