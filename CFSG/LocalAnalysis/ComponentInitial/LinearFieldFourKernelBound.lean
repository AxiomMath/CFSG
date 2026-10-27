module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFourKernel

open Subgroup LinearFlag LinearFieldFour LinearCover

theorem field_four_linear_three_central_two_kernel_rank_and_exponent_bound {P : Type*}
    {Q : Type} [Group P] [Group Q] [Finite P] [Finite Q] [Group.IsPerfect P] (η : P →* Q)
    (hη : Function.Surjective η) (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSL 3 2 2) :
    IsMulCommutative η.ker ∧ (∀ z ∈ η.ker, z ^ 4 = 1) ∧
      (∃ a b : P, a ∈ η.ker ∧ b ∈ η.ker ∧ closure {a, b} = η.ker) ∧
      (∃ f : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* P, f.range = η.ker) ∧
      Nat.card η.ker ≤ 16 := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hQ
  have hk : Nat.card k = 4 := by rw [hcard]; norm_num
  have := charP_two_of_card_eq_four hk
  set η' : P →* projectiveSL 3 k := e.toMonoidHom.comp η with hη'def
  have hη' : Function.Surjective η' := e.surjective.comp hη
  have hker' : ∀ z, η' z = 1 ↔ η z = 1 := fun z => e.map_eq_one_iff
  have hc' : ∀ z, η' z = 1 → z ∈ center P := fun z hz => hK ((hker' z).mp hz)
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hk
  have hω3 := omega_cube hk hω0
  have hω4 := one_add_omega_add_omega_sq hk hω0 hω1
  set u := lift η' hη' (hP ω hω3)
  have hu : η' u = hP ω hω3 := map_lift η' hη' _
  set κ₁ := normComm η' hη' ω 1 1 with hκ₁def
  set κ₂ := normComm η' hη' ω ω 1 with hκ₂def
  have hκ₁ : κ₁ ∈ η.ker := (hker' _).mp (map_normComm η' hη' hω3 hω4 1 1)
  have hκ₂ : κ₂ ∈ η.ker := (hker' _).mp (map_normComm η' hη' hω3 hω4 ω 1)
  have hpow4 : ∀ a b : k, normComm η' hη' ω a b ^ 4 = 1 := fun a b => by
    rw [show 4 = 2 * 2 from rfl, pow_mul, normComm_sq η' hη' hc' hω3 u hu hk hω0 hω1, sq,
      wxComm_mul_self η' hη' hc']
  have hκ₁4 : κ₁ ^ 4 = 1 := hpow4 1 1
  have hκ₂4 : κ₂ ^ 4 = 1 := hpow4 ω 1
  have hgen : closure {κ₁, κ₂} = η.ker := by
    refine le_antisymm ((closure_le _).mpr ?_) fun z hz => ?_
    · rintro _ (rfl | rfl)
      · exact hκ₁
      · exact hκ₂
    · obtain ⟨n, hn⟩ := h2 ⟨z, hz⟩
      exact twoPart_le_closure_normComm η' hη' hc' hω3 u hu hk hω0 hω1 z ((hker' z).mpr hz)
        ⟨n, congrArg Subtype.val hn⟩
  have hcomm : ∀ m n : Multiplicative (ZMod 4), Commute (zmodHom 4 κ₁ hκ₁4 m)
      (zmodHom 4 κ₂ hκ₂4 n) := fun m n => by
    have hmem : ∀ (c : P) (hc : c ^ 4 = 1), c ∈ η.ker →
        ∀ m : Multiplicative (ZMod 4), zmodHom 4 c hc m ∈ η.ker := fun c hc hcK m => by
      have hm : m = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd m).val := by
        rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      rw [hm, map_pow, zmodHom_ofAdd_one]
      exact pow_mem hcK _
    exact (mem_center_iff.mp (hK (hmem κ₂ hκ₂4 hκ₂ n)) _)
  let f := MonoidHom.noncommCoprod (zmodHom 4 κ₁ hκ₁4) (zmodHom 4 κ₂ hκ₂4) hcomm
  have hfrange : f.range = η.ker := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨m, n⟩, rfl⟩
      have hmem : ∀ (c : P) (hc : c ^ 4 = 1), c ∈ η.ker →
          ∀ m : Multiplicative (ZMod 4), zmodHom 4 c hc m ∈ η.ker := fun c hc hcK m => by
        have hm : m = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd m).val := by
          rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
        rw [hm, map_pow, zmodHom_ofAdd_one]
        exact pow_mem hcK _
      exact mul_mem (hmem κ₁ hκ₁4 hκ₁ m) (hmem κ₂ hκ₂4 hκ₂ n)
    · rw [← hgen, closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨(Multiplicative.ofAdd 1, 1), by
          simp [f, MonoidHom.noncommCoprod_apply, zmodHom_ofAdd_one]⟩
      · exact ⟨(1, Multiplicative.ofAdd 1), by
          simp [f, MonoidHom.noncommCoprod_apply, zmodHom_ofAdd_one]⟩
  have hcardC4 : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  refine ⟨⟨⟨fun a b => Subtype.ext ((mem_center_iff.mp (hK a.2) b).symm)⟩⟩, fun z hz => ?_,
    ⟨κ₁, κ₂, hκ₁, hκ₂, hgen⟩, ⟨f, hfrange⟩, ?_⟩
  · rw [← hfrange] at hz
    obtain ⟨x, rfl⟩ := hz
    have h4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hx4 : x ^ 4 = 1 := by
      have h1 := pow_card_eq_one' (G := Multiplicative (ZMod 4)) (x := x.1)
      have h2 := pow_card_eq_one' (G := Multiplicative (ZMod 4)) (x := x.2)
      rw [h4] at h1 h2
      exact Prod.ext (by rw [Prod.pow_fst, h1, Prod.fst_one])
        (by rw [Prod.pow_snd, h2, Prod.snd_one])
    rw [← map_pow, hx4, map_one]
  · rw [← hfrange, ← hcardC4]
    exact Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective

end LinearFieldFourKernel

end CFSG.LocalAnalysis.ComponentInitial
