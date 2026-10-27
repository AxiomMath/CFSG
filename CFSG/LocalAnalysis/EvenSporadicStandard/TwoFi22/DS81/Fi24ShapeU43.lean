module

public import CFSG.LieType.Multipliers.U43Bridge
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43 CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen

theorem isSimpleGroup_X₀ : IsSimpleGroup X₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F9 3 1
    (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num) 4 (by norm_num) (by decide)
  rwa [pow_one] at h

theorem exists_hom_X₀ {K : Type} [Group K] [Finite K]
    (Nt : Subgroup K) [Nt.Normal] (x y : K)
    (hrel : ∀ v ∈ rels, wordProd (img2 x y) (v.map fun l => (l.1.val, l.2)) ∈ Nt)
    (hx : x ∉ Nt) (hcard : Nat.card K = 3265920 * Nat.card Nt) :
    ∃ π : K →* X₀, Function.Surjective π ∧ π.ker = Nt := by
  have := isSimpleGroup_X₀
  set q : K →* K ⧸ Nt := QuotientGroup.mk' Nt with hq
  have hP := isPresentation_X₀
  set g : Fin 2 → X₀ := fun i => img2 xElt yElt i.val
  set φ : FreeGroup (Fin 2) →* K ⧸ Nt := FreeGroup.lift fun i : Fin 2 => img2 (q x) (q y) i.val
    with hφ
  have himg : (fun i : ℕ => q (img2 x y i)) = img2 (q x) (q y) := by
    funext i
    unfold img2
    split_ifs <;> rfl
  have hker : (FreeGroup.lift g).ker ≤ φ.ker := by
    rw [hP.ker_lift]
    refine Subgroup.normalClosure_le_normal fun r hr => ?_
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ, lift_mk_eq_wordProd, ← himg, ← map_wordProd]
    exact (QuotientGroup.eq_one_iff _).2 (hrel v hv)
  set ρ : X₀ →* K ⧸ Nt :=
    (FreeGroup.lift g).liftOfSurjective hP.lift_surjective ⟨φ, hker⟩
  have hρφ : ∀ w, ρ (FreeGroup.lift g w) = φ w := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ (Function.rightInverse_surjInv _) ⟨φ, hker⟩ w
  have hρx : ρ xElt = q x := by
    have := hρφ (FreeGroup.of 0)
    rwa [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this
  have hqx : q x ≠ 1 := fun h => hx ((QuotientGroup.eq_one_iff x).1 h)
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exact absurd (hρx ▸ MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top xElt)) hqx
  have hcardQ : Nat.card (K ⧸ Nt) = 3265920 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Nt
    rw [hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h.symm)
  have hbij : Function.Bijective ρ :=
    hinj.bijective_of_nat_card_le (by rw [hcardQ, card_X₀])
  refine ⟨((MulEquiv.ofBijective ρ hbij).symm : K ⧸ Nt →* X₀).comp q, ?_, ?_⟩
  · exact (MulEquiv.ofBijective ρ hbij).symm.surjective.comp (QuotientGroup.mk_surjective)
  · ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    simp [hq, QuotientGroup.eq_one_iff]

end CFSG.EvenSporadicStandard.TwoFi22.DS81
