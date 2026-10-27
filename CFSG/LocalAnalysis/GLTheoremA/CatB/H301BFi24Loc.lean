module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24Planes
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeC
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.GlueO23
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.LocalAnalysis.GLTheoremA.H1017 (k_side)

private theorem card_map_of_card_ker_two {G M : Type*} [Group G] [Group M] {f : G →* M}
    (hf : Nat.card f.ker = 2) {X : Subgroup G} (hX : IsElemAbelian 3 X) :
    Nat.card (X.map f) = Nat.card X := by
  have hinj : Function.Injective (f.comp X.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hxX⟩ hx
    have hxk : x ∈ f.ker := MonoidHom.mem_ker.2 hx
    have h2 : x ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := f.ker) (x := ⟨x, hxk⟩)
      rw [hf] at h
      simpa using congrArg Subtype.val h
    have h3 : x ^ 3 = 1 := hX.2 x hxX
    refine Subtype.ext ?_
    show x = 1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3, inv_one, mul_one]
  rw [show X.map f = (f.comp X.subtype).range by rw [MonoidHom.range_comp, Subgroup.range_subtype]]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm


theorem fi24QC_inf_centralizer_le {F : Subgroup ↥fi24C} (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 243) :
    fi24QC ⊓ Subgroup.centralizer (F : Set ↥fi24C) ≤ Subgroup.zpowers ⟨fi24R2, fi24R2_mem_C⟩ ∧
      ∀ H : Subgroup ↥fi24C, H ≤ F → Nat.card H * 3 = Nat.card F →
        Nat.card ↥(fi24QC ⊓ Subgroup.centralizer (H : Set ↥fi24C)) ≤ 2 ^ 3 := by
  have hK := Certificates.certificate15027
  have hN := (fi24TwoBKCheck_parts hK).2.1
  have hker : Nat.card fi24Rho.ker = 2 := fi24Rho_range_card.2
  have hkerK : Nat.card fi24RhoK.ker = 2 := card_ker_fi24RhoK
  refine ⟨fun q hq => ?_, fun H hHF hH => ?_⟩
  · obtain ⟨hqQ, hqF⟩ := Subgroup.mem_inf.1 hq
    have hEc : Nat.card (F.map fi24RhoK) = 3 ^ 5 := by
      rw [card_map_of_card_ker_two hkerK hF, hc]
      norm_num
    have h1 : fi24RhoK q = 1 := k_side.2 _ (hF.map fi24RhoK) hEc _
      (Subtype.ext (fi24N_mul_self hN hqQ)) (by
        rintro _ ⟨f, hf, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hqF f hf])
    have hqk : q ∈ fi24Rho.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val h1)
    by_cases hq1 : q = 1
    · rw [hq1]
      exact Subgroup.one_mem _
    have hz1 : (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) ≠ 1 := fun h =>
      fi24R2_ne_one (congrArg Subtype.val h)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : fi24Rho.ker)).1 hker
    have e : (⟨q, hqk⟩ : fi24Rho.ker) = ⟨_, fi24Rho_z⟩ :=
      (hy _ fun h => hq1 (congrArg Subtype.val h)).trans
        (hy _ fun h => hz1 (congrArg Subtype.val h)).symm
    rw [show q = ⟨fi24R2, fi24R2_mem_C⟩ from congrArg Subtype.val e]
    exact Subgroup.mem_zpowers _
  ·
    have hFK : F.map fi24Rho ≤ fi24K := by
      rintro _ ⟨c, -, rfl⟩
      exact (fi24RhoK c).2
    have hHc : Nat.card (H.map fi24Rho) * 3 = Nat.card (F.map fi24Rho) := by
      rw [card_map_of_card_ker_two hker (hF.mono hHF), card_map_of_card_ker_two hker hF, hH]
    have h4 := card_fi24N_inf_centralizer_le hFK (hF.map fi24Rho)
      ((card_map_of_card_ker_two hker hF).trans hc) (Subgroup.map_mono hHF) hHc
    have hk : Nat.card (fi24Rho.comp
        (fi24QC ⊓ Subgroup.centralizer (H : Set ↥fi24C)).subtype).ker ≤ 2 := by
      rw [← hker]
      exact Nat.card_le_card_of_injective
        (fun y => ⟨((y : _) : ↥fi24C), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)⟩)
        fun a b h => by
          have e := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext e)
    have hr : Nat.card (fi24Rho.comp
        (fi24QC ⊓ Subgroup.centralizer (H : Set ↥fi24C)).subtype).range ≤ 4 := by
      refine le_trans (Subgroup.card_le_of_le ?_) h4
      rintro _ ⟨y, rfl⟩
      obtain ⟨hyQ, hyH⟩ := Subgroup.mem_inf.1 y.2
      refine Subgroup.mem_inf.2 ⟨hyQ, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      show fi24Rho h * fi24Rho y = fi24Rho y * fi24Rho h
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hyH h hh]
    calc Nat.card ↥(fi24QC ⊓ Subgroup.centralizer (H : Set ↥fi24C)) = _ :=
        (Subgroup.card_ker_mul_card_range _).symm
      _ ≤ 2 * 4 := Nat.mul_le_mul hk hr
      _ = 2 ^ 3 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
