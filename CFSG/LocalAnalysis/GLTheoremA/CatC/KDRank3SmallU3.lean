module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallU3PsuF2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS01Rest
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Psu
open TauCeti

theorem unitaryFieldData_729 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 3 (GaloisField 3 (2 * 3)) :=
  ⟨Nat.prime_three, by norm_num, GaloisField.card 3 (2 * 3) (by norm_num)⟩

theorem nonempty_psu_iso {S : Type} [Group S] (c fe : ℕ) [Fact c.Prime] (hc : c = 3) (hfe : fe = 3)
    (E : S ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (c ^ fe) (GaloisField c (2 * fe)))) :
    Nonempty (S ≃* unitaryPSU unitaryFieldData_729 3) := by
  subst hc hfe
  exact ⟨E.trans (unitaryPSUEquiv unitaryFieldData_729 (by norm_num)).symm⟩

theorem smallF12_U3 : ∀ q : TauCeti.PrimePower, q.card = 27 → SmallF12At (.twistedA 2 q) := by
  intro q hq S _ _ hv he E hE hEcard hnot hE0
  obtain ⟨e⟩ := he
  have hp3 : q.p = 3 := CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallL3.prime_eq_three_of_card_eq_27 q hq
  have hpow : q.p ^ q.exponent = 3 ^ 3 := by
    rw [← PrimePower.card_def, hq]
    norm_num
  have hf3 : q.exponent = 3 := by
    rw [hp3] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hc : ValidLieTypeIndex.characteristic ⟨LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    simp [ValidLieTypeIndex.characteristic, hp3]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    simp [ValidLieTypeIndex.fieldExponent, hf3]
  obtain ⟨e₀⟩ := nonempty_psu_iso _ _ hc hfe
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv))
  have hφi : Function.Injective (MulAut.congr e₀).toMonoidHom := (MulAut.congr e₀).injective
  have hin : ((inner S).map (MulAut.congr e₀).toMonoidHom) = inner (unitaryPSU unitaryFieldData_729 3) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e₀
  have hE' : IsElemAbelian 3 (E.map (MulAut.congr e₀).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE (MulAut.congr e₀).toMonoidHom
  have hcard' : Nat.card (E.map (MulAut.congr e₀).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hφi, hEcard]
  have hnot' : ¬ E.map (MulAut.congr e₀).toMonoidHom ≤ inner (unitaryPSU unitaryFieldData_729 3) := by
    intro hle
    apply hnot
    intro x hx
    have hx' : (MulAut.congr e₀).toMonoidHom x ∈ inner (unitaryPSU unitaryFieldData_729 3) :=
      hle (Subgroup.mem_map_of_mem _ hx)
    rw [← hin] at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    rw [← hφi hyx]
    exact hy
  have hmap : E.map (MulAut.congr e₀).toMonoidHom ⊓ inner (unitaryPSU unitaryFieldData_729 3) =
      (E ⊓ inner S).map (MulAut.congr e₀).toMonoidHom := by
    rw [← hin, Subgroup.map_inf_eq _ _ _ hφi]
  have hE0' : Nat.card ↥(E.map (MulAut.congr e₀).toMonoidHom ⊓ inner (unitaryPSU unitaryFieldData_729 3)) =
      3 ^ 2 := by
    rw [hmap, Subgroup.card_map_of_injective hφi, hE0]
  have hK3 : ringChar (GaloisField 3 (2 * 3)) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 (2 * 3)) 3]
    norm_num
  have h3 : (3 : GaloisField 3 (2 * 3)) = 0 := CharP.cast_eq_zero _ 3
  have hF2G : SmallF2 (unitaryPSU unitaryFieldData_729 3) (E.map (MulAut.congr e₀).toMonoidHom) :=
    f2_psu unitaryFieldData_729 hK3 h3 _ hE' hcard' hnot' hE0'
  have hF2 : SmallF2 S E := by
    intro W hW hWI hWC
    have hW' : W.map (MulAut.congr e₀).toMonoidHom = ⊥ := by
      apply hF2G _ (hW.map _)
      · exact (Subgroup.map_mono hWI).trans hin.le
      · intro y hy
        rw [hmap] at hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
        rw [Subgroup.mem_centralizer_iff]
        intro w' hw'
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hw'
        have hcw := Subgroup.mem_centralizer_iff.1 (hWC hx) w hw
        rw [← map_mul, ← map_mul, hcw]
    ext x
    constructor
    · intro hx
      have hmem : (MulAut.congr e₀).toMonoidHom x ∈ W.map (MulAut.congr e₀).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hW', Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.2 (hφi (by rw [hmem, map_one]))
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact W.one_mem
  have hK : KleinFour3 (inner S) := by
    intro g₁ g₂ k hg₁ hg₂ hg1 hg2 hne1 hne2 hne hcomm hk hk3 hkg1 hkg2
    have hin' : ∀ x ∈ inner S, (MulAut.congr e₀).toMonoidHom x ∈ inner (unitaryPSU unitaryFieldData_729 3) :=
      fun x hx => by
        rw [← hin]
        exact Subgroup.mem_map_of_mem _ hx
    have hk' := KDRank3SmallU3Psu.klein_psu unitaryFieldData_729 hK3 h3
      ((MulAut.congr e₀).toMonoidHom g₁) ((MulAut.congr e₀).toMonoidHom g₂)
      ((MulAut.congr e₀).toMonoidHom k) (hin' g₁ hg₁) (hin' g₂ hg₂)
      (by rw [← map_pow, hg1, map_one]) (by rw [← map_pow, hg2, map_one])
      (fun h => hne1 (hφi (by rw [h, map_one]))) (fun h => hne2 (hφi (by rw [h, map_one])))
      (fun h => hne (hφi h)) (by rw [← map_mul, ← map_mul, hcomm]) (hin' k hk)
      (by rw [← map_pow, hk3, map_one]) (by rw [← map_mul, ← map_mul, hkg1])
      (by rw [← map_mul, ← map_mul, hkg2])
    exact hφi (by rw [hk', map_one])
  exact ⟨hF2, smallF1_of_f2_klein S E hE hEcard hE0 hF2 hK⟩

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3

end
