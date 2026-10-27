module

public import CFSG.LargeExtraspecial.AS35UB
public import CFSG.LargeExtraspecial.S12InspXOrd
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBUFourUnitaryAxisFlagKernel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary
open CFSG.Blueprint.Fischer (K)

namespace S12Insp4P

theorem two_pow_dvd_card_PG {m : ℕ} (hm : 4 ≤ m) {e : Fin m → K} (he0 : e ≠ 0)
    (he : herm frob e e = 0) : 2 ^ (1 + 2 * (m - 2)) ∣ Nat.card (PG m) := by
  have hm3 : 3 ≤ m := by omega
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, hcard, hSU, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  let π := QuotientGroup.mk' (center (SUid frob m))
  let A := axisKernel (AS35U.hermB m) e
  let Ahat := A.comap (AS35U.ι m)
  have hAmap : Ahat.map (AS35U.ι m) = A := Subgroup.map_comap_eq_self fun y hy => by
    obtain ⟨a, ha⟩ := AS35U.exists_ι_eq (hSU hy)
    exact ⟨a, ha⟩
  have hfix : ∀ a ∈ Ahat, a • e = e := fun a ha => by
    rw [← AS35U.ι_apply]
    exact (mem_axisKernel.mp ha).2.1
  have hinj : ∀ x ∈ Ahat, π x = 1 → x = 1 := by
    intro x hx h1
    have hxZ : x ∈ center (SUid frob m) := (QuotientGroup.eq_one_iff _).mp h1
    rw [center_SUid hm3] at hxZ
    obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hxZ
    have hce : c • e = e := (hc e).symm.trans (hfix x hx)
    have hc1 : c = 1 := by
      have h0 : (c - 1) • e = 0 := by rw [sub_smul, one_smul, hce, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right he0)
    exact ext_smul _ fun y => by rw [hc, hc1, one_smul, one_smul]
  let r := π.comp Ahat.subtype
  have hr : Function.Injective r := (injective_iff_map_eq_one r).mpr fun x hx =>
    Subtype.ext (hinj x x.2 hx)
  have hcardbar : Nat.card (Ahat.map π) = 2 ^ (1 + 2 * (m - 2)) := by
    have hrange : r.range = Ahat.map π := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hr).toEquiv,
      ← Subgroup.card_map_of_injective (K := Ahat) (f := AS35U.ι m) AS35U.ι_injective, hAmap,
      hcard, Module.finrank_fin_fun]
  rw [← hcardbar]
  exact card_subgroup_dvd_card _

end S12Insp4P

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem le_five_of_psu {g : G} {t : S.O}
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {m : ℕ} (hm : 4 ≤ m)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) : m ≤ 5 := by
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 hmod
  have htE := mem_Ebar12_of_mem_Lbar ht htA
  have hψd : (φ.trans (u2Equiv m)) ⟨t, subset_Xbar12 htE⟩ ∈ DG m := by
    rw [← image_DU, ← hφ]
    exact ⟨φ ⟨t, subset_Xbar12 htE⟩, ⟨⟨t, subset_Xbar12 htE⟩, htE, rfl⟩, rfl⟩
  obtain ⟨e, he0, he, -⟩ := hψd
  have h1 := S12Insp4P.two_pow_dvd_card_PG hm he0 he
  rw [← Nat.card_congr (φ.trans (u2Equiv m)).toEquiv] at h1
  have := le_seven_of_two_pow_dvd_card_Xbar12 hP h1
  omega

end Setting

end CFSG.LargeExtraspecial
