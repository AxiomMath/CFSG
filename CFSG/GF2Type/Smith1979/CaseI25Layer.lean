module

public import CFSG.LargeExtraspecial.S5Five
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case25

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification
open CFSG.Assembly (InCatalog KProper)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem commutator_eq_bot_of_perfect_of_cyclic {M : Type*} [Group M] {P N : Subgroup M}
    [N.Normal] [IsCyclic N] (hP : ⁅P, P⁆ = P) : ⁅P, N⁆ = ⊥ := by
  have hperf : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  let φ : P →* MulAut N := (MulAut.conjNormal (H := N)).comp P.subtype
  let ψ : P →* (ZMod (Nat.card N))ˣ := (IsCyclic.mulAutMulEquiv N).toMonoidHom.comp φ
  have hker : (⊤ : Subgroup P) ≤ ψ.ker := by
    rw [← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker ψ
  rw [commutator_eq_bot_iff_le_centralizer]
  intro g hg
  rw [mem_centralizer_iff]
  intro n hn
  have h1 : ψ ⟨g, hg⟩ = 1 := hker (mem_top _)
  have h2 : φ ⟨g, hg⟩ = 1 := (IsCyclic.mulAutMulEquiv N).injective (by simpa [ψ] using h1)
  have h3 := congrArg (fun a : MulAut N => ((a ⟨n, hn⟩ : N) : M)) h2
  simp only [φ, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc n * g = (g * n * g⁻¹) * g := by rw [h3]
    _ = g * n := by group

theorem eq_layer_of_isComponentOf {H : Type*} [Group H] [Finite H]
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer H)) {A : Subgroup H}
    (hA : IsComponentOf A ⊤) : A = timmesfeldLayer H := by
  have hAE : A ≤ timmesfeldLayer H := Layer.component_le hA
  have hnorm : (A.subgroupOf (timmesfeldLayer H)).Normal := Layer.normal_component hA
  rcases Quasisimple.normal_le_center_or_eq_top hq (A.subgroupOf (timmesfeldLayer H)) with
    hc | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := Helpers.quasisimple_central_quotient_nonabelian A hA.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    have hx : (⟨x, hAE x.2⟩ : timmesfeldLayer H) ∈ center (timmesfeldLayer H) :=
      hc (mem_subgroupOf.mpr x.2)
    have hxy := congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hAE y.2⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hxy.symm
  · exact le_antisymm hAE (subgroupOf_eq_top.mp htop)

section Setting

variable {G : Type} [Group G] [Finite G]

theorem center_layer_le_oddCore (S : Setting G) :
    (center (timmesfeldLayer S.Mbar)).map (timmesfeldLayer S.Mbar).subtype ≤
      timmesfeldOddCore S.Mbar :=
  (GeneralizedFitting.layer_center_le_fitting S.Mbar).trans (S5.fitting_le_oddCore S)

theorem M_ne_top_of_isSimpleGroup [IsSimpleGroup G] (S : Setting G) : S.M ≠ ⊤ := by
  intro htop
  have hz : S.z ∈ center G := mem_center_iff.mpr fun g => S.mem_M_iff.mp (htop ▸ mem_top g)
  have hcomm : ∀ x y : G, x * y = y * x := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · exact absurd (by simpa [h] using hz) S.z_ne_one
    · intro x y
      exact (mem_center_iff.mp (h ▸ mem_top x) y).symm
  have hc : center S.Q = ⊤ := eq_top_iff.mpr fun x _ =>
    mem_center_iff.mpr fun y => Subtype.ext (Subtype.ext (hcomm _ _))
  have hperf : Group.IsPerfect S.Q := ⟨S.extraspecial.2.1.trans hc⟩
  have hsub : Subsingleton S.Q := by
    have : IsMulCommutative S.Q := ⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ _))⟩⟩
    exact Group.IsPerfect.subsingleton_of_isMulCommutative
  have h2 := S.extraspecial.2.2.2
  rw [Nat.card_of_subsingleton (1 : center S.Q)] at h2
  exact absurd h2 (by norm_num)

variable {S : Setting G}

theorem card_center_layer_dvd (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) :
    Nat.card (center (timmesfeldLayer S.Mbar)) ∣ 3 := by
  have h2 : Nat.card ((center (timmesfeldLayer S.Mbar)).map
      (timmesfeldLayer S.Mbar).subtype) = Nat.card (center (timmesfeldLayer S.Mbar)) :=
    card_map_of_injective (timmesfeldLayer S.Mbar).subtype_injective
  rw [← h2]
  exact (card_dvd_of_le (center_layer_le_oddCore S)).trans hodd

theorem inCatalog_layer_quotient (hK : KProper InCatalog G) (hM : S.M ≠ ⊤)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar)) :
    InCatalog (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  have hMnonab : KCore.KGroupNonab InCatalog S.M :=
    KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hK S.M hM
  have hMbar : KCore.KGroupNonab InCatalog S.Mbar :=
    hMnonab.of_surjective CFSG.Assembly.inCatalog_isoInvariant S.ρ.rangeRestrict
      S.ρ.rangeRestrict_surjective
  haveI : IsSimpleGroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := hq.2
  exact hMbar.catalogue_of_surjective CFSG.Assembly.inCatalog_isoInvariant
    (timmesfeldLayer S.Mbar) (Helpers.quasisimple_central_quotient_nonabelian _ hq)
    (QuotientGroup.mk' (center (timmesfeldLayer S.Mbar))) (QuotientGroup.mk'_surjective _)

theorem layer_data (hK : KProper InCatalog G) (hM : S.M ≠ ⊤)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) :
    (timmesfeldLayer S.Mbar).Normal ∧
      ⁅timmesfeldLayer S.Mbar, timmesfeldLayer S.Mbar⁆ = timmesfeldLayer S.Mbar ∧
      Odd (Nat.card (center (timmesfeldLayer S.Mbar))) ∧
      Nat.card (center (timmesfeldLayer S.Mbar)) ∣ 3 ∧
      IsSimpleGroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∧
      (∃ a b : timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar), a * b ≠ b * a) ∧
      InCatalog (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  have hZ := card_center_layer_dvd hodd
  exact ⟨Layer.normal S.Mbar, Subgroup.isPerfect_iff.mp (Layer.perfect S.Mbar),
    Odd.of_dvd_nat (by decide) hZ, hZ, hq.2,
    Helpers.quasisimple_central_quotient_nonabelian _ hq, inCatalog_layer_quotient hK hM hq⟩

theorem perfect_le_layer_of_inCatalog (hS : SchreierFor InCatalog)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hX : InCatalog (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)))
    {P : Subgroup S.Mbar} (hperf : ⁅P, P⁆ = P) : P ≤ timmesfeldLayer S.Mbar := by
  haveI : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hperf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (timmesfeldOddCore S.Mbar).Normal := S5.timmesfeldOddCore_normal S.Mbar
  haveI : IsCyclic (timmesfeldOddCore S.Mbar) := isCyclic_of_card_dvd_prime hodd
  have hFit : ⁅P, Fitting.subgroup S.Mbar⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_mono le_rfl (S5.fitting_le_oddCore S)).trans
      (commutator_eq_bot_of_perfect_of_cyclic hperf).le)
  have hnormal : (timmesfeldLayer S.Mbar).Normal := Layer.normal S.Mbar
  refine GeneralizedFitting.perfect_normalizer_enters_layer P hFit (fun A hA => ?_)
    (fun A hA => ?_)
  · rw [eq_layer_of_isComponentOf hq hA, normalizer_eq_top_iff.mpr hnormal]
    exact le_top
  · rw [eq_layer_of_isComponentOf hq hA]
    haveI : IsSimpleGroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := hq.2
    exact hS _ (Helpers.quasisimple_central_quotient_nonabelian _ hq) hX

theorem perfect_le_layer (hS : SchreierFor InCatalog) (hK : KProper InCatalog G)
    (hM : S.M ≠ ⊤) (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) {P : Subgroup S.Mbar} (hperf : ⁅P, P⁆ = P) :
    P ≤ timmesfeldLayer S.Mbar :=
  perfect_le_layer_of_inCatalog hS hq hodd (inCatalog_layer_quotient hK hM hq) hperf

theorem perfect_le_layer_map (hS : SchreierFor InCatalog) (hK : KProper InCatalog G)
    (hM : S.M ≠ ⊤)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) {P : Subgroup S.O} (hPM : P ≤ S.Mbar)
    (hperf : ⁅P, P⁆ = P) : P ≤ (timmesfeldLayer S.Mbar).map S.Mbar.subtype := by
  have h1 : ⁅P.subgroupOf S.Mbar, P.subgroupOf S.Mbar⁆ = P.subgroupOf S.Mbar := by
    apply Subgroup.map_injective S.Mbar.subtype_injective
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hPM, hperf]
  calc P = (P.subgroupOf S.Mbar).map S.Mbar.subtype := (map_subgroupOf_eq_of_le hPM).symm
    _ ≤ _ := map_mono (perfect_le_layer hS hK hM hq hodd h1)

end Setting

end CFSG.GF2Type.Smith1979.Case25
