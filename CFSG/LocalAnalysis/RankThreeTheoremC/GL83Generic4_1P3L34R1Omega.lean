module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts4
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Omegab
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Omegac
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Sign
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectc
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_omega (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK10 : KFactL34OuterCentralizer) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsElemAbelian 3 (((P : Subgroup G) ⊓ J) ⊔ zpowers x) ∧
      Nat.card (((P : Subgroup G) ⊓ J) ⊔ zpowers x : Subgroup G) = 3 ^ 3 ∧
      ∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ 3 = 1 →
        y ∈ ((P : Subgroup G) ⊓ J) ⊔ zpowers x := by
  obtain ⟨hEel, hEcard⟩ := l34omega_E hS hU0 hK1 hK2 hp hM hgen hJ
  refine ⟨hEel, hEcard, fun y hy hy3 => ?_⟩
  by_cases hyx : y ∈ zpowers x
  · exact (le_sup_right : zpowers x ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x) hyx
  have hAel := l34omega_inf_elem hS hU0 hK1 hK2 hp hM hgen hJ
  set yc : ↥(centralizer ({x} : Set G)) := ⟨y, hy.2⟩ with hyc
  have hyK := l34omega_mem_K hS hU0 hK1 hK2 hK10 hp hM hgen hJ hy.1 hy.2 hy3 hyx
  have hyA : y ∈ normalizer (((P : Subgroup G) ⊓ J : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy.1, hJ.centralizer_le hy.2⟩
  have hyN := l34insp_hom_mem_normalizer x J ((P : Subgroup G) ⊓ J) (u := yc) hyA
  have hyc3 : yc ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hy3' : l34Hom x J yc ^ 3 = 1 := by rw [← map_pow, hyc3, map_one]
  have hyT := l34omega_mem_of_normalizer (l34omega_T_sylow hS hU0 hK1 hK2 hp hM hgen hJ) hyK hyN
    hy3'
  obtain ⟨a, haA, ha⟩ := Subgroup.mem_map.mp hyT
  have haA' : (a : G) ∈ (P : Subgroup G) ⊓ J := mem_subgroupOf.mp haA
  set n : ↥(centralizer ({x} : Set G)) := a⁻¹ * yc with hn
  have hn1 : l34Hom x J n = 1 := by rw [hn, map_mul, map_inv, ha, inv_mul_cancel]
  have hnP : (n : G) ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem (P.inv_mem haA'.1) hy.1
  have han : a * n = n * a := by
    have hPC : IsPGroup 3 ((P : Subgroup G).subgroupOf (centralizer ({x} : Set G))) :=
      P.isPGroup'.comap_subtype
    have haP : a ∈ (P : Subgroup G).subgroupOf (centralizer ({x} : Set G)) :=
      mem_subgroupOf.mpr haA'.1
    have hnP' : n ∈ (P : Subgroup G).subgroupOf (centralizer ({x} : Set G)) :=
      mem_subgroupOf.mpr hnP
    refine p34_mk_inj (primeComplementCore_coprime 3) hPC (mul_mem haP hnP') (mul_mem hnP' haP) ?_
    have hnD := (l34insp_hom_eq_one_iff hJ n).mp hn1
    have haJ : QuotientGroup.mk' (primeComplementCore (G := ↥(centralizer ({x} : Set G))) 3) a ∈
        r1sBar x J := ⟨a, mem_subgroupOf.mpr haA'.2, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hnD _ haJ
  have hya : y = (a : G) * n := by simp [hn, hyc]
  have hn3 : (n : G) ^ 3 = 1 := by
    have h := Commute.mul_pow (congrArg Subtype.val han : (a : G) * n = n * a) 3
    rw [← hya, hy3, hAel.2 _ haA', one_mul] at h
    exact h.symm
  have hnx := l34omega_mem_zpowers hS hU0 hK1 hK2 hp hM hgen hJ n hnP hn1 hn3
  rw [hya]
  exact mul_mem ((le_sup_left : (P : Subgroup G) ⊓ J ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x) haA')
    ((le_sup_right : zpowers x ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x) hnx)

theorem l34_elem27_conj (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK10 : KFactL34OuterCentralizer) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) {R₁ : Subgroup G}
    (hR₁C : R₁ ≤ centralizer ({x} : Set G)) (hR₁el : IsElemAbelian 3 R₁)
    (hR₁card : Nat.card R₁ = 3 ^ 3) :
    ∃ c ∈ centralizer ({x} : Set G),
      R₁ = (((P : Subgroup G) ⊓ J) ⊔ zpowers x).map (MulAut.conj c).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hEcard, hΩ⟩ := l34_omega hS hU0 hK1 hK2 hK10 hp hM hgen hJ
  obtain ⟨S, hS⟩ := hgen.2.2.1
  have hR₁p : IsPGroup 3 (R₁.subgroupOf (centralizer ({x} : Set G))) := by
    rintro ⟨r, hr⟩
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hR₁el.2 _ (mem_subgroupOf.mp hr)))⟩
  obtain ⟨S', hS'⟩ := hR₁p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer ({x} : Set G)) S S'
  have h : ((c • S : Sylow 3 _) : Subgroup ↥(centralizer ({x} : Set G))) =
      (S' : Subgroup ↥(centralizer ({x} : Set G))) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h
  refine ⟨c, c.2, Subgroup.eq_of_le_of_card_ge (fun r hr => ?_) ?_⟩
  · have hrS' : (⟨r, hR₁C hr⟩ : ↥(centralizer ({x} : Set G))) ∈ (S' : Subgroup _) :=
      hS' (mem_subgroupOf.mpr hr)
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at hrS'
    obtain ⟨z, hz, hzr⟩ := hrS'
    have hzQ : (z : G) ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      rw [← hS]
      exact ⟨z, hz, rfl⟩
    have hrz : r = (c : G) * z * (c : G)⁻¹ := by
      have h2 := congrArg Subtype.val hzr
      simp only [MulAut.smul_def, MulAut.conj_apply] at h2
      rw [← h2]
      rfl
    have hz3 : (z : G) ^ 3 = 1 := by
      have hr3 := hR₁el.2 r hr
      rw [hrz, conj_pow] at hr3
      calc (z : G) ^ 3 = (c : G)⁻¹ * ((c : G) * (z : G) ^ 3 * (c : G)⁻¹) * c := by group
        _ = 1 := by rw [hr3]; group
    exact ⟨z, hΩ _ hzQ hz3, by rw [hrz]; rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj (c : G)).injective, hEcard, hR₁card]

theorem l34_elem27 (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK10 : KFactL34OuterCentralizer) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) {R₁ : Subgroup G}
    (hR₁C : R₁ ≤ centralizer ({x} : Set G)) (hR₁el : IsElemAbelian 3 R₁)
    (hR₁card : Nat.card R₁ = 3 ^ 3) :
    x ∈ R₁ ∧ IsSylowOf 3 (R₁ ⊓ J) J ∧ R₁ = (R₁ ⊓ J) ⊔ zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcC, hR⟩ := l34_elem27_conj hS hU0 hK1 hK2 hK10 hp hM hgen hJ hR₁C hR₁el hR₁card
  have hxJ := l34_x_not_mem_J hS hU0 hK1 hK2 hp hM hgen hJ
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hAcard := l34Sign_card_inf hS hU0 hK1 hK2 hp hM hgen hJ
  have hxR : x ∈ R₁ := by
    rw [hR]
    refine ⟨x, (le_sup_right : zpowers x ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x) (mem_zpowers x),
      ?_⟩
    have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hcC
    change c * x * c⁻¹ = x
    rw [hcx, mul_inv_cancel_right]
  have hAsyl : IsSylowOf 3 ((P : Subgroup G) ⊓ J) J := by
    have h := hgen.2.2.1.inf_of_le_normalizer hJ.le_centralizer hJ.centralizer_le
    rwa [inf_assoc, inf_eq_right.mpr hJ.le_centralizer] at h
  have hAcJ : ((P : Subgroup G) ⊓ J).map (MulAut.conj c).toMonoidHom ≤ J := by
    rintro _ ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.mp (hJ.centralizer_le hcC) a).mp ha.2
  have hAcsyl : IsSylowOf 3 (((P : Subgroup G) ⊓ J).map (MulAut.conj c).toMonoidHom) J :=
    isSylowOf_of_card hAcJ
      (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]; exact hAsyl.card_eq)
  have hR₁p : IsPGroup 3 R₁ := fun r => ⟨1, Subtype.ext (by simpa using hR₁el.2 r r.2)⟩
  have hRJ : R₁ ⊓ J = ((P : Subgroup G) ⊓ J).map (MulAut.conj c).toMonoidHom :=
    hAcsyl.eq_of_le (le_inf (by rw [hR]; exact Subgroup.map_mono le_sup_left) hAcJ) inf_le_right
      (hR₁p.to_le inf_le_left)
  refine ⟨hxR, by rw [hRJ]; exact hAcsyl, ?_⟩
  have h1 := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (R₁ ⊓ J) hx3
    (fun h => hxJ h.2) (fun e he => mem_centralizer_singleton_iff.mp (hR₁C he.1))
  have h2 : Nat.card (R₁ ⊓ J : Subgroup G) = 3 ^ 2 := by
    rw [hRJ, Subgroup.card_map_of_injective (MulAut.conj c).injective, hAcard]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr hxR))
    (by rw [h1, h2, hR₁card]; norm_num)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
