module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Sign
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectc
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34omega_exists_fixed {C : Type*} [Group C] [Finite C] {O : Subgroup C} [hOn : O.Normal]
    (hO : Nat.Coprime 3 (Nat.card O)) {y j : C} (hy : y ^ 3 = 1)
    (hjy : j * y * j⁻¹ * y⁻¹ ∈ O) : ∃ o ∈ O, y * (j * o) * y⁻¹ = j * o := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk : j⁻¹ * y * j * y⁻¹ ∈ O := by
    have h := hOn.conj_mem _ (O.inv_mem hjy) j⁻¹
    convert h using 1
    group
  have hk' : j⁻¹ * y⁻¹ * j * y ∈ O := by
    have h := hOn.conj_mem _ (O.inv_mem hk) y⁻¹
    convert h using 1
    group
  have hf : ∀ o ∈ O, j⁻¹ * y * j * o * y⁻¹ ∈ O := fun o ho => by
    have h := O.mul_mem hk (hOn.conj_mem o ho y)
    convert h using 1
    group
  have hg : ∀ o ∈ O, j⁻¹ * y⁻¹ * j * o * y ∈ O := fun o ho => by
    have h := O.mul_mem hk' (hOn.conj_mem o ho y⁻¹)
    convert h using 1
    group
  let σ : Equiv.Perm O :=
    { toFun := fun o => ⟨j⁻¹ * y * j * o * y⁻¹, hf o o.2⟩
      invFun := fun o => ⟨j⁻¹ * y⁻¹ * j * o * y, hg o o.2⟩
      left_inv := fun o => Subtype.ext (by simp only; group)
      right_inv := fun o => Subtype.ext (by simp only; group) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext o
    have h3 : y * y * y = 1 := by rw [← hy, pow_three, mul_assoc]
    simp only [pow_one, Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq]
    show j⁻¹ * y * j * (j⁻¹ * y * j * (j⁻¹ * y * j * (o : C) * y⁻¹) * y⁻¹) * y⁻¹ = o
    calc j⁻¹ * y * j * (j⁻¹ * y * j * (j⁻¹ * y * j * (o : C) * y⁻¹) * y⁻¹) * y⁻¹
        = j⁻¹ * (y * y * y) * j * o * (y * y * y)⁻¹ := by group
      _ = o := by rw [h3]; group
  have : Fintype O := Fintype.ofFinite O
  have hndvd : ¬ 3 ∣ Fintype.card O := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO
  obtain ⟨o, ho⟩ := Equiv.Perm.exists_fixed_point_of_prime hndvd hσ
  refine ⟨o, o.2, ?_⟩
  have h := congrArg Subtype.val ho
  change j⁻¹ * y * j * (o : C) * y⁻¹ = o at h
  calc y * (j * o) * y⁻¹ = j * (j⁻¹ * y * j * (o : C) * y⁻¹) := by group
    _ = j * o := by rw [h]

theorem l34omega_mem_zpowers (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    (n : ↥(centralizer ({x} : Set G))) (hnP : (n : G) ∈ (P : Subgroup G))
    (h1 : l34Hom x J n = 1) (hn3 : (n : G) ^ 3 = 1) : (n : G) ∈ zpowers x := by
  have hDcyc := l34_reducedCentralizer_isCyclic hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨hxD, hxo⟩ := l34_xbar_facts hS hU0 hp hM hgen J
  have hnD := (l34insp_hom_eq_one_iff hJ n).mp h1
  set ρ := QuotientGroup.mk' (primeComplementCore (G := ↥(centralizer ({x} : Set G))) 3)
    with hρ
  set xc : ↥(centralizer ({x} : Set G)) := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ with hxc
  set d : ↥(reducedCentralizerOfJ x J) := ⟨ρ n, hnD⟩ with hd
  set g : ↥(reducedCentralizerOfJ x J) := ⟨ρ xc, hxD⟩ with hg
  have hd3 : d ^ 3 = 1 := by
    have hn3' : n ^ 3 = 1 := Subtype.ext (by simpa using hn3)
    apply Subtype.ext
    simp only [hd, SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hn3', map_one]
  have hgo : orderOf g = 3 := by
    rw [hg, Subgroup.orderOf_mk]
    exact hxo
  have hle : zpowers d ≤ zpowers g := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hgo]
    exact orderOf_dvd_of_pow_eq_one hd3
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hle (mem_zpowers d))
  have hk' : ρ (xc ^ k) = ρ n := by
    rw [map_zpow]
    exact congrArg Subtype.val hk
  have hPC : IsPGroup 3 ((P : Subgroup G).subgroupOf (centralizer ({x} : Set G))) :=
    P.isPGroup'.comap_subtype
  have hxkP : xc ^ k ∈ (P : Subgroup G).subgroupOf (centralizer ({x} : Set G)) :=
    Subgroup.zpow_mem _ (mem_subgroupOf.mpr hgen.1) k
  have heq := p34_mk_inj (primeComplementCore_coprime 3) hPC hxkP (mem_subgroupOf.mpr hnP) hk'
  rw [← heq]
  exact ⟨k, by simp [hxc]⟩

theorem l34omega_inf_elem (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsElemAbelian 3 ((P : Subgroup G) ⊓ J) := by
  obtain ⟨hTel, -, -⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  have hAC : A ≤ C := inf_le_right.trans hJ.le_centralizer
  set ψ : ↥A →* L34Quot x J := (l34Hom x J).comp (inclusion hAC) with hψ
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h : ((inclusion hAC a : ↥C) : G) = 1 :=
      congrArg Subtype.val (l34Sign_eq_one_of_mem hK1 hK2 hJ (inclusion hAC a) a.2 ha)
    exact Subtype.ext h
  have hψT : ∀ a : ↥A, ψ a ∈ l34Img x J A := fun a =>
    ⟨inclusion hAC a, mem_subgroupOf.mpr a.2, rfl⟩
  refine ⟨⟨⟨fun a b => hψi ?_⟩⟩, fun a ha => ?_⟩
  · rw [map_mul, map_mul]
    exact congrArg Subtype.val (hTel.1.is_comm.comm ⟨ψ a, hψT a⟩ ⟨ψ b, hψT b⟩)
  · have h : (⟨a, ha⟩ : ↥A) ^ 3 = 1 :=
      hψi (by rw [map_pow, map_one]; exact hTel.2 _ (hψT _))
    simpa using congrArg Subtype.val h

theorem l34omega_E (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsElemAbelian 3 (((P : Subgroup G) ⊓ J) ⊔ zpowers x) ∧
      Nat.card (((P : Subgroup G) ⊓ J) ⊔ zpowers x : Subgroup G) = 3 ^ 3 := by
  have hAel := l34omega_inf_elem hS hU0 hK1 hK2 hp hM hgen hJ
  have hAcard := l34Sign_card_inf hS hU0 hK1 hK2 hp hM hgen hJ
  have hxJ := l34_x_not_mem_J hS hU0 hK1 hK2 hp hM hgen hJ
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hAx : ∀ a ∈ (P : Subgroup G) ⊓ J, a * x = x * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (hJ.le_centralizer ha.2)
  refine ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hAel
    (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) fun a ha => ?_, ?_⟩
  · rw [p34_centralizer_zpowers x]
    exact hJ.le_centralizer ha.2
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three ((P : Subgroup G) ⊓ J) hx3
      (fun h => hxJ h.2) hAx, hAcard]
    norm_num

theorem l34omega_mem_of_normalizer {X : Type*} [Group X] [Finite X] {T K : Subgroup X}
    (hT : IsSylowOf 3 T K) {z : X} (hzK : z ∈ K) (hzN : z ∈ normalizer (T : Set X))
    (hz3 : z ^ 3 = 1) : z ∈ T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (zpowers z) := by
    rintro ⟨w, hw⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hsup := IsPGroup.to_sup_of_normal_left' hT.isPGroup hzp (zpowers_le.mpr hzN)
  have heq := hT.eq_of_le le_sup_left (sup_le hT.le (zpowers_le.mpr hzK)) hsup
  rw [← heq]
  exact (le_sup_right : zpowers z ≤ T ⊔ zpowers z) (mem_zpowers z)

end CFSG.LocalAnalysis.RankThreeTheoremC
