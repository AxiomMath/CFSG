module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Abelb
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Abelc
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Abeld

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_stepL (hS : Setting G) (hU0 : FullCoreLocal G) (_hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK6 : KFactL34OutThree)
    (hK9 : KFactL34ThreeExponent) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) (hR1 : L34Prop34 3 P J x) {U : Subgroup G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (_hUJ : U ⊓ J ≠ ⊥)
    {S : Subgroup G} (_hS2 : IsPGroup 2 S) (_hSne : S ≠ ⊥) (hUS : U ≤ normalizer (S : Set G))
    (_hesc : ¬ normalizer (S : Set G) ≤ M) (hrk : pRank 3 (normalizer (S : Set G)) ≤ 2) :
    ∃ F : Subgroup G, IsSylowOf 3 F (normalizer (S : Set G)) ∧ IsMulCommutative F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := normalizer (S : Set G) with hH
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hUp : IsPGroup 3 U := fun u => ⟨1, Subtype.ext (by simpa using hU.2 u u.2)⟩
  obtain ⟨T, hT⟩ := (hUp.comap_subtype (K := H)).exists_le_sylow
  set F : Subgroup G := (T : Subgroup H).map H.subtype with hF
  have hFH : IsSylowOf 3 F H := ⟨T, rfl⟩
  have hUF : U ≤ F := fun u hu =>
    ⟨⟨u, hUS hu⟩, hT (show (⟨u, hUS hu⟩ : H) ∈ U.comap H.subtype from hu), rfl⟩
  have hFp : IsPGroup 3 F := hFH.isPGroup
  have hrkF : CFSG.Open.pRank 3 F ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hrk
    exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hFH.le).trans hrk
  refine ⟨F, hFH, ?_⟩
  have hmem : ∀ f ∈ F, f ^ 3 = 1 → f ∈ U := fun f hf hf3 =>
    l34abel_mem_of_pow hR1 hU hUc hUF hFp hrkF hf hf3
  have hFU := l34abel_le_normalizer hU hUF hmem
  have hFC : F ≤ C := l34abel_le_centralizer hR1.2.2.2.2 hx3 hxU hUP hFU hFp
  have hxJ := l34abel_not_mem hK1 hK2 hJ hx1 hx3
  have hcomm : ∀ u ∈ U ⊓ J, ∀ g ∈ F, g * u * g⁻¹ = u := fun u hu g hg =>
    l34abel_inf_comm hJ.centralizer_le hU hUc hxU hxJ hFC hFU hFp hu hg
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set ρ : C →* GenericReduced 3 x := QuotientGroup.mk' O with hρ
  have hDn := l34_reducedCentralizer_normal hJ
  obtain ⟨hKn, hKc, hKt⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  rw [l34Img_J_eq] at hKn hKc hKt
  set π := QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore with hπ
  have hker : π.ker = reducedCentralizerOfJ x J := by
    rw [hπ, QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have h3elt : ∀ c : C, (c : G) ∈ F → ∃ n : ℕ, (c : G) ^ 3 ^ n = 1 := fun c hc => by
    obtain ⟨n, hn⟩ := hFp ⟨c, hc⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hFb : IsPGroup 3 ((F.subgroupOf C).map ρ) := (hFp.comap_subtype (K := C)).map ρ
  have hcen : ∀ a ∈ (F.subgroupOf C).map ρ, a ∈ r1sBar x J →
      ∀ b ∈ (F.subgroupOf C).map ρ, a * b = b * a := by
    rintro _ ⟨f, hf, rfl⟩ hfJ _ ⟨g, hg, rfl⟩
    have hf' : (f : G) ∈ F := Subgroup.mem_subgroupOf.mp hf
    have hg' : (g : G) ∈ F := Subgroup.mem_subgroupOf.mp hg
    obtain ⟨n, hn⟩ := h3elt f hf'
    have hf3' : ρ f ^ 3 = 1 := l34abel_pow_three_of_mem_bar hK1 hK2 hJ hfJ
      ⟨n, by rw [← map_pow, show f ^ 3 ^ n = 1 from Subtype.ext (by simpa using hn), map_one]⟩
    have hf3 : (f : G) ^ 3 = 1 := by
      have h4 : ((f ^ 3 : C) : G) ^ 3 ^ n = 1 := by
        rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hn, one_pow]
      simpa using congrArg Subtype.val (l34abel_eq_one_of_mk h4 (by rw [map_pow]; exact hf3'))
    have hfJ' : (f : G) ∈ J := r1s_mem_of_mk_mem_l34 hJ f.2 hf3 hfJ
    have hgf := hcomm f ⟨hmem f hf' hf3, hfJ'⟩ g hg'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (f : G) * g = ((g : G) * f * (g : G)⁻¹) * g := by rw [hgf]
      _ = g * f := by group
  have hFbab := l34abel_comm π hker hKn
    (fun d hd j hj => (mem_centralizer_iff.mp hd j hj).symm)
    (l34_reducedCentralizer_isCyclic hS hU0 hK1 hK2 hp hM hgen hJ)
    (l34_reducedCentralizer_isPGroup hS hU0 hK1 hK2 hp hM hgen hJ)
    (l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ)
    (fun A hA hAK a ha b hb => l34abel_comm_of_le hK1 hKt hA hAK ha hb)
    (hK6 _ _ hKn hKc hKt) (hK9 _ _ hKn hKc hKt)
    (fun b hb => l34abel_mem_sup hJ hR1 hb) hFb hcen
  have hcommF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    have haC : a ∈ C := hFC ha
    have hbC : b ∈ C := hFC hb
    have hab := hFbab (ρ ⟨a, haC⟩) ⟨⟨a, haC⟩, ha, rfl⟩ (ρ ⟨b, hbC⟩) ⟨⟨b, hbC⟩, hb, rfl⟩
    have hk1 : ρ ((⟨a, haC⟩ : C) * ⟨b, hbC⟩ * (⟨a, haC⟩ : C)⁻¹ * (⟨b, hbC⟩ : C)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
      group
    have hkF : a * b * a⁻¹ * b⁻¹ ∈ F :=
      F.mul_mem (F.mul_mem (F.mul_mem ha hb) (F.inv_mem ha)) (F.inv_mem hb)
    obtain ⟨n, hn⟩ :=
      h3elt ((⟨a, haC⟩ : C) * ⟨b, hbC⟩ * (⟨a, haC⟩ : C)⁻¹ * (⟨b, hbC⟩ : C)⁻¹) hkF
    have h1 := congrArg Subtype.val (l34abel_eq_one_of_mk hn hk1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  exact ⟨⟨fun a b => Subtype.ext (hcommF a a.2 b b.2)⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
