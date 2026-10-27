module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBIrr
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXY
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem irrPB_of_yLevel (hB : YLevelIrr) : KFactParabolicAutomizerIrrPB := by
  intro X _ _ L J U Z y p r hL hcl hpar hJL hJnb hp hp2 hcyc hUL hUJ hUp hUZ hZc hpow h3 hCZ
    hyL hyJ hyU hr hr2 hr3 hrp hrp1 hyr hynt hirr
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hJLe, T, hT, hTJ⟩ := hpar
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hZU : Z ≤ U := hUZ ▸ Subgroup.commutator_le_self U
  have ho : orderOf y ≠ 0 := (orderOf_pos y).ne'
  set o' := (orderOf y) / r ^ (orderOf y).factorization r with ho'
  have hcop : Nat.Coprime o' r := (Nat.coprime_ordCompl hr ho).symm
  set y' := y ^ o' with hy'
  have hy'r : y' ^ r ^ (orderOf y).factorization r = 1 := by
    rw [hy', ← pow_mul, ho', Nat.div_mul_cancel (Nat.ordProj_dvd _ _), pow_orderOf_eq_one]
  have hy'L : y' ∈ Subgroup.normalizer (L : Set X) := Subgroup.pow_mem _ hyL _
  have hy'J : y' ∈ Subgroup.normalizer (J : Set X) := Subgroup.pow_mem _ hyJ _
  have hy'U : y' ∈ Subgroup.normalizer (U : Set X) := Subgroup.pow_mem _ hyU _
  have hirr' : IrrAct y' U Z := (IrrAct.pow_of_coprime ⟨hZU, hirr⟩ hyr hcop)
  set A : Subgroup X := Subgroup.normalizer (L : Set X) ⊓ Subgroup.normalizer (J : Set X) with hA
  have hAL : A ≤ Subgroup.normalizer (L : Set X) := inf_le_left
  have hUA : U ≤ A := fun u hu => ⟨hUL hu, hUJ hu⟩
  have hy'A : y' ∈ A := ⟨hy'L, hy'J⟩
  set ρ : ↥A →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.RankThree.PartOne.centerQuotientAction hAL with hρ
  set U₁ : Subgroup ↥A := U.subgroupOf A with hU₁
  set Z₁ : Subgroup ↥A := Z.subgroupOf A with hZ₁
  set y₁ : ↥A := ⟨y', hy'A⟩ with hy₁
  have hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : X) ∈ J := fun z hz =>
    center_le_of_normalizer_le hT hTJ hz
  have hU₁p : IsPGroup p U₁ := hUp.comap_of_injective A.subtype A.subtype_injective
  have hUmap : U₁.map A.subtype = U := by
    rw [hU₁, Subgroup.subgroupOf_map_subtype, inf_of_le_left hUA]
  have hZmap : Z₁.map A.subtype = Z := by
    rw [hZ₁, Subgroup.subgroupOf_map_subtype, inf_of_le_left (hZU.trans hUA)]
  have hcomm₁ : ⁅U₁, U₁⁆ = Z₁ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_commutator, hUmap, hZmap, hUZ]
  have hZ₁U₁ : Z₁ ≤ U₁ := fun z hz => Subgroup.mem_subgroupOf.2 (hZU (Subgroup.mem_subgroupOf.1 hz))
  have hirr₁ : IrrAct y₁ U₁ Z₁ := IrrAct.subgroupOf hy'A hUA hirr'
  have hy₁N : y₁ ∈ Subgroup.normalizer (U₁ : Set ↥A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact Subgroup.mem_normalizer_iff.1 hy'U (h : X)
  have hker : U₁ ⊓ ρ.ker ≤ Z₁ := by
    rintro u ⟨hu, hρu⟩
    have hc := CFSG.RankThree.PartOne.commute_of_centerQuotientAction_eq_one hAL u
      (MonoidHom.mem_ker.1 hρu)
    have hmem : (u : X) ∈ U ⊓ Subgroup.centralizer (L : Set X) :=
      ⟨hu, Subgroup.mem_centralizer_iff.2 fun h hh => (hc ⟨h, hh⟩).symm⟩
    exact Subgroup.mem_subgroupOf.2 (hCZ hmem)
  have hrel : Z₁.relIndex U₁ = Z.relIndex U := by
    rw [← Subgroup.relIndex_map_map_of_injective Z₁ U₁ A.subtype_injective, hZmap, hUmap]
  have hact : ∀ a : ↥A, ∀ x : ↥L ⧸ Subgroup.center ↥L,
      x ∈ quotImage L J ↔ ρ a x ∈ quotImage L J := by
    intro a x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hρ, CFSG.RankThree.PartOne.centerQuotientAction_mk, mk_mem_quotImage_iff hZ,
      mk_mem_quotImage_iff hZ, CFSG.RankThree.PartOne.coe_normalizerMonoidHom_apply]
    exact Subgroup.mem_normalizer_iff.1 a.2.2 (l : X)
  refine hB (↥L ⧸ Subgroup.center ↥L) hcl (conj_injective_of_isQuasisimple hLq) p r hp hp2 hr hr2
    hr3 hrp (barSylow hT) (quotImage L J) (normalizer_barSylow_le_quotImage hT hTJ)
    (fun V hV hVp A hAV hA => perfectCyclicSylow_quotImage hZ hcyc hV hVp hAV hA) (U₁.map ρ)
    (Z₁.map ρ) (ρ y₁) (hU₁p.map ρ) ?_
    (IrrAct.map ρ hirr₁ hy₁N) ?_ ?_ (Subgroup.le_normalizer_map ρ ⟨y₁, hy₁N, rfl⟩) ?_ ?_ ?_
  · rw [← hcomm₁, Subgroup.map_commutator]
  · rw [relIndex_map_eq ρ hZ₁U₁ hker, hrel]
    exact h3
  · rintro _ ⟨u₁, hu₁, rfl⟩
    refine ⟨u₁ ^ p, Subgroup.mem_subgroupOf.2 ?_, map_pow ρ u₁ p⟩
    simpa using hpow _ (Subgroup.mem_subgroupOf.1 hu₁)
  · rintro _ ⟨u₁, hu₁, rfl⟩
    exact mem_normalizer_map_conj_of_iff (hact u₁)
  · exact mem_normalizer_map_conj_of_iff (hact y₁)
  · refine ⟨(orderOf y).factorization r, ?_⟩
    rw [← map_pow]
    have : y₁ ^ r ^ (orderOf y).factorization r = 1 := Subtype.ext (by simpa using hy'r)
    rw [this, map_one]

end CFSG.AGLEmbedding.ParabAutIrr
