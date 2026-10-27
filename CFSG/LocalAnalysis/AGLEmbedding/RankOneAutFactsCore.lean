module

public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicLift
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SylowIntersectionNormalizerGrowth

public section

namespace CFSG.AGLEmbedding.RankOneAut

open CFSG.Open CFSG.AGLEmbedding.KFactProofs.RankOneCore
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup)
open scoped commutatorElement

theorem kSylowTI_of_rankOneCoreData {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : ∀ U : Sylow p K, RankOneCoreData K (U : Subgroup K)) : KSylowTI p K := by
  intro U V hUV
  by_contra hne
  have hle : ¬ (U : Subgroup K) ≤ V := fun hle =>
    hne (Sylow.ext (U.is_maximal' V.isPGroup' hle).symm)
  refine CFSG.GorensteinWalter.sylow_intersection_not_le_of_inner_normalizer_le U V V hle ?_
    inf_le_right
  intro x hx
  have h1 : x ∈ (U : Subgroup K) ⊓ Subgroup.normalizer (V : Set K) :=
    ⟨hx.1, (h V).normalizer_le _ inf_le_right hUV hx.2⟩
  rw [IsPGroup.inf_normalizer_sylow U.isPGroup' V] at h1
  exact h1.2

theorem inf_normalizer_eq_bot_of_ti {K : Type} [Group K] {p : ℕ} (hTI : KSylowTI p K)
    {U V : Sylow p K} (hUV : U ≠ V) :
    (U : Subgroup K) ⊓ Subgroup.normalizer (V : Set K) = ⊥ := by
  rw [IsPGroup.inf_normalizer_sylow U.isPGroup' V]
  by_contra h
  exact hUV (hTI U V h)

theorem exists_map_conj_eq_of_ti {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hTI : KSylowTI p K) (U V W : Sylow p K) (hV : V ≠ U) (hW : W ≠ U)
    (hcard : Nat.card (Sylow p K) = Nat.card (U : Subgroup K) + 1) :
    ∃ u ∈ (U : Subgroup K), (V : Subgroup K).map (MulAut.conj u).toMonoidHom = W := by
  classical
  have hne : ∀ u : (U : Subgroup K), (u : K) • V ≠ U := by
    intro u h
    apply hV
    have h1 : ((u : K)⁻¹ • U : Sylow p K) = U := Sylow.smul_eq_iff_mem_normalizer.2
      (Subgroup.le_normalizer (inv_mem u.2))
    exact ((smul_eq_iff_eq_inv_smul (u : K)).1 h).trans h1
  let f : ↥(U : Subgroup K) → {X : Sylow p K // X ≠ U} := fun u => ⟨(u : K) • V, hne u⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : ((v : K)⁻¹ * u) • V = V := by
      rw [mul_smul, inv_smul_eq_iff]
      exact congrArg Subtype.val huv
    have h2 : (v : K)⁻¹ * u ∈ (U : Subgroup K) ⊓ Subgroup.normalizer (V : Set K) :=
      ⟨(U : Subgroup K).mul_mem ((U : Subgroup K).inv_mem v.2) u.2,
        Sylow.smul_eq_iff_mem_normalizer.1 h1⟩
    rw [inf_normalizer_eq_bot_of_ti hTI (Ne.symm hV), Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2.symm
  have hc : Nat.card {X : Sylow p K // X ≠ U} ≤ Nat.card (U : Subgroup K) := by
    have h1 := Nat.card_congr (Equiv.optionSubtypeNe U)
    rw [Finite.card_option] at h1
    omega
  obtain ⟨u, hu⟩ := (hf.bijective_of_nat_card_le hc).2 ⟨W, hW⟩
  refine ⟨u, u.2, ?_⟩
  have h1 : ((u : K) • V : Sylow p K) = W := congrArg Subtype.val hu
  rw [← h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem kOutRankLeOne_of_outPChain {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : CFSG.RankThree.PartOne.OutStructure.OutPChain p K) : KOutRankLeOne p K := by
  intro F hF hFI
  let π : F →* Outer K := (QuotientGroup.mk' (inner K)).comp F.subtype
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (a : MulAut K) ∈ F ⊓ (MulAut.conj : K →* MulAut K).range := ⟨a.2, h1⟩
    rw [hFI, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hE : IsElemAbelian p π.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul,
        hF.1.is_comm.comm a b])
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hF.2 a a.2)
      rw [this, map_one]
  rw [Nat.card_congr (MonoidHom.ofInjective hπ).toEquiv]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.card_le_of_outPChain hp h hE

@[expose] def BorelMetabelianAt (K : Type) [Group K] (U : Subgroup K) : Prop :=
  ⁅⁅Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)),
      Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K))⁆,
    ⁅Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)),
      Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K))⁆⁆ ≤ U.map (MulAut.conj : K →* MulAut K)

theorem BorelMetabelianAt.of_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {U : Subgroup K} {U' : Subgroup K'} (hU : U.map e.toMonoidHom = U')
    (h : BorelMetabelianAt K' U') : BorelMetabelianAt K U := by
  have hc : (U.map (MulAut.conj : K →* MulAut K)).map (MulAut.congr e).toMonoidHom =
      U'.map (MulAut.conj : K' →* MulAut K') := by
    rw [← hU, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext k : 1
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e k
  unfold BorelMetabelianAt at h ⊢
  rw [← Subgroup.map_le_map_iff_of_injective (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective, Subgroup.map_commutator, Subgroup.map_commutator,
    Subgroup.map_equiv_normalizer_eq, hc]
  exact h

theorem mulAutConj_injective_of_center_eq_bot {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun x => by
    have h1 : g * x * g⁻¹ = x := by
      have := DFunLike.congr_fun hg x
      rwa [MulAut.conj_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem mem_of_mem_normalizer_map_conj {K : Type} [Group K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {U : Subgroup K} {α : MulAut K}
    (hα : α ∈ Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K))) {u : K} : α u ∈ U ↔ u ∈ U := by
  have key : α * MulAut.conj u * α⁻¹ = MulAut.conj (α u) := by
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]
  have hiff := (Subgroup.mem_normalizer_iff.1 hα) (MulAut.conj u)
  rw [key] at hiff
  have hmem : ∀ x : K, MulAut.conj x ∈ U.map (MulAut.conj : K →* MulAut K) ↔ x ∈ U :=
    fun x => Subgroup.mem_map_iff_mem hinj
  rw [hmem, hmem] at hiff
  exact hiff.symm

theorem commutator_commutator_le_of_hom {G H : Type} [Group G] [Group H] {N M : Subgroup G}
    (Ψ : N →* H) (hH : derivedSeries H 2 = ⊥) (hker : ∀ x, Ψ x = 1 → (x : G) ∈ M) :
    ⁅⁅N, N⁆, ⁅N, N⁆⁆ ≤ M := by
  have h1 : ⁅⁅N, N⁆, ⁅N, N⁆⁆ = (derivedSeries N 2).map N.subtype := by
    rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1]
  rintro _ ⟨x, hx, rfl⟩
  apply hker
  have h2 := map_derivedSeries_le_derivedSeries Ψ 2 ⟨x, hx, rfl⟩
  rwa [hH, Subgroup.mem_bot] at h2

theorem borelMetabelianAt_of_hom {K H : Type} [Group K] [Group H] {U : Subgroup K}
    (Ψ : Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) →* H) (hH : derivedSeries H 2 = ⊥)
    (hker : ∀ x, Ψ x = 1 → (x : MulAut K) ∈ U.map (MulAut.conj : K →* MulAut K)) :
    BorelMetabelianAt K U :=
  commutator_commutator_le_of_hom Ψ hH hker

theorem borelMetabelianAt_of_outer {K : Type} [Group K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hOut : ∀ α β : MulAut K, ⁅α, β⁆ ∈ inner K) {U : Subgroup K}
    (hB : ⁅Subgroup.normalizer (U : Set K), Subgroup.normalizer (U : Set K)⁆ ≤ U) :
    BorelMetabelianAt K U := by
  set N := Subgroup.normalizer ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
    Set (MulAut K))
  have h1 : ⁅N, N⁆ ≤ (Subgroup.normalizer (U : Set K)).map (MulAut.conj : K →* MulAut K) := by
    rw [Subgroup.commutator_le]
    intro α hα β hβ
    obtain ⟨g, hg⟩ := hOut α β
    have hgN : MulAut.conj g ∈ N := by
      rw [hg, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hα hβ) (N.inv_mem hα)) (N.inv_mem hβ)
    refine ⟨g, Subgroup.mem_normalizer_iff.2 fun u => ?_, hg⟩
    have h2 := mem_of_mem_normalizer_map_conj hinj hgN (u := u)
    rw [MulAut.conj_apply] at h2
    exact h2.symm
  show ⁅⁅N, N⁆, ⁅N, N⁆⁆ ≤ _
  refine (Subgroup.commutator_mono h1 h1).trans ?_
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono hB

theorem borelMetabelianAt_of_pairAut {K : Type} [Group K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {U V : Subgroup K}
    (hA : derivedSeries (pairAutSubgroup U V) 2 = ⊥)
    (htrans : ∀ α : MulAut K, U.map α.toMonoidHom = U →
      ∃ u ∈ U, V.map ((MulAut.conj u)⁻¹ * α).toMonoidHom = V) :
    BorelMetabelianAt K U := by
  set M : Subgroup (MulAut K) := U.map (MulAut.conj : K →* MulAut K)
  set N := Subgroup.normalizer (M : Set (MulAut K))
  have hmapU : ∀ α ∈ N, U.map α.toMonoidHom = U := by
    intro α hα
    ext x
    rw [Subgroup.mem_map_equiv]
    exact mem_of_mem_normalizer_map_conj hinj (inv_mem hα)
  have hAN : pairAutSubgroup U V ≤ N := by
    intro β hβ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨β u, ?_, by ext y; simp [MulAut.mul_apply, MulAut.conj_apply]⟩
      rw [← hβ.1]
      exact ⟨u, hu, rfl⟩
    · rintro ⟨w, hw, hwx⟩
      have hw' : β.symm w ∈ U := by
        have h1 : w ∈ U.map β.toMonoidHom := by rw [hβ.1]; exact hw
        exact Subgroup.mem_map_equiv.1 h1
      refine ⟨β.symm w, hw', ?_⟩
      have : x = β⁻¹ * MulAut.conj w * β := by rw [hwx]; group
      rw [this]
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]
  let Q := N ⧸ M.subgroupOf N
  have : (M.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let π : N →* Q := QuotientGroup.mk' (M.subgroupOf N)
  let ι : pairAutSubgroup U V →* N := Subgroup.inclusion hAN
  have hsurj : Function.Surjective (π.comp ι) := by
    intro y
    obtain ⟨⟨α, hα⟩, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf N) y
    obtain ⟨u, hu, huV⟩ := htrans α (hmapU α hα)
    have huN : MulAut.conj u ∈ N := Subgroup.le_normalizer ⟨u, hu, rfl⟩
    have hβ : (MulAut.conj u)⁻¹ * α ∈ pairAutSubgroup U V :=
      ⟨hmapU _ (mul_mem (inv_mem huN) hα), huV⟩
    refine ⟨⟨_, hβ⟩, ?_⟩
    show π ⟨(MulAut.conj u)⁻¹ * α, _⟩ = π ⟨α, hα⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((MulAut.conj u)⁻¹ * α)⁻¹ * α ∈ M
    have h2 := (Subgroup.mem_normalizer_iff.1 (inv_mem hα) (MulAut.conj u)).1 ⟨u, hu, rfl⟩
    rw [inv_inv] at h2
    have h3 : ((MulAut.conj u)⁻¹ * α)⁻¹ * α = α⁻¹ * MulAut.conj u * α := by group
    rw [h3]
    exact h2
  have hQ : derivedSeries Q 2 = ⊥ := by
    rw [← map_derivedSeries_eq hsurj, hA, Subgroup.map_bot]
  exact borelMetabelianAt_of_hom π hQ fun x hx => (QuotientGroup.eq_one_iff x).1 hx

end CFSG.AGLEmbedding.RankOneAut
