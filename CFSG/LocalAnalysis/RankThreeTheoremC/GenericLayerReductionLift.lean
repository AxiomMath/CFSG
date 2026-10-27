module

public import CFSG.LocalAnalysis.ComponentClassification.Components
import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux
import CFSG.LieType.CurtisTits.Recognition
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

open CFSG.Open Subgroup

section PerfectCore

variable {H : Type*} [Group H]

def perfectCore (N : Subgroup H) : Subgroup H :=
  sSup {K : Subgroup H | K ≤ N ∧ ⁅K, K⁆ = K}

theorem perfectCore_le (N : Subgroup H) : perfectCore N ≤ N :=
  sSup_le fun _ hK => hK.1

theorem le_perfectCore {N K : Subgroup H} (hKN : K ≤ N) (hK : ⁅K, K⁆ = K) :
    K ≤ perfectCore N :=
  le_sSup ⟨hKN, hK⟩

theorem commutator_perfectCore (N : Subgroup H) :
    ⁅perfectCore N, perfectCore N⁆ = perfectCore N := by
  refine le_antisymm ?_ (sSup_le fun K hK => ?_)
  · simpa only [sup_idem] using Subgroup.commutator_le_sup (perfectCore N) (perfectCore N)
  · rw [← hK.2]
    exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem normal_perfectCore (N : Subgroup H) [N.Normal] : (perfectCore N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : perfectCore N ≤ (perfectCore N).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_perfectCore ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact ‹N.Normal›.conj_mem k (hK.1 hk) g
    · rw [← Subgroup.map_commutator, hK.2]
  simpa using h hn


theorem map_perfectCore_comap {Q : Type*} [Finite H] [Group Q] (f : H →* Q)
    (hf : Function.Surjective f) (Lb : Subgroup Q) [Lb.Normal] (hLb : ⁅Lb, Lb⁆ = Lb) :
    (perfectCore (Lb.comap f)).map f = Lb := by
  have : Group.IsPerfect Lb := Subgroup.isPerfect_iff.mpr hLb
  obtain ⟨lift, -, hmap, hperf, -⟩ :=
    CFSG.ComponentClassification.Components.perfect_subnormal_lift f hf Lb
      (‹Lb.Normal›).isSubnormal
  have hl : ⁅lift, lift⁆ = lift := Subgroup.isPerfect_iff.mp ⟨hperf⟩
  have hle : lift ≤ Lb.comap f := by rw [← Subgroup.map_le_iff_le_comap, hmap]
  refine le_antisymm ((Subgroup.map_mono (perfectCore_le _)).trans (Subgroup.map_comap_le f Lb)) ?_
  calc Lb = lift.map f := hmap.symm
    _ ≤ (perfectCore (Lb.comap f)).map f := Subgroup.map_mono (le_perfectCore hle hl)

end PerfectCore

section Components

variable {G : Type} [Group G]

theorem isComponentOf_subgroupOf {K C : Subgroup G} (hK : IsComponentOf K C) :
    IsComponentOf (K.subgroupOf C) ⊤ :=
  ⟨le_top, CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
    (CFSG.AGLEmbedding.NoXBlock.isSubnormal_subgroupOf_of_open hK.2.1),
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hK.1) hK.2.2⟩

theorem isComponentOf_map_subtype {C : Subgroup G} {K : Subgroup C} (hK : IsComponentOf K ⊤) :
    IsComponentOf (K.map C.subtype) C := by
  refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
  · have h := CFSG.ComponentClassification.Components.chain_map C.subtype hK.2.1
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (K.equivMapOfInjective C.subtype C.subtype_injective).symm hK.2.2

theorem isQuasisimple_iff_cfsg (Q : Type*) [Group Q] :
    CFSG.Open.IsQuasisimple Q ↔ CFSG.IsQuasisimple Q := by
  constructor
  · intro h
    exact ⟨Group.isPerfect_def.mpr h.1, h.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1.commutator_eq_top, h2⟩

theorem map_eq_bot_or_isComponentOf {H Q : Type*} [Group H] [Group Q] (f : H →* Q)
    (hf : Function.Surjective f) {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    K.map f = ⊥ ∨ IsComponentOf (K.map f) ⊤ := by
  by_cases h : K.map f = ⊥
  · exact Or.inl h
  refine Or.inr ⟨le_top, ?_, ?_⟩
  · have := CFSG.ComponentClassification.Components.chain_map f hK.2.1
    rwa [Subgroup.map_top_of_surjective f hf] at this
  · let φ : K →* K.map f := (f.comp K.subtype).codRestrict (K.map f)
      fun k => Subgroup.mem_map_of_mem f k.2
    have hφ : Function.Surjective φ := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    have hne : ∃ k, φ k ≠ 1 := by
      by_contra hno
      push Not at hno
      apply h
      rw [eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      have := hno ⟨k, hk⟩
      have h1 : f k = 1 := congrArg Subtype.val this
      simp [h1]
    exact (isQuasisimple_iff_cfsg _).mpr
      (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
        ((isQuasisimple_iff_cfsg _).mp hK.2.2) hφ hne)

end Components

section LiftToG

variable {G : Type} [Group G] {p : ℕ} {C : Subgroup G}

theorem normal_subgroupOf_map_subtype (J : Subgroup C) [J.Normal] :
    ((J.map C.subtype).subgroupOf C).Normal := by
  have h : (J.map C.subtype).subgroupOf C = J :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
  rw [h]
  infer_instance

theorem le_normalizer_map_subtype (J : Subgroup C) [J.Normal] :
    C ≤ normalizer ((J.map C.subtype : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le J)).mp
    (normal_subgroupOf_map_subtype J)

theorem commutator_map_subtype (J : Subgroup C) (hJ : ⁅J, J⁆ = J) :
    ⁅J.map C.subtype, J.map C.subtype⁆ = J.map C.subtype := by
  rw [← Subgroup.map_commutator, hJ]

theorem rankThreePrimeCore_map_subtype [Finite G] (J : Subgroup C) [J.Normal] :
    rankThreePrimeCore p (J.map C.subtype) =
      (J ⊓ primeComplementCore (G := C) p).map C.subtype := by
  have hJC : J.map C.subtype ≤ C := Subgroup.map_subtype_le J
  have hn : ((J.map C.subtype).subgroupOf C).Normal := normal_subgroupOf_map_subtype J
  have hsub : IsSubnormal (J.map C.subtype) C := IsSubnormal.step hJC hn (IsSubnormal.refl C)
  apply le_antisymm
  · have h1 : GLBPrimeCore p (J.map C.subtype) ≤ GLBPrimeCore p C := by
      rw [glbPrimeCore_eq_primeComplementCoreOf, glbPrimeCore_eq_primeComplementCoreOf]
      exact cfsg_subnormal_primeComplementCoreOf_le p hsub
    have h2 : GLBPrimeCore p C = (primeComplementCore (G := C) p).map C.subtype :=
      glbPrimeCore_eq_primeComplementCoreOf p C
    have h3 : GLBPrimeCore p (J.map C.subtype) ≤ J.map C.subtype := glbPrimeCore_le p _
    rw [Subgroup.map_inf _ _ C.subtype C.subtype_injective]
    exact le_inf h3 (h2 ▸ h1)
  · have hcop : p.Coprime (Nat.card ((J ⊓ primeComplementCore (G := C) p).map C.subtype)) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact (primeComplementCore_coprime p).of_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    refine le_glbPrimeCore (Subgroup.map_mono inf_le_left) ?_ hcop
    exact hJC.trans (le_normalizer_map_subtype (J ⊓ primeComplementCore (G := C) p))


section Lattice

variable [Finite G]

theorem eq_or_eq_of_normal [Fact p.Prime] (J : Subgroup C) [J.Normal]
    (hsimple : IsSimpleGroup ↥(J.map (QuotientGroup.mk' (primeComplementCore (G := C) p))))
    (N : Subgroup G) (hNJ : N ≤ J.map C.subtype)
    (hNn : (N.subgroupOf (J.map C.subtype)).Normal)
    (hON : rankThreePrimeCore p (J.map C.subtype) ≤ N) :
    N = rankThreePrimeCore p (J.map C.subtype) ∨ N = J.map C.subtype := by
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  rw [rankThreePrimeCore_map_subtype] at hON ⊢
  have hJC : (J.map C.subtype).subgroupOf C = J :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
  set NC : Subgroup C := N.subgroupOf C with hNC
  have hNCJ : NC ≤ J := by
    intro n hn
    have : (n : G) ∈ J.map C.subtype := hNJ hn
    obtain ⟨j, hj, hjn⟩ := this
    have : j = n := Subtype.ext hjn
    exact this ▸ hj
  have hN : N = NC.map C.subtype := by
    rw [hNC, Subgroup.map_subgroupOf_eq_of_le (hNJ.trans (Subgroup.map_subtype_le J))]
  have hconj : ∀ n ∈ NC, ∀ j ∈ J, j * n * j⁻¹ ∈ NC := by
    intro n hn j hj
    have hjG : (j : G) ∈ J.map C.subtype := ⟨j, hj, rfl⟩
    have := (Subgroup.normal_subgroupOf_iff hNJ).mp hNn n j hn hjG
    exact this
  have hNb : ((NC.map π).subgroupOf (J.map π)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNCJ)]
    rintro h k ⟨n, hn, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨j * n * j⁻¹, hconj n hn j hj, by simp⟩
  have := hNb
  rcases hsimple.eq_bot_or_eq_top_of_normal ((NC.map π).subgroupOf (J.map π)) with h | h
  ·
    left
    have hbot : NC.map π = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact (disjoint_iff_inf_le.mp h |> fun h' => eq_bot_iff.mpr (le_inf le_rfl
        (Subgroup.map_mono hNCJ) |>.trans h'))
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
    rw [hN]
    refine le_antisymm (Subgroup.map_mono (le_inf hNCJ hbot)) ?_
    rw [← hN]; exact hON
  ·
    right
    rw [Subgroup.subgroupOf_eq_top] at h
    have hJN : J ≤ NC := by
      intro j hj
      obtain ⟨n, hn, hnj⟩ := h (Subgroup.mem_map_of_mem π hj)
      have hker : n⁻¹ * j ∈ O := by
        have : π (n⁻¹ * j) = 1 := by rw [map_mul, map_inv, hnj, inv_mul_cancel]
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      have hmem : (n⁻¹ * j : C) ∈ J ⊓ O := ⟨J.mul_mem (J.inv_mem (hNCJ hn)) hj, hker⟩
      have hNmem : ((n⁻¹ * j : C) : G) ∈ N := hON (Subgroup.mem_map_of_mem _ hmem)
      have : n⁻¹ * j ∈ NC := hNmem
      simpa using NC.mul_mem hn this
    rw [hN]
    exact congrArg (Subgroup.map C.subtype) (le_antisymm hNCJ hJN)


theorem rankThreePrimeCore_map_subtype_lt [Fact p.Prime] (J : Subgroup C) [J.Normal]
    (hJ : J.map (QuotientGroup.mk' (primeComplementCore (G := C) p)) ≠ ⊥) :
    rankThreePrimeCore p (J.map C.subtype) < J.map C.subtype := by
  rw [rankThreePrimeCore_map_subtype]
  refine lt_of_le_of_ne (Subgroup.map_mono inf_le_left) fun h => hJ ?_
  have h1 : J ⊓ primeComplementCore (G := C) p = J := Subgroup.map_injective C.subtype_injective h
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact h1 ▸ inf_le_right

theorem nonempty_mulEquiv_quotient_center [Fact p.Prime] (J : Subgroup C) [J.Normal]
    (hcenter : center ↥(J.map (QuotientGroup.mk' (primeComplementCore (G := C) p))) = ⊥)
    (hRQ : rankThreePrimeCore p (J.map C.subtype) ≤
      centralizer ((J.map C.subtype : Subgroup G) : Set G)) :
    Nonempty (↥(J.map C.subtype) ⧸ center ↥(J.map C.subtype) ≃*
      ↥(J.map (QuotientGroup.mk' (primeComplementCore (G := C) p)))) := by
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  let e : J ≃* J.map C.subtype := J.equivMapOfInjective C.subtype C.subtype_injective
  let ψ₀ : J →* J.map π := (π.comp J.subtype).codRestrict (J.map π)
    fun j => Subgroup.mem_map_of_mem π j.2
  let ψ : J.map C.subtype →* J.map π := ψ₀.comp e.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨e ⟨j, hj⟩, by simp [ψ, ψ₀]⟩
  have hcoe : ∀ a : J.map C.subtype, (((e.symm a : J) : C) : G) = (a : G) := by
    intro a
    conv_rhs => rw [← e.apply_symm_apply a]
    rfl
  have hker : ψ.ker = center ↥(J.map C.subtype) := by
    ext a
    constructor
    · intro ha
      have h1 : π ((e.symm a : J) : C) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
        simpa [ψ, ψ₀] using this
      have h2 : ((e.symm a : J) : C) ∈ O := by
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h3 : (a : G) ∈ rankThreePrimeCore p (J.map C.subtype) := by
        rw [rankThreePrimeCore_map_subtype]
        exact ⟨((e.symm a : J) : C), ⟨(e.symm a).2, h2⟩, hcoe a⟩
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp (hRQ h3) g g.2)
    · intro ha
      rw [MonoidHom.mem_ker]
      have : ψ a ∈ center ↥(J.map π) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨b, rfl⟩ := hψ y
        rw [← map_mul, ← map_mul, mem_center_iff.mp ha b]
      rwa [hcenter, mem_bot] at this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩


theorem le_map_perfectCore_of_isComponentOf (hodd : Odd (Nat.card (primeComplementCore (G := C) p)))
    (Lb : Subgroup (C ⧸ primeComplementCore (G := C) p))
    (huniq : ∀ L' : Subgroup (C ⧸ primeComplementCore (G := C) p), IsComponentOf L' ⊤ → L' = Lb)
    {K : Subgroup G} (hK : IsComponentOf K C) :
    K ≤ (perfectCore (Lb.comap (QuotientGroup.mk' (primeComplementCore (G := C) p)))).map
      C.subtype := by
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have hKC := isComponentOf_subgroupOf hK
  have hK' : K = (K.subgroupOf C).map C.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hK.1).symm
  have hperf : ⁅K.subgroupOf C, K.subgroupOf C⁆ = K.subgroupOf C :=
    Subgroup.isPerfect_iff.mp ⟨hKC.2.2.1⟩
  rcases map_eq_bot_or_isComponentOf π (QuotientGroup.mk'_surjective O) hKC with h | h
  · exfalso
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
    have hodd' : Odd (Nat.card (K.subgroupOf C)) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le h)
    have hsolv : Group.IsSolvable ↥(K.subgroupOf C) := CFSG.Milestones.odd_order_solvable hodd'
    have : Group.IsPerfect ↥(K.subgroupOf C) := ⟨hKC.2.2.1⟩
    have : Nontrivial ↥(K.subgroupOf C) := by
      have : IsSimpleGroup (↥(K.subgroupOf C) ⧸ center ↥(K.subgroupOf C)) := hKC.2.2.2
      exact (QuotientGroup.mk'_surjective (center ↥(K.subgroupOf C))).nontrivial
    exact Group.IsPerfect.not_isSolvable _ hsolv
  · have hL : (K.subgroupOf C).map π = Lb := huniq _ h
    have hle : K.subgroupOf C ≤ Lb.comap π := by
      rw [← Subgroup.map_le_iff_le_comap, hL]
    rw [hK']
    exact Subgroup.map_mono (le_perfectCore hle hperf)

end Lattice


end LiftToG

end CFSG.LocalAnalysis.RankThreeTheoremC
