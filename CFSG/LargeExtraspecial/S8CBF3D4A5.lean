module

public import CFSG.LargeExtraspecial.S8CBF3D4Cfg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped commutatorElement

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
include hσ

theorem false_of_a5Config_of_long (hσ1 : ∃ c, σ c ≠ c) (hK : 8 ≤ Nat.card K)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {s : ModGL TwistTag.D4.tag K} {R N : Subgroup (ModGL TwistTag.D4.tag K)}
    (h : A5Config (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) s R N)
    (hCP : ∀ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ centralizer ({s} : Set _),
      x ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J)
    {k : ModGL TwistTag.D4.tag K} (hk : k ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hks : k * s * k⁻¹ ∈ heightSeries TwistTag.D4.tag K 5)
    (hRt : ∀ (p : graphFixedParabolic TwistTag.D4 K σ.toRingHom J →*
        graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J),
      (∀ x, p x = 1 ↔ (x : ModGL TwistTag.D4.tag K) ∈
        graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) →
      Nat.card (projImage p R) = 60) : False := by
  have hK4 : 4 ≤ Nat.card K := by omega
  set D : RootWeightDatum K := .fixed TwistTag.D4 σ hσ with hD
  have hRP : R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J :=
    fun x hx => hCP x (h.le_centralizer hx)
  obtain ⟨-, p, hp, -⟩ := exists_graphFixedParabolic_proj σ J
  have hR60 := hRt p hp
  obtain ⟨f, hf, hfC⟩ := exists_sl2_le_centralizer_of_long σ hσ hk hks
  have hMC : f.range ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ centralizer ({s} : Set _) := by
    rintro _ ⟨x, rfl⟩
    exact mem_inf.2 ⟨(hfC x).1, mem_centralizer_singleton_iff.2 (hfC x).2⟩
  have hMP : f.range ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J :=
    fun x hx => hCP x (hMC hx)
  have hSL : ⁅(⊤ : Subgroup (SL2 K)), ⊤⁆ = ⊤ :=
    (_root_.commutator_def _).symm.trans
      (RankThree.PartOne.KCOrthogonal.sl2_isPerfect (F := K) hK4).commutator_eq_top
  have hMperf : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, hSL]
  have hMR : ∀ m ∈ f.range, ∀ r ∈ R, m * r * m⁻¹ ∈ R :=
    conj_mem_of_perfect_of_sq hMperf fun c hc r hr => h.sq c (hMC hc) r hr
  have hMQ : ∀ x, f x ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J → x = 1 := by
    have hTn : (Subgroup.comap f (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J)).Normal :=
      ⟨fun t ht g => by
        rw [mem_comap, map_mul, map_mul, map_inv]
        exact D.conj_mem_radical J (hMP ⟨g, rfl⟩) ht⟩
    have hT2 : IsPGroup 2
        (Subgroup.comap f (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J)) :=
      (D.isPGroup_radical 2 J).comap_of_injective f hf
    have hT := sl2_eq_bot_of_isPGroup_of_normal hK4 _ hT2 hTn
    intro x hx
    have hx' : x ∈ Subgroup.comap f (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
      hx
    rw [hT, mem_bot] at hx'
    exact hx'
  let θ₀ : SL2 K →* graphFixedParabolic TwistTag.D4 K σ.toRingHom J :=
    f.codRestrict _ fun x => hMP ⟨x, rfl⟩
  let θ : SL2 K →* ModGL TwistTag.D4.tag K :=
    (graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J).subtype.comp (p.comp θ₀)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : p (θ₀ x) = 1 := Subtype.ext hx
    exact hMQ x ((hp _).1 h1)
  have hθM : ∀ x, θ x ∈ projImage p f.range := fun x =>
    mem_projImage_of_mem p (⟨x, rfl⟩ : f x ∈ f.range) (hMP ⟨x, rfl⟩)
  obtain ⟨hMA, -⟩ := projImage_le_leviRoot σ p hMP hMperf h.isPGroup
  obtain ⟨hRA, -⟩ := projImage_le_leviRoot σ p hRP h.perfect h.isPGroup
  have hLΓ : ∀ H : Subgroup (ModGL TwistTag.D4.tag K), projImage p H ≤
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := fun H =>
    (projImage_le p H).trans (inf_le_right.trans (graphFixedRootGroup_le _ _ _))
  rcases orbitUnion_subset_of_ne_univ hJ with hA | hA
  ·
    obtain ⟨c, hc⟩ := hσ1
    have hle : leviRoot K (TwistTag.D4.orbitUnion J) ≤
        (rankOneHom TwistTag.D4 K (ν 2)).range := by
      rw [rankOneHom_range, ← leviRoot_singleton]
      exact leviRoot_mono hA
    have hρ := rankOneHom_injective K (ν 2)
    have hθρ : ∀ x, θ x ∈ (rankOneHom TwistTag.D4 K (ν 2)).range := fun x => hle (hMA (hθM x))
    let F : SL2 K →* SL2 K := (MonoidHom.ofInjective hρ).symm.toMonoidHom.comp
      (θ.codRestrict _ hθρ)
    have hF : ∀ x, rankOneHom TwistTag.D4 K (ν 2) (F x) = θ x := fun x => by
      have := (MonoidHom.ofInjective hρ).apply_symm_apply ⟨θ x, hθρ x⟩
      exact congrArg Subtype.val this
    have hFinj : Function.Injective F := fun x y hxy => hθ (by rw [← hF, ← hF, hxy])
    have hfix : ∀ x, Matrix.SpecialLinearGroup.map σ.toRingHom (F x) = F x := fun x => by
      apply hρ
      have h1 := twistHom_rankOneHom K σ.toRingHom (ν 2) (F x)
      rw [show TwistTag.D4.perm (ν 2) = ν 2 by decide, hF] at h1
      rw [← h1, hF]
      exact ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hLΓ _ (hθM x))).2
    exact hc (eq_of_sl2_injective_fixed σ.toRingHom F hFinj hfix c)
  ·
    set H := leviRoot K outerSet ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom with hH
    have hMH : projImage p f.range ≤ H := le_inf (hMA.trans (leviRoot_mono hA)) (hLΓ _)
    have hRH : projImage p R ≤ H := le_inf (hRA.trans (leviRoot_mono hA)) (hLΓ _)
    set ι := outerFirst K σ.toRingHom with hι
    have hιi := outerFirst_injective K σ.toRingHom
    set M' := ((projImage p f.range).subgroupOf H).map ι with hM'
    set R' := ((projImage p R).subgroupOf H).map ι with hR'
    have hcardM : Nat.card (projImage p f.range) = Nat.card (SL2 K) := by
      refine le_antisymm ?_ ?_
      · have := card_projImage_mul p hp hMP
        rw [MonoidHom.range_eq_map] at this ⊢
        rw [card_map_of_injective hf, card_top] at this
        calc Nat.card (projImage p (map f ⊤)) ≤ Nat.card (projImage p (map f ⊤)) *
              Nat.card ↥(map f ⊤ ⊓ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
              Nat.le_mul_of_pos_right _ Nat.card_pos
          _ = Nat.card (SL2 K) := this
      · exact Nat.card_le_card_of_injective (fun x => (⟨θ x, hθM x⟩ : projImage p f.range))
          fun x y hxy => hθ (congrArg (fun z : projImage p f.range =>
            (z : ModGL TwistTag.D4.tag K)) hxy)
    have hM'top : M' = ⊤ := by
      apply eq_top_of_card_eq
      rw [hM', card_map_of_injective hιi, ← hcardM]
      exact Nat.card_congr (subgroupOfEquivOfLe hMH).toEquiv
    have hR'n : R'.Normal := by
      refine ⟨fun r hr g => ?_⟩
      have hg : g ∈ M' := hM'top ▸ mem_top g
      obtain ⟨m, hm, rfl⟩ := hg
      obtain ⟨r₀, hr₀, rfl⟩ := hr
      rw [SetLike.mem_coe, mem_subgroupOf] at hm hr₀
      refine ⟨m * r₀ * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact projImage_conj_mem p hMR _ hm _ hr₀
    have hcardR : Nat.card R' = 60 := by
      rw [hR', card_map_of_injective hιi, ← hR60]
      exact Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv
    exact sl2_card_normal_ne_sixty hK R' hR'n hcardR

theorem card_lt_of_a5Config_of_le (hσ1 : ∃ c, σ c ≠ c) (hK : 8 ≤ Nat.card K)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {s : ModGL TwistTag.D4.tag K} {R N : Subgroup (ModGL TwistTag.D4.tag K)}
    (h : A5Config (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) s R N)
    (hCP : ∀ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ centralizer ({s} : Set _),
      x ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J) : Nat.card N < 2 ^ 9 := by
  set D : RootWeightDatum K := .fixed TwistTag.D4 σ hσ with hD
  have hRP : R ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J :=
    fun x hx => hCP x (h.le_centralizer hx)
  have hNQ : N ≤ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :=
    le_graphFixedParabolicRadical_of_perfect σ hJ hRP h.le h.perfect h.isPGroup h.normal
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hRQ : R ⊓ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J = N := by
    rcases h.maximal _ (le_inf h.le hNQ) inf_le_left (fun r hr x hx =>
        mem_inf.2 ⟨mul_mem (mul_mem hr (mem_inf.1 hx).1) (inv_mem hr),
          D.conj_mem_radical J (hRP hr) (mem_inf.1 hx).2⟩) with h1 | h1
    · exact h1
    · exfalso
      have hRQ' : R ≤ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J := by
        rw [← h1]
        exact inf_le_right
      have hR2 : IsPGroup 2 R := (D.isPGroup_radical 2 J).to_le hRQ'
      have hcard := h.card
      rw [eq_bot_of_perfect_of_isPGroup h.perfect hR2, card_bot] at hcard
      omega
  have hRt : ∀ (p : graphFixedParabolic TwistTag.D4 K σ.toRingHom J →*
        graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J),
      (∀ x, p x = 1 ↔ (x : ModGL TwistTag.D4.tag K) ∈
        graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) →
      Nat.card (projImage p R) = 60 := by
    intro p hp
    have hc := card_projImage_mul p hp hRP
    rw [hRQ, h.card] at hc
    exact Nat.eq_of_mul_eq_mul_right hNpos hc
  by_cases hlong : ∃ k ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      k * s * k⁻¹ ∈ heightSeries TwistTag.D4.tag K 5
  · obtain ⟨k, hk, hks⟩ := hlong
    exact (false_of_a5Config_of_long σ hσ hσ1 hK hJ h hCP hk hks hRt).elim
  · obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian
    have hsxy : ⁅x, y⁆ = s := (h.commutator x hx y hy).resolve_left fun h1 =>
      hxy (commutatorElement_eq_one_iff_mul_comm.1 h1)
    have hsQQ : s ∈ ⁅graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J,
        graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J⁆ :=
      hsxy ▸ commutator_mem_commutator (hNQ hx) (hNQ hy)
    have hsΓ : s ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedRootGroup_le _ _ _ h.s_mem
    by_cases h0 : (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J <;>
      by_cases h1 : (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J
    · exact absurd (Set.eq_univ_of_forall fun i => by fin_cases i <;> assumption) hJ
    ·
      have hJ0 : J = {⟨0, by decide⟩} := by
        ext i
        fin_cases i <;> simp [h0, h1, Fin.ext_iff]
      subst hJ0
      have hle : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {⟨0, by decide⟩} ≤
          parabolicRadical TwistTag.D4.tag K outerSet :=
        inf_le_left.trans (le_of_eq (by rw [orbitUnion_outer]))
      have hs5 := commutator_parabolicRadical_outer_le K (commutator_mono hle hle hsQQ)
      exact (hlong ⟨1, one_mem _, by simpa using hs5⟩).elim
    ·
      have hJ1 : J = {⟨1, by decide⟩} := by
        ext i
        fin_cases i <;> simp [h0, h1, Fin.ext_iff]
      subst hJ1
      have hle : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩} ≤
          parabolicRadical TwistTag.D4.tag K {ν 2} :=
        inf_le_left.trans (le_of_eq (by rw [orbitUnion_middle]))
      have hs3 := commutator_parabolicRadical_middle_le K (commutator_mono hle hle hsQQ)
      by_cases hs4 : s ∈ heightSeries TwistTag.D4.tag K 4
      · obtain ⟨k, hk, hks⟩ := exists_conj_mem_heightSeries_five σ hσ hs4 hsΓ
        exact (hlong ⟨k, hk, hks⟩).elim
      · calc Nat.card N ≤ 2 ^ 7 :=
            card_le_of_middle σ hσ hs3 hs4 hNQ h.s_mem_N h.center h.commutator
          _ < 2 ^ 9 := by norm_num
    ·
      have hJe : J = ∅ := by
        ext i
        fin_cases i <;> simp [h0, h1]
      subst hJe
      obtain ⟨-, p, hp, -⟩ := exists_graphFixedParabolic_proj σ ∅
      obtain ⟨hRA, -⟩ := projImage_le_leviRoot σ p hRP h.perfect h.isPGroup
      have hbot : leviRoot K (TwistTag.D4.orbitUnion ∅) = ⊥ := by
        rw [eq_bot_iff, leviRoot, closure_le]
        rintro _ ⟨j, hj, -⟩
        simp [TwistTag.orbitUnion] at hj
      have h60 := hRt p hp
      rw [eq_bot_iff.2 (hRA.trans hbot.le), card_bot] at h60
      omega

theorem card_lt_of_a5Config (hσ1 : ∃ c, σ c ≠ c) (hK : 8 ≤ Nat.card K)
    {s : ModGL TwistTag.D4.tag K} {R N : Subgroup (ModGL TwistTag.D4.tag K)}
    (h : A5Config (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) s R N) :
    Nat.card N < 2 ^ 9 := by
  obtain ⟨g, hg, J, hJ, hCP⟩ :=
    exists_centralizer_le_graphFixedParabolic σ hσ h.s_mem h.orderOf_s
  have h' := h.conj (inv_mem hg)
  have hCP' : ∀ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      centralizer ({g⁻¹ * s * g⁻¹⁻¹} : Set _),
      x ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
    intro x hx
    obtain ⟨hxC, hxs⟩ := mem_inf.1 hx
    rw [mem_centralizer_singleton_iff] at hxs
    have hy : g * x * g⁻¹ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        centralizer ({s} : Set _) := by
      refine mem_inf.2 ⟨mul_mem (mul_mem hg hxC) (inv_mem hg), ?_⟩
      rw [mem_centralizer_singleton_iff]
      calc g * x * g⁻¹ * s = g * (x * (g⁻¹ * s * g⁻¹⁻¹)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * s * g⁻¹⁻¹) * x) * g⁻¹ := by rw [hxs]
        _ = s * (g * x * g⁻¹) := by group
    have h1 := hCP _ hy
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h1
  rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective]
  exact card_lt_of_a5Config_of_le σ hσ hσ1 hK hJ h' hCP'

end CFSG.LargeExtraspecial.S8
