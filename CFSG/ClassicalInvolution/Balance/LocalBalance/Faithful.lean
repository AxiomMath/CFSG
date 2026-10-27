module

public import CFSG.ClassicalInvolution.Balance.Delta
public import CFSG.ClassicalInvolution.Balance.Prop311
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved

public section

namespace CFSG.ClassicalInvolution.Balance.LocalBalance

open CFSG CFSG.LocalCores CFSG.Open CFSG.LocalAnalysis.ComponentInitial

@[expose] def _root_.CFSG.ClassicalInvolution.Balance.IsLocallyTwoBalanced (K : Type*) [Group K] :
    Prop :=
  ∀ H : Subgroup (MulAut K), (MulAut.conj : K →* MulAut K).range ≤ H →
    ∀ F : Subgroup H, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) → deltaCore F = ⊥

section Transfer

variable {X : Type*} [Group X] [Finite X]

theorem subgroupOf_involutionOddCore_le {M : Subgroup X} (m : M) :
    (CFSG.Assembly.Dichotomy.involutionOddCore (m : X)).subgroupOf M ≤
      CFSG.Assembly.Dichotomy.involutionOddCore m := by
  rw [involutionOddCore_eq_oddCoreCentralizer, involutionOddCore_eq_oddCoreCentralizer]
  have hcen : ∀ u : M, u ∈ Subgroup.centralizer ((Subgroup.zpowers m : Subgroup M) : Set M) ↔
      (u : X) ∈ Subgroup.centralizer ((Subgroup.zpowers (m : X) : Subgroup X) : Set X) := by
    intro u
    rw [centralizer_zpowers_eq, centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  apply le_oddCoreCentralizer
  · intro u hu
    exact (hcen u).mpr (oddCoreCentralizer_le_centralizer _ ((Subgroup.mem_subgroupOf).mp hu))
  · intro c hc s hs
    have hs' : (s : X) ∈ oddCoreCentralizer (Subgroup.zpowers (m : X)) :=
      (Subgroup.mem_subgroupOf).mp hs
    rw [Subgroup.mem_subgroupOf]
    change (c : X) * (s : X) * (c : X)⁻¹ ∈ oddCoreCentralizer (Subgroup.zpowers (m : X))
    exact conj_mem_oddCoreCentralizer_of_mem_centralizer ((hcen c).mp hc) hs'
  · have h1 : Nat.card ((oddCoreCentralizer (Subgroup.zpowers (m : X))).subgroupOf M) =
        Nat.card (((oddCoreCentralizer (Subgroup.zpowers (m : X))).subgroupOf M).map M.subtype) :=
      (Subgroup.card_map_of_injective M.subtype_injective).symm
    rw [h1, Subgroup.subgroupOf_map_subtype]
    exact (odd_card_oddCoreCentralizer _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

end Transfer

section Faithful

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem conjSub_eq_of_mem_normalizer {L : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (L : Set X)) : conjSub g L = L := by
  ext y
  rw [mem_conjSub_iff]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

omit [Finite X] in
theorem mem_normalizer_of_conjSub_eq {L : Subgroup X} {g : X} (hg : conjSub g L = L) :
    g ∈ Subgroup.normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have := mem_conjSub_iff (g := g) (L := L) (y := g * h * g⁻¹)
  rw [hg] at this
  have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  rw [e] at this
  exact this.symm

theorem commute_of_faithful {L : Subgroup X} (hL : IsComponent L)
    (hbal : IsLocallyTwoBalanced (L ⧸ Subgroup.center L))
    {F : Subgroup X} (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFL : ∀ f ∈ F, conjSub f L = L)
    (hFfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f)
    {D : Subgroup X} (hD : ∀ d ∈ D, conjSub d L = L)
    (hDF : ∀ f ∈ F, f ≠ 1 → D ≤ CFSG.Assembly.Dichotomy.involutionOddCore f) :
    ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
  have : Group.IsPerfect L := hL.1.1
  set M : Subgroup X := Subgroup.normalizer (L : Set X) with hM
  have hFM : F ≤ M := fun f hf => mem_normalizer_of_conjSub_eq (hFL f hf)
  have hDM : D ≤ M := fun d hd => mem_normalizer_of_conjSub_eq (hD d hd)
  let ρ : M →* MulAut (L ⧸ Subgroup.center L) :=
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom L).comp (normalizerConjHom L)
  have hker : ρ.ker = (Subgroup.centralizer (L : Set X)).subgroupOf M :=
    ker_centerQuotient_comp_normalizerConjHom L
  have hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      ρ.range := inner_le_range_centerQuotient_comp L
  let φ : M →* ρ.range := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hφker : φ.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  set F' : Subgroup M := F.subgroupOf M with hF'
  have hFinj : ∀ m ∈ F', φ m = 1 → m = 1 := by
    intro m hm hm1
    have h1 : m ∈ ρ.ker := by rw [← hφker]; exact hm1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    by_contra hne
    refine hFfaith (m : X) ((Subgroup.mem_subgroupOf).mp hm) (fun h => hne (Subtype.ext h)) ?_
    intro x hx
    exact (h1 x hx).symm
  have hcard : Nat.card (F'.map φ) = 4 := by
    have hbij : Function.Bijective (φ.subgroupMap F') := by
      refine ⟨?_, φ.subgroupMap_surjective F'⟩
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro m hm
      have := hFinj m m.2 (by
        have h2 := (MonoidHom.mem_ker.mp hm)
        have h3 := congrArg Subtype.val h2
        exact h3)
      exact Subtype.ext this
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), ← hF4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
  have hexp : ∀ g ∈ F'.map φ, g * g = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hF2 m ((Subgroup.mem_subgroupOf).mp hm))
    rw [this, map_one]
  have hdelta : deltaCore (F'.map φ) = ⊥ := hbal ρ.range hInn (F'.map φ) hcard hexp
  have hDle : (D.subgroupOf M).map φ ≤ deltaCore (F'.map φ) := by
    refine le_deltaCore fun g hg hg1 => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    have hmF : (m : X) ∈ F := (Subgroup.mem_subgroupOf).mp hm
    have hm1 : (m : X) ≠ 1 := by
      intro h
      have hm1' : m = 1 := Subtype.ext h
      exact hg1 (by rw [hm1']; exact map_one φ)
    have hDm : D.subgroupOf M ≤ CFSG.Assembly.Dichotomy.involutionOddCore m := fun u hu =>
      subgroupOf_involutionOddCore_le m
        ((Subgroup.mem_subgroupOf).mpr (hDF (m : X) hmF hm1 ((Subgroup.mem_subgroupOf).mp hu)))
    exact (Subgroup.map_mono hDm).trans
      (map_involutionOddCore_le φ hφ (isPGroup_zpowers_of_mul_self_eq_one
        (Subtype.ext (hF2 (m : X) hmF) : m * m = 1)))
  rw [hdelta] at hDle
  intro d hd x hx
  have hmem : φ ⟨d, hDM hd⟩ ∈ (⊥ : Subgroup (ρ.range)) :=
    hDle ⟨⟨d, hDM hd⟩, (Subgroup.mem_subgroupOf).mpr hd, rfl⟩
  have h1 : (⟨d, hDM hd⟩ : M) ∈ φ.ker := Subgroup.mem_bot.mp hmem
  rw [hφker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

end Faithful

end CFSG.ClassicalInvolution.Balance.LocalBalance
