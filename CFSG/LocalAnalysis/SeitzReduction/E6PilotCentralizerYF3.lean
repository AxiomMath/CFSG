module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerY
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem commutator_sup_le_of_commute {N T : Subgroup G} (hTN : T ≤ normalizer (N : Set G))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : ⁅N ⊔ T, N ⊔ T⁆ ≤ N := by
  have hdec : ∀ a ∈ N ⊔ T, ∃ t ∈ T, ∃ n ∈ N, a = t * n := by
    intro a ha
    rw [sup_comm] at ha
    have ha' : a ∈ ((T ⊔ N : Subgroup G) : Set G) := ha
    rw [coe_mul_of_left_le_normalizer_right T N hTN] at ha'
    obtain ⟨t, ht, n, hn, rfl⟩ := ha'
    exact ⟨t, ht, n, hn, rfl⟩
  have hconj : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun t ht n hn =>
    (mem_normalizer_iff.1 (hTN ht) n).1 hn
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨t₁, ht₁, n₁, hn₁, rfl⟩ := hdec a ha
  obtain ⟨t₂, ht₂, n₂, hn₂, rfl⟩ := hdec b hb
  have e : ⁅t₁ * n₁, t₂ * n₂⁆ = (t₁ * n₁ * t₁⁻¹) * ((t₁ * t₂) * (n₂ * n₁⁻¹) * (t₁ * t₂)⁻¹) *
      (⁅t₁, t₂⁆ * (t₂ * n₂⁻¹ * t₂⁻¹)) := by
    simp only [commutatorElement_def]
    group
  have h12 : ⁅t₁, t₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hT t₁ ht₁ t₂ ht₂)
  rw [e, h12, one_mul]
  exact mul_mem (mul_mem (hconj t₁ ht₁ n₁ hn₁)
    (hconj _ (mul_mem ht₁ ht₂) _ (mul_mem hn₂ (inv_mem hn₁))))
    (hconj t₂ ht₂ _ (inv_mem hn₂))

theorem perfectCore_eq_of_le_sup [Finite G] {X N T : Subgroup G} (hNX : N ≤ X)
    (hN : ⁅N, N⁆ = N) (hXT : X ≤ N ⊔ T) (hTN : T ≤ normalizer (N : Set G))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : perfectCore X = N :=
  F4Pilot.perfectCore_eq_of_forall_le hNX hN fun Q hQX hQ => by
    rw [← hQ]
    exact (commutator_mono (hQX.trans hXT) (hQX.trans hXT)).trans
      (commutator_sup_le_of_commute hTN hT)

theorem mem_normalizer_closure_of_conj {S : Set G} {g : G}
    (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) (h2 : ∀ s ∈ S, g⁻¹ * s * g ∈ closure S) :
    g ∈ normalizer (closure S : Set G) := by
  have key : ∀ x : G, (∀ s ∈ S, x * s * x⁻¹ ∈ closure S) →
      ∀ n ∈ closure S, x * n * x⁻¹ ∈ closure S := by
    intro x hx n hn
    have hle : closure S ≤ (closure S).comap (MulAut.conj x).toMonoidHom :=
      (closure_le _).2 fun s hs => hx s hs
    exact hle hn
  refine mem_normalizer_iff.2 fun n => ⟨fun hn => key g h1 n hn, fun hn => ?_⟩
  have h2' : ∀ s ∈ S, g⁻¹ * s * g⁻¹⁻¹ ∈ closure S := fun s hs => by
    rw [inv_inv]
    exact h2 s hs
  have := key g⁻¹ h2' _ hn
  rwa [inv_inv, show g⁻¹ * (g * n * g⁻¹) * g = n by group] at this

end Abstract

section Torus

variable (K : Type) [Field K]

@[expose] noncomputable def yTorus : Subgroup (adjointGroup .E6 K) :=
  (torusGroup .E6 K ⊓
    centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))).subgroupOf
    (adjointGroup .E6 K)

variable {K}

theorem yTorus_commute : ∀ a ∈ yTorus K, ∀ b ∈ yTorus K, a * b = b * a := by
  intro a ha b hb
  have ha' := (mem_inf.1 (mem_subgroupOf.1 ha)).1
  have hb' := (mem_inf.1 (mem_subgroupOf.1 hb)).1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha'
  refine Subtype.ext ?_
  simp only [coe_mul]
  rw [hl]
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l hb'

theorem torusRootChar_yA_eq_one {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K)
    (hy : h ∈ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))) :
    torusRootChar h yA1 = 1 ∧ torusRootChar h yA4 = 1 := by
  have hA : IsRoot .E6 yA1 := isRoot_single _ _
  have hB : IsRoot .E6 yA4 := isRoot_single _ _
  have hy' : h * (e6Rep K 1 : ModGL .E6 K) * h⁻¹ = (e6Rep K 1 : ModGL .E6 K) := by
    rw [mem_centralizer_singleton_iff] at hy
    rw [hy, mul_inv_cancel_right]
  rw [coe_e6Rep_one] at hy'
  have e : h * (pinnedX .E6 K yA1 1 * pinnedX .E6 K yA4 1) * h⁻¹ =
      pinnedX .E6 K yA1 (torusRootChar h yA1 * 1) *
        pinnedX .E6 K yA4 (torusRootChar h yA4 * 1) := by
    rw [← conj_pinnedX_of_mem_torusGroup hh hA, ← conj_pinnedX_of_mem_torusGroup hh hB]
    group
  rw [hy'] at e
  have hne : yA1 ≠ yA4 := by decide
  have hL := pinnedX_list_prod_injective (R := K) [yA1, yA4] (by simp [hne])
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl
      · exact ⟨hA, by decide⟩
      · exact ⟨hB, by decide⟩)
    (fun α => if α = yA1 then 1 else 1)
    (fun α => if α = yA1 then torusRootChar h yA1 * 1 else torusRootChar h yA4 * 1)
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ↓reduceIte, hne.symm]
      simpa only [mul_one] using e)
  have h1 := hL yA1 (by simp)
  have h4 := hL yA4 (by simp)
  simp only [↓reduceIte, hne.symm, mul_one] at h1 h4
  exact ⟨h1.symm, h4.symm⟩

theorem torusRootChar_add_eq [CharP K 2] {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K)
    {γ ε : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (hε : IsRoot .E6 ε) (hγε : iform γ ε = -1)
    (h1 : torusRootChar h ε = 1) : torusRootChar h γ = torusRootChar h (γ + ε) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hr, hne, hne'⟩ := classD4_isRoot_add e6_simplyLaced hγ hε hγε
  have hchk := oddDerivLacedCheck_of_simplyLaced e6_simplyLaced
  have hc := commutatorElement_pinnedX_of_oddDerivLaced (R := K) h2 hchk hγ hε hne hne' hr 1 1
  have hc' : h * ⁅pinnedX .E6 K γ 1, pinnedX .E6 K ε 1⁆ * h⁻¹ =
      h * pinnedX .E6 K (γ + ε) (1 * 1) * h⁻¹ := by rw [hc]
  rw [conj_pinnedX_of_mem_torusGroup hh hr] at hc'
  have e : h * ⁅pinnedX .E6 K γ 1, pinnedX .E6 K ε 1⁆ * h⁻¹ =
      ⁅h * pinnedX .E6 K γ 1 * h⁻¹, h * pinnedX .E6 K ε 1 * h⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, conj_pinnedX_of_mem_torusGroup hh hγ, conj_pinnedX_of_mem_torusGroup hh hε, h1,
    commutatorElement_pinnedX_of_oddDerivLaced h2 hchk hγ hε hne hne' hr] at hc'
  have := pinnedX_injective .E6 K _ hc'
  simpa using this

theorem torusRootChar_yPartner [CharP K 2] {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K)
    (hy : h ∈ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)))
    {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ yPairRoots) :
    torusRootChar h (yPartner δ) = torusRootChar h δ := by
  obtain ⟨h1, h4⟩ := torusRootChar_yA_eq_one hh hy
  obtain ⟨hpr, hp1, -, -, hsum⟩ := yPartner_spec hδ
  rw [torusRootChar_add_eq hh hδ.1 (isRoot_single _ _) hδ.2.2 h4,
    torusRootChar_add_eq hh hpr (isRoot_single _ _) hp1 h1, hsum]

theorem conj_mem_yLeviGens [CharP K 2] {h : ModGL .E6 K} (hh : h ∈ torusGroup .E6 K)
    (hy : h ∈ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)))
    {g : ModGL .E6 K} (hg : g ∈ yLeviGens K) : h * g * h⁻¹ ∈ yLeviGens K := by
  rcases hg with ⟨γ, hγ, c, rfl⟩ | ⟨δ, hδ, c, rfl⟩
  · exact Or.inl ⟨γ, hγ, _, conj_pinnedX_of_mem_torusGroup hh hγ.1 c⟩
  · refine Or.inr ⟨δ, hδ, torusRootChar h δ * c, ?_⟩
    have e : h * (pinnedX .E6 K δ c * pinnedX .E6 K (yPartner δ) c) * h⁻¹ =
        (h * pinnedX .E6 K δ c * h⁻¹) * (h * pinnedX .E6 K (yPartner δ) c * h⁻¹) := by group
    rw [e, conj_pinnedX_of_mem_torusGroup hh hδ.1, conj_pinnedX_of_mem_torusGroup hh
      (yPartner_spec hδ).1, torusRootChar_yPartner hh hy hδ]

theorem torus_inf_centralizer_le_normalizer_yLeviGL [CharP K 2] :
    torusGroup .E6 K ⊓ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ≤
      normalizer (yLeviGL K : Set (ModGL .E6 K)) := by
  intro h hh
  obtain ⟨hT, hC⟩ := mem_inf.1 hh
  have hT' : h⁻¹ ∈ torusGroup .E6 K := inv_mem hT
  have hC' : h⁻¹ ∈ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := inv_mem hC
  refine mem_normalizer_closure_of_conj (fun s hs => subset_closure (conj_mem_yLeviGens hT hC hs))
    (fun s hs => ?_)
  have := conj_mem_yLeviGens hT' hC' hs
  rw [inv_inv] at this
  exact subset_closure this

theorem torus_inf_centralizer_le_normalizer_rootSpan_yRadicalRoots :
    torusGroup .E6 K ⊓ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ≤
      normalizer (rootSpan .E6 K yRadicalRoots : Set (ModGL .E6 K)) :=
  inf_le_left.trans (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)

theorem yTorus_le_normalizer [CharP K 2] :
    yTorus K ≤ normalizer ((yRadical K ⊔ yLevi K : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) := by
  have hQC : rootSpan .E6 K yRadicalRoots ≤ adjointGroup .E6 K :=
    rootSpan_le_adjointGroup K _
  have hMC : yLeviGL K ≤ adjointGroup .E6 K := yLeviGL_le_adjointGroup
  have hsup : yRadical K ⊔ yLevi K =
      (rootSpan .E6 K yRadicalRoots ⊔ yLeviGL K).subgroupOf (adjointGroup .E6 K) := by
    rw [yRadical, yLevi, subgroupOf_sup hQC hMC]
  rw [hsup]
  intro m hm
  have hm' := mem_subgroupOf.1 hm
  have hN := F4Pilot.mem_normalizer_sup
    (torus_inf_centralizer_le_normalizer_rootSpan_yRadicalRoots hm')
    (torus_inf_centralizer_le_normalizer_yLeviGL hm')
  rw [mem_normalizer_iff]
  intro y
  have hmN := mem_normalizer_iff.1 hN (y : ModGL .E6 K)
  simp only [mem_subgroupOf, coe_mul, coe_inv]
  exact hmN

end Torus

section F3

variable {K : Type} [Field K]

theorem perfectCore_centralizer_yD_eq [Finite K] [CharP K 2]
    (hperf : ⁅yRadical K ⊔ yLevi K, yRadical K ⊔ yLevi K⁆ = yRadical K ⊔ yLevi K)
    (hUB : centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K)) ≤
      yRadical K ⊔ yLevi K ⊔ yTorus K) :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
      yRadical K ⊔ yLevi K :=
  perfectCore_eq_of_le_sup yRadical_sup_yLevi_le_centralizer hperf hUB yTorus_le_normalizer
    yTorus_commute

end F3

end CFSG.SeitzReduction.E6Pilot
