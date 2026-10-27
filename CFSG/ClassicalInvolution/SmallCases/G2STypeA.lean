module

public import CFSG.ClassicalInvolution.SmallCases.G2SNorm2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace Ctx

theorem typeA_false [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (C : Ctx p f (𝒞 K) K z) (hconn : RouteD.DeltaConnected (𝒞 K)) {M M' : Subgroup G}
    (hM : M ∈ nbhd (𝒞 K) K) (hM' : M' ∈ nbhd (𝒞 K) K) (hne : M ≠ M') {t s : G}
    (ht : IsClassicalMember p f M t) (hs : IsClassicalMember p f M' s) (hts : t * s = s * t)
    (hA : ∀ x ∈ layer (𝒞 K) M, s * x = x * s) : False := by
  classical
  have Ct := C.at_member hM.1 ht
  have Cs := C.at_member hM'.1 hs
  have heq : nbhd (𝒞 K) M = nbhd (𝒞 K) M' := C.nbhd_eq_of_cent hM hM' hne hs hA
  have hlay : layer (𝒞 K) M = layer (𝒞 K) M' := by
    unfold layer
    rw [heq]
  have hQt : ∀ c : G, c * t * c⁻¹ = t → c ∈ Subgroup.normalizer (layer (𝒞 K) M : Set G) :=
    fun c hc => Ct.mem_normalizer_layer_of_cent hc
  have hQs : ∀ c : G, c * s * c⁻¹ = s → c ∈ Subgroup.normalizer (layer (𝒞 K) M : Set G) :=
    fun c hc => hlay ▸ Cs.mem_normalizer_layer_of_cent hc
  have hXK : layer (𝒞 K) K ≤ Subgroup.normalizer (layer (𝒞 K) M : Set G) :=
    C.layer_le_normalizer_of_pair hM hM' hne ht hs hts hQt hQs
  have hKM : K ∈ nbhd (𝒞 K) M := nbhd_symm C.mem hM
  have hY : centralizingLayer (𝒞 K) {z} ≤ Subgroup.normalizer (layer (𝒞 K) M : Set G) := by
    rw [C.layer_eq]
    exact sup_le ((le_layer hKM).trans Subgroup.le_normalizer) hXK
  have hlayN : ∀ N' ∈ nbhd (𝒞 K) K, layer (𝒞 K) N' = layer (𝒞 K) M := by
    intro N' hN'
    obtain ⟨y, hy, rfl⟩ := C.nbhd_transitive hM hN'
    rw [← conjSub_layer C.inClass.conjInvariant]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY hy)
  have hcentQ : ∀ N' ∈ nbhd (𝒞 K) K, N' ≤ Subgroup.centralizer (layer (𝒞 K) M : Set G) := by
    intro N' hN' n hn
    rw [← hlayN N' hN', Subgroup.mem_centralizer_iff]
    intro x hx
    have hlc : layer (𝒞 K) N' ≤ Subgroup.centralizer (N' : Set G) := by
      refine iSup₂_le fun N'' hN'' y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (hN''.2.2 g hg y hy)
    have := Subgroup.mem_centralizer_iff.mp (hlc hx) n hn
    exact this.symm
  have hXKc : layer (𝒞 K) K ≤ Subgroup.centralizer (layer (𝒞 K) M : Set G) :=
    iSup₂_le fun N' hN' => hcentQ N' hN'
  have hQc : layer (𝒞 K) M ≤ Subgroup.centralizer (layer (𝒞 K) K : Set G) :=
    Subgroup.le_centralizer_iff.mp hXKc
  have hne1 : ∀ {N : Subgroup G} {u : G}, IsClassicalMember p f N u → u ≠ 1 := by
    intro N u hu h
    have := hu.orderOf_eq_two
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hgen := generated_pair C hconn hM
  have hK1 : K ≠ ⊥ := by
    intro h
    exact hne1 C.cls (Subgroup.mem_bot.mp (h ▸ C.cls.mem))
  have hnc : Subgroup.normalClosure (K : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (K : Set G)) with
      h | h
    · exfalso
      apply hK1
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ Subgroup.normalClosure (K : Set G) := Subgroup.subset_normalClosure hx
      rw [h] at hx'
      exact hx'
    · exact h
  have htop : layer (𝒞 K) K ⊔ layer (𝒞 K) M = ⊤ := by
    rw [eq_top_iff, ← hnc]
    refine (Subgroup.closure_le _).mpr ?_
    intro c hc
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    obtain ⟨x, hx⟩ := isConj_iff.mp hbc
    have hmem : conjSub x K ∈ 𝒞 K := ⟨x, rfl⟩
    have := hgen _ hmem (conj_mem_conjSub hb)
    rwa [show x * b * x⁻¹ = c from hx] at this
  have hnorm : (layer (𝒞 K) K).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer (hQc.trans (Subgroup.centralizer_le_normalizer _))
  have : (layer (𝒞 K) K).Normal := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (layer (𝒞 K) K) with h | h
  · have h1 := le_layer hM
    rw [h, le_bot_iff] at h1
    have htM : t ∈ (⊥ : Subgroup G) := by
      rw [← h1]
      exact ht.mem
    exact hne1 ht (Subgroup.mem_bot.mp htM)
  · have hKc : layer (𝒞 K) K ≤ Subgroup.centralizer (K : Set G) := by
      refine iSup₂_le fun N' hN' y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hN'.2.2 g hg y hy
    obtain ⟨a, b, hab⟩ := hnab
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ layer (𝒞 K) K := by rw [h]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp (hKc hg) z C.cls.mem).symm
    have hcenter : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
      · exact h1
      · exfalso
        have : a ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp this b).symm
    rw [hcenter] at hzc
    exact hne1 C.cls (Subgroup.mem_bot.mp hzc)

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
