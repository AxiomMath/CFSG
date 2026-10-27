module

public import CFSG.CGT.Timmesfeld75.Sec4NineProof
public import CFSG.CGT.T75I.Conj

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem hnine_of_ctx (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ 2 2) :
    ∀ c ∈ hSub T (normIn T₁ T), (∀ t ∈ T, c * t = t * c) →
      ∀ x ∈ hSub T (normIn T₁ T), ⁅c, x⁆ ∈ T := by
  intro c hcH hct x hxH
  have : Finite G := hc.finite
  have h4 : 4 < Nat.card T := by rw [hc.hT]; norm_num
  rw [← sec58 h1 hc.hy hc.hS hc.hI] at hcH hxH
  exact sec4Nine_of_noA h1 G T T₁ hc.hy hc.hS hc.hI h4 c hcH hct x hxH

theorem conj_mem_centralizer {n c : G} (hn : n ∈ Subgroup.normalizer (T : Set G))
    (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro t ht
  have ht' : n⁻¹ * t * n ∈ T := by
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hn) ht
    simpa using this
  have h1 := hc (n⁻¹ * t * n) ht'
  calc t * (n * c * n⁻¹) = n * ((n⁻¹ * t * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * t * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * t := by group

theorem barSub_le_commutator {H : Subgroup G} [(T.subgroupOf H).Normal]
    (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hperf : commutator (↥H ⧸ T.subgroupOf H) = ⊤) :
    barSub T H ≤ ⁅barSub T H, barSub T H⁆ := by
  classical
  intro y hy
  obtain ⟨x, hxN, hxH, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
  let π : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmap : (commutator ↥H).map π = ⊤ := by
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥H) ⊤ π
    rw [Subgroup.map_top_of_surjective π hπ] at h
    have hh : (commutator ↥H).map π = commutator (↥H ⧸ T.subgroupOf H) := h
    rw [hh, hperf]
  have hx' : π ⟨x, hxH⟩ ∈ (commutator ↥H).map π := by rw [hmap]; trivial
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.1 hx'
  have hwT : (w : G)⁻¹ * x ∈ T := by
    have := QuotientGroup.eq.1 hwx
    exact Subgroup.mem_subgroupOf.1 this
  let φ : ↥H →* NQuot T :=
    (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G)))).comp
      (Subgroup.inclusion hHN)
  have hφ : ∀ z : ↥H, φ z = barElt T (hHN z.2) := fun z => rfl
  have hwA : φ w ∈ ⁅barSub T H, barSub T H⁆ := by
    have h1 : φ w ∈ (commutator ↥H).map φ := Subgroup.mem_map_of_mem φ hw
    have h2 : (commutator ↥H).map φ = ⁅(⊤ : Subgroup ↥H).map φ, (⊤ : Subgroup ↥H).map φ⁆ :=
      Subgroup.map_commutator (⊤ : Subgroup ↥H) ⊤ φ
    rw [h2] at h1
    refine Subgroup.commutator_mono ?_ ?_ h1
    · rintro _ ⟨z, -, rfl⟩
      rw [hφ]
      exact barElt_mem_barSub _ z.2
    · rintro _ ⟨z, -, rfl⟩
      rw [hφ]
      exact barElt_mem_barSub _ z.2
  have heq : barElt T hxN = φ w := by
    rw [hφ]
    exact ((barElt_eq_iff (hHN w.2) hxN).2 hwT).symm
  rw [heq]
  exact hwA

theorem conj_mem_hSub {n y : G} (hn : n ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ hSub T (normIn T₁ T)) : n * y * n⁻¹ ∈ hSub T (normIn T₁ T) :=
  mul_mul_inv_mem_hSub hn hy

theorem comm_mem_of_centralizer (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ 2 2)
    [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hperf : commutator (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) = ⊤)
    {c x : G} (hcC : c ∈ Subgroup.centralizer (T : Set G)) (hxH : x ∈ hSub T (normIn T₁ T)) :
    ⁅x, c⁆ ∈ T := by
  classical
  have hnine := hnine_of_ctx h1 hc
  set H := hSub T (normIn T₁ T) with hH
  have hHN : H ≤ Subgroup.normalizer (T : Set G) := hSub_le_normalizer'
  set C := Subgroup.centralizer (T : Set G) with hC
  have hCN : C ≤ Subgroup.normalizer (T : Set G) := Subgroup.centralizer_le_normalizer (T : Set G)
  set A := barSub T H with hA
  set B := barSub T C with hB
  have hAperf : A ≤ ⁅A, A⁆ := barSub_le_commutator hHN hperf
  have hAAle : ⁅A, A⁆ ≤ A := (Subgroup.commutator_le).2 fun a ha b hb =>
    A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  have hAA : ⁅A, A⁆ = A := le_antisymm hAAle hAperf
  have hcommN : ∀ {x c : G}, x ∈ Subgroup.normalizer (T : Set G) →
      c ∈ Subgroup.normalizer (T : Set G) → ⁅x, c⁆ ∈ Subgroup.normalizer (T : Set G) :=
    fun hx hc' => by
      simp only [commutatorElement_def]
      exact (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem
          ((Subgroup.normalizer (T : Set G)).mul_mem hx hc')
          ((Subgroup.normalizer (T : Set G)).inv_mem hx)) ((Subgroup.normalizer (T : Set G)).inv_mem hc')
  have hAB : ⁅A, B⁆ ≤ Subgroup.centralizer (A : Set (NQuot T)) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hxN, hxH, rfl⟩ := exists_eq_barElt_of_mem_barSub ha
    obtain ⟨c, hcN, hcC, rfl⟩ := exists_eq_barElt_of_mem_barSub hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨z, hzN, hzH, rfl⟩ := exists_eq_barElt_of_mem_barSub hz
    have hc'N : ⁅x, c⁆ ∈ Subgroup.normalizer (T : Set G) := hcommN hxN hcN
    have hc'H : ⁅x, c⁆ ∈ H := by
      have h2 : c * x⁻¹ * c⁻¹ ∈ H := conj_mem_hSub hcN (H.inv_mem hxH)
      have : ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact H.mul_mem hxH h2
    have hc'C : ⁅x, c⁆ ∈ C := by
      have h2 : x * c * x⁻¹ ∈ C := conj_mem_centralizer hxN hcC
      simp only [commutatorElement_def]
      exact C.mul_mem h2 (C.inv_mem hcC)
    have hct : ∀ t ∈ T, ⁅x, c⁆ * t = t * ⁅x, c⁆ := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 hc'C t ht).symm
    have hT' := hnine ⁅x, c⁆ hc'H hct z hzH
    have h1' : ⁅barElt T hc'N, barElt T hzN⁆ = 1 := by
      have : ⁅barElt T hc'N, barElt T hzN⁆ = barElt T (hcommN hc'N hzN) := rfl
      rw [this]
      exact (barElt_eq_one_iff _).2 hT'
    have h2' : ⁅barElt T hxN, barElt T hcN⁆ = barElt T hc'N := rfl
    rw [h2']
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1').symm
  have hABbot : ⁅A, B⁆ = ⊥ := by
    have h1' : ⁅⁅A, B⁆, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAB
    have h2' : ⁅⁅B, A⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm B A]; exact h1'
    have h3' : ⁅⁅A, A⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1' h2'
    rwa [hAA] at h3'
  have hxN := hHN hxH
  have hcN := hCN hcC
  have hmem : ⁅barElt T hxN, barElt T hcN⁆ ∈ ⁅A, B⁆ :=
    Subgroup.commutator_mem_commutator (barElt_mem_barSub hxN hxH) (barElt_mem_barSub hcN hcC)
  rw [hABbot, Subgroup.mem_bot] at hmem
  have h2' : ⁅barElt T hxN, barElt T hcN⁆ = barElt T (hcommN hxN hcN) := rfl
  rw [h2'] at hmem
  exact (barElt_eq_one_iff _).1 hmem

end CFSG.CGT.T75I
