module

public import CFSG.Goldschmidt75.B3Prelim
public import CFSG.Goldschmidt75.Transfer

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_mul_mul {S : Subgroup G} {s s' c c' : G} (hs : s ∈ S) (hs' : s' ∈ S)
    (hc : c ∈ centralizer (S : Set G)) (hc' : c' ∈ centralizer (S : Set G)) :
    ⁅s * c, s' * c'⁆ = ⁅s, s'⁆ * ⁅c, c'⁆ := by
  let φ := S.subtype.noncommCoprod (centralizer (S : Set G)).subtype
    (fun a b => mem_centralizer_iff.mp b.2 a a.2)
  have h := map_commutatorElement φ (⟨s, hs⟩, ⟨c, hc⟩) (⟨s', hs'⟩, ⟨c', hc'⟩)
  simp only [commutatorElement_def, Prod.mk_mul_mk, Prod.inv_mk, φ] at h
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  exact h.symm

omit [Finite G] in
theorem commutator_inf_le_of_le_sup {S N T : Subgroup G} (hST : S ≤ T)
    (hN : N ≤ S ⊔ centralizer (S : Set G)) :
    ⁅N, N⁆ ⊓ T ≤ (⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ T) ⊔ S := by
  set C := centralizer (S : Set G) with hC
  have hSC : S ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp le_rfl).trans (centralizer_le_normalizer _)
  have hcomm : ⁅N, N⁆ ≤ ⁅S, S⁆ ⊔ ⁅C, C⁆ := by
    rw [commutator_le]
    intro x hx y hy
    have hx' : x ∈ ((S ⊔ C : Subgroup G) : Set G) := hN hx
    have hy' : y ∈ ((S ⊔ C : Subgroup G) : Set G) := hN hy
    rw [coe_mul_of_left_le_normalizer_right _ _ hSC] at hx' hy'
    obtain ⟨s, hs, c, hc, rfl⟩ := hx'
    obtain ⟨s', hs', c', hc', rfl⟩ := hy'
    rw [commutatorElement_mul_mul hs hs' hc hc']
    exact mul_mem_sup (commutator_mem_commutator hs hs') (commutator_mem_commutator hc hc')
  intro z hz
  have hz' := mem_inf.mp hz
  have hS'C : ⁅S, S⁆ ≤ normalizer ((⁅C, C⁆ : Subgroup G) : Set G) :=
    (commutator_le_self S).trans (le_normalizer_commutator hSC hSC)
  have hz1 : z ∈ ((⁅S, S⁆ ⊔ ⁅C, C⁆ : Subgroup G) : Set G) := hcomm hz'.1
  rw [coe_mul_of_left_le_normalizer_right _ _ hS'C] at hz1
  obtain ⟨a, ha, b, hb, rfl⟩ := hz1
  have haS : a ∈ S := commutator_le_self S ha
  have hbT : b ∈ T := by
    have := mul_mem (inv_mem (hST haS)) hz'.2
    simpa using this
  exact mul_mem (mem_sup_right haS) (mem_sup_left (mem_inf.mpr ⟨hb, hbT⟩))

theorem eq_bot_of_le_center (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T)
    (hTRS : (T : Subgroup G) ≤
      (⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ T) ⊔ S)
    (hRZ : ⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ T ≤ center G) :
    ⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ T = ⊥ := by
  set C := centralizer (S : Set G) with hC
  set R := ⁅C, C⁆ ⊓ (T : Subgroup G) with hR
  have hRC : R ≤ C := inf_le_left.trans (commutator_le_self C)
  have hTN := fusionIsSylowIn_normalizer T hST hS
  have hP := G3a.fusionIsSylowIn_inf hTN (centralizer_le_normalizer _)
    (normal_centralizer_subgroupOf S).isSubnormal
  obtain ⟨P, hP'⟩ := G310.exists_sylow_of_fusionIsSylowIn hP
  have hRS : R ≤ normalizer (S : Set G) := hRC.trans (centralizer_le_normalizer _)
  have hdec : ∀ x ∈ (T : Subgroup G) ⊓ C, ∃ r ∈ R, ∃ s ∈ S ⊓ C, x = r * s := by
    intro x hx
    have hx' : x ∈ ((R ⊔ S : Subgroup G) : Set G) := hTRS (mem_inf.mp hx).1
    rw [coe_mul_of_left_le_normalizer_right _ _ hRS] at hx'
    obtain ⟨r, hr, s, hs, rfl⟩ := hx'
    refine ⟨r, hr, s, mem_inf.mpr ⟨hs, ?_⟩, rfl⟩
    have := mul_mem (inv_mem (hRC hr)) (mem_inf.mp hx).2
    simpa using this
  have hab : ∀ x ∈ (T : Subgroup G) ⊓ C, ∀ y ∈ (T : Subgroup G) ⊓ C, x * y = y * x := by
    intro x hx y hy
    obtain ⟨r, hr, s, hs, rfl⟩ := hdec x hx
    obtain ⟨r', hr', s', hs', rfl⟩ := hdec y hy
    have hrc : ∀ g : G, g * r = r * g := mem_center_iff.mp (hRZ hr)
    have hr'c : ∀ g : G, g * r' = r' * g := mem_center_iff.mp (hRZ hr')
    have hss : s * s' = s' * s := (mem_centralizer_iff.mp (mem_inf.mp hs').2 s (mem_inf.mp hs).1)
    calc r * s * (r' * s') = r * (s * r') * s' := by group
      _ = r * (r' * s) * s' := by rw [hr'c s]
      _ = (r * r') * (s * s') := by group
      _ = (r' * r) * (s' * s) := by rw [hrc r', hss]
      _ = r' * (r * s') * s := by group
      _ = r' * (s' * r) * s := by rw [hrc s']
      _ = r' * s' * (r * s) := by group
  have hPcomm : ⁅(P : Subgroup C), (P : Subgroup C)⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have hx' : (x : G) ∈ (T : Subgroup G) ⊓ C := hP' ▸ ⟨x, hx, rfl⟩
    have hy' : (y : G) ∈ (T : Subgroup G) ⊓ C := hP' ▸ ⟨y, hy, rfl⟩
    exact Subtype.ext (hab _ hy' _ hx')
  rw [eq_bot_iff]
  intro r hr
  have hrC : r ∈ C := hRC hr
  have hzc : (⟨r, hrC⟩ : C) ∈ center C := mem_center_iff.mpr fun g =>
    Subtype.ext (mem_center_iff.mp (hRZ hr) g)
  have hzP : (⟨r, hrC⟩ : C) ∈ (P : Subgroup C) := by
    have : r ∈ (P : Subgroup C).map C.subtype := hP' ▸ mem_inf.mpr ⟨(mem_inf.mp hr).2, hrC⟩
    obtain ⟨w, hw, hwr⟩ := this
    rwa [show (⟨r, hrC⟩ : C) = w from Subtype.ext hwr.symm]
  have hzG : (⟨r, hrC⟩ : C) ∈ commutator C := by
    have h1 : ⁅C, C⁆ = (commutator C).map C.subtype := by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    have : r ∈ (commutator C).map C.subtype := h1 ▸ (mem_inf.mp hr).1
    obtain ⟨w, hw, hwr⟩ := this
    rwa [show (⟨r, hrC⟩ : C) = w from Subtype.ext hwr.symm]
  have h2 := mem_commutator_of_mem_center P hzc hzP hzG
  rw [hPcomm, mem_bot] at h2
  exact (mem_bot).mpr (congrArg Subtype.val h2)

theorem mem_center_of_mem_inf (T : Sylow 2 G) {S R : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hR : fusionStronglyClosed (R : Set G) T)
    (hRC : R ≤ centralizer (S : Set G))
    (hN : normalizer (S : Set G) ≤ S ⊔ centralizer (S : Set G))
    (hO : goldschmidtOddCore G = ⊥) {z : G} (hzR : z ∈ R) (hzS : z ∈ S)
    (hz2 : orderOf z = 2) : z ∈ center G := by
  have hSC : S ≤ normalizer ((centralizer (S : Set G) : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp le_rfl).trans (centralizer_le_normalizer _)
  have hcl : fusionStronglyClosed ((zpowers z : Subgroup G) : Set G) T := by
    intro x hx g hg
    rcases eq_one_or_eq_of_mem_zpowers hz2 hx with rfl | rfl
    · simp
    · have hbS := hS x hzS g hg
      have hbR := hR x hzR g hg
      obtain ⟨m, hm, hmeq⟩ := exists_normalizer_conj T hST hS (hRC hzR) (hRC hbR)
      have hm' : m ∈ ((S ⊔ centralizer (S : Set G) : Subgroup G) : Set G) := hN hm
      rw [coe_mul_of_left_le_normalizer_right _ _ hSC] at hm'
      obtain ⟨s, hs, c, hc, rfl⟩ := hm'
      have h1 : s⁻¹ * x * s = x := by
        have := mem_centralizer_iff.mp (hRC hzR) s hs
        calc s⁻¹ * x * s = s⁻¹ * (x * s) := by group
          _ = s⁻¹ * (s * x) := by rw [this]
          _ = x := by group
      have h2 : c⁻¹ * x * c = x := by
        have := mem_centralizer_iff.mp hc x hzS
        calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
          _ = c⁻¹ * (c * x) := by rw [this]
          _ = x := by group
      have e : (s * c)⁻¹ * x * (s * c) = x := by
        calc (s * c)⁻¹ * x * (s * c) = c⁻¹ * (s⁻¹ * x * s) * c := by group
          _ = x := by rw [h1, h2]
      rw [SetLike.mem_coe, ← hmeq, e]
      exact mem_zpowers x
  exact mem_center_of_stronglyClosed_zpowers T hz2 hcl hO

end CFSG.Goldschmidt75
