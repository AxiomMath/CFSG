module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSRoot

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] {L : Subgroup G}

theorem symm_commute_iff_sixS {K : Type} [Field K] (e : L ≃* LinearFlag.projectiveSL 6 K)
    (p q : LinearFlag.projectiveSL 6 K) :
    ((e.symm p : L) : G) * ((e.symm q : L) : G) = ((e.symm q : L) : G) * ((e.symm p : L) : G) ↔
      p * q = q * p := by
  constructor
  · intro h
    have h1 : e.symm (p * q) = e.symm (q * p) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    exact e.symm.injective h1
  · intro h
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]

section J

variable [Finite G]
  (hset : SeitzSetting G L)
  {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
  (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G} (ht : orderOf t = 2)
  (htC : t ∈ centralizer (L : Set G)) {c : Fin 6} {W₁ : Subgroup G}
  (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
  (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
  (htW₁ : t ∈ normalizer (W₁ : Set G))
  (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G))
include hset hK hW₁c hW₁2 hW₁t htW₁ hLW htC ht

theorem pointRadOn_le_centralizer_wZero_sixS {a b : Fin 6} (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) {S : Finset (Fin 6)} (hS : ({c}ᶜ : Finset (Fin 6)) \ {a, b} = S)
    (hall' : ∀ (i j : Fin 6) (hij : i ≠ j) (htX : t ∈ centralizer (modelToG e
      (zpowers (xab hij (1 : K) * xab hij.symm 1)) : Set G)),
      LinearTwoSwapKindAt e t i j (zpowers (xab hij (1 : K) * xab hij.symm 1)) htX) :
    modelToG e (pointRadOn (K := K) a (insert b S)) ≤
        centralizer ((W₁ ⊓ centralizer ({rootTorusSixG e hab} : Set G) : Subgroup G) : Set G) ∧
      modelToG e (pointRadOn (K := K) b S) ≤
        centralizer ((W₁ ⊓ centralizer ({rootTorusSixG e hab} : Set G) : Subgroup G) : Set G) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  obtain ⟨hV₁card, hWV⟩ := card_vOne_sixS hK e hW₁c hW₁t
  obtain ⟨-, hV₀, -⟩ := wZero_facts_sixS hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hab hca hcb
  rw [hS] at hV₀
  obtain ⟨-, hJ⟩ := wZero_le_and_rootSL2_le_centralizer_sixS hset hK e ht htC hW₁c hW₁2 hW₁t
    htW₁ hLW hab hca hcb (hall' a b hab)
  set W₀ : Subgroup G := W₁ ⊓ centralizer ({rootTorusSixG e hab} : Set G) with hW₀
  have hW₀2 : ∀ w ∈ W₀, w * w = 1 := fun w hw => hW₁2 w hw.1
  have hxt0 : rootTorusSixG e hab * t = t * rootTorusSixG e hab := hLt _ (e.symm _).2
  have htW₀ : t ∈ normalizer (W₀ : Set G) := mem_normalizer_inf_centralizer htW₁ hxt0.symm
  have hSc : ∀ j ∈ S, j ≠ c := fun j hj h => by rw [← hS, h] at hj; simp at hj
  have hSa : a ∉ S := fun h => by rw [← hS] at h; simp at h
  have hSb : b ∉ S := fun h => by rw [← hS] at h; simp at h
  have hSsub : insert a S ⊆ ({c}ᶜ : Finset (Fin 6)) := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · simpa using hca.symm
    · simpa using hSc j hj
  have hstep1 : ∀ s : Fin 6 → K, (∀ j ∉ S, s j = 0) →
      ((e.symm (LinearFlag.proj 6 K (pointRadElem a s)) : L) : G) ∈ normalizer (W₀ : Set G) := by
    intro s hs
    have hsc : s c = 0 := hs c (fun h => hSc c h rfl)
    have hsa : s a = 0 := hs a hSa
    by_cases hs0 : s = 0
    · rw [hs0, pointRadElem_zero, map_one, map_one]
      exact one_mem _
    obtain ⟨d, hd⟩ : ∃ d, s d ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hs0 (funext hcon)
    have hdS : d ∈ S := by
      by_contra h
      exact hd (hs d h)
    have hsd : s d = 1 := (eq_zero_or_eq_one_of_natCard_eq_two hK (s d)).resolve_left hd
    have had : a ≠ d := fun h => hSa (h ▸ hdS)
    have hcd : c ≠ d := fun h => hSc d hdS h.symm
    set x : G := ((e.symm (LinearFlag.proj 6 K (pointRadElem a s)) : L) : G) with hx
    have hxB : LinearFlag.proj 6 K (pointRadElem a s) ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
      blockSL_mono hSsub (pointRadOn_le_blockSL a S ⟨_, ⟨s, hs, rfl⟩, rfl⟩)
    have hxW : x ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hxB)
    have hxt : x * t = t * x := hLt x (e.symm _).2
    have hx2 : x * x = 1 := by
      rw [hx, ← Subgroup.coe_mul, ← map_mul,
        pointRadOn_mul_self a S ⟨_, ⟨s, hs, rfl⟩, rfl⟩, map_one, Subgroup.coe_one]
    set g : G := ((e.symm (LinearFlag.proj 6 K (pointRadElem d s)) : L) : G) with hg
    have hgB : LinearFlag.proj 6 K (pointRadElem d s) ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) :=
      blockSL_mono (fun j hj => by
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simpa using hcd.symm
        · simpa using hSc j hj) (pointRadOn_le_blockSL d S ⟨_, ⟨s, hs, rfl⟩, rfl⟩)
    have hgW : g ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hgB)
    have hconj : g * ((e.symm (xab had (1 : K)) : L) : G) * g⁻¹ = x := by
      rw [hg, hx, ← proj_pointRadElem_single_eq_xab_sixS had,
        ← pointRadElem_conj_single_sixS had hsa hsd,
        map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
      rfl
    have hroot : Nat.card W₁ ≤ 4 * Nat.card (W₁ ⊓ centralizer ({x} : Set G) : Subgroup G) := by
      rw [← hconj, card_inf_centralizer_conj_eq_sixS hgW]
      exact root_bound_sixS hset hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW had hca hcd
        (hall' a d had)
    have hxV : x ∉ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
      intro hC
      have hv : ((e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single a (1 : K)))) : L) : G) ∈
          W₁ ⊓ centralizer ({t} : Set G) := by
        rw [hW₁t]
        exact symm_mem_modelToG e (proj_pointRadElem_mem_pointRadical c _)
      have h1 := (mem_centralizer_iff.1 hC) _ hv
      rw [hx, symm_commute_iff_sixS] at h1
      exact hs0 (eq_zero_of_proj_pointRadElem_commute_sixS hK hca hsc hsa h1.symm)
    have hxV₀ : W₀ ⊓ centralizer ({t} : Set G) ≤ centralizer ({x} : Set G) := by
      intro v hv
      rw [hV₀] at hv
      obtain ⟨_, ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hv
      rw [mem_centralizer_singleton_iff]
      have hwa : w a = 0 := hw a hSa
      have h1 := conj_proj_pointRadElem_eq_sixS (K := K) hca hsc hsa w
      rw [hwa, zero_smul, add_zero] at h1
      have h2 : LinearFlag.proj 6 K (pointRadElem c w) * LinearFlag.proj 6 K (pointRadElem a s) =
          LinearFlag.proj 6 K (pointRadElem a s) * LinearFlag.proj 6 K (pointRadElem c w) := by
        calc _ = (LinearFlag.proj 6 K (pointRadElem a s) * LinearFlag.proj 6 K (pointRadElem c w) *
              (LinearFlag.proj 6 K (pointRadElem a s))⁻¹) *
              LinearFlag.proj 6 K (pointRadElem a s) := by rw [h1]
          _ = _ := by group
      exact (symm_commute_iff_sixS e _ _).2 h2
    have hVx : ∀ v ∈ W₁ ⊓ centralizer ({t} : Set G), x * v * x⁻¹ * v⁻¹ ∈
        W₀ ⊓ centralizer ({t} : Set G) := by
      intro v hv
      rw [hW₁t] at hv
      obtain ⟨_, ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hv
      rw [hV₀]
      have h1 := conj_proj_pointRadElem_eq_sixS (K := K) hca hsc hsa w
      have h2 : LinearFlag.proj 6 K (pointRadElem a s) * LinearFlag.proj 6 K (pointRadElem c w) *
          (LinearFlag.proj 6 K (pointRadElem a s))⁻¹ * (LinearFlag.proj 6 K (pointRadElem c w))⁻¹ =
          LinearFlag.proj 6 K (pointRadElem c (w a • (-s))) := by
        rw [h1, ← map_inv, ← map_mul, pointRadElem_inv_sixS, pointRadElem_mul]
        congr 2
        abel
      have h3 : x * ((e.symm (LinearFlag.proj 6 K (pointRadElem c w)) : L) : G) * x⁻¹ *
          ((e.symm (LinearFlag.proj 6 K (pointRadElem c w)) : L) : G)⁻¹ =
          ((e.symm (LinearFlag.proj 6 K (pointRadElem c (w a • (-s)))) : L) : G) := by
        rw [← h2, hx]
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      change x * ((e.symm (LinearFlag.proj 6 K (pointRadElem c w)) : L) : G) * x⁻¹ *
          ((e.symm (LinearFlag.proj 6 K (pointRadElem c w)) : L) : G)⁻¹ ∈ _
      rw [h3]
      refine symm_mem_modelToG e ⟨_, ⟨w a • (-s), fun j hj => ?_, rfl⟩, rfl⟩
      rw [Pi.smul_apply, Pi.neg_apply, hs j hj, neg_zero, smul_zero]
    have hW₀t : ∀ w ∈ W₀, t * w * t⁻¹ * w⁻¹ ∈ W₀ ⊓ centralizer ({t} : Set G) := fun w hw =>
      Subgroup.mem_inf.2 ⟨tcomm_mem htW₀ hw, tcomm_mem_centralizer hW₀2 ht2 htW₀ hw⟩
    exact mem_normalizer_of_root hW₁2 ht2 htW₁ hWV inf_le_left inf_le_left hW₀t hxW hxt hx2
      hroot hxV hxV₀ hVx
  have hab' : b ≠ a := hab.symm
  have hxba : ((e.symm (xab hab' (1 : K)) : L) : G) ∈ centralizer (W₀ : Set G) :=
    hJ (symm_mem_modelToG e (by rw [rootSL2_comm]; exact xab_mem_rootSL2 hab' 1))
  have hxab : ((e.symm (xab hab (1 : K)) : L) : G) ∈ centralizer (W₀ : Set G) :=
    hJ (symm_mem_modelToG e (xab_mem_rootSL2 hab 1))
  have hstep2 : ∀ s : Fin 6 → K, (∀ j ∉ S, s j = 0) →
      ((e.symm (LinearFlag.proj 6 K (pointRadElem b s)) : L) : G) ∈ centralizer (W₀ : Set G) := by
    intro s hs
    have h1 := commutator_mem_centralizer hxba (hstep1 s hs)
    rwa [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      xab_commutator_proj_pointRadElem_sixS hab' (hs b hSb) (hs a hSa)] at h1
  have hstep3 : ∀ s : Fin 6 → K, (∀ j ∉ S, s j = 0) →
      ((e.symm (LinearFlag.proj 6 K (pointRadElem a s)) : L) : G) ∈ centralizer (W₀ : Set G) := by
    intro s hs
    have h1 := commutator_mem_centralizer hxab
      (centralizer_le_normalizer_of_le le_rfl (hstep2 s hs))
    rwa [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      xab_commutator_proj_pointRadElem_sixS hab (hs a hSa) (hs b hSb)] at h1
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    have hsplit : pointRadElem a r = pointRadElem a (r b • Pi.single b (1 : K)) *
        pointRadElem a (Function.update r b 0) := by
      rw [pointRadElem_mul]
      congr 1
      funext j
      by_cases hj : j = b
      · rw [hj, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
          Function.update_self, add_zero]
      · rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, zero_add,
          Function.update_of_ne hj]
    have hr' : ∀ j ∉ S, Function.update r b 0 j = 0 := by
      intro j hj
      by_cases hjb : j = b
      · rw [hjb, Function.update_self]
      · rw [Function.update_of_ne hjb]
        exact hr j (by simp [hjb, hj])
    have hfirst : ((e.symm (LinearFlag.proj 6 K (pointRadElem a (r b • Pi.single b (1 : K))))
        : L) : G) ∈ centralizer (W₀ : Set G) := by
      rcases eq_zero_or_eq_one_of_natCard_eq_two hK (r b) with h0 | h1
      · rw [h0, zero_smul, pointRadElem_zero, map_one, map_one]
        exact one_mem _
      · rw [h1, one_smul, proj_pointRadElem_single_eq_xab_sixS hab]
        exact hxab
    change ((e.symm (LinearFlag.proj 6 K (pointRadElem a r)) : L) : G) ∈ _
    rw [hsplit, map_mul, map_mul, Subgroup.coe_mul]
    exact mul_mem hfirst (hstep3 _ hr')
  · rintro _ ⟨_, ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact hstep2 s hs

end J

end CFSG.SeitzReduction.LinearPilot
