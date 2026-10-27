module

public import CFSG.CGT.Stroth77.Section1NonSplitGL5

public section

namespace CFSG.CGT.Stroth77

open Subgroup GL5

variable {G : Type*} [Group G] [Finite G] {ι : ↥Tsp →* G}

attribute [local instance] trSAspCommGroup

theorem code_mem_vCodes_of_commute (hι : Function.Injective ι)
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = ι.range) (g : normalizer (trS ι Asp : Set G))
    (h1 : Mconj g * Mconj (nA hι spUV_mem_Tsp) = Mconj (nA hι spUV_mem_Tsp) * Mconj g)
    (h2 : Mconj g * Mconj (nA hι spT_mem_Tsp) = Mconj (nA hι spT_mem_Tsp) * Mconj g) :
    code (basisA ι) (Mconj g) ∈ vCodes := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := sq_trS_Asp ι
  have hgen := closure_basisA ι
  have hcard := card_trS_Asp hι
  obtain ⟨P, hP⟩ := hS
  set guv := Mconj (nA hι spUV_mem_Tsp)
  set gt := Mconj (nA hι spT_mem_Tsp)
  set Mh := (trS ι Asp).normalizerMonoidHom
  set X := Mh.range
  have hPN : (P : Subgroup G) ≤ normalizer (trS ι Asp : Set G) := by
    rw [hP]; exact range_le_normalizer_trS_Asp hι
  set Q : Sylow 2 X := (P.subtype hPN).mapSurjective Mh.rangeRestrict_surjective
  have hQcode : ∀ q ∈ (Q : Subgroup X), code (basisA ι) (q : MulAut ↥(trS ι Asp)) ∈ dCodes := by
    intro q hq
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    have hs' : (s : G) ∈ ι.range := by rw [← hP]; exact mem_subgroupOf.1 hs
    exact code_mem_dCodes hι s hs'
  have hcV : ∀ x : MulAut ↥(trS ι Asp), x * guv = guv * x → x * gt = gt * x →
      ∀ v : MulAut ↥(trS ι Asp), (v = 1 ∨ v = guv ∨ v = gt ∨ v = guv * gt) → x * v = v * x := by
    intro x hx1 hx2 v hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [mul_one, one_mul]
    · exact hx1
    · exact hx2
    · rw [← mul_assoc, hx1, mul_assoc, hx2, mul_assoc]
  set CV : Subgroup X :=
    (Subgroup.centralizer ({guv, gt} : Set (MulAut ↥(trS ι Asp)))).subgroupOf X with hCV
  have hmemCV : ∀ x : X, x ∈ CV ↔ (x : MulAut ↥(trS ι Asp)) * guv = guv * x ∧
      (x : MulAut ↥(trS ι Asp)) * gt = gt * x := by
    intro x
    rw [hCV, mem_subgroupOf, mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hCVp : IsPGroup 2 CV := by
    intro x
    refine ⟨6, ?_⟩
    have hx := (hmemCV x).1 x.2
    have := pow_sixtyFour_eq_one hsq hgen hcard (code_uv hι) (code_t hι)
      ((x : X) : MulAut ↥(trS ι Asp)) hx.1 hx.2
    apply Subtype.ext; apply Subtype.ext
    simpa using this
  have hconjCV : ∀ q ∈ (Q : Subgroup X), ∀ x : X, x ∈ CV → q * x * q⁻¹ ∈ CV := by
    intro q hq x hx
    have hx' := (hmemCV x).1 hx
    have hqi : code (basisA ι) ((q⁻¹ : X) : MulAut ↥(trS ι Asp)) ∈ dCodes :=
      hQcode _ (inv_mem hq)
    have hV := exists_mul_eq_of_normV hsq hgen hcard (code_uv hι) (code_t hι) _
      (normV_dCodes _ hqi)
    rw [hmemCV]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ∀ v ∈ [guv, gt], ((q : MulAut ↥(trS ι Asp)) * x * (q : MulAut ↥(trS ι Asp))⁻¹) *
        v = v * ((q : MulAut ↥(trS ι Asp)) * x * (q : MulAut ↥(trS ι Asp))⁻¹) := by
      intro v hv
      obtain ⟨v', hv', hqv⟩ := hV v hv
      simp only [Subgroup.coe_inv] at hqv
      have e : (q : MulAut ↥(trS ι Asp))⁻¹ * v * (q : MulAut ↥(trS ι Asp)) = v' := by
        rw [hqv]; group
      have hxv' := hcV _ hx'.1 hx'.2 v' hv'
      calc (q : MulAut ↥(trS ι Asp)) * x * (q : MulAut ↥(trS ι Asp))⁻¹ * v
          = (q : MulAut ↥(trS ι Asp)) * (x * ((q : MulAut ↥(trS ι Asp))⁻¹ * v *
            (q : MulAut ↥(trS ι Asp)))) * (q : MulAut ↥(trS ι Asp))⁻¹ := by group
        _ = (q : MulAut ↥(trS ι Asp)) * (v' * x) * (q : MulAut ↥(trS ι Asp))⁻¹ := by
          rw [e, hxv']
        _ = (q : MulAut ↥(trS ι Asp)) * ((q : MulAut ↥(trS ι Asp))⁻¹ * v *
            (q : MulAut ↥(trS ι Asp)) * x) * (q : MulAut ↥(trS ι Asp))⁻¹ := by rw [e]
        _ = v * ((q : MulAut ↥(trS ι Asp)) * x * (q : MulAut ↥(trS ι Asp))⁻¹) := by group
    exact ⟨key guv (by simp), key gt (by simp)⟩
  have hQN : (Q : Subgroup X) ≤ normalizer (CV : Set X) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconjCV q hq x, fun h => ?_⟩
    have := hconjCV q⁻¹ (inv_mem hq) _ h
    simpa [mul_assoc] using this
  have hsup : IsPGroup 2 ↥((Q : Subgroup X) ⊔ CV) :=
    IsPGroup.to_sup_of_normal_right' Q.2 hCVp hQN
  have hle : CV ≤ Q := by
    have := Q.is_maximal' hsup le_sup_left
    rw [← this]; exact le_sup_right
  have hgCV : (⟨Mconj g, g, rfl⟩ : X) ∈ CV := (hmemCV _).2 ⟨h1, h2⟩
  have hgD := hQcode _ (hle hgCV)
  refine centralizer_V_dCodes _ hgD ?_ ?_
  · rw [← code_uv hι, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard]
    exact congrArg _ h1
  · rw [← code_t hι, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard]
    exact congrArg _ h2

theorem exists_conj_spPhi (hι : Function.Injective ι)
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = ι.range)
    (hρ : ∃ gρ : normalizer (trS ι Asp : Set G), code (basisA ι) (Mconj gρ) = rhoC)
    (n : normalizer (trS ι Asp : Set G)) {r : Nat} (hr : r < 16) :
    ∃ r', r' < 16 ∧ (n : G) * ιe ι (spPhi r) * (n : G)⁻¹ = ιe ι (spPhi r') := by
  have hsq := sq_trS_Asp ι
  have hgen := closure_basisA ι
  have hcard := card_trS_Asp hι
  obtain ⟨gρ, hgρ⟩ := hρ
  set X := (trS ι Asp).normalizerMonoidHom.range
  have hC : ∀ h ∈ X, h * Mconj (nA hι spUV_mem_Tsp) = Mconj (nA hι spUV_mem_Tsp) * h →
      h * Mconj (nA hι spT_mem_Tsp) = Mconj (nA hι spT_mem_Tsp) * h →
      h = 1 ∨ h = Mconj (nA hι spUV_mem_Tsp) ∨ h = Mconj (nA hι spT_mem_Tsp) ∨
        h = Mconj (nA hι spUV_mem_Tsp) * Mconj (nA hι spT_mem_Tsp) := by
    rintro _ ⟨g', rfl⟩ h1 h2
    exact eq_of_code_mem_vCodes hsq hgen hcard (code_uv hι) (code_t hι)
      (code_mem_vCodes_of_commute hι hS g' h1 h2)
  have hr32 : r < 32 := by omega
  have ha : coord (basisA ι) (Φ (basisA ι) r) < 16 := by
    rw [coord_Φ hsq hgen hcard hr32]; exact hr
  have hst := coord_lt_sixteen hsq hgen hcard (code_uv hι) (code_t hι) (code_u hι) hgρ X
    ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ hC (f := Mconj n) ⟨n, rfl⟩ ha
  refine ⟨_, hst, ?_⟩
  rw [← coe_Φ_basisA, ← coe_Mconj_apply, ← coe_Φ_basisA, Φ_coord hsq hgen]

end CFSG.CGT.Stroth77
