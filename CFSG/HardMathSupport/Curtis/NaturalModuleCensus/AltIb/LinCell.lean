module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinTZ

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ToralCensus CFSG.QuasithinUnique CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.Open
open scoped commutatorElement

section Cases

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ}

omit [Finite Y] in
theorem false_of_tf_cell {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    {σ : SpecialLinearGroup (Fin n) K →* ↥L} (hσs : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)) {I : Set ℕ}
    (hne : I.Nonempty) (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hQ : (J.subgroupOf L).comap σ = flagStabilizer n K I) (hJL : J ≤ L)
    (hA1 : AltA1 J p) (hpq : ¬ p ∣ Nat.card K - 1) {x : Y} (hxL : x ∈ L) (hxp : x ^ p = 1)
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) {V E : Subgroup Y} (hVJ : V ≤ J)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set Y)) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by
    obtain ⟨i, hi⟩ := hne
    have := (hI i hi).2
    omega
  set σ' : SpecialLinearGroup (Fin n) K →* Y := L.subtype.comp σ with hσ'
  have hker' : σ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    ker_subtype_comp_le hker
  have hQle : flagStabilizer n K I ≤ J.comap σ' := by
    intro g hg
    rw [← hQ] at hg
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hA1c : CoverA1 n K I p := coverA1_of_hom σ' hker' hQle hA1
  have hpk : ¬ p ∣ Nat.card σ'.ker := fun h => hpq
    (dvd_of_dvd_card_center_SL hp hn0 (h.trans (Subgroup.card_dvd_of_le hker'))).2
  have hxr : x ∈ σ'.range := by
    obtain ⟨g, hg⟩ := hσs ⟨x, hxL⟩
    exact ⟨g, by simp [hσ', hg]⟩
  obtain ⟨xh, hxh, hxhp⟩ := exists_lift_pow_eq_one_cover hker' hp hpk hxp hxr
  have hxh' : ((σ xh : ↥L) : Y) = x := hxh
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  obtain ⟨W, Eh, hW, hWmap, hWQ, hWx, hEhW, hEhp, hEhmap⟩ := lift_core_cover hσs hker hp hVJ
    (hVJ.trans hJL) hV hVx hxh' hEp hEV
  rw [hQ] at hWQ
  have hfixc := centralizer_le_flagStabilizer_of_fix hQ hfix hxh'
  obtain ⟨hEhel, hEhc⟩ := lift_core_elemAbelian (σ := σ') hp hpk hEhp (hEhmap ▸ hEel)
  rw [hEhmap, hEc] at hEhc
  exact coreTF hne hI hp57 hpq hA1c hxhp hfixc hWQ hWx hW hEhW (fun e he => hEhel.2 e he)
    hEhc.ge

theorem false_of_split_cell {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    {σ : SpecialLinearGroup (Fin n) K →* ↥L} (hσs : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)) {I : Set ℕ}
    (hne : I.Nonempty) (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hQ : (J.subgroupOf L).comap σ = flagStabilizer n K I) (hJL : J ≤ L)
    (hA1 : AltA1 J p) (hA2 : AltA2 J p) (hpq : p ∣ Nat.card K - 1) {V E : Subgroup Y}
    (hVJ : V ≤ J) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V) (hEel : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  set σ' : SpecialLinearGroup (Fin n) K →* Y := L.subtype.comp σ with hσ'
  have hker' : σ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    ker_subtype_comp_le hker
  have hQle : flagStabilizer n K I ≤ J.comap σ' := by
    intro g hg
    rw [← hQ] at hg
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hA1c : CoverA1 n K I p := coverA1_of_hom σ' hker' hQle hA1
  have hA2c : CoverA2 n K I p := coverA2_of_hom σ' hker' hQle hA2
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  obtain ⟨W, Eh, hW, hWmap, hWQ, -, hEhW, hEhp, hEhmap⟩ := lift_core_cover (x := (1 : Y))
    (xh := 1) hσs hker hp hVJ (hVJ.trans hJL) hV (fun v _ => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]) (by simp) hEp hEV
  rw [hQ] at hWQ
  have hcyc := coreSplit hne hI hp57 hpq hA1c hA2c hWQ hW hEhW hEhp
  have hcycE : IsCyclic ↥(Eh.map σ') :=
    isCyclic_of_surjective (σ'.subgroupMap Eh) (MonoidHom.subgroupMap_surjective _ _)
  rw [hEhmap] at hcycE
  exact not_isCyclic_of_exponent hp (fun e he => hEel.2 e he) hEc hcycE

end Cases


section Assembly

theorem altIbCell_a
    (hSch : KFactCatalogSchreier) (hGA : CFSG.Open.GriessAllModelsStatement) :
    AltIbCell (IsLieOf IdxA) := by
  intro Y _ _ L J hL htype hX hpar hJL hnB p hp57 hAlt x hxL hxp hfix W hW hWN hWx hE
  obtain ⟨E, hEW, hEel, hEcard⟩ := hE
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨-, hcover, V, hVle, hV, hEVZ, hEV⟩ := altIbA_setup hSch hGA hL htype hX hpar hJL hnB hp
    hp5 hxL hfix hW hWN hWx hEW hEp hEcard
  obtain ⟨n, f, σ, e, I, hn3, hf1, hσs, hker, -, hI, hne, -, hQ⟩ := hcover
  have hJ : J ≤ L := hpar.1
  have hLperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hL.2.2.1
  have hA1 : AltA1 J p := fun X hXJ hXq => not_sq_dvd_card_of_quasisimple hp57 hAlt hXJ hXq
  have hA2 : AltA2 J p := fun X₁ X₂ h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂ =>
    false_of_commuting_noAp hp57 hAlt h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂
  have hVJ : V ≤ J := fun v hv => (hVle hv).1
  have hVx : V ≤ Subgroup.centralizer ({x} : Set Y) := fun v hv => (hVle hv).2
  by_cases hpZ : p ∣ Nat.card (Subgroup.center ↥L)
  · exact false_of_tz_cell hp57 hσs hker hLperf hne hI hQ hJ hA1 hA2 hxL hxp hfix hVJ hVx hV hEVZ
      (fun e he => hEel.2 e he) hEcard hpZ
  · have hEV' : E ≤ V := hEV hpZ
    by_cases hpq : p ∣ Nat.card (GaloisField 2 f) - 1
    · exact false_of_split_cell hp57 hσs hker hne hI hQ hJ hA1 hA2 hpq hVJ hV hEV' hEel hEcard
    · exact false_of_tf_cell hp57 hσs hker hne hI hQ hJ hA1 hpq hxL hxp hfix hVJ hVx hV hEV' hEel
        hEcard

end Assembly

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell
