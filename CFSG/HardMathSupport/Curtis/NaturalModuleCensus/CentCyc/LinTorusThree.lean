module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.LinBar
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinAux

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.AGLEmbedding Matrix
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le le_perfectJoin)
open CFSG.AGLEmbedding.ToralCensus CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb (sl2_central_of_perfect_hom)
open scoped commutatorElement

section Core

variable {K : Type} [Field K] [Finite K] {p : ℕ} {G : Type*} [Group G]

theorem eq_one_of_mul_self_eq_one_of_pow {g : G} (hp : p.Prime) (hp2 : p ≠ 2) (hg : g * g = 1)
    {k : ℕ} (hk : g ^ (p ^ k) = 1) : g = 1 := by
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
  have hpk : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : orderOf g ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 hpk
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem torusThree_core [Finite G] (hp : p.Prime) (hp2 : p ≠ 2)
    (ρ₁ : G →* K) (ρ₂ : G →* Matrix (Fin 2) (Fin 2) K)
    (hdet : ∀ g, ρ₁ g * (ρ₂ g).det = 1) (hker : ∀ g, ρ₁ g = 1 → ρ₂ g = 1 → g * g = 1)
    {D E : Subgroup G} (hD : ⁅D, D⁆ = D) (hD1 : ∀ d ∈ D, ρ₁ d = 1) (hdvd : p ∣ Nat.card D)
    (hEp : IsPGroup p E) (hcomm : ∀ e ∈ E, ∀ d ∈ D, e * d = d * e) : IsCyclic E := by
  have : Fact p.Prime := ⟨hp⟩
  have htriv : ∀ g : G, ρ₁ g = 1 → ρ₂ g = 1 → ∀ k, g ^ (p ^ k) = 1 → g = 1 :=
    fun g h1 h2 k hk => eq_one_of_mul_self_eq_one_of_pow hp hp2 (hker g h1 h2) hk
  have hne : ∃ d ∈ D, ρ₂ d ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) p hdvd
    refine ⟨x, x.2, fun h2 => ?_⟩
    have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    have h1 : (x : G) = 1 := htriv x (hD1 x x.2) h2 1 (by
      rw [pow_one]
      exact congrArg Subtype.val hxp)
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hsc : ∀ e ∈ E, ∃ c : K, ρ₂ e = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro e he
    refine sl2_central_of_perfect_hom ρ₂ hD (fun d hd => ?_) hne
    rw [← map_mul, ← map_mul, hcomm e he d hd]
  let τ : E →* K :=
    { toFun := fun e => ρ₂ (e : G) 0 0
      map_one' := by simp
      map_mul' := fun e e' => by
        obtain ⟨c, hc⟩ := hsc e e.2
        obtain ⟨c', hc'⟩ := hsc e' e'.2
        simp [hc, hc', Matrix.mul_apply] }
  have hinj : Function.Injective τ.toHomUnits := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : τ e = 1 := by simpa using congrArg Units.val he
    obtain ⟨c, hc⟩ := hsc e e.2
    have hcτ : c = τ e := by simp [τ, hc]
    have h2 : ρ₂ (e : G) = 1 := by rw [hc, hcτ, h1, one_smul]
    have h3 : ρ₁ (e : G) = 1 := by
      have := hdet e
      rwa [h2, Matrix.det_one, mul_one] at this
    obtain ⟨k, hk⟩ := hEp e
    exact Subtype.ext (htriv e h3 h2 k (congrArg Subtype.val hk))
  exact isCyclic_of_injective τ.toHomUnits hinj

end Core

section Transfer

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem torusThree_of_homs {I : Set ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ρ₁ : ↥(flagStabilizer 3 K I) →* K)
    (ρ₂ : ↥(flagStabilizer 3 K I) →* Matrix (Fin 2) (Fin 2) K)
    (hdet : ∀ g, ρ₁ g * (ρ₂ g).det = 1) (hker : ∀ g, ρ₁ g = 1 → ρ₂ g = 1 → g * g = 1)
    (hD1 : ∀ (d : Matrix.SpecialLinearGroup (Fin 3) K) (hd : d ∈ flagStabilizer 3 K I),
      d ∈ perfectJoin (flagStabilizer 3 K I) → ρ₁ ⟨d, hd⟩ = 1)
    {E D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hEQ : E ≤ flagStabilizer 3 K I) (hDQ : D ≤ flagStabilizer 3 K I) (hEp : IsPGroup p E)
    (hD : ⁅D, D⁆ = D) (hdvd : p ∣ Nat.card D) (hcomm : ∀ e ∈ E, ∀ d ∈ D, e * d = d * e) :
    IsCyclic E := by
  have hD' : ⁅D.subgroupOf (flagStabilizer 3 K I), D.subgroupOf (flagStabilizer 3 K I)⁆ =
      D.subgroupOf (flagStabilizer 3 K I) := perfect_subgroupOf_of_le hD hDQ
  have hcard : Nat.card (D.subgroupOf (flagStabilizer 3 K I)) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv
  have hc : IsCyclic ↥(E.subgroupOf (flagStabilizer 3 K I)) :=
    torusThree_core hp hp2 ρ₁ ρ₂ hdet hker hD'
      (fun d hd => hD1 d.1 d.2 (le_perfectJoin hDQ hD (Subgroup.mem_subgroupOf.1 hd)))
      (hcard ▸ hdvd) (hEp.comap_subtype) (fun e he d hd => Subtype.ext (hcomm e he d hd))
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEQ).toMonoidHom
    (MulEquiv.surjective _)

end Transfer

section Cases

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

omit [Finite K] [CharP K 2] in
theorem entry_zero_of_mem_single {c : ℕ} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ flagStabilizer 3 K {c}) {k l : Fin 3} (hl : (l : ℕ) < c) (hk : c ≤ (k : ℕ)) :
    (g : Matrix (Fin 3) (Fin 3) K) k l = 0 :=
  apply_eq_zero_of_mem_flagStabilizer (Or.inr (Set.mem_singleton c)) hg hl hk

theorem torusThree_one (hp : p.Prime) (hp2 : p ≠ 2)
    {E D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hEQ : E ≤ flagStabilizer 3 K {1}) (hDQ : D ≤ flagStabilizer 3 K {1}) (hEp : IsPGroup p E)
    (hD : ⁅D, D⁆ = D) (hdvd : p ∣ Nat.card D) (hcomm : ∀ e ∈ E, ∀ d ∈ D, e * d = d * e) :
    IsCyclic E := by
  have hS : IsConsecutiveCut 3 ({1} : Set ℕ) 0 1 :=
    ⟨by omega, by omega, Or.inl rfl, Or.inr rfl, by simp⟩
  have hB : IsConsecutiveCut 3 ({1} : Set ℕ) 1 3 :=
    ⟨by omega, le_rfl, Or.inr rfl, Or.inl rfl, by simp⟩
  let ρ₁ : ↥(flagStabilizer 3 K {1}) →* K := detMonoidHom.comp (cutBlockHom hS)
  let ρ₂ : ↥(flagStabilizer 3 K {1}) →* Matrix (Fin 2) (Fin 2) K := cutBlockHom hB
  have hρ₁ : ∀ g : ↥(flagStabilizer 3 K {1}),
      ρ₁ g = (g.1 : Matrix (Fin 3) (Fin 3) K) 0 0 := by
    intro g
    show Matrix.det (cutBlock (g.1 : Matrix (Fin 3) (Fin 3) K) 0 1 hS.2.1 :
      Matrix (Fin 1) (Fin 1) K) = _
    rw [Matrix.det_fin_one]
    rfl
  have hρ₂ : ∀ g : ↥(flagStabilizer 3 K {1}), ρ₂ g =
      !![(g.1 : Matrix (Fin 3) (Fin 3) K) 1 1, (g.1 : Matrix (Fin 3) (Fin 3) K) 1 2;
        (g.1 : Matrix (Fin 3) (Fin 3) K) 2 1, (g.1 : Matrix (Fin 3) (Fin 3) K) 2 2] := by
    intro g
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine torusThree_of_homs hp hp2 ρ₁ ρ₂ ?_ ?_ ?_ hEQ hDQ hEp hD hdvd hcomm
  · intro g
    have h10 := entry_zero_of_mem_single g.2 (k := 1) (l := 0) (by simp) (by simp)
    have h20 := entry_zero_of_mem_single g.2 (k := 2) (l := 0) (by simp) (by simp)
    have hd : (g.1 : Matrix (Fin 3) (Fin 3) K).det = 1 := g.1.2
    rw [Matrix.det_fin_three, h10, h20] at hd
    rw [hρ₁, hρ₂, Matrix.det_fin_two_of]
    linear_combination hd
  · intro g h1 h2
    have h10 := entry_zero_of_mem_single g.2 (k := 1) (l := 0) (by simp) (by simp)
    have h20 := entry_zero_of_mem_single g.2 (k := 2) (l := 0) (by simp) (by simp)
    rw [hρ₁] at h1
    rw [hρ₂] at h2
    have h11 := congrFun (congrFun h2 0) 0
    have h12 := congrFun (congrFun h2 0) 1
    have h21 := congrFun (congrFun h2 1) 0
    have h22 := congrFun (congrFun h2 1) 1
    simp at h11 h12 h21 h22
    refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h10, h20, h11, h12, h21, h22,
        CharTwo.add_self_eq_zero]
  · intro d hd hdP
    have h := (gradedPerfectSL_holds K 3 {1} d hdP 0 1 hS).1
    rw [hρ₁]
    have h' : (cutBlock (d : Matrix (Fin 3) (Fin 3) K) 0 1 hS.2.1 :
      Matrix (Fin 1) (Fin 1) K).det = 1 := h
    rw [Matrix.det_fin_one] at h'
    exact h'

theorem torusThree_two (hp : p.Prime) (hp2 : p ≠ 2)
    {E D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hEQ : E ≤ flagStabilizer 3 K {2}) (hDQ : D ≤ flagStabilizer 3 K {2}) (hEp : IsPGroup p E)
    (hD : ⁅D, D⁆ = D) (hdvd : p ∣ Nat.card D) (hcomm : ∀ e ∈ E, ∀ d ∈ D, e * d = d * e) :
    IsCyclic E := by
  have hS : IsConsecutiveCut 3 ({2} : Set ℕ) 2 3 :=
    ⟨by omega, le_rfl, Or.inr rfl, Or.inl rfl, by simp⟩
  have hB : IsConsecutiveCut 3 ({2} : Set ℕ) 0 2 :=
    ⟨by omega, by omega, Or.inl rfl, Or.inr rfl, by simp⟩
  let ρ₁ : ↥(flagStabilizer 3 K {2}) →* K := detMonoidHom.comp (cutBlockHom hS)
  let ρ₂ : ↥(flagStabilizer 3 K {2}) →* Matrix (Fin 2) (Fin 2) K := cutBlockHom hB
  have hρ₁ : ∀ g : ↥(flagStabilizer 3 K {2}),
      ρ₁ g = (g.1 : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    intro g
    show Matrix.det (cutBlock (g.1 : Matrix (Fin 3) (Fin 3) K) 2 3 hS.2.1 :
      Matrix (Fin 1) (Fin 1) K) = _
    rw [Matrix.det_fin_one]
    rfl
  have hρ₂ : ∀ g : ↥(flagStabilizer 3 K {2}), ρ₂ g =
      !![(g.1 : Matrix (Fin 3) (Fin 3) K) 0 0, (g.1 : Matrix (Fin 3) (Fin 3) K) 0 1;
        (g.1 : Matrix (Fin 3) (Fin 3) K) 1 0, (g.1 : Matrix (Fin 3) (Fin 3) K) 1 1] := by
    intro g
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine torusThree_of_homs hp hp2 ρ₁ ρ₂ ?_ ?_ ?_ hEQ hDQ hEp hD hdvd hcomm
  · intro g
    have h20 := entry_zero_of_mem_single g.2 (k := 2) (l := 0) (by simp) (by simp)
    have h21 := entry_zero_of_mem_single g.2 (k := 2) (l := 1) (by simp) (by simp)
    have hd : (g.1 : Matrix (Fin 3) (Fin 3) K).det = 1 := g.1.2
    rw [Matrix.det_fin_three, h20, h21] at hd
    rw [hρ₁, hρ₂, Matrix.det_fin_two_of]
    linear_combination hd
  · intro g h1 h2
    have h20 := entry_zero_of_mem_single g.2 (k := 2) (l := 0) (by simp) (by simp)
    have h21 := entry_zero_of_mem_single g.2 (k := 2) (l := 1) (by simp) (by simp)
    rw [hρ₁] at h1
    rw [hρ₂] at h2
    have h00 := congrFun (congrFun h2 0) 0
    have h01 := congrFun (congrFun h2 0) 1
    have h10 := congrFun (congrFun h2 1) 0
    have h11 := congrFun (congrFun h2 1) 1
    simp at h00 h01 h10 h11
    refine Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h20, h21, h00, h01, h10, h11,
        CharTwo.add_self_eq_zero]
  · intro d hd hdP
    have h := (gradedPerfectSL_holds K 3 {2} d hdP 2 3 hS).1
    rw [hρ₁]
    have h' : (cutBlock (d : Matrix (Fin 3) (Fin 3) K) 2 3 hS.2.1 :
      Matrix (Fin 1) (Fin 1) K).det = 1 := h
    rw [Matrix.det_fin_one] at h'
    exact h'

theorem torusThreeCell_proof : TorusThreeCell := by
  intro K _ _ _ I p hp hp5 hK hpK hI hne hnb E D hEQ hDQ hEp hD hdvd hcomm
  have hp2 : p ≠ 2 := by omega
  obtain ⟨c, hc⟩ := hne
  obtain ⟨i, hi1, hi3, hiI⟩ := hnb
  have hI' : I = {c} := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have h1 := hI x hx
      have h2 := hI c hc
      have : x ≠ i := fun h => hiI (h ▸ hx)
      have : c ≠ i := fun h => hiI (h ▸ hc)
      show x = c
      omega
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hc
  subst hI'
  rcases (show c = 1 ∨ c = 2 by have := hI c hc; omega) with rfl | rfl
  · exact torusThree_one hp (by omega) hEQ hDQ hEp hD hdvd hcomm
  · exact torusThree_two hp (by omega) hEQ hDQ hEp hD hdvd hcomm

end Cases

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
