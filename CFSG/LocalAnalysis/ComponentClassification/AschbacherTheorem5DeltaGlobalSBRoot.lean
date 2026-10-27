module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalWeyl
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLRoot

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem root_comm_mem (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    {U₁ : Subgroup G} (hU₁S : U₁ ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T)
    (hU₁N : U₁ ≤ Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔
      AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
          Set G))
    {u₁ : G} (hu₁ : u₁ ∈ U₁) {x : G} (hx : x ∈ AschbacherTheorem3.omegaOne d.T) :
    x⁻¹ * u₁⁻¹ * x * u₁ ∈ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) := by
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) with hVdef
  have hUc : ∀ y ∈ U, ∀ y' ∈ U, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hT.is_comm.comm ⟨y, EndHyp.U_le_T hy⟩ ⟨y', EndHyp.U_le_T hy'⟩)
  have hS : x⁻¹ * u₁⁻¹ * x * u₁ ∈ d.S :=
    comm_mem_of_mem_sup EndHyp.U_le_normalizer_S hUc (hU₁S hu₁) hx
  have hK : x⁻¹ * u₁⁻¹ * x * u₁ ∈ U ⊔ V := by
    have h1 : u₁⁻¹ * x * u₁ ∈ U ⊔ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hU₁N hu₁)) x).mp
        (Subgroup.mem_sup_left hx)
      simpa using this
    have : x⁻¹ * u₁⁻¹ * x * u₁ = x⁻¹ * (u₁⁻¹ * x * u₁) := by group
    rw [this]
    exact (U ⊔ V).mul_mem (Subgroup.mem_sup_left (U.inv_mem hx)) h1
  have hmem : x⁻¹ * u₁⁻¹ * x * u₁ ∈ (U ⊔ V) ⊓ aschbacherThm5Preimage D (Abar a) :=
    ⟨hK, d.sylowS.le hS⟩
  rwa [sup_inf_A_eq hC d hT hWab] at hmem

theorem comm_of_mem_zStar_conj {i : Fin r} {g x u : G}
    (hx : x ∈ rightConjugate (aschbacherThm5Preimage D (Abar i)) g)
    (hu : u ∈ rightConjugate (zStar D Abar) g)
    (h2 : ∃ k : ℕ, (u⁻¹ * x⁻¹ * u * x) ^ (2 ^ k) = 1) : x * u = u * x := by
  rw [mem_rightConjugate_iff] at hx hu
  have h1 := (mem_zStar_iff.mp hu).2 i _ hx
  have e : (g * u * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ * (g * u * g⁻¹) * (g * x * g⁻¹) =
      g * (u⁻¹ * x⁻¹ * u * x) * g⁻¹ := by group
  rw [e] at h1
  have h3 := eq_one_of_mem_core h1 (twoElt_conj h2 g)
  have h4 : u⁻¹ * x⁻¹ * u * x = 1 := by
    calc u⁻¹ * x⁻¹ * u * x = g⁻¹ * (g * (u⁻¹ * x⁻¹ * u * x) * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  calc x * u = x * u * (u⁻¹ * x⁻¹ * u * x) := by rw [h4, mul_one]
    _ = u * x := by group

theorem exists_swap_root_comm (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hVZ : AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a)
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T)
    (hPnot : ¬ P ≤ Subgroup.normalizer (D : Set G)) {z : G}
    (hzL : z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g)
    (hzP : rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hzK : ¬ rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    ∃ d'' : DeltaDatum D Abar a, d''.g = d.g⁻¹ ∧
      d''.T = rightConjugate (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) d.g⁻¹ ∧
      d''.S = rightConjugate P d.g⁻¹ ∧
      ∃ c ∈ aschbacherThm5Preimage D (Abar a),
        rightConjugate (AschbacherTheorem3.omegaOne d''.T) c ≤
          d''.S ⊔ AschbacherTheorem3.omegaOne d''.T ∧
        rightConjugate (AschbacherTheorem3.omegaOne d''.T) c ≤
          Subgroup.normalizer ((AschbacherTheorem3.omegaOne d''.T ⊔ AschbacherTheorem3.omegaOne
            (d''.S ⊓ Subgroup.normalizer
              (rightConjugate (aschbacherThm5Preimage D (Abar a)) d''.g : Set G)) : Subgroup G) :
                Set G) ∧
        rightConjugate (AschbacherTheorem3.omegaOne d''.T) c ⊓
          rightConjugate (Subgroup.normalizer (D : Set G)) d''.g = ⊥ ∧
        ∀ x ∈ rightConjugate (AschbacherTheorem3.omegaOne d''.T) c,
          ∀ v ∈ AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
            (rightConjugate (aschbacherThm5Preimage D (Abar a)) d''.g : Set G)), x * v = v * x := by
  obtain ⟨d'', hg'', hT'', hS''⟩ := exists_swap_datum hloc hC d hW hP hWP hPH
  obtain ⟨hU'', hW''⟩ := swap_datum_facts d d'' hg'' hT'' hS'' hPT
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate A d.g : Set G)) with hVdef
  have hV'' : AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) = rightConjugate U d.g⁻¹ := by
    rw [hW'', omegaOne_rightConjugate]
  have hT''ab : IsMulCommutative d''.T := by
    rw [hT'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hWab _
  have hW''ab : IsMulCommutative (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G) : Subgroup G) := by
    rw [hW'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hT _
  have hcard'' : Nat.card (AschbacherTheorem3.omegaOne d''.T) =
      Nat.card (AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
        (rightConjugate A d''.g : Set G))) := by
    rw [hU'', hV'', rightConjugate_card, rightConjugate_card]
    exact hcard.symm
  have hUZ'' : AschbacherTheorem3.omegaOne d''.T ≤ rightConjugate (zStar D Abar) d''.g := by
    rw [hU'', hg'']
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate
      (hVZ.trans (factorZStar_le_zStar hC.hyp a)) _
  have hSH'' : ¬ d''.S ≤ rightConjugate H d''.g := by
    rw [hS'', hg'']
    intro h
    apply hPnot
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate h d.g
    rwa [rightConjugate_inv_rightConjugate, rightConjugate_inv_rightConjugate] at h1
  have hnot'' : ∃ c ∈ A, rightConjugate (AschbacherTheorem3.omegaOne d''.T) c ≤
        d''.S ⊔ AschbacherTheorem3.omegaOne d''.T ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d''.T) c ≤
        AschbacherTheorem3.omegaOne d''.T ⊔ AschbacherTheorem3.omegaOne (d''.S ⊓
          Subgroup.normalizer (rightConjugate A d''.g : Set G)) := by
    refine ⟨d.g * z * d.g⁻¹, (mem_rightConjugate_iff A d.g z).mp hzL, ?_, ?_⟩
    · rw [hU'', hS'', rightConjugate_conj_inv, ← rightConjugate_sup]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hzP _
    · rw [hU'', hV'', rightConjugate_conj_inv, ← rightConjugate_sup]
      intro h
      apply hzK
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate h d.g
      rwa [rightConjugate_inv_rightConjugate, rightConjugate_inv_rightConjugate, sup_comm] at h1
  obtain ⟨c, hc, hcS, hcN, -, hcH, hcC⟩ :=
    exists_root_conj hloc hC d'' hT''ab hW''ab hcard'' hUZ'' hSH'' hnot''
  exact ⟨d'', hg'', hT'', hS'', c, hc, hcS, hcN, hcH, hcC⟩

theorem exists_L_root (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hT : IsMulCommutative d.T)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hVZ : AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a)
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)))
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T)
    (hPnot : ¬ P ≤ Subgroup.normalizer (D : Set G)) {z : G}
    (hzL : z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g)
    (hzP : rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    (hzK : ¬ rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    ∃ V₁ : Subgroup G, V₁ ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g ∧
      V₁ ≤ Subgroup.normalizer ((AschbacherTheorem3.omegaOne d.T ⊔
        AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) : Subgroup G) :
            Set G) ∧
      V₁ ⊓ Subgroup.normalizer (D : Set G) = ⊥ ∧
      Nat.card V₁ = Nat.card (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) ∧
      (∀ v₁ ∈ V₁, v₁ * v₁ = 1) ∧
      (∀ v₁ ∈ V₁, ∀ x ∈ AschbacherTheorem3.omegaOne d.T, v₁ * x = x * v₁) ∧
      (∀ v₁ ∈ V₁, ∀ y ∈ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)),
        y⁻¹ * v₁⁻¹ * y * v₁ ∈ AschbacherTheorem3.omegaOne d.T) := by
  obtain ⟨d'', hg'', hT'', hS'', c, -, hcS, hcN, hcH, hcC⟩ :=
    exists_swap_root_comm hloc hC d hW hT hWab hcard hVZ hP hWP hPH hPT hPnot hzL hzP hzK
  obtain ⟨hU'', hW''⟩ := swap_datum_facts d d'' hg'' hT'' hS'' hPT
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate A d.g : Set G)) with hVdef
  have hV'' : AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G)) = rightConjugate U d.g⁻¹ := by
    rw [hW'', omegaOne_rightConjugate]
  rw [hV''] at hcN hcC
  have hT''ab : IsMulCommutative d''.T := by
    rw [hT'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hWab _
  have hW''ab : IsMulCommutative (d''.S ⊓ Subgroup.normalizer
      (rightConjugate A d''.g : Set G) : Subgroup G) := by
    rw [hW'']
    exact AschbacherTheorem3.isMulCommutative_rightConjugate hT _
  have hq : ∀ y₁ ∈ rightConjugate (AschbacherTheorem3.omegaOne d''.T) c,
      ∀ x ∈ AschbacherTheorem3.omegaOne d''.T, x⁻¹ * y₁⁻¹ * x * y₁ ∈ rightConjugate U d.g⁻¹ :=
    fun y₁ hy₁ x hx => by
      have h1 := root_comm_mem hC d'' hT''ab hW''ab hcS (by rw [hV'']; exact hcN) hy₁ hx
      rwa [hV''] at h1
  have hel : IsElemAbelian 2
      (rightConjugate (rightConjugate (AschbacherTheorem3.omegaOne d''.T) c) d.g) :=
    isElemAbelian_rightConjugate (isElemAbelian_rightConjugate (isElemAbelian_omegaOne hT''ab) c)
      d.g
  have hmemY : ∀ y ∈ V, d.g * y * d.g⁻¹ ∈ AschbacherTheorem3.omegaOne d''.T := fun y hy => by
    rw [hU'', mem_rightConjugate_iff]
    simpa [mul_assoc] using hy
  have hmemU : ∀ x ∈ U, d.g * x * d.g⁻¹ ∈ rightConjugate U d.g⁻¹ := fun x hx => by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hx
  refine ⟨rightConjugate (rightConjugate (AschbacherTheorem3.omegaOne d''.T) c) d.g,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine AschbacherTheorem3.rightConjugate_le_rightConjugate (hcS.trans ?_) d.g
    exact sup_le (d''.sylowS.le.trans EndHyp.A_le_H) (EndHyp.U_le_H hC)
  · have h1 := AschbacherTheorem3.rightConjugate_le_normalizer hcN d.g
    rw [hU''] at h1 ⊢
    rwa [← rightConjugate_sup, rightConjugate_inv_rightConjugate, sup_comm] at h1
  · rw [← rightConjugate_inv_rightConjugate H d.g, ← AschbacherTheorem3.rightConjugate_inf,
      ← hg'', hcH, AschbacherTheorem3.rightConjugate_bot]
  · rw [rightConjugate_card, rightConjugate_card, hU'', rightConjugate_card]
  · intro v₁ hv₁
    rw [← sq]
    exact hel.2 v₁ hv₁
  · intro v₁ hv₁ x hx
    have h1 := hcC _ ((mem_rightConjugate_iff _ _ _).mp hv₁) _ (hmemU x hx)
    have h2 : d.g * (v₁ * x) * d.g⁻¹ = d.g * (x * v₁) * d.g⁻¹ := by
      calc d.g * (v₁ * x) * d.g⁻¹ = (d.g * v₁ * d.g⁻¹) * (d.g * x * d.g⁻¹) := by group
        _ = (d.g * x * d.g⁻¹) * (d.g * v₁ * d.g⁻¹) := h1
        _ = d.g * (x * v₁) * d.g⁻¹ := by group
    simpa using h2
  · intro v₁ hv₁ y hy
    have h1 := hq _ ((mem_rightConjugate_iff _ _ _).mp hv₁) _ (hmemY y hy)
    have e : (d.g * y * d.g⁻¹)⁻¹ * (d.g * v₁ * d.g⁻¹)⁻¹ * (d.g * y * d.g⁻¹) *
        (d.g * v₁ * d.g⁻¹) = d.g * (y⁻¹ * v₁⁻¹ * y * v₁) * d.g⁻¹ := by group
    rw [e, mem_rightConjugate_iff] at h1
    simpa [mul_assoc] using h1

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
