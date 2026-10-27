module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSpread
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndBar
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalRoot
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSwap
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSwapTen

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_swap_datum (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
    {P : Subgroup G} (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g))
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hPH : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G))) :
    ∃ d'' : DeltaDatum D Abar a, d''.g = d.g⁻¹ ∧
      d''.T = rightConjugate (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) d.g⁻¹ ∧
      d''.S = rightConjugate P d.g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set W := d.S ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) with hWdef
  obtain ⟨-, -, hne', U'', hU''⟩ := inv_mem_deltaConjugates hloc hC (datum_mem_delta d)
  have hT'' : IsSylowOf 2 (rightConjugate W d.g⁻¹) (rightConjugate A d.g⁻¹ ⊓
      Subgroup.normalizer (A : Set G)) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hW d.g⁻¹
    rwa [rightConjugate_inf_normalizer'] at h1
  have hS'' : IsSylowOf 2 (rightConjugate P d.g⁻¹) A := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hP d.g⁻¹
    rwa [rightConjugate_rightConjugate_inv] at h1
  have hinv'' : rightConjugate W d.g⁻¹ ≤
      Subgroup.normalizer (rightConjugate P d.g⁻¹ : Set G) :=
    AschbacherTheorem3.rightConjugate_le_normalizer hWP d.g⁻¹
  have hI'' : IsSylowOf 2 (rightConjugate P d.g⁻¹ ⊓ rightConjugate H d.g⁻¹)
      (A ⊓ rightConjugate H d.g⁻¹) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hPH d.g⁻¹
    rwa [AschbacherTheorem3.rightConjugate_inf, AschbacherTheorem3.rightConjugate_inf,
      rightConjugate_rightConjugate_inv] at h1
  exact ⟨⟨d.g⁻¹, hne', U'', hU'', rightConjugate W d.g⁻¹, hT'',
    rightConjugate P d.g⁻¹, hS'', hinv'', hI''⟩, rfl, rfl, rfl⟩

omit [Finite G] in
theorem rightConjugate_conj_inv (X : Subgroup G) (g z : G) :
    rightConjugate (rightConjugate X g⁻¹) (g * z * g⁻¹) =
      rightConjugate (rightConjugate X z) g⁻¹ := by
  rw [rightConjugate_mul, rightConjugate_mul]
  congr 1
  group

omit [Finite G] in
theorem rightConjugate_inv_rightConjugate (X : Subgroup G) (g : G) :
    rightConjugate (rightConjugate X g⁻¹) g = X := by
  rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]

omit [Finite G] in
theorem swap_datum_facts {a : Fin r} (d d'' : DeltaDatum D Abar a) {P : Subgroup G}
    (hg'' : d''.g = d.g⁻¹)
    (hT'' : d''.T = rightConjugate (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) d.g⁻¹)
    (hS'' : d''.S = rightConjugate P d.g⁻¹)
    (hPT : P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T) :
    AschbacherTheorem3.omegaOne d''.T = rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)))
        d.g⁻¹ ∧
    d''.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d''.g : Set G) =
      rightConjugate d.T d.g⁻¹ := by
  refine ⟨by rw [hT'', omegaOne_rightConjugate], ?_⟩
  rw [hS'', hg'', ← AschbacherTheorem3.rightConjugate_normalizer,
    ← AschbacherTheorem3.rightConjugate_inf, hPT]

theorem exists_swap_root (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a)
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
          rightConjugate (Subgroup.normalizer (D : Set G)) d''.g = ⊥ := by
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
  obtain ⟨c, hc, hcS, hcN, -, hcH, -⟩ :=
    exists_root_conj hloc hC d'' hT''ab hW''ab hcard'' hUZ'' hSH'' hnot''
  exact ⟨d'', hg'', hT'', hS'', c, hc, hcS, hcN, hcH⟩

theorem le_zStar_conj_of_root (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a)
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
    (hSH : ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
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
    AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d'', hg'', hT'', hS'', c, -, hcS, hcN, hcH⟩ :=
    exists_swap_root hloc hC d hW hT hWab hcard hVZ hP hWP hPH hPT hPnot hzL hzP hzK
  obtain ⟨hU'', hW''⟩ := swap_datum_facts d d'' hg'' hT'' hS'' hPT
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
    (rightConjugate A d.g : Set G)) with hVdef
  set Y := AschbacherTheorem3.omegaOne d''.T with hYdef
  set X := AschbacherTheorem3.omegaOne (d''.S ⊓ Subgroup.normalizer
    (rightConjugate A d''.g : Set G)) with hXdef
  have hX : X = rightConjugate U d.g⁻¹ := by rw [hXdef, hW'', omegaOne_rightConjugate]
  obtain ⟨b, hbS, hbH, hbU⟩ := exists_conj_of_not_le d hSH
  have hUV := sup_conj_eq hloc hC d hT hWab hcard hbS hbH hbU
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hV2 : IsPGroup 2 V := d.sylowS.isPGroup.to_le
    ((AschbacherTheorem3.omegaOne_le _).trans inf_le_left)
  have hcomm := UV_comm hC d hT hWab
  have hUNV : U ≤ Subgroup.normalizer (V : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hcomm.is_comm.comm ⟨v, Subgroup.mem_sup_right hv⟩
        ⟨u, Subgroup.mem_sup_left hu⟩))
  have hVU : V ⊓ U = ⊥ := le_bot_iff.mp (by
    rw [inf_comm]
    exact (inf_le_inf_left U ((AschbacherTheorem3.omegaOne_le _).trans
      (inf_le_left.trans d.sylowS.le))).trans (EndHyp.U_inf_A hC).le)
  have hKeq : Y ⊔ X = rightConjugate (V ⊔ U) d.g⁻¹ := by
    rw [rightConjugate_sup, ← hX, hU'']
  have hK2 : IsPGroup 2 (Y ⊔ X : Subgroup G) := by
    rw [hKeq]
    exact AschbacherTheorem3.isPGroup_rightConjugate
      (by rw [sup_comm]; exact IsPGroup.to_sup_of_normal_right' hU2 hV2 hUNV) _
  have hcardK : Nat.card (Y ⊔ X : Subgroup G) = Nat.card X * Nat.card Y := by
    rw [hU'', hX, card_sup_of_inf_eq_bot (AschbacherTheorem3.rightConjugate_le_normalizer hUNV _)
      (by rw [← AschbacherTheorem3.rightConjugate_inf, hVU, AschbacherTheorem3.rightConjugate_bot]),
      mul_comm]
  have hXY : Nat.card X = Nat.card Y := by
    rw [hU'', hX, rightConjugate_card, rightConjugate_card]
    exact hcard
  have hdist : ∀ y₁ ∈ rightConjugate Y c, ∀ y₁' ∈ rightConjugate Y c,
      d''.g * y₁ * (d''.g * y₁')⁻¹ ∈ H → y₁ = y₁' := by
    intro y₁ hy₁ y₁' hy₁' hmem
    have h1 : y₁ * y₁'⁻¹ ∈ rightConjugate Y c ⊓ rightConjugate H d''.g := by
      refine ⟨(rightConjugate Y c).mul_mem hy₁ ((rightConjugate Y c).inv_mem hy₁'), ?_⟩
      refine (mem_rightConjugate_iff _ _ _).mpr ?_
      have : d''.g * (y₁ * y₁'⁻¹) * d''.g⁻¹ = d''.g * y₁ * (d''.g * y₁')⁻¹ := by group
      rw [this]
      exact hmem
    rw [hcH, Subgroup.mem_bot] at h1
    calc y₁ = y₁ * y₁'⁻¹ * y₁' := by group
      _ = y₁' := by rw [h1, one_mul]
  have hYH : d''.S ⊔ Y ≤ H := sup_le (d''.sylowS.le.trans EndHyp.A_le_H) (EndHyp.U_le_H hC)
  have hdistX : ∀ y₁ ∈ rightConjugate Y c, d''.g * y₁ * (1 : G)⁻¹ ∉ H := by
    intro y₁ hy₁ hmem
    apply datum_g_not_mem d''
    have : d''.g = d''.g * y₁ * (1 : G)⁻¹ * y₁⁻¹ := by group
    rw [this]
    exact H.mul_mem hmem (H.inv_mem (hYH (hcS hy₁)))
  have hZK : rightConjugate (rightConjugate U b) d.g⁻¹ ≤ Y ⊔ X := by
    rw [hKeq, sup_comm, hUV]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right _
  have hZX : rightConjugate (rightConjugate U b) d.g⁻¹ ⊓ X = ⊥ := by
    rw [hX, ← AschbacherTheorem3.rightConjugate_inf, inf_comm, U_inf_conj hC d hbH,
      AschbacherTheorem3.rightConjugate_bot]
  have hZA : rightConjugate (rightConjugate U b) d.g⁻¹ ≤
      rightConjugate A (d.g * b * d.g⁻¹) := by
    refine (AschbacherTheorem3.rightConjugate_le_rightConjugate
      (AschbacherTheorem3.rightConjugate_le_rightConjugate (EndHyp.U_le_L (d := d)) b)
        d.g⁻¹).trans (le_of_eq ?_)
    rw [rightConjugate_mul, rightConjugate_mul, mul_assoc]
  obtain ⟨y₁, -, hZle⟩ := le_rightConjugate_of_spread hC (K := Y ⊔ X) (X := X) (Y := Y)
    (Y₁ := rightConjugate Y c) (Z := rightConjugate (rightConjugate U b) d.g⁻¹)
    (κX := 1) (κY := d''.g) (κZ := d.g * b * d.g⁻¹) hK2 le_sup_right le_sup_left hcardK hXY
    hcN (by rw [rightConjugate_card])
    (fun x hx _ => hasType_of_mem_factor hC (d''.sylowS.le
      ((AschbacherTheorem3.omegaOne_le _ hx).1)))
    (fun y hy _ => hasType_of_mem_conj_factor hC (d''.sylowT.le
      (EndHyp.U_le_T hy)).1)
    hdist hdistX hZK hZX (fun x hx _ => hasType_of_mem_conj_factor hC (hZA hx))
  have hU4 := four_le_card_U hloc hC d
  have hUb1 : rightConjugate (rightConjugate U b) d.g⁻¹ ≠ ⊥ := by
    intro h
    rw [AschbacherTheorem3.rightConjugate_eq_bot_iff,
      AschbacherTheorem3.rightConjugate_eq_bot_iff] at h
    rw [← hUdef, h, Subgroup.card_bot] at hU4
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUb1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzY := hZle hz
  rw [mem_rightConjugate_iff] at hzY
  have hy1 : y₁ * z * y₁⁻¹ ≠ 1 := by
    intro h
    apply hz1'
    calc z = y₁⁻¹ * (y₁ * z * y₁⁻¹) * y₁ := by group
      _ = 1 := by rw [h]; group
  have hty := hasType_conj (hasType_of_mem_conj_factor hC (d''.sylowT.le
    (EndHyp.U_le_T hzY)).1) y₁
  rw [show y₁⁻¹ * (y₁ * z * y₁⁻¹) * y₁ = z by group] at hty
  have hK2z : ∃ k : ℕ, z ^ (2 ^ k) = 1 := twoElt_of_mem hK2 (hZK hz)
  have hm := hasType_unique hC hK2z hz1' hty (hasType_of_mem_conj_factor hC (hZA hz))
  rw [hg''] at hm
  have hUle : U ≤ rightConjugate V (d.g⁻¹ * y₁ * d.g * b⁻¹) := by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hZle d.g
    rw [rightConjugate_inv_rightConjugate, hU'', rightConjugate_conj_conj] at h1
    have h2 := AschbacherTheorem3.rightConjugate_le_rightConjugate h1 b⁻¹
    rwa [rightConjugate_mul U b b⁻¹, mul_inv_cancel, rightConjugate_one,
      rightConjugate_mul] at h2
  have hVZ' : V ≤ zStar D Abar := hVZ.trans (factorZStar_le_zStar hC.hyp a)
  refine hUle.trans ((AschbacherTheorem3.rightConjugate_le_rightConjugate hVZ' _).trans
    (le_of_eq ?_))
  have hn : d.g⁻¹ * y₁ * d.g * b⁻¹ = d.g⁻¹ * y₁ * (d.g * b * d.g⁻¹)⁻¹ * d.g := by group
  rw [hn, ← rightConjugate_mul, (rightConjugate_eq_self_iff (zStar D Abar) _).mpr
    (normalizer_le_normalizer_zStar hC.hyp hm)]

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
