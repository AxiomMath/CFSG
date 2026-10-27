module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaximal
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2BigCell
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Hom

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement MatrixGroups

section F2

theorem twF2_comm_t21_t13 {K : Type} [Field K] (a b : K) :
    ⁅t21 a, t13 b⁆ = t23 (a * b) := by
  rw [commutatorElement_def, t21_inv, t13_inv]
  apply Subtype.ext
  show (t21 a : Matrix (Fin 3) (Fin 3) K) * t13 b * t21 (-a) * t13 (-b) = t23 (a * b)
  rw [t21_coe, t13_coe, t21_coe, t13_coe, t23_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem twF2_comm_t13_t32 {K : Type} [Field K] (a b : K) :
    ⁅t13 a, t32 b⁆ = t12 (a * b) := by
  rw [commutatorElement_def, t13_inv, t32_inv]
  apply Subtype.ext
  show (t13 a : Matrix (Fin 3) (Fin 3) K) * t32 b * t13 (-a) * t32 (-b) = t12 (a * b)
  rw [t13_coe, t32_coe, t13_coe, t32_coe, t12_coe]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem twF2_comm_mem {K : Type} [Field K] {H₁ : Subgroup SL(3, K)} {x y : SL(3, K)}
    (hx : x ∈ H₁) (hy : y ∈ H₁) : ⁅x, y⁆ ∈ H₁ := by
  rw [commutatorElement_def]
  exact H₁.mul_mem (H₁.mul_mem (H₁.mul_mem hx hy) (H₁.inv_mem hx)) (H₁.inv_mem hy)

theorem twF2_a2_close {K : Type} [Field K] [Finite K] {k : Subfield K}
    (hk : Nat.card k = 2) (hmax : ∀ F : Subfield K, k ≤ F → F = k ∨ F = ⊤)
    {H₁ : Subgroup SL(3, K)} (h12 : t12 1 ∈ H₁) (h23 : t23 1 ∈ H₁) (h31 : t31 1 ∈ H₁)
    (h13 : t13 1 ∈ H₁) {s : K} (hs : s ∉ k) (hts : t13 s ∈ H₁) (c : K) :
    t12 c ∈ H₁ := by
  have hA : t21 1 ∈ H₁ := by
    have e := comm_t23_t31 (1 : K) 1
    rw [mul_one] at e
    rw [← e]
    exact twF2_comm_mem h23 h31
  have hB : t32 1 ∈ H₁ := by
    have e := comm_t31_t12 (1 : K) 1
    rw [mul_one] at e
    rw [← e]
    exact twF2_comm_mem h31 h12
  have hT12 : ∀ a : K, t13 a ∈ H₁ → t12 a ∈ H₁ := by
    intro a ha
    have e := twF2_comm_t13_t32 a 1
    rw [mul_one] at e
    rw [← e]
    exact twF2_comm_mem ha hB
  have hT23 : ∀ b : K, t13 b ∈ H₁ → t23 b ∈ H₁ := by
    intro b hb
    have e := twF2_comm_t21_t13 1 b
    rw [one_mul] at e
    rw [← e]
    exact twF2_comm_mem hA hb
  have hmul : ∀ a b : K, t13 a ∈ H₁ → t13 b ∈ H₁ → t13 (a * b) ∈ H₁ := by
    intro a b ha hb
    rw [← comm_t12_t23 a b]
    exact twF2_comm_mem (hT12 a ha) (hT23 b hb)
  have hadd : ∀ a b : K, t13 a ∈ H₁ → t13 b ∈ H₁ → t13 (a + b) ∈ H₁ := by
    intro a b ha hb
    rw [t13_add]
    exact H₁.mul_mem ha hb
  have hneg : ∀ a : K, t13 a ∈ H₁ → t13 (-a) ∈ H₁ := by
    intro a ha
    rw [← t13_inv]
    exact H₁.inv_mem ha
  have hinv : ∀ a : K, t13 a ∈ H₁ → a ≠ 0 → t13 a⁻¹ ∈ H₁ := by
    intro a ha ha0
    let f : {x : K | t13 x ∈ H₁} → {x : K | t13 x ∈ H₁} := fun x =>
      ⟨a * x, hmul a x ha x.2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ ha0 (congrArg Subtype.val hxy)
    obtain ⟨x, hx⟩ := (Finite.surjective_of_injective hf) ⟨1, h13⟩
    have hx1 : a * (x : K) = 1 := congrArg Subtype.val hx
    have hxa : (x : K) = a⁻¹ := (inv_eq_of_mul_eq_one_right hx1).symm
    rw [← hxa]
    exact x.2
  let U : Subfield K :=
    { carrier := {x : K | t13 x ∈ H₁}
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := h13
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      zero_mem' := by
        show t13 0 ∈ H₁
        rw [t13_zero]
        exact H₁.one_mem
      neg_mem' := fun {a} ha => hneg a ha
      inv_mem' := fun {a} ha => by
        by_cases ha0 : a = 0
        · subst ha0
          show t13 (0 : K)⁻¹ ∈ H₁
          rw [inv_zero, t13_zero]
          exact H₁.one_mem
        · exact hinv a ha ha0 }
  have hkU : k ≤ U := by
    intro d hd
    rcases zero_or_one_of_mem_card_two hk hd with rfl | rfl
    · show t13 0 ∈ H₁
      rw [t13_zero]
      exact H₁.one_mem
    · exact h13
  rcases hmax U hkU with hUk | hUtop
  · exact absurd (by rw [← hUk]; exact hts) hs
  · have hcU : c ∈ U := by
      rw [hUtop]
      exact Subfield.mem_top c
    exact hT12 c hcU

theorem twF2_eq_top_of_e2 {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (hσ1 : ∃ x : K, σ x ≠ x)
    {H : Subgroup (adjointGroup Tag.D4 K)} (hΓ : fixedSubgroup (d4Twist 1 σ) ≤ H)
    (hE2 : ∀ u : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) u ∈ H) : H = ⊤ := by
  have hw1 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.D4))
      (nd 2) (1 : Kˣ) ∈ H := by
    unfold CFSG.LieType.Steinberg.weylElement
    refine H.mul_mem (H.mul_mem (hE2 _) ?_) (hE2 _)
    refine hΓ (xPar_neg_e2_mem_fixed hσ3 ?_)
    simp
  have hrefl : CFSG.LieType.RootSystem.reflection Tag.D4.cartan (nd 2)
      (Pi.single (nd 2) 1) = -Pi.single (nd 2) 1 := by
    erw [CFSG.LieType.RootSystem.reflection_apply]
    funext j
    fin_cases j <;> decide
  have hE2neg : ∀ u : K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) u ∈ H := by
    intro u
    obtain ⟨ε, hε, hcj⟩ := weylElement_xPar_conj (F := rootOperatorFamily Tag.D4) (K := K)
      (nd 2) (isRoot_single Tag.D4 (nd 2))
    have hm := H.mul_mem (H.mul_mem hw1 (hE2 (ε * u))) (H.inv_mem hw1)
    rw [hcj 1 (ε * u), hrefl] at hm
    have e : (ε : K) * (((1 : Kˣ) ^ (-(∑ j, Tag.D4.cartan (nd 2) j *
        (Pi.single (nd 2) 1 : Fin Tag.D4.rank → ℤ) j)) : Kˣ) : K) * ((ε : K) * u) = u := by
      rcases hε with rfl | rfl <;> simp
    rw [e] at hm
    exact hm
  have hE' : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ H ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ H :=
    fun c => ⟨hE2 c, hE2neg c⟩
  obtain ⟨o0, o1, o3⟩ := outer_root_mem_of_triples hσ3 hσ1 hE'
    (fun s => hΓ (triple_pos_mem hσ3 s)) (fun s => hΓ (triple_neg_mem hσ3 s))
  have hsimple : ∀ i : Fin Tag.D4.rank, ∀ c : K,
      xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c ∈ H ∧
        xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c ∈ H := by
    intro i
    fin_cases i
    · exact o0
    · exact o1
    · exact hE'
    · exact o3
  have hw : ∀ i : Fin Tag.D4.rank, CFSG.LieType.Steinberg.weylElement
      (xPar (rootOperatorFamily Tag.D4)) i (1 : Kˣ) ∈ H := by
    intro i
    unfold CFSG.LieType.Steinberg.weylElement
    exact H.mul_mem (H.mul_mem ((hsimple i _).1) ((hsimple i _).2)) ((hsimple i _).1)
  exact eq_top_of_forall_xPar_mem H fun γ hγ c =>
    (xPar_mem_iff_of_roots H hw cartanD4_connected hγ (isRoot_single Tag.D4 (nd 0)) c).2
      ((hsimple (nd 0) c).1)

theorem twF2_core {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hK : Nat.card K = Nat.card k ^ d) (H : Subgroup ↥(adjointGroup Tag.D4 K))
    (h1 : xPar (rootOperatorFamily Tag.D4) d4F2Theta 1 ∈ H)
    (h2 : xPar (rootOperatorFamily Tag.D4) d4F2Delta1 1 ∈ H)
    (h3 : xPar (rootOperatorFamily Tag.D4) d4F2Delta2 1 ∈ H)
    {q : ↥(adjointGroup Tag.D4 K)} (hq : q ∈ d4F2_Qgrp K) {μ : K} (hμ : μ ∉ k)
    (hy : q * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) μ * q⁻¹ ∈ H) :
    ∃ s : K, s ∉ k ∧ xPar (rootOperatorFamily Tag.D4) d4F2Theta s ∈ H := by
  obtain ⟨φ, h12, h23, h13, h31⟩ := d4F2_exists_a2Hom (K := K)
  obtain ⟨c₁, hc₁⟩ := d4F2_Q_conj_delta (Subgroup.inv_mem _ hq) d4F2_isRoot_delta1 d4F2_lvl_delta1
  obtain ⟨c₂, hc₂⟩ := d4F2_Q_conj_delta (Subgroup.inv_mem _ hq) d4F2_isRoot_delta2 d4F2_lvl_delta2
  let H₁ : Subgroup SL(3, K) := (H.comap (MulAut.conj q).toMonoidHom).comap φ
  have hmem : ∀ g : SL(3, K), g ∈ H₁ ↔ q * φ g * q⁻¹ ∈ H := fun g => Iff.rfl
  have hsub : A2Gen μ c₁ c₂ ≤ H₁ := by
    rw [A2Gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · show q * φ (t13 1) * q⁻¹ ∈ H
      rw [h13, ((d4F2_commute_Q_theta hq 1).eq), mul_inv_cancel_right]
      exact h1
    · show q * φ (t31 μ) * q⁻¹ ∈ H
      rw [h31]
      exact hy
    · show q * φ (t12 1 * t13 c₁) * q⁻¹ ∈ H
      have h := hc₁
      rw [inv_inv] at h
      rw [map_mul, h12, h13, ← h]
      have e : q * (q⁻¹ * xPar (rootOperatorFamily Tag.D4) d4F2Delta1 1 * q) * q⁻¹ =
          xPar (rootOperatorFamily Tag.D4) d4F2Delta1 1 := by group
      rw [e]
      exact h2
    · show q * φ (t23 1 * t13 c₂) * q⁻¹ ∈ H
      have h := hc₂
      rw [inv_inv] at h
      rw [map_mul, h23, h13, ← h]
      have e : q * (q⁻¹ * xPar (rootOperatorFamily Tag.D4) d4F2Delta2 1 * q) * q⁻¹ =
          xPar (rootOperatorFamily Tag.D4) d4F2Delta2 1 := by group
      rw [e]
      exact h3
  obtain ⟨s, hs, hts⟩ := a2_lemma hk hd hd2 hK hμ c₁ c₂
  refine ⟨s, hs, ?_⟩
  have h1' := (hmem _).1 (hsub hts)
  rwa [h13, ((d4F2_commute_Q_theta hq s).eq), mul_inv_cancel_right] at h1'

@[expose] def D4TwF2EntryProp : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), orderOf σ = 3 →
    Nat.card (fixSubfield σ) = 2 →
    ∀ g : adjointGroup Tag.D4 K, g ∉ fixedSubgroup (d4Twist 1 σ) →
      ∃ r ∈ fixedSubgroup (d4Twist 1 σ), ∃ r' ∈ fixedSubgroup (d4Twist 1 σ),
        entry (r * g * r') (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) ∉
          fixSubfield σ

theorem twF2_rho_theta : rho d4F2Theta = d4F2Theta := by
  rw [← d4Root_22_eq]
  exact rho_d4Root_22

theorem twF2_rho_delta2 : rho d4F2Delta2 = d4F2Delta2 := by
  funext i
  fin_cases i <;> rfl

theorem twF2_rho_negTheta : rho (-d4F2Theta) = -d4F2Theta := by
  funext i
  fin_cases i <;> rfl

theorem twF2_maximal (hE : D4TwF2EntryProp) : D4TwistedF2Case := by
  intro K _ _ σ hσ hk M hΓM
  by_cases hM : M ≤ fixedSubgroup (d4Twist 1 σ)
  · exact Or.inl (le_antisymm hM hΓM)
  right
  obtain ⟨g, hgM, hg⟩ : ∃ g ∈ M, g ∉ fixedSubgroup (d4Twist 1 σ) := by
    by_contra h
    push Not at h
    exact hM h
  have hσ3 := sigma_cube_of_orderOf hσ
  have hσ1 := exists_sigma_ne_self hσ
  obtain ⟨r, hr, r', hr', hbad⟩ := hE K σ hσ hk g hg
  have h2 : (2 : K) = 0 := by
    have h11 : (1 : K) + 1 ∈ fixSubfield σ :=
      (fixSubfield σ).add_mem (fixSubfield σ).one_mem (fixSubfield σ).one_mem
    rcases zero_or_one_of_mem_card_two hk h11 with h | h
    · rw [one_add_one_eq_two] at h
      exact h
    · exfalso
      have : (1 : K) = 0 := by
        have := congrArg (fun x => x - 1) h
        simpa using this
      exact one_ne_zero this
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hK : Nat.card K = Nat.card (fixSubfield σ) ^ 3 :=
    (CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ).trans (by rw [hσ])
  have hne0 : entry (r * g * r') (negLabel d4F2_theta_isMax.1)
      (rootLabel d4F2_theta_isMax.1) ≠ 0 :=
    fun h => hbad (h ▸ (fixSubfield σ).zero_mem)
  have hg'M : r * g * r' ∈ M := M.mul_mem (M.mul_mem (hΓM hr) hgM) (hΓM hr')
  obtain ⟨q, hq, ε, hε, hconj⟩ := d4F2_bigCell_conj_Q (r * g * r') hne0
  have hθ1 : xPar (rootOperatorFamily Tag.D4) d4F2Theta 1 ∈ M :=
    hΓM (xPar_mem_fixedSubgroup_d4Twist hσ3 d4F2_isRoot_theta twF2_rho_theta (map_one σ))
  have hy : q * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta)
      ((ε : K) * entry (r * g * r') (negLabel d4F2_theta_isMax.1)
        (rootLabel d4F2_theta_isMax.1)) * q⁻¹ ∈ M := by
    have h := hconj 1
    rw [mul_one] at h
    rw [← h]
    exact M.mul_mem (M.mul_mem hg'M hθ1) (M.inv_mem hg'M)
  have hμ : (ε : K) * entry (r * g * r') (negLabel d4F2_theta_isMax.1)
      (rootLabel d4F2_theta_isMax.1) ∉ fixSubfield σ := by
    intro hm
    apply hbad
    rcases hε with rfl | rfl
    · simpa using hm
    · simpa using (fixSubfield σ).neg_mem hm
  have hδ1 : xPar (rootOperatorFamily Tag.D4) d4F2Delta1 1 ∈ M :=
    hΓM (xPar_e2_mem_fixed hσ3 (map_one σ))
  have hδ2 : xPar (rootOperatorFamily Tag.D4) d4F2Delta2 1 ∈ M :=
    hΓM (xPar_mem_fixedSubgroup_d4Twist hσ3 d4F2_isRoot_delta2 twF2_rho_delta2 (map_one σ))
  obtain ⟨s, hs, hsM⟩ := twF2_core hk Nat.prime_three (by norm_num) hK M hθ1 hδ1 hδ2 hq hμ hy
  have hθ1' : xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) 1 ∈ M :=
    hΓM (xPar_mem_fixedSubgroup_d4Twist hσ3 (CFSG.LieType.Chevalley.IsRoot.neg d4F2_isRoot_theta)
      twF2_rho_negTheta (map_one σ))
  obtain ⟨φ, h12, h23, h13, h31⟩ := d4F2_exists_a2Hom (K := K)
  have hmax : ∀ F : Subfield K, fixSubfield σ ≤ F → F = fixSubfield σ ∨ F = ⊤ :=
    fun F hF => subfield_eq_or_top σ Nat.prime_three hσ F hF
  have m12 : t12 1 ∈ M.comap φ := Subgroup.mem_comap.2 (by rw [h12 1]; exact hδ1)
  have m23 : t23 1 ∈ M.comap φ := Subgroup.mem_comap.2 (by rw [h23 1]; exact hδ2)
  have m31 : t31 1 ∈ M.comap φ := Subgroup.mem_comap.2 (by rw [h31 1]; exact hθ1')
  have m13 : t13 1 ∈ M.comap φ := Subgroup.mem_comap.2 (by rw [h13 1]; exact hθ1)
  have mts : t13 s ∈ M.comap φ := Subgroup.mem_comap.2 (by rw [h13 s]; exact hsM)
  have hE2 : ∀ u : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) u ∈ M := by
    intro u
    have h := twF2_a2_close hk hmax m12 m23 m31 m13 hs mts u
    rw [Subgroup.mem_comap, h12 u] at h
    exact h
  exact twF2_eq_top_of_e2 hσ3 hσ1 hΓM hE2

theorem D4TwistedSubfieldMaximal_of_entry (hE : D4TwF2EntryProp) :
    D4TwistedSubfieldMaximal :=
  D4TwistedSubfieldMaximal_of_F2 (twF2_maximal hE)

end F2

end CFSG.LieType.SeitzGeneration.ExcWideThree
