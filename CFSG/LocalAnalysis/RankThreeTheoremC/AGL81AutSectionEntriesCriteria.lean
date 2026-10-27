module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionDefs
public import CFSG.RankThree.PartOne.CTP.StrongPLinear
public import CFSG.RankThree.PartOne.K159.AutCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.RankThree.PartOne.K159 (AutWitness)

variable {p : ℕ}

theorem SmallAutomizer.of_mulEquiv {K X : Type} [Group K] [Finite K] [Group X] [Finite X]
    (e : K ≃* X) (h : SmallAutomizer p K) : SmallAutomizer p X := by
  intro T
  have hr : (T : Subgroup X) ≤ e.toMonoidHom.range := fun x _ => ⟨e.symm x, by simp⟩
  set T' : Sylow p K := T.comapOfInjective e.toMonoidHom e.injective hr with hT'
  have hmem : ∀ x : K, x ∈ (T' : Subgroup K) ↔ e x ∈ (T : Subgroup X) := fun x => Iff.rfl
  have hmem' : ∀ t ∈ (T : Subgroup X), e.symm t ∈ (T' : Subgroup K) := fun t ht => by
    rw [hmem, e.apply_symm_apply]
    exact ht
  obtain ⟨hab, hnorm⟩ := h T'
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun k hk => ?_⟩
  · have h1 := congrArg (fun z : ↥(T' : Subgroup K) => e (z : K))
      (hab.is_comm.comm ⟨_, hmem' a a.2⟩ ⟨_, hmem' b b.2⟩)
    apply Subtype.ext
    simpa using h1
  · have hk' : e.symm k ∈ Subgroup.normalizer ((T' : Subgroup K) : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmem, hmem, map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact (Subgroup.mem_normalizer_iff.mp hk) (e y)
    have key : ∀ n : ℕ, (∀ t ∈ (T' : Subgroup K), e.symm k ^ n * t * (e.symm k ^ n)⁻¹ = t) →
        ∀ t ∈ (T : Subgroup X), k ^ n * t * (k ^ n)⁻¹ = t := by
      intro n hn t ht
      have h1 := congrArg e (hn (e.symm t) (hmem' t ht))
      simpa [map_mul, map_pow, map_inv] using h1
    rcases hnorm _ hk' with h3 | h4
    · exact Or.inl (key 3 h3)
    · exact Or.inr (key 4 h4)

theorem not_smallAutomizer_of_hasNoncommPair {K : Type} [Group K] [Finite K]
    (h : HasNoncommPair p K) : ¬ SmallAutomizer p K := by
  intro hS
  obtain ⟨x, y, -, -, hxy, hP⟩ := h
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hx : x ∈ (T : Subgroup K) := hT (Subgroup.subset_closure (Set.mem_insert x {y}))
  have hy : y ∈ (T : Subgroup K) :=
    hT (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y)))
  exact hxy (congrArg Subtype.val ((hS T).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem autWitness_of_injective {X K : Type} [Group X] [Group K] (f : X →* K)
    (hf : Function.Injective f) (h : AutWitness p X) : AutWitness p K := by
  obtain ⟨U, hexp, hcard, g, hg, hmove⟩ := h
  refine ⟨U.map f, ?_, ?_, f g, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  · rw [Subgroup.card_map_of_injective hf]
    exact hcard
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨g * u * g⁻¹, hg u hu, by simp⟩
  · intro k hk1 hk4
    obtain ⟨u, hu, hne⟩ := hmove k hk1 hk4
    refine ⟨f u, ⟨u, hu, rfl⟩, fun h => hne (hf ?_)⟩
    simpa [map_mul, map_pow, map_inv] using h

theorem not_smallAutomizer_of_autWitness [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (h : AutWitness p K) : ¬ SmallAutomizer p K := by
  intro hS
  obtain ⟨U, hexp, -, g, hgU, hmove⟩ := h
  have hUp : IsPGroup p U := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨T, hUT⟩ := hUp.exists_le_sylow
  obtain ⟨hTab, hTaut⟩ := hS T
  set C : Subgroup K := Subgroup.centralizer (U : Set K) with hC
  have hTC : (T : Subgroup K) ≤ C := by
    intro t ht
    rw [hC, Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (hTab.is_comm.comm ⟨u, hUT hu⟩ ⟨t, ht⟩)
  have hpow : ∀ j : ℕ, ∀ u ∈ U, g ^ j * u * (g ^ j)⁻¹ ∈ U := by
    intro j
    induction j with
    | zero => intro u hu; simpa using hu
    | succ j ih =>
      intro u hu
      have h1 := hgU _ (ih u hu)
      rw [pow_succ']
      simpa only [mul_inv_rev, mul_assoc] using h1
  have hgU' : ∀ u : K, g * u * g⁻¹ ∈ U → u ∈ U := by
    intro u hu
    obtain ⟨m, hm⟩ : ∃ m, orderOf g = m + 1 := ⟨orderOf g - 1, by
      have := orderOf_pos g
      omega⟩
    have h1 : g ^ m * g = 1 := by rw [← pow_succ, ← hm, pow_orderOf_eq_one]
    have h2 : g ^ m * (g * u * g⁻¹) * (g ^ m)⁻¹ = u := by
      have h3 : (g ^ m)⁻¹ = g := (eq_inv_of_mul_eq_one_right h1).symm
      calc g ^ m * (g * u * g⁻¹) * (g ^ m)⁻¹ = (g ^ m * g) * u * (g⁻¹ * (g ^ m)⁻¹) := by
            simp only [mul_assoc]
        _ = u := by rw [h1, h3, inv_mul_cancel, one_mul, mul_one]
    rw [← h2]
    exact hpow m _ hu
  have hgTC : ((g • T : Sylow p K) : Subgroup K) ≤ C := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : g⁻¹ * x * g ∈ (T : Subgroup K) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      apply hgU'
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one, SetLike.mem_coe]
        using hu
    have h1 := (Subgroup.mem_centralizer_iff.mp (hTC hx')) _ hu'
    have h2 := congrArg (fun z => g * z * g⁻¹) h1
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C ((g • T).subtype hgTC) (T.subtype hTC)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hc
  have hn : (c : K) * g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hc)
  have hcU : ∀ v ∈ U, (c : K) * v * (c : K)⁻¹ = v := by
    intro v hv
    rw [← (Subgroup.mem_centralizer_iff.mp c.2) v hv, mul_inv_cancel_right]
  have hact : ∀ j : ℕ, ∀ u ∈ U,
      ((c : K) * g) ^ j * u * (((c : K) * g) ^ j)⁻¹ = g ^ j * u * (g ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro u _; simp
    | succ j ih =>
      intro u hu
      calc ((c : K) * g) ^ (j + 1) * u * (((c : K) * g) ^ (j + 1))⁻¹
          = (c : K) * (g * (((c : K) * g) ^ j * u * (((c : K) * g) ^ j)⁻¹) * g⁻¹) *
              (c : K)⁻¹ := by
            rw [pow_succ']
            simp only [mul_inv_rev, mul_assoc]
        _ = (c : K) * (g * (g ^ j * u * (g ^ j)⁻¹) * g⁻¹) * (c : K)⁻¹ := by rw [ih u hu]
        _ = g * (g ^ j * u * (g ^ j)⁻¹) * g⁻¹ := hcU _ (hgU _ (hpow j u hu))
        _ = g ^ (j + 1) * u * (g ^ (j + 1))⁻¹ := by
            rw [pow_succ']
            simp only [mul_inv_rev, mul_assoc]
  rcases hTaut _ hn with h3 | h4
  · obtain ⟨u, hu, hne⟩ := hmove 3 (by norm_num) (by norm_num)
    exact hne ((hact 3 u hu).symm.trans (h3 u (hUT hu)))
  · obtain ⟨u, hu, hne⟩ := hmove 4 (by norm_num) (by norm_num)
    exact hne ((hact 4 u hu).symm.trans (h4 u (hUT hu)))

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
