module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F1

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem rank_le_one_of_isCyclic {G : Type} [Group G] [Finite G] (h : IsCyclic G) :
    Group.rank G ≤ 1 := by
  obtain ⟨g, hg⟩ := h.exists_generator
  have hcl : Subgroup.closure (({g} : Finset G) : Set G) = ⊤ := by
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
    exact (Subgroup.eq_top_iff' _).mpr hg
  simpa using Group.rank_le hcl

theorem exists_comm_subgroup {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (K : Subgroup S) (hKn : K.Normal) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (U : Subgroup S) (g : S) (hg : g ∈ U) :
    ∃ M : Subgroup S, M ≤ U ⊓ K ∧ M ≤ phi U ∧
      Nat.card (U ⊓ K : Subgroup S) ≤
        Nat.card (Subgroup.centralizer ({g} : Set S) ⊓ K : Subgroup S) * Nat.card M := by
  set N : Subgroup S := U ⊓ K with hN
  let ψ : N →* S := MonoidHom.mk' (fun y : N => g * (y : S) * g⁻¹ * (y : S)⁻¹) (by
    intro y₁ y₂
    have hy₁K : (y₁ : S) ∈ K := (y₁.2).2
    have hc2K : g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹ ∈ K :=
      mul_mem (hKn.conj_mem _ (y₂.2).2 g) (inv_mem (y₂.2).2)
    have hc : (y₁ : S)⁻¹ * (g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹) =
        (g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹) * (y₁ : S)⁻¹ := hKab _ (inv_mem hy₁K) _ hc2K
    have e1 : g * ((y₁ * y₂ : N) : S) * g⁻¹ * ((y₁ * y₂ : N) : S)⁻¹ =
        (g * (y₁ : S) * g⁻¹) * ((g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹) * (y₁ : S)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e1, ← hc]
    group)
  refine ⟨ψ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · exact U.mul_mem (U.mul_mem (U.mul_mem hg (y.2).1) (U.inv_mem hg)) (U.inv_mem (y.2).1)
    · exact K.mul_mem (hKn.conj_mem _ (y.2).2 g) (K.inv_mem (y.2).2)
  · rintro _ ⟨y, rfl⟩
    exact comm_mem_phi hS hg (y.2).1
  · have hcard : Nat.card N = Nat.card ψ.ker * Nat.card ψ.range := card_eq_ker_mul_range ψ
    have hker : Nat.card ψ.ker ≤
        Nat.card (Subgroup.centralizer ({g} : Set S) ⊓ K : Subgroup S) := by
      refine Nat.card_le_card_of_injective
        (fun y : ψ.ker => (⟨((y : N) : S), ?_⟩ :
          (Subgroup.centralizer ({g} : Set S) ⊓ K : Subgroup S))) ?_
      · refine ⟨?_, ((y : N).2).2⟩
        have h1 : g * ((y : N) : S) * g⁻¹ * ((y : N) : S)⁻¹ = 1 := y.2
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have h2 : g * ((y : N) : S) = ((y : N) : S) * g := by
          calc g * ((y : N) : S) = (g * ((y : N) : S) * g⁻¹ * ((y : N) : S)⁻¹) * ((y : N) : S) * g := by
                group
            _ = ((y : N) : S) * g := by rw [h1, one_mul]
        exact h2.symm
      · intro y₁ y₂ h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
    rw [hcard]
    exact Nat.mul_le_mul_right _ hker

theorem genLE4_of_abelian_normal {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (K : Subgroup S) (hKn : K.Normal) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hK16 : Nat.card K ≤ 16) (hKc : Subgroup.centralizer (K : Set S) ≤ K)
    (hrank : ∀ U : Subgroup S, Group.rank (U.map (QuotientGroup.mk' K)) ≤ 2)
    (hcomm : ∀ U : Subgroup S, ¬ IsCyclic (U.map (QuotientGroup.mk' K)) →
      ∃ g ∈ U, Nat.card (Subgroup.centralizer ({g} : Set S) ⊓ K : Subgroup S) ≤ 4) :
    GenLE4 S := by
  apply genLE4_of_rank_le_four
  intro U
  by_cases hUK : U ≤ K
  · have hcard : Nat.card U ≤ 2 ^ 4 := by
      have := Subgroup.card_le_of_le hUK
      omega
    exact rank_le_of_card_le_two_pow 4 U (hS.to_subgroup U) hcard
  · obtain ⟨g₀, hg₀U, hg₀K⟩ : ∃ g₀ ∈ U, g₀ ∉ K := by
      by_contra h
      push Not at h
      exact hUK h
    have hker : (QuotientGroup.mk' K).ker = K := QuotientGroup.ker_mk' K
    by_cases hcyc : IsCyclic (U.map (QuotientGroup.mk' K))
    · have hm : Group.rank (U.map (QuotientGroup.mk' K)) ≤ 1 := rank_le_one_of_isCyclic hcyc
      by_cases hN8 : Nat.card (U ⊓ K : Subgroup S) ≤ 8
      · have h := rank_le_add_of_frattini hS (QuotientGroup.mk' K) U ⊥ (m := 1) (k := 3) hm
          (by simp) (by simp) (by
            rw [hker, Subgroup.card_bot]
            omega)
        simpa using h
      · have hNK : U ⊓ K = K := by
          have hle : U ⊓ K ≤ K := inf_le_right
          have hdvd : Nat.card (U ⊓ K : Subgroup S) ∣ Nat.card K := by
            exact Subgroup.card_dvd_of_le hle
          have hKle := Subgroup.card_le_of_le hle
          obtain ⟨c, hc⟩ := hdvd
          have hKpos : 0 < Nat.card K := Nat.card_pos
          have hc1 : c = 1 := by
            rcases c with _ | _ | c
            · omega
            · rfl
            · nlinarith
          rw [hc1, mul_one] at hc
          exact Subgroup.eq_of_le_of_card_ge hle (by omega)
        have hKU : K ≤ U := by
          rw [← hNK]
          exact inf_le_left
        obtain ⟨y, hyK, hy⟩ : ∃ y ∈ K, y * g₀ ≠ g₀ * y := by
          by_contra h
          push Not at h
          exact hg₀K (hKc (Subgroup.mem_centralizer_iff.mpr h))
        set w : S := g₀ * y * g₀⁻¹ * y⁻¹ with hw
        have hw1 : w ≠ 1 := by
          intro h
          apply hy
          have h2 : g₀ * y = y * g₀ := by
            calc g₀ * y = (g₀ * y * g₀⁻¹ * y⁻¹) * y * g₀ := by group
              _ = y * g₀ := by rw [← hw, h, one_mul]
          exact h2.symm
        have hwK : w ∈ K := mul_mem (hKn.conj_mem _ hyK g₀) (inv_mem hyK)
        have hwU : w ∈ U := mul_mem (mul_mem (mul_mem hg₀U (hKU hyK)) (inv_mem hg₀U))
          (inv_mem (hKU hyK))
        have hwphi : w ∈ phi U := comm_mem_phi hS hg₀U (hKU hyK)
        have hMle : Subgroup.zpowers w ≤ U ⊓ K :=
          (Subgroup.zpowers_le).mpr ⟨hwU, hwK⟩
        have hMphi : Subgroup.zpowers w ≤ phi U := (Subgroup.zpowers_le).mpr hwphi
        have hMcard : 2 ≤ Nat.card (Subgroup.zpowers w) := by
          rw [Nat.card_zpowers]
          have hpos : 0 < orderOf w := orderOf_pos w
          have hne : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
          omega
        have hN16 : Nat.card (U ⊓ K : Subgroup S) ≤ 16 := by rw [hNK]; exact hK16
        have h := rank_le_add_of_frattini hS (QuotientGroup.mk' K) U (Subgroup.zpowers w)
          (m := 1) (k := 3) hm (by rw [hker]; exact hMle) hMphi (by
            rw [hker]
            omega)
        simpa using h
    · obtain ⟨g, hgU, hgc⟩ := hcomm U hcyc
      obtain ⟨M, hMle, hMphi, hMcard⟩ := exists_comm_subgroup hS K hKn hKab U g hgU
      have h := rank_le_add_of_frattini hS (QuotientGroup.mk' K) U M (m := 2) (k := 2)
        (hrank U) (by rw [hker]; exact hMle) hMphi (by
          rw [hker]
          have hMpos : 0 < Nat.card M := Nat.card_pos
          nlinarith)
      simpa using h

end CFSG.EvenSporadicStandard.Fin76b
