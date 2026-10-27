module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9H

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem orbit_location_in_swap [Finite X] {Y : Subgroup X} {x : X} (hxY : x ∈ Y)
    (hx : orderOf x = 2) {T : Subgroup X} (hTY : T ≤ Y ⊓ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) :
    ∃ M : Subgroup X, M ≤ Y ∧ IsPComponent 2 (M.subgroupOf Y) ∧
      T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ M.map (MulAut.conj x).toMonoidHom) ⊓
        centralizer ({x} : Set X))) ∧
      (M.map (MulAut.conj x).toMonoidHom ≠ M →
        Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* ↥M ⧸ Open.fusionZStar ↥M)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hTYY : T ≤ Y := hTY.trans inf_le_left
  set T' := T.subgroupOf Y with hT'def
  have hcent : centralizer ({x'} : Set ↥Y) = (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, inf_comm]
  have hT'C : T' ≤ centralizer ({x'} : Set ↥Y) := by
    rw [hcent]
    intro y hy
    exact hTY hy
  have hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({x'} : Set ↥Y))) := by
    rw [hcent, hT'def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two]
    exact hTpc
  have hTE : T' ≤ pLayer ↥Y 2 := FooteLit.le_pLayer_of_isPComponent_centralizer_singleton hx' hT'C
    hT'pc
  obtain ⟨M₀, hM₀pc, hTM₀, hTM₀pc⟩ := UnbalancedLayer.two_layer_fixed_component_orbit_location hx'
    hT'C hT'pc hTE
  set M := M₀.map Y.subtype with hMdef
  have hMY : M ≤ Y := map_subtype_le _
  have hMsub : M.subgroupOf Y = M₀ := by
    change (M₀.map Y.subtype).comap Y.subtype = M₀
    exact comap_map_eq_self_of_injective Y.subtype_injective M₀
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def] at hconj
  set Mx := M.map (MulAut.conj x).toMonoidHom with hMxdef
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype = M ⊔ Mx := by
    rw [Subgroup.map_sup, hconj]
  have hMxY : Mx ≤ Y := by
    rw [← hconj]
    exact map_subtype_le _
  let φM : ↥M₀ ≃* ↥M := M₀.equivMapOfInjective Y.subtype Y.subtype_injective
  refine ⟨M, hMY, by rw [hMsub]; exact hM₀pc, ?_, ?_, ?_⟩
  · rw [← hsup]
    intro y hy
    exact ⟨⟨y, hTYY hy⟩, hTM₀ hy, rfl⟩
  · have hle : (M ⊔ Mx) ⊓ centralizer ({x} : Set X) ≤ Y :=
      inf_le_left.trans (sup_le hMY hMxY)
    have heq : (M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y) =
        ((M ⊔ Mx) ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
      rw [centralizer_mk_eq hxY, ← hsup]
      ext y
      simp only [mem_inf, mem_subgroupOf]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨⟨y, h1, rfl⟩, h2⟩
      · rintro ⟨⟨z, hz, hzy⟩, h2⟩
        have hzy' : z = y := Subtype.ext hzy
        exact ⟨hzy' ▸ hz, h2, y.2⟩
    rw [heq] at hTM₀pc
    rw [← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2 Nat.prime_two]
    exact hTM₀pc
  · intro hne
    have hfix : conjugate M₀ x' ≠ M₀ := by
      intro h
      apply hne
      show Mx = M
      rw [← hconj, h]
    obtain ⟨φ⟩ := CatLeaf.swap_case_type hx' M₀ hM₀pc (Ne.symm hfix) T' (le_inf hTM₀ hT'C)
      hTM₀pc
    exact ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTYY)).symm.trans
      (φ.trans (Sol78.fusionZStarQuotCongr φM))⟩

theorem commutator_mem_oddCore_of_ne [Finite X] {Y K L : Subgroup X} (hKY : K ≤ Y)
    (hKpc : IsPComponent 2 (K.subgroupOf Y)) (hLY : L ≤ Y)
    (hLpc : IsPComponent 2 (L.subgroupOf Y)) (hne : K ≠ L) {k l : X} (hk : k ∈ K)
    (hl : l ∈ L) : k * l * k⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : K.subgroupOf Y ≠ L.subgroupOf Y := fun h => by
    rw [subgroupOf_inj, inf_of_le_left hKY, inf_of_le_left hLY] at h
    exact hne h
  obtain ⟨-, -, hc', -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hKpc hLpc).2
      hne'
  obtain ⟨-, -, hsK, -, -⟩ := id hKpc
  have h1 : ⁅(⟨k, hKY hk⟩ : ↥Y), (⟨l, hLY hl⟩ : ↥Y)⁆ ∈ pPrimeCore 2 ↥Y := by
    have h2 := hc' (commutator_mem_commutator (show (⟨k, hKY hk⟩ : ↥Y) ∈ K.subgroupOf Y from hk)
      (show (⟨l, hLY hl⟩ : ↥Y) ∈ L.subgroupOf Y from hl))
    have h3 := (mem_inf.1 h2).1
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsK] at h3
    exact (mem_inf.1 h3).2
  exact ⟨_, h1, rfl⟩

theorem forall_commutator_mem_oddCore_of_le_sup [Finite X] {Y K A B : Subgroup X}
    (hAY : A ≤ Y) (hBY : B ≤ Y)
    (hA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ * a⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype)
    (hB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ * b⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype) :
    ∀ k ∈ K, ∀ y ∈ A ⊔ B, k * y * k⁻¹ * y⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
  set O : Subgroup X := (pPrimeCore 2 ↥Y).map Y.subtype with hOdef
  have hON : ∀ y ∈ Y, ∀ o ∈ O, y * o * y⁻¹ ∈ O := by
    rintro y hy _ ⟨o, ho, rfl⟩
    have hc := (inferInstance : (pPrimeCore 2 ↥Y).Normal).conj_mem o ho ⟨y, hy⟩
    exact ⟨_, hc, rfl⟩
  let Z : Subgroup X :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ K, k * y * k⁻¹ * y⁻¹ ∈ O}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun k hk => ?_⟩
        have h3 := mul_mem (h₁ k hk) (hON y₁ hy₁ _ (h₂ k hk))
        rwa [show k * y₁ * k⁻¹ * y₁⁻¹ * (y₁ * (k * y₂ * k⁻¹ * y₂⁻¹) * y₁⁻¹) =
          k * (y₁ * y₂) * k⁻¹ * (y₁ * y₂)⁻¹ by group] at h3
      one_mem' := ⟨one_mem Y, fun k _ => by simp⟩
      inv_mem' := by
        rintro y ⟨hy, h₁⟩
        refine ⟨inv_mem hy, fun k hk => ?_⟩
        have h3 := hON y⁻¹ (inv_mem hy) _ (inv_mem (h₁ k hk))
        rwa [show y⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ = k * y⁻¹ * k⁻¹ * y⁻¹⁻¹ by group] at h3 }
  have hAZ : A ≤ Z := fun a ha => ⟨hAY ha, fun k hk => hA k hk a ha⟩
  have hBZ : B ≤ Z := fun b hb => ⟨hBY hb, fun k hk => hB k hk b hb⟩
  intro k hk y hy
  exact ((sup_le hAZ hBZ) hy).2 k hk

theorem mem_of_commutator_mem_oddCore [Finite X] {H Y V : Subgroup X}
    (hVN : normalizer (V : Set X) ≤ H) (hVH : V ≤ H)
    (hOH : (pPrimeCore 2 ↥Y).map Y.subtype ≤ H) (hV2 : IsPGroup 2 V) (hVY : V ≤ Y) {k : X}
    (hk : ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype) : k ∈ H := by
  set O : Subgroup X := (pPrimeCore 2 ↥Y).map Y.subtype with hOdef
  have hVO : V ≤ normalizer (O : Set X) := fun v hv =>
    le_normalizer_pPrimeCore (le_normalizer (hVY hv))
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine mem_of_map_conj_le_sup_odd hVN hVH hOH hV2 hVO hOodd ?_
  rintro _ ⟨v, hv, rfl⟩
  have h1 : (MulAut.conj k).toMonoidHom v = k * v * k⁻¹ * v⁻¹ * v := by
    simp [MulAut.conj_apply]
  rw [h1]
  exact mul_mem (mem_sup_right (hk v hv)) (mem_sup_left hv)

end CFSG.ComponentClassification.SolMax
