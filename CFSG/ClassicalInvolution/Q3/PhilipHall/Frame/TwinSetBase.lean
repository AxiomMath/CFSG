module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section Defs

variable {Y : Type} [Group Y]

@[expose] def LongFundSet3 (R : Subgroup Y) (t : Y) : Prop :=
  ∃ Λ : Subgroup Y → Subgroup Y,
    (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      J ≤ Λ J ∧ IsClassicalMember3 (Λ J) t) ∧
    (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J ≠ J' →
        ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x) ∧
    ((⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), Λ J).subgroupOf
      (Subgroup.centralizer ({t} : Set Y))).Normal

theorem tightCore_mem_twinSet_of_twin {R : Subgroup Y}
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  obtain ⟨K', ⟨-, z, hz, -⟩, -⟩ := htw
  exact ⟨CoreAssembly.mem_conjClass_self _, z, hz, hz⟩

theorem LongFundSet3.hasLift {R : Subgroup Y} {t : Y} (h : LongFundSet3 R t)
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    TightHasLift R t := by
  obtain ⟨Λ, hΛ, -, -⟩ := h
  exact ⟨Λ (tightCore R), hΛ _ (tightCore_mem_twinSet_of_twin htw)⟩

theorem iSup_twinSet_eq_of_pair {Ω : Set (Subgroup Y)} {K K' : Subgroup Y}
    (hK : K ∈ twinSet Ω K) (hK' : K' ∈ twinSet Ω K)
    (hV : ∀ J ∈ twinSet Ω K, J = K ∨ J = K') (Λ : Subgroup Y → Subgroup Y) :
    (⨆ J ∈ twinSet Ω K, Λ J) = Λ K ⊔ Λ K' := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    rcases hV J hJ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup₂_of_le K hK le_rfl) (le_iSup₂_of_le K' hK' le_rfl)

theorem LongFundPair3.toSet {R : Subgroup Y} {t : Y} (h : LongFundPair3 R t) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R)
    (hV : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      J = tightCore R ∨ J = K') :
    LongFundSet3 R t := by
  classical
  obtain ⟨L, L', hKL, hKL', hL, hL', hcomm, hn⟩ := h K' hK' hne
  have hK₀ := tightCore_mem_twinSet_of_twin ⟨K', hK', hne⟩
  let Λ : Subgroup Y → Subgroup Y := fun J => if J = tightCore R then L else L'
  have hΛ₀ : Λ (tightCore R) = L := ite_eq_left rfl
  have hΛ' : Λ K' = L' := ite_eq_right hne
  refine ⟨Λ, ?_, ?_, ?_⟩
  · intro J hJ
    rcases hV J hJ with rfl | rfl
    · rw [hΛ₀]; exact ⟨hKL, hL⟩
    · rw [hΛ']; exact ⟨hKL', hL'⟩
  · intro J hJ J' hJ' hJJ' x hx y hy
    rcases hV J hJ with rfl | rfl <;> rcases hV J' hJ' with rfl | rfl
    · exact absurd rfl hJJ'
    · rw [hΛ₀] at hx; rw [hΛ'] at hy; exact hcomm x hx y hy
    · rw [hΛ'] at hx; rw [hΛ₀] at hy; exact (hcomm y hy x hx).symm
    · exact absurd rfl hJJ'
  · rw [iSup_twinSet_eq_of_pair hK₀ hK' hV Λ, hΛ₀, hΛ']
    exact hn

theorem LongFundSet3.toPair {R : Subgroup Y} {t : Y} (h : LongFundSet3 R t) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R)
    (hV : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      J = tightCore R ∨ J = K') :
    LongFundPair3 R t := by
  obtain ⟨Λ, hΛ, hcomm, hn⟩ := h
  have hK₀ := tightCore_mem_twinSet_of_twin ⟨K', hK', hne⟩
  intro K'' hK'' hne''
  have h'' : K'' = K' := (hV K'' hK'').resolve_left hne''
  subst h''
  refine ⟨Λ (tightCore R), Λ K'', (hΛ _ hK₀).1, (hΛ _ hK'').1, (hΛ _ hK₀).2, (hΛ _ hK'').2,
    hcomm _ hK₀ _ hK'' (Ne.symm hne), ?_⟩
  rw [← iSup_twinSet_eq_of_pair hK₀ hK'' hV Λ]
  exact hn

end Defs

@[expose] def Thm1RTwinLiftGenBelow (P : ∀ (Y : Type) [Group Y], Subgroup Y → Y → Prop) (n : ℕ) :
    Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) →
      TightInO2 t ∨ TwinE4 Y ∨ P Y R t

theorem Thm1RTwinLiftGenBelow.mono {P : ∀ (Y : Type) [Group Y], Subgroup Y → Y → Prop}
    {m n : ℕ} (h : m ≤ n) (H : Thm1RTwinLiftGenBelow P n) : Thm1RTwinLiftGenBelow P m :=
  fun Y _ _ hlt => H Y (lt_of_lt_of_le hlt h)

@[expose] def Thm1RTwinHasLiftBelow (n : ℕ) : Prop :=
  Thm1RTwinLiftGenBelow (fun _ _ R t => TightHasLift R t) n

theorem Thm1RTwinHasLiftBelow.mono {m n : ℕ} (h : m ≤ n) (H : Thm1RTwinHasLiftBelow n) :
    Thm1RTwinHasLiftBelow m :=
  Thm1RTwinLiftGenBelow.mono h H

theorem thm1RTwinHasLiftBelow_zero : Thm1RTwinHasLiftBelow 0 :=
  fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)

theorem Thm1RTwinLiftBelow.toHasLift {n : ℕ} (H : Thm1RTwinLiftBelow n) :
    Thm1RTwinHasLiftBelow n := by
  intro Y _ _ hlt R S t hd hq hg hO hΩ hA htw
  rcases H Y hlt R S t hd hq hg hO hΩ hA htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.hasLift htw))

@[expose] def Thm1RTwinLiftSetBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) →
      TightInO2 t ∨ TwinE4 Y ∨ LongFundSet3 R t

theorem Thm1RTwinLiftSetBelow.mono {m n : ℕ} (h : m ≤ n) (H : Thm1RTwinLiftSetBelow n) :
    Thm1RTwinLiftSetBelow m :=
  fun Y _ _ hlt => H Y (lt_of_lt_of_le hlt h)

theorem thm1RTwinLiftSetBelow_zero : Thm1RTwinLiftSetBelow 0 :=
  fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)

theorem Thm1RTwinLiftSetBelow.hasLift {n : ℕ} (H : Thm1RTwinLiftSetBelow n) {Y : Type} [Group Y]
    [Finite Y] (hY : Nat.card Y < n) {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hd : QuaternionBridge.Q8TwinDatum R S t) (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hg : TightSelfGen R) (hO : TightOddFree Y) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    TightInO2 t ∨ TwinE4 Y ∨ TightHasLift R t := by
  rcases H Y hY R S t hd hq hg hO hΩ hA htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.hasLift htw))

theorem Thm1RTwinLiftSetBelow.toHasLift {n : ℕ} (H : Thm1RTwinLiftSetBelow n) :
    Thm1RTwinHasLiftBelow n :=
  fun _ _ _ hlt _ _ _ hd hq hg hO hΩ hA htw => H.hasLift hlt hd hq hg hO hΩ hA htw

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
