module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

@[expose] def HasU4Quot {S : Type} [Group S] (K : Subgroup S) : Prop :=
  ∃ (Y : Type) (_ : Group Y), catalogIs Y S9.isU4two ∧ ∃ f : ↥K →* Y, Function.Surjective f

@[expose] def U42E27CentAt : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S IsU42Host →
    ∀ s : S, orderOf s = 3 → ∀ K : Subgroup S, K ≤ Subgroup.centralizer ({s} : Set S) →
      Group.IsPerfect ↥K → HasU4Quot K →
        s ∉ K ∧
          (∀ g ∈ Subgroup.centralizer ({s} : Set S), ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
          (∀ g ∈ Subgroup.centralizer ({s} : Set S), ∃ n : ℕ, ∃ k ∈ K, g = s ^ n * k) ∧
          Subgroup.center ↥K = ⊥

@[expose] def U42E27LocAt : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S IsU42Host →
    ∀ (E U₀ K : Subgroup S) (s : S), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → IsPGroup 2 ↥U₀ →
      E ≤ Subgroup.normalizer (U₀ : Set S) → (⁅U₀, E⁆ : Subgroup S) ≠ ⊥ → s ∈ E → s ≠ 1 →
      K ≤ Subgroup.centralizer ({s} : Set S) → Group.IsPerfect ↥K → HasU4Quot K →
        ∃ T : Subgroup S, T ≤ K ∧ IsPGroup 2 ↥T ∧ (E ⊓ K) ≤ Subgroup.normalizer (T : Set S) ∧
          (⁅T, E ⊓ K⁆ : Subgroup S) ≠ ⊥ ∧ 8 < Nat.card T

theorem orderOf_eq_three_of_mem {S : Type} [Group S] {E : Subgroup S} (hE : IsElemAbelian 3 E)
    {s : S} (hs : s ∈ E) (hs1 : s ≠ 1) : orderOf s = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : s ^ 3 = 1 := hE.2 s hs
  exact orderOf_eq_prime h3 hs1

theorem u42E27At_of_residuals (hC : U42E27CentAt) (hL : U42E27LocAt) : U42E27At := by
  intro S _ _ hS E U₀ hE hE27 hU₀ hnorm hcomm s hsE hs1 K hK hKperf hU4
  have hsord : orderOf s = 3 := orderOf_eq_three_of_mem hE hsE hs1
  obtain ⟨hsK, hKnorm, hgen, hZ⟩ := hC S hS s hsord K hK hKperf hU4
  obtain ⟨T, hTK, hT2, hEN, hTE, hT8⟩ := hL S hS E U₀ K s hE hE27 hU₀ hnorm hcomm hsE hs1 hK hKperf hU4
  have hsN : s ∈ Subgroup.normalizer (T : Set S) := by
    intro n
    constructor
    · intro hn
      have hnK : n ∈ K := hTK hn
      have hc : s * n = n * s := (Subgroup.mem_centralizer_iff.1 (hK hnK)) s (Set.mem_singleton s)
      rw [hc, mul_inv_cancel_right]
      exact hn
    · intro hn
      have htK : s * n * s⁻¹ ∈ K := hTK hn
      have hc : s * (s * n * s⁻¹) = (s * n * s⁻¹) * s :=
        (Subgroup.mem_centralizer_iff.1 (hK htK)) s (Set.mem_singleton s)
      have hnt : n = s * n * s⁻¹ := by
        calc n = s⁻¹ * (s * n * s⁻¹) * s := by group
          _ = s⁻¹ * ((s * n * s⁻¹) * s) := by rw [mul_assoc]
          _ = s⁻¹ * (s * (s * n * s⁻¹)) := by rw [hc]
          _ = s * n * s⁻¹ := by group
      rw [← hnt] at hn
      exact hn
  have hEle : E ≤ Subgroup.normalizer (T : Set S) := by
    intro e he
    have hecent : e ∈ Subgroup.centralizer ({s} : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hc := congrArg Subtype.val (hE.1.is_comm.comm (⟨h, hsE⟩ : ↥E) ⟨e, he⟩)
      simpa using hc
    obtain ⟨n, k, hk, rfl⟩ := hgen e hecent
    have hkE : k ∈ E := by
      have hsn : s ^ n ∈ E := E.pow_mem hsE n
      have : k = (s ^ n)⁻¹ * (s ^ n * k) := by group
      rw [this]
      exact E.mul_mem (E.inv_mem hsn) he
    have hkEK : k ∈ E ⊓ K := ⟨hkE, hk⟩
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hsN n) (hEN hkEK)
  have hTE' : (⁅T, E⁆ : Subgroup S) ≠ ⊥ := by
    intro h
    apply hTE
    apply eq_bot_iff.2
    have hmono : (⁅T, E ⊓ K⁆ : Subgroup S) ≤ ⁅T, E⁆ :=
      Subgroup.commutator_mono le_rfl inf_le_left
    rw [h] at hmono
    exact hmono
  have hTne : ∃ t ∈ T, t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    apply hTE
    have hT1 : T = ⊥ := eq_bot_iff.2 fun t ht => by
      rw [Subgroup.mem_bot]
      exact hcon t ht
    rw [hT1]
    simp
  obtain ⟨t, htT, ht1⟩ := hTne
  refine ⟨T, hTK, hT2, hEle, hTE', hT8, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hall : ∀ x ∈ T, x = 1 := by
    intro x hx
    have hxK : x ∈ K := hTK hx
    have hcen : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k'
      apply Subtype.ext
      exact (hcon x hx k'.1 k'.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  exact ht1 (hall t htT)

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
