module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Red
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
open scoped commutatorElement

section Core

variable {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q]

theorem map_glaPPrimeCoreOf_fixSubgroup_le (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : MulAut K) (β : MulAut Q) (hαβ : ∀ k, π (α k) = β (π k))
    (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) :
    (GLAPPrimeCoreOf p (fixSubgroup α)).map π ≤ GLAPPrimeCoreOf p (fixSubgroup β) := by
  set O := GLAPPrimeCoreOf p (fixSubgroup α) with hO
  have hconj : ∀ k : K, π k ∈ fixSubgroup β → ∀ o ∈ O, k * o * k⁻¹ ∈ O := by
    intro k hk o ho
    set T : Subgroup K := O.map (MulAut.conj k).toMonoidHom with hT
    have hTF : T ≤ fixSubgroup α := by
      rintro _ ⟨o', ho', rfl⟩
      exact conj_mem_fixSubgroup π hker α β hαβ hk (GLAPPrimeCoreOf_le _ ho')
    have hTO : T ≤ O := by
      refine le_GLAPPrimeCoreOf_of_normal hTF ?_ ?_
      · intro g hg x hx
        obtain ⟨o', ho', rfl⟩ := hx
        have hk' : π k⁻¹ ∈ fixSubgroup β := by
          rw [map_inv]; exact inv_mem hk
        have hg' : k⁻¹ * g * k ∈ fixSubgroup α := by
          simpa using conj_mem_fixSubgroup π hker α β hαβ hk' hg
        refine ⟨(k⁻¹ * g * k) * o' * (k⁻¹ * g * k)⁻¹, GLAPPrimeCoreOf_conj_mem _ hg' o' ho', ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rw [hT, Subgroup.card_map_of_injective (MulAut.conj k).injective]
        exact coprime_card_GLAPPrimeCoreOf hp _
    exact hTO ⟨o, ho, rfl⟩
  refine le_GLAPPrimeCoreOf_of_normal ?_ ?_ ?_
  · exact (Subgroup.map_mono (GLAPPrimeCoreOf_le _)).trans
      (map_fixSubgroup_le π hker α β hαβ)
  · intro g hg x hx
    obtain ⟨o, ho, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hπ g
    exact ⟨k * o * k⁻¹, hconj k hg o ho, by simp⟩
  · exact (coprime_card_GLAPPrimeCoreOf hp _).coprime_dvd_right (Subgroup.card_map_dvd O π)

theorem glaPLayer_le {p : ℕ} (X : Subgroup K) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hJ => hJ.1

theorem commutator_glaPLayer_le {p : ℕ} (X : Subgroup K) :
    ⁅GLAPLayer p X, GLAPPrimeCoreOf p X⁆ ≤ GLAPPrimeCoreOf p X := by
  rw [Subgroup.commutator_le]
  intro l hl o ho
  have h := GLAPPrimeCoreOf_conj_mem (p := p) (C := X) l (glaPLayer_le X hl) o ho
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ ho)

end Core

@[expose] def B3Simple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → ∀ β : MulAut S, β ^ 3 = 1 →
      ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥

@[expose] def B3SimpleSpor : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group)) →
      ∀ β : MulAut S, β ^ 3 = 1 →
        ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥

@[expose] def B3SimpleLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
      ∀ β : MulAut S, β ^ 3 = 1 →
        ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥

@[expose] def B3SimpleAlt : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ (n : ℕ) (hn : 5 ≤ n),
      Nonempty (S ≃* (TauCeti.CFSGIndex.alternating n hn).Group)) →
      ∀ β : MulAut S, β ^ 3 = 1 →
        ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥

theorem b3Simple_of_families (hSpor : B3SimpleSpor) (hLie : B3SimpleLie) (hAlt : B3SimpleAlt) :
    B3Simple := by
  intro S _ _ hs hnc hcat β hβ
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (e a) (e b)
  | alternating n hn => exact hAlt S hs hnc ⟨n, hn, ⟨e⟩⟩ β hβ
  | lie idx => exact hLie S hs hnc ⟨idx, ⟨e⟩⟩ β hβ
  | sporadic name => exact hSpor S hs hnc ⟨name, ⟨e⟩⟩ β hβ

theorem pow_three_apply {G : Type*} [Group G] (γ : MulAut G) (x : G) :
    (γ ^ 3) x = γ (γ (γ x)) := by
  simp [pow_succ, MulAut.mul_apply]

theorem b3Quasi_of_b3Simple (h : B3Simple) : B3Quasi := by
  intro K _ _ hq hO hcat α hα
  obtain ⟨-, hsimple, hnc⟩ := hq
  set Z := Subgroup.center K with hZ
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker ≤ Z := by rw [QuotientGroup.ker_mk']
  have hZmap : Z.map α.toMonoidHom = Z :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance α
  let β : MulAut (K ⧸ Z) := QuotientGroup.congr Z Z α hZmap
  have hαβ : ∀ k, π (α k) = β (π k) := fun k => rfl
  have hα3 : ∀ k, α (α (α k)) = k := fun k => by
    have := congrArg (fun f : MulAut K => f k) hα
    simpa [pow_three_apply] using this
  have hβ : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := hπ x
    rw [pow_three_apply, ← hαβ, ← hαβ, ← hαβ, hα3]
    rfl
  have hB := h (K ⧸ Z) hsimple hnc hcat β hβ
  show ⁅GLAPLayer 3 (fixSubgroup α), GLAPPrimeCoreOf 3 (fixSubgroup α)⁆ = ⊥
  set L := GLAPLayer 3 (fixSubgroup α)
  set O := GLAPPrimeCoreOf 3 (fixSubgroup α) with hOdef
  have hLmap : L.map π ≤ GLAPLayer 3 (fixSubgroup β) :=
    (map_glaPLayer_fixSubgroup_eq π hker α β hαβ hπ Nat.prime_three).le
  have hOmap := map_glaPPrimeCoreOf_fixSubgroup_le π hker α β hαβ hπ Nat.prime_three
  have hcm : (⁅L, O⁆).map π = ⊥ := by
    rw [Subgroup.map_commutator]
    exact eq_bot_iff.2 (hB ▸ Subgroup.commutator_mono hLmap hOmap)
  have hOle : ⁅L, O⁆ ≤ O := commutator_glaPLayer_le _
  rw [eq_bot_iff]
  intro x hx
  have hxO : x ∈ O := hOle hx
  have hx1 : π x = 1 := by
    have : π x ∈ (⁅L, O⁆).map π := Subgroup.mem_map_of_mem _ hx
    rw [hcm, Subgroup.mem_bot] at this
    exact this
  have hxZ : x ∈ Subgroup.center K := hker hx1
  have hnorm : (Subgroup.zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : n ∈ Subgroup.center K := (Subgroup.zpowers_le.2 hxZ) hn
    have := Subgroup.mem_center_iff.1 hn' g
    rw [this, mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers x)) :=
    (coprime_card_GLAPPrimeCoreOf Nat.prime_three _).coprime_dvd_right
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hxO))
  have hmem : x ∈ GLAPPrimeCore 3 K :=
    le_sSup (show Subgroup.zpowers x ∈ {N : Subgroup K | N.Normal ∧ Nat.Coprime 3 (Nat.card N)}
      from ⟨hnorm, hcop⟩) (Subgroup.mem_zpowers x)
  rw [hO] at hmem
  exact hmem

end CFSG.HardMathSupport.Solomon.Coordinator
