module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Pieces
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.AltOn
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_val_mem {p : ℕ} {H : Type*} [Group H] {S : Subgroup G} (hS : IsPGroup p S)
    (f : H →* G) (hf : Function.Injective f) (hfS : ∀ x, f x ∈ S) : IsPGroup p H := by
  refine IsPGroup.of_injective hS (f.codRestrict S hfS) ?_
  intro x y hxy
  apply hf
  have := congrArg Subtype.val hxy
  simpa using this

theorem map_pCore_eq_bot_of_simple {p : ℕ} {H K : Type*} [Group H] [Group K] [Finite K]
    [IsSimpleGroup K] (f : H →* K) (hf : Function.Surjective f)
    (hK : ¬ IsPGroup p K) : (CFSG.pCore p H).map f = ⊥ := by
  have hn : ((CFSG.pCore p H).map f).Normal := (CFSG.pCore_normal (p := p) (G := H)).map f hf
  rcases hn.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hK
    have hp : IsPGroup p ((CFSG.pCore p H).map f) :=
      (CFSG.pCore_isPGroup (p := p) (G := H)).map f
    rw [h] at hp
    exact hp.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).surjective

theorem altQuotSubLStmt_holds : AltQuotSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁
  set Ω₁ := omegaOne Δ₀ ω a with hΩ₁
  have h6 : Ω₁.card = 6 := hE.toE0Data.card_omegaOne ha
  have hLM : L₁ ≤ L ⊔ S := (hL₁ ▸ subL_le S L θ _).trans le_sup_left
  set ψ : ↥L₁ →* Perm (Fin N) := θ.comp (Subgroup.inclusion hLM) with hψ
  have hrange : ψ.range = altOn Ω₁ := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range, hθ₁]
  have hmem : ∀ x : ↥L₁, ψ x ∈ altOn Ω₁ := fun x => hrange ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩
  set ψ' : ↥L₁ →* altOn Ω₁ := ψ.codRestrict (altOn Ω₁) hmem with hψ'
  have hsurj : Function.Surjective ψ' := by
    rintro ⟨σ, hσ⟩
    rw [← hrange] at hσ
    obtain ⟨x, hx⟩ := hσ
    exact ⟨x, Subtype.ext hx⟩
  have hkerψ' : ψ'.ker = ψ.ker := MonoidHom.ker_codRestrict ψ (altOn Ω₁) hmem
  have hS2 : IsPGroup 2 S := hE.asc.twoRadical.isPGroup
  have hker : ψ.ker = CFSG.pCore 2 ↥L₁ := by
    apply le_antisymm
    · refine le_sSup ⟨ψ.normal_ker, ?_⟩
      refine isPGroup_of_val_mem hS2 (L₁.subtype.comp ψ.ker.subtype) ?_ ?_
      · exact Subtype.val_injective.comp Subtype.val_injective
      · intro x
        have hx : ψ x = 1 := x.2
        exact hE.ker_le _ hx
    · have hsimple : IsSimpleGroup (altOn Ω₁) := isSimpleGroup_altOn (by omega)
      have hnot : ¬ IsPGroup 2 (altOn Ω₁) := by
        intro hp
        obtain ⟨n, hn⟩ := hp.exists_card_eq
        rw [card_altOn h6] at hn
        have h2 : n ≤ 9 := by
          by_contra hlt
          push Not at hlt
          have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
          omega
        interval_cases n <;> omega
      have hbot := map_pCore_eq_bot_of_simple ψ' hsurj hnot
      rw [← hkerψ', ← Subgroup.map_eq_bot_iff]
      exact hbot
  have e₁ : (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ≃* altOn Ω₁ :=
    (QuotientGroup.quotientMulEquivOfEq (hker.symm.trans hkerψ'.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hsurj)
  have hcard : Fintype.card ↥Ω₁ = 6 := by rw [Fintype.card_coe, h6]
  exact ⟨(e₁.trans (altOnEquiv Ω₁)).trans (Fintype.equivFinOfCardEq hcard).altCongrHom⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
