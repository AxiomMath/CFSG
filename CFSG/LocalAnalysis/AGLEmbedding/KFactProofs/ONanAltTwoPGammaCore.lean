module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAltTwoPGammaBlock

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv Equiv.Perm CFSG.AGLEmbeddingD2.AltSurvivor

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {p : ℕ} {a₁ a₂ : Perm Ω} {O₁ O₂ : Finset Ω}
  {G : Type*} [Group G]

@[expose] noncomputable def blockChar (ψ : G →* Perm Ω) (hpres : ∀ g, ψ g ∈ blockStab O₁)
    (x₀ : Ω) : G →* Multiplicative (ZMod 2) :=
  (swapChar O₁ x₀).comp (ψ.codRestrict (blockStab O₁) hpres)

omit [Fintype Ω] in
theorem blockChar_eq_one_iff (ψ : G →* Perm Ω) (hpres : ∀ g, ψ g ∈ blockStab O₁) (x₀ : Ω)
    (g : G) : blockChar ψ hpres x₀ g = 1 ↔ ∀ x, x ∈ O₁ ↔ ψ g x ∈ O₁ :=
  swapChar_eq_one_iff O₁ x₀ ⟨ψ g, hpres g⟩

theorem eq_bot_of_normal_pGroup (h : TwoCycles p a₁ a₂ O₁ O₂) (hp5 : 5 ≤ p) (ψ : G →* Perm Ω)
    (hψ : Function.Injective ψ) (hpres : ∀ g, ψ g ∈ blockStab O₁)
    (hB₁ : altOn O₁ ≤ ψ.range) (hB₂ : altOn O₂ ≤ ψ.range) {N : Subgroup G} (hN : N.Normal)
    (hNp : IsPGroup p N) : N = ⊥ := by
  classical
  have hodd : Odd p := h.prime.eq_two_or_odd'.resolve_left (by omega)
  obtain ⟨x₀, hx₀⟩ : O₁.Nonempty := Finset.card_pos.1 (by rw [h.card₁]; exact h.prime.pos)
  have hNord : ∀ n ∈ N, ∃ k : ℕ, n ^ (p ^ k) = 1 := by
    intro n hn
    obtain ⟨k, hk⟩ := hNp ⟨n, hn⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hpr : ∀ n ∈ N, ∀ x, x ∈ O₁ ↔ ψ n x ∈ O₁ := by
    intro n hn
    obtain ⟨k, hk⟩ := hNord n hn
    rw [← blockChar_eq_one_iff ψ hpres x₀]
    have h1 : (blockChar ψ hpres x₀ n) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have h2 : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
    obtain ⟨m, hm⟩ := hodd.pow (n := k)
    rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  have hVn : ∀ {O : Finset Ω}, altOn O ≤ ψ.range → ∀ l ∈ altOn O, ∀ v ∈ N.map ψ,
      l * v * l⁻¹ ∈ N.map ψ := by
    intro O hO l hl v hv
    obtain ⟨g, rfl⟩ := hO hl
    obtain ⟨n, hn, rfl⟩ := hv
    exact ⟨g * n * g⁻¹, hN.conj_mem n hn g, by simp⟩
  have hVbot : ∀ {O : Finset Ω}, 5 ≤ O.card → altOn O ≤ ψ.range → N.map ψ ⊓ altOn O = ⊥ := by
    intro O hO5 hO
    rcases inf_altOn_eq_bot_or_le hO5 (hVn hO) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, haO, -⟩ := exists_notMem_of_card_le (O := O) (S := ∅) (k := 0) (by simp)
        (by omega)
      obtain ⟨b, hbO, hb⟩ := exists_notMem_of_card_le (O := O) (S := {a}) (k := 1) (by simp)
        (by omega)
      obtain ⟨c, hcO, hc⟩ := exists_notMem_of_card_le (O := O) (S := {a, b}) (k := 2)
        Finset.card_le_two (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
      have hl : swap b a * swap b c ∈ altOn O := by
        rw [swap_comm b a]
        exact swap_mul_swap_mem_altOn haO hbO hcO (Ne.symm hb) (Ne.symm hc.2)
      obtain ⟨n, hn, hln⟩ := h1 hl
      obtain ⟨k, hk⟩ := hNord n hn
      have hlp : (swap b a * swap b c) ^ (p ^ k) = 1 := by rw [← hln, ← map_pow, hk, map_one]
      have h3 : (swap b a * swap b c).IsThreeCycle :=
        isThreeCycle_swap_mul_swap_same hb (Ne.symm hc.2) (Ne.symm hc.1)
      have hdvd : 3 ∣ p ^ k := by
        have := orderOf_dvd_of_pow_eq_one hlp
        rwa [h3.orderOf] at this
      have h35 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).1
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
      omega
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  apply hψ
  rw [map_one]
  set v := ψ n with hvdef
  have hv1 : ∀ x, x ∈ O₁ ↔ v x ∈ O₁ := hpr n hn
  have hv2 : ∀ x, x ∈ O₂ ↔ v x ∈ O₂ := fun x => by
    rw [h.mem_snd_iff, h.mem_snd_iff]
    exact not_congr (hv1 x)
  have hvV : v ∈ N.map ψ := ⟨n, hn, rfl⟩
  have hcentral : ∀ {O : Finset Ω}, 5 ≤ O.card → altOn O ≤ ψ.range →
      (∀ x, x ∈ O ↔ v x ∈ O) → ∀ x ∈ O, v x = x := by
    intro O hO5 hO hvO x hx
    refine eq_self_of_commute_altOn hO5 (fun l hl => ?_) hx
    have hc : v * l * v⁻¹ * l⁻¹ ∈ N.map ψ ⊓ altOn O := by
      refine ⟨?_, ?_⟩
      · have := (N.map ψ).mul_mem hvV (hVn hO l hl v⁻¹ ((N.map ψ).inv_mem hvV))
        simpa [mul_assoc] using this
      · exact (altOn O).mul_mem (conj_mem_altOn hvO hl) ((altOn O).inv_mem hl)
    rw [hVbot hO5 hO, Subgroup.mem_bot] at hc
    calc v * l = (v * l * v⁻¹ * l⁻¹) * (l * v) := by group
      _ = l * v := by rw [hc, one_mul]
  ext x
  rcases h.cover x with hx | hx
  · exact hcentral (by rw [h.card₁]; omega) hB₁ hv1 x hx
  · exact hcentral (by rw [h.card₂]; omega) hB₂ hv2 x hx

@[expose] def restrBlock {H : Type*} [Group H] (φ : H →* Perm Ω) (O : Finset Ω)
    (hO : ∀ v x, x ∈ O ↔ φ v x ∈ O) : H →* Perm {x // x ∈ O} where
  toFun v := (φ v).subtypePerm fun x => (hO v x).symm
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' := fun v w => Equiv.ext fun x => Subtype.ext (by
    show (φ (v * w)) (x : Ω) = (φ v) ((φ w) (x : Ω))
    rw [map_mul, Perm.mul_apply])

omit [Fintype Ω] [DecidableEq Ω] in
theorem restrBlock_apply {H : Type*} [Group H] (φ : H →* Perm Ω) (O : Finset Ω)
    (hO : ∀ v x, x ∈ O ↔ φ v x ∈ O) (v : H) (x : {x // x ∈ O}) :
    ((restrBlock φ O hO v x : {x // x ∈ O}) : Ω) = φ v x := rfl

omit [Fintype Ω] in
theorem exists_injective_hom_of_perfect (h : TwoCycles p a₁ a₂ O₁ O₂) (ψ : G →* Perm Ω)
    (hψ : Function.Injective ψ) (hpres : ∀ g, ψ g ∈ blockStab O₁) {V : Subgroup G}
    (hV : ⁅V, V⁆ = V) :
    ∃ f : ↥V →* alternatingGroup (Fin p) × alternatingGroup (Fin p), Function.Injective f := by
  classical
  obtain ⟨x₀, hx₀⟩ : O₁.Nonempty := Finset.card_pos.1 (by rw [h.card₁]; exact h.prime.pos)
  set φ : ↥V →* Perm Ω := ψ.comp V.subtype with hφ
  have hφinj : Function.Injective φ := hψ.comp Subtype.val_injective
  have hker₁ : ∀ v x, x ∈ O₁ ↔ φ v x ∈ O₁ := by
    intro v
    have := eq_one_of_perfect hV
      ((blockChar ψ hpres x₀).comp V.subtype) v
    exact (blockChar_eq_one_iff ψ hpres x₀ v).1 this
  have hker₂ : ∀ v x, x ∈ O₂ ↔ φ v x ∈ O₂ := fun v x => by
    rw [h.mem_snd_iff, h.mem_snd_iff]
    exact not_congr (hker₁ v x)
  have e₁ : {x // x ∈ O₁} ≃ Fin p :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, h.card₁])
  have e₂ : {x // x ∈ O₂} ≃ Fin p :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, h.card₂])
  have hs₁ : ∀ v, Perm.sign (e₁.permCongr (restrBlock φ O₁ hker₁ v)) = 1 := by
    intro v
    rw [Perm.sign_permCongr]
    exact eq_one_of_perfect hV (Perm.sign.comp (restrBlock φ O₁ hker₁)) v
  have hs₂ : ∀ v, Perm.sign (e₂.permCongr (restrBlock φ O₂ hker₂ v)) = 1 := by
    intro v
    rw [Perm.sign_permCongr]
    exact eq_one_of_perfect hV (Perm.sign.comp (restrBlock φ O₂ hker₂)) v
  let g₁ : ↥V →* Perm (Fin p) := e₁.permCongrHom.toMonoidHom.comp (restrBlock φ O₁ hker₁)
  let g₂ : ↥V →* Perm (Fin p) := e₂.permCongrHom.toMonoidHom.comp (restrBlock φ O₂ hker₂)
  let f₁ : ↥V →* alternatingGroup (Fin p) :=
    g₁.codRestrict (alternatingGroup (Fin p)) fun v => Perm.mem_alternatingGroup.2 (hs₁ v)
  let f₂ : ↥V →* alternatingGroup (Fin p) :=
    g₂.codRestrict (alternatingGroup (Fin p)) fun v => Perm.mem_alternatingGroup.2 (hs₂ v)
  refine ⟨f₁.prod f₂, ?_⟩
  rw [injective_iff_map_eq_one]
  intro v hv
  have h1 : f₁ v = 1 := (Prod.ext_iff.1 hv).1
  have h2 : f₂ v = 1 := (Prod.ext_iff.1 hv).2
  have h1' : g₁ v = 1 := congrArg Subtype.val h1
  have h2' : g₂ v = 1 := congrArg Subtype.val h2
  have r1 : restrBlock φ O₁ hker₁ v = 1 := e₁.permCongrHom.injective (by
    rw [map_one]; exact h1')
  have r2 : restrBlock φ O₂ hker₂ v = 1 := e₂.permCongrHom.injective (by
    rw [map_one]; exact h2')
  apply hφinj
  ext x
  rw [map_one, Perm.one_apply]
  rcases h.cover x with hx | hx
  · exact congrArg (fun t => ((t ⟨x, hx⟩ : {x // x ∈ O₁}) : Ω)) r1
  · exact congrArg (fun t => ((t ⟨x, hx⟩ : {x // x ∈ O₂}) : Ω)) r2

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
