module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3Sp
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open Module

@[expose] def RankFine (M : Type*) [Group M] (B : ℕ) : Prop :=
  ∀ E T : Subgroup M, IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
    E ≤ Subgroup.normalizer (T : Set M) → Nat.card E ≤ B

theorem RankFine.of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) {B : ℕ}
    (h : RankFine N B) : RankFine M B := by
  intro E T hE hT hTne hET
  have hE' : IsElemAbelian 3 (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      have h1 : (a : N) * b = e (a' * b') := by rw [map_mul]; simp [← ha, ← hb]
      have h2 : (b : N) * a = e (b' * a') := by rw [map_mul]; simp [← ha, ← hb]
      have h3 : a' * b' = b' * a' := by
        have := hE.1
        have h4 := mul_comm' (⟨a', ha'⟩ : E) ⟨b', hb'⟩
        exact congrArg (fun z : ↥E => (z : M)) h4
      show (a : N) * b = b * a
      rw [h1, h2, h3]
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow, hE.2 x' hx', map_one]
  have hT' : IsPGroup 2 (T.map e.toMonoidHom) := hT.map e.toMonoidHom
  have hne : T.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [eq_bot_iff]
    intro t ht
    have : e t ∈ T.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom ht
    rw [hbot, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (e.injective (by simpa using this))
  have hnorm : E.map e.toMonoidHom ≤
      Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup N) : Set N) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have h1 : e.symm (e.toMonoidHom g' * y * (e.toMonoidHom g')⁻¹) = g' * e.symm y * g'⁻¹ := by
      simp
    rw [h1]
    exact Subgroup.mem_normalizer_iff.1 (hET hg') (e.symm y)
  have := h _ _ hE' hT' hne hnorm
  rw [Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  exact this

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem apply_fixed_of_normalizes {M : Type*} [Group M] (ρ : M →* Module.End (ZMod 2) V)
    {E T : Subgroup M} (hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) {e : M} (he : e ∈ E) {y : V}
    (hy : ∀ t : ↥T, ρ (t : M) y = y) (t : ↥T) : ρ (t : M) (ρ e y) = ρ e y := by
  have ht' : e⁻¹ * (t : M) * e⁻¹⁻¹ ∈ T := hN _ (E.inv_mem he) _ t.2
  have h1 : ρ (e⁻¹ * (t : M) * e⁻¹⁻¹) y = y := hy ⟨_, ht'⟩
  rw [← Module.End.mul_apply, ← map_mul]
  have : (t : M) * e = e * (e⁻¹ * (t : M) * e⁻¹⁻¹) := by group
  rw [this, map_mul, Module.End.mul_apply, h1]

theorem card_mul_le_of_normalizes
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate) (hrefl : B.IsRefl)
    (heven : Even (finrank (ZMod 2) V))
    {M : Type*} [Group M] [Finite M] (ρ : M →* Module.End (ZMod 2) V)
    (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    {A : Type*} [CommGroup A] [Finite A] (hA3 : ∀ a : A, a ^ 3 = 1)
    (α : A →* Module.End (ZMod 2) V) (hα : ∀ a x y, B (α a x) (α a y) = B x y)
    (hαρ : ∀ a g, Commute (α a) (ρ g))
    (hfaith : ∀ g a, ρ g * α a = 1 → g = 1 ∧ a = 1)
    {E T : Subgroup M} (hcomm : ∀ a b : ↥E, a * b = b * a) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hT : IsPGroup 2 ↥T) (hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) (hTne : T ≠ ⊥) :
    Nat.card E * Nat.card A ≤ 3 ^ (finrank (ZMod 2) V / 2 - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hcomm }
  let ρE : ↥E →* Module.End (ZMod 2) V := ρ.comp E.subtype
  let τ : ↥T →* Module.End (ZMod 2) V := ρ.comp T.subtype
  let ρP : (↥E × A) →* Module.End (ZMod 2) V :=
    ρE.noncommCoprod α (fun e a => (hαρ a e).symm)
  have hρP : ∀ p : ↥E × A, ρP p = ρ (p.1 : M) * α p.2 := fun p => rfl
  have hP3 : ∀ p : ↥E × A, p ^ 3 = 1 := fun p =>
    Prod.ext (Subtype.ext (by simpa using hE3 p.1 p.1.2)) (hA3 p.2)
  have hfix : Rank3.fixSub ρP ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Rank3.mem_fixSub] at hp
    have h1 : ρ (p.1 : M) * α p.2 = 1 := by
      ext x
      have := hp x Submodule.mem_top
      rw [hρP] at this
      simpa using this
    obtain ⟨h2, h3⟩ := hfaith _ _ h1
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext h2) h3
  have hle : Nat.card (↥E × A) ≤ 3 ^ (finrank (ZMod 2) V / 2) := by
    have h := Rank3.index_fixSub_le hP3 ρP _ ⊤ rfl (fun _ _ _ => Submodule.mem_top)
    rw [hfix, Subgroup.index_bot, finrank_top] at h
    exact h
  have hlt : Nat.card (↥E × A) < 3 ^ (finrank (ZMod 2) V / 2) := by
    refine lt_of_le_of_ne hle fun heq => ?_
    apply hTne
    have hfull : 3 ^ (finrank (ZMod 2) V / 2) ≤ (Rank3.fixSub ρP ⊤).index := by
      rw [hfix, Subgroup.index_bot]
      exact heq.ge
    have hρPiso : ∀ p : ↥E × A, ∀ x y, B (ρP p x) (ρP p y) = B x y := by
      intro p x y
      rw [hρP]
      simp only [Module.End.mul_apply]
      rw [hρ, hα]
    have hinv : ∀ p : ↥E × A, ∀ x, (∀ t, τ t x = x) → ∀ t, τ t (ρP p x) = ρP p x := by
      intro p x hx t
      have hαx : ∀ t' : ↥T, ρ (t' : M) (α p.2 x) = α p.2 x := by
        intro t'
        have h1 := (hαρ p.2 (t' : M)).eq
        have h2 : ρ (t' : M) (α p.2 x) = α p.2 (ρ (t' : M) x) := by
          have := congrArg (fun f : Module.End (ZMod 2) V => f x) h1
          simpa [Module.End.mul_apply] using this.symm
        rw [h2]
        have h3 : ρ (t' : M) x = x := hx t'
        rw [h3]
      show ρ (t : M) (ρP p x) = ρP p x
      rw [hρP]
      simp only [Module.End.mul_apply]
      exact apply_fixed_of_normalizes ρ hN p.1.2 hαx t
    have hmain := Rank3.fixed_eq_top_of_full (E := ↥E × A) B hP3 hB hrefl ρP hρPiso hT τ
      (fun t => hρ t) hinv heven hfull
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have h1 : ρ t * α 1 = 1 := by
      rw [map_one, mul_one]
      ext x
      exact hmain ⟨t, ht⟩ x
    exact (hfaith t 1 h1).1
  have hpow : IsPGroup 3 (↥E × A) := fun p => ⟨1, by simpa using hP3 p⟩
  obtain ⟨k, hk⟩ := hpow.exists_card_eq
  rw [hk] at hlt
  have hk' : k < finrank (ZMod 2) V / 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  rw [Nat.card_prod] at hk
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_le_of_normalizes
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate) (hrefl : B.IsRefl)
    (heven : Even (finrank (ZMod 2) V))
    {M : Type*} [Group M] [Finite M] (ρ : M →* Module.End (ZMod 2) V)
    (hρinj : Function.Injective ρ) (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y) :
    RankFine M (3 ^ (finrank (ZMod 2) V / 2 - 1)) := by
  intro E T hE hT hTne hET
  have hcomm : ∀ a b : ↥E, a * b = b * a := by
    have := hE.1
    exact fun a b => mul_comm' a b
  have hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := fun e he t ht =>
    (Subgroup.mem_normalizer_iff.1 (hET he) t).1 ht
  have h := card_mul_le_of_normalizes B hB hrefl heven ρ hρ (A := Unit)
    (fun a => Subsingleton.elim _ _) 1 (fun a x y => by simp)
    (fun a g => by simp [Commute.one_left]) (fun g a h => ⟨hρinj (by simpa using h),
      Subsingleton.elim _ _⟩) hcomm (fun e he => hE.2 e he) hT hN hTne
  simpa using h

end Abstract

end CFSG.LocalAnalysis.GLTheoremA.CatB
