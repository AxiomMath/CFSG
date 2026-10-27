module

public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Aux

theorem exists_mul_of_mem_sup_of_commute' {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := h₂
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← this]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv y _ h₁ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a⁻¹ * b = b * a⁻¹ := this
        calc b⁻¹ * a⁻¹ = b⁻¹ * (a⁻¹ * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

theorem commutes_of_exponent_two {Q : Type*} [Group Q] (h : ∀ x : Q, x * x = 1) (a b : Q) :
    a * b = b * a := by
  have h1 : ∀ x : Q, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h x)
  calc a * b = (a * b)⁻¹ := (h1 (a * b)).symm
    _ = b⁻¹ * a⁻¹ := by group
    _ = b * a := by rw [h1, h1]

theorem not_exponent_two_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ ∀ x : Q, x * x = 1 := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, commutes_of_exponent_two h])

theorem mem_center_of_commutators_central {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) {x : Q}
    (h : ∀ y : Q, x * y * x⁻¹ * y⁻¹ ∈ center Q) : x ∈ center Q := by
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  have hx : (QuotientGroup.mk' (center Q)) x ∈ center (Q ⧸ center Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Q) g
    have h1 : (QuotientGroup.mk' (center Q)) (x * y * x⁻¹ * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (h y)
    simp only [map_mul, map_inv] at h1
    have h2 : (QuotientGroup.mk' (center Q)) x * (QuotientGroup.mk' (center Q)) y =
        (QuotientGroup.mk' (center Q)) y * (QuotientGroup.mk' (center Q)) x :=
      mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
    exact h2.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with h0 | h0
  · rw [h0, Subgroup.mem_bot] at hx
    exact (QuotientGroup.eq_one_iff x).1 hx
  · exfalso
    have : a ∈ center (Q ⧸ center Q) := h0 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

end Aux

section Pair

theorem card_le_two_of_normal_sq {Y : Type} [Group Y] {L₁ L₂ : Subgroup Y} {r₁ r₂ : ℕ}
    (hr₁ : Odd r₁) (h4 : 4 ≤ r₁) (hr₂ : Odd r₂)
    (h₁ : HasSL2Model ↥L₁ (fun r => r = r₁)) (h₂ : HasSL2Model ↥L₂ (fun r => r = r₂))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2)
    {B : Subgroup Y} (hB : B.Normal) (hsq : ∀ x ∈ B, x * x = 1) (hle : B ≤ L₁ ⊔ L₂) :
    Nat.card ↥B ≤ 2 := by
  classical
  obtain ⟨t₁, ht₁L, ht₁o, ht₁sq, ht₁c⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₁ h₁
  obtain ⟨t₂, ht₂L, ht₂o, ht₂sq, -⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₂ h₂
  have hq1 : IsQuasisimple ↥L₁ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4 h₁
  have ht₁1 : t₁ * t₁ = 1 := by
    have h' := pow_orderOf_eq_one t₁
    rw [ht₁o] at h'
    simpa [pow_two] using h'
  have ht₁ne : t₁ ≠ 1 := by
    intro h'
    rw [h', orderOf_one] at ht₁o
    omega
  obtain ⟨s, hs₁, hs₂, hs1⟩ : ∃ s : Y, s ∈ L₁ ∧ s ∈ L₂ ∧ s ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : L₁ ⊓ L₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hno x hx.1 hx.2)
    rw [hbot] at hcard
    simp at hcard
  have hst₁ : s = t₁ := by
    rcases ht₁c s hs₁ (fun w hw => (hcomm w hw s hs₂).symm) with h' | h'
    · exact absurd h' hs1
    · exact h'
  subst hst₁
  have hts : s = t₂ := by
    rcases ht₂sq s hs₂ ht₁1 with h' | h'
    · exact absurd h' ht₁ne
    · exact h'
  have key : ∀ b ∈ B, b = 1 ∨ b = s := by
    intro b hb
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup_of_commute' hcomm (hle hb)
    have hNn : (B.subgroupOf L₁).Normal := hB.subgroupOf L₁
    have hNc : B.subgroupOf L₁ ≤ center ↥L₁ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq1 hNn with htop | hcent
      · exfalso
        apply not_exponent_two_of_isQuasisimple hq1
        intro x
        have hx : x ∈ B.subgroupOf L₁ := by rw [htop]; trivial
        exact Subtype.ext (hsq (x : Y) hx)
      · exact hcent
    have hcen : (⟨l₁, hl₁⟩ : ↥L₁) ∈ center ↥L₁ := by
      apply mem_center_of_commutators_central hq1
      intro y
      have hcB : l₁ * (y : Y) * l₁⁻¹ * (y : Y)⁻¹ ∈ B := by
        have h1 : (l₁ * l₂) * ((y : Y) * (l₁ * l₂)⁻¹ * (y : Y)⁻¹) ∈ B :=
          B.mul_mem hb (by simpa [mul_assoc] using hB.conj_mem _ (B.inv_mem hb) (y : Y))
        have h3 : (l₁ * l₂) * ((y : Y) * (l₁ * l₂)⁻¹ * (y : Y)⁻¹) =
            l₁ * (y : Y) * l₁⁻¹ * (y : Y)⁻¹ := by
          have hyl : (y : Y) * l₂ = l₂ * (y : Y) := hcomm y y.2 l₂ hl₂
          calc (l₁ * l₂) * ((y : Y) * (l₁ * l₂)⁻¹ * (y : Y)⁻¹)
              = l₁ * (l₂ * (y : Y) * l₂⁻¹) * l₁⁻¹ * (y : Y)⁻¹ := by group
            _ = l₁ * (y : Y) * l₁⁻¹ * (y : Y)⁻¹ := by
              rw [← hyl]; group
        rwa [h3] at h1
      exact hNc (show (⟨l₁, hl₁⟩ : ↥L₁) * y * (⟨l₁, hl₁⟩ : ↥L₁)⁻¹ * y⁻¹ ∈ B.subgroupOf L₁ from hcB)
    have hl₁c : l₁ = 1 ∨ l₁ = s := by
      refine ht₁c l₁ hl₁ (fun w hw => ?_)
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨w, hw⟩)
      exact this.symm
    have hl₁sq : l₁ * l₁ = 1 := by
      rcases hl₁c with h' | h' <;> rw [h'] <;> simp [ht₁1]
    have hl₂sq : l₂ * l₂ = 1 := by
      have hb2 := hsq _ hb
      have hc12 : l₁ * l₂ = l₂ * l₁ := hcomm l₁ hl₁ l₂ hl₂
      calc l₂ * l₂ = (l₁ * l₁) * (l₂ * l₂) := by rw [hl₁sq, one_mul]
        _ = l₁ * (l₁ * l₂) * l₂ := by group
        _ = l₁ * (l₂ * l₁) * l₂ := by rw [hc12]
        _ = l₁ * l₂ * (l₁ * l₂) := by group
        _ = 1 := hb2
    have hl₂c : l₂ = 1 ∨ l₂ = s := by
      rcases ht₂sq l₂ hl₂ hl₂sq with h' | h'
      · exact Or.inl h'
      · exact Or.inr (h'.trans hts.symm)
    rcases hl₁c with h1 | h1 <;> rcases hl₂c with h2 | h2
    · left; rw [h1, h2]; simp
    · right; rw [h1, h2]; simp
    · right; rw [h1, h2]; simp
    · left; rw [h1, h2]; exact ht₁1
  have hinj : Function.Injective (fun b : ↥B => decide ((b : Y) = 1)) := by
    intro b b' hbb
    simp only [decide_eq_decide] at hbb
    apply Subtype.ext
    by_cases h1 : (b : Y) = 1
    · rw [h1, ← hbb.1 h1]
    · have h1' : (b' : Y) ≠ 1 := fun h => h1 (hbb.2 h)
      rcases key b b.2 with h | h
      · exact absurd h h1
      · rcases key b' b'.2 with h' | h'
        · exact absurd h' h1'
        · rw [h, h']
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

end Pair

section Kinds

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

@[expose] def KillNormal2 (z : G) : Prop :=
  ∀ B : Subgroup (CentralizerBar z), B.Normal → (∀ x ∈ B, x * x = 1) → Nat.card ↥B ≤ 2

theorem le_generalizedFitting_of_normal_sq {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y}
    (hB : B.Normal) (hsq : ∀ x ∈ B, x * x = 1) : B ≤ generalizedFitting Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa [pow_two] using hsq (g : Y) g.2)⟩
  have h1 : B ≤ pCore 2 Y := le_sSup ⟨hB, hp⟩
  exact (h1.trans (pCore_le_fitting Y 2)).trans le_sup_left

theorem killNormal2 (hctx : Stage2Ctx G z k S) (hk : k ≠ Kind.m12) : KillNormal2 z := by
  intro B hB hsq
  have hBF := le_generalizedFitting_of_normal_sq hB hsq
  cases hctx.data with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, ho₁, ho₂, h3, hprod, hs₁, hs₂, -, hW3, hW4, -⟩ := h.shape
    have hF : generalizedFitting (CentralizerBar z) ≤ LBar z := by
      rcases Nat.lt_or_ge 3 r₂ with hlt | hge
      · exact (hW4 hlt).2.le
      · have hr21 : 1 < r₂ := by
          obtain ⟨F, hF, hFin, hr, -⟩ := hs₂
          rw [← hr]
          exact Finite.one_lt_card
        have hr23 : r₂ = 3 := by
          obtain ⟨m, hm⟩ := ho₂
          omega
        rw [(hW3 hr23).2]
        exact Subgroup.map_subtype_le _
    obtain ⟨hsup, hcomm, hcard⟩ := hprod
    exact card_le_two_of_normal_sq ho₁ (by omega) ho₂ hs₁ hs₂ hcomm hcard hB hsq
      (hsup ▸ hBF.trans hF)
  | m12 h => exact absurd rfl hk
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨hsup, hcomm, hcard⟩ := h.pair.prod
    exact card_le_two_of_normal_sq h.pair.odd (by have := h.pair.gt3; omega) h.pair.odd h.pair.sl₁
      h.pair.sl₂ hcomm hcard hB hsq (hsup ▸ h.pair.fitting ▸ hBF)
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨hsup, hcomm, hcard⟩ := h.pair.prod
    exact card_le_two_of_normal_sq h.pair.odd (by have := h.pair.gt3; omega) h.pair.odd h.pair.sl₁
      h.pair.sl₂ hcomm hcard hB hsq (hsup ▸ h.pair.fitting ▸ hBF)
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    obtain ⟨hq, hc, -⟩ := h.cover
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hB with htop | hcen
    · exact absurd (fun x => hsq x (by rw [htop]; trivial)) (not_exponent_two_of_isQuasisimple hq)
    · exact (Subgroup.card_le_of_le hcen).trans hc.le
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    obtain ⟨hq, hc, -⟩ := h.cover
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hB with htop | hcen
    · exact absurd (fun x => hsq x (by rw [htop]; trivial)) (not_exponent_two_of_isQuasisimple hq)
    · exact (Subgroup.card_le_of_le hcen).trans hc.le

end Kinds

end CFSG.GH74.GLS.Stage2.Local.P34
