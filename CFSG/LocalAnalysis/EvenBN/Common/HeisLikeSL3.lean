module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroLayerSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.TrialityD4 (HeisLike heisLike_projUnitriangular)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped commutatorElement

theorem heisLike_sylow_of_lieModel {Q : Type} [Group Q] [Finite Q] {g : ℕ} (hg : 1 ≤ g)
    (hQ : LieModel Q .PSL 3 2 g) (S : Sylow 2 Q) : HeisLike (S : Subgroup Q) (2 ^ g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFf, hFfin, hF, ⟨ψ⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hQ
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hg hF
  obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
    (K := F) 2 (n := 3) (by norm_num)
  set S' : Sylow 2 (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    S.mapSurjective (f := ψ.toMonoidHom) ψ.surjective with hS'
  obtain ⟨x, hx⟩ : ∃ x : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F,
      x • U = S' := MulAction.exists_smul_eq _ U S'
  have hUh : HeisLike (U : Subgroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) (Nat.card F) := by
    rw [hU]
    exact heisLike_projUnitriangular
  have hS'h : HeisLike (S' : Subgroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) (Nat.card F) := by
    rw [← hx]
    exact (HeisLike.map_iff (MulAut.conj x).toMonoidHom fun y _ hy =>
      (MulAut.conj x).injective (hy.trans (map_one _).symm)).2 hUh
  have e : (S' : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) =
      (S : Subgroup Q).map ψ.toMonoidHom := rfl
  rw [e] at hS'h
  rw [← hF]
  exact (HeisLike.map_iff ψ.toMonoidHom fun y _ hy =>
    ψ.injective (hy.trans (map_one _).symm)).1 hS'h

theorem heisLike_of_isSylowOf_of_lieModel {Y : Type} [Group Y] [Finite Y] {Kc : Subgroup Y}
    {g : ℕ} (hg : 1 ≤ g) (hKc : LieModel Kc .PSL 3 2 g) {V : Subgroup Y}
    (hV : IsSylowOf 2 V Kc) : HeisLike V (2 ^ g) := by
  obtain ⟨S, hS⟩ := hV.exists_sylow_eq_subgroupOf
  have h1 := heisLike_sylow_of_lieModel hg hKc S
  have e : (S : Subgroup Kc).map Kc.subtype = V := by
    rw [hS, subgroupOf_map_subtype, inf_eq_left.2 hV.le]
  rw [← e]
  exact (HeisLike.map_iff Kc.subtype fun x _ hx => Subtype.ext hx).2 h1

section Prod

variable {Y : Type*} [Group Y] [Finite Y] {A B : Subgroup Y}

omit [Finite Y] in
theorem eq_and_eq_of_mul_eq_mul (hinf : A ⊓ B = ⊥) {a a' b b' : Y} (ha : a ∈ A) (ha' : a' ∈ A)
    (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [hinf, mem_bot] at h2
  have e1 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem prod_heisLike_facts (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) {k : ℕ}
    (hA : HeisLike A k) (hB : HeisLike B k) :
    Nat.card ((A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup Y) : Set Y) : Subgroup Y) = k ^ 2 ∧
      (∀ z ∈ (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup Y) : Set Y), z * z = 1) ∧
      (∀ x ∈ A ⊔ B, x * x ∈ (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup Y) : Set Y)) ∧
      ∀ D : Subgroup Y, D ⊓ A = ⊥ → D ⊓ B = ⊥ → ∀ a ∈ D ⊓ (A ⊔ B), ∀ b ∈ D ⊓ (A ⊔ B),
        a * b ≠ b * a → ∀ x ∈ A ⊔ B, x * a = a * x → x * b = b * x →
          x ∈ (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB
  have hdec : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hx' : x ∈ ((A ⊔ B : Subgroup Y) : Set Y) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  set Z := (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup Y) : Set Y) with hZ
  set ZA := A ⊓ centralizer (A : Set Y) with hZA
  set ZB := B ⊓ centralizer (B : Set Y) with hZB
  have hcomm : ∀ {a b a' b' : Y}, a ∈ A → b ∈ B → a' ∈ A → b' ∈ B →
      (a * b * (a' * b') = a' * b' * (a * b) ↔ a * a' = a' * a ∧ b * b' = b' * b) := by
    intro a b a' b' ha hb ha' hb'
    have e1 : a * b * (a' * b') = (a * a') * (b * b') := by
      rw [mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]; group
    have e2 : a' * b' * (a * b) = (a' * a) * (b' * b) := by
      rw [mul_assoc, ← mul_assoc b', ← hAB a ha b' hb']; group
    rw [e1, e2]
    constructor
    · intro h
      exact eq_and_eq_of_mul_eq_mul hinf (mul_mem ha ha') (mul_mem ha' ha) (mul_mem hb hb')
        (mul_mem hb' hb) h
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
  have hcen : ∀ {a b : Y}, a ∈ A → b ∈ B → (a * b ∈ Z ↔ a ∈ ZA ∧ b ∈ ZB) := by
    intro a b ha hb
    constructor
    · intro h
      refine ⟨⟨ha, mem_centralizer_iff.2 fun a' ha' => ?_⟩, ⟨hb, mem_centralizer_iff.2
        fun b' hb' => ?_⟩⟩
      · have h1 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 h).2 (a' * 1) (mem_sup_left
          (by simpa using ha'))
        have h2 := (hcomm ha' (one_mem B) ha hb).1 (by simpa using h1)
        exact h2.1
      · have h1 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 h).2 (1 * b') (mem_sup_right
          (by simpa using hb'))
        have h2 := (hcomm (one_mem A) hb' ha hb).1 (by simpa using h1)
        exact h2.2
    · rintro ⟨hza, hzb⟩
      refine ⟨mul_mem (mem_sup_left ha) (mem_sup_right hb), mem_centralizer_iff.2 fun x hx => ?_⟩
      obtain ⟨a', ha', b', hb', rfl⟩ := hdec x hx
      exact (hcomm ha' hb' ha hb).2 ⟨mem_centralizer_iff.1 (Subgroup.mem_inf.1 hza).2 a' ha',
        mem_centralizer_iff.1 (Subgroup.mem_inf.1 hzb).2 b' hb'⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hZeq : Z = ZA ⊔ ZB := by
      apply le_antisymm
      · intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := hdec z (Subgroup.mem_inf.1 hz).1
        obtain ⟨h1, h2⟩ := (hcen ha hb).1 hz
        exact mul_mem (mem_sup_left h1) (mem_sup_right h2)
      · refine sup_le (fun a ha => ?_) (fun b hb => ?_)
        · have := (hcen (Subgroup.mem_inf.1 ha).1 (one_mem B)).2 ⟨ha, ⟨one_mem B, by
            exact mem_centralizer_iff.2 fun _ _ => by rw [mul_one, one_mul]⟩⟩
          rwa [mul_one] at this
        · have := (hcen (one_mem A) (Subgroup.mem_inf.1 hb).1).2 ⟨⟨one_mem A, by
            exact mem_centralizer_iff.2 fun _ _ => by rw [mul_one, one_mul]⟩, hb⟩
          rwa [one_mul] at this
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute ZA ZB
      fun a ha b hb => hAB a (Subgroup.mem_inf.1 ha).1 b (Subgroup.mem_inf.1 hb).1).1
    have hinf' : ZA ⊓ ZB = ⊥ := le_bot_iff.1 (hinf ▸ inf_le_inf inf_le_left inf_le_left)
    rw [hinf', card_bot, mul_one, hA.card_center, hB.card_center] at h1
    rw [hZeq, h1, sq]
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec z (Subgroup.mem_inf.1 hz).1
    obtain ⟨h1, h2⟩ := (hcen ha hb).1 hz
    have e : a * b * (a * b) = (a * a) * (b * b) := by
      rw [mul_assoc, ← mul_assoc b, ← hAB a ha b hb]; group
    rw [e, hA.center_mul_self a h1, hB.center_mul_self b h2, one_mul]
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    have e : a * b * (a * b) = (a * a) * (b * b) := by
      rw [mul_assoc, ← mul_assoc b, ← hAB a ha b hb]; group
    rw [e]
    exact (hcen (mul_mem ha ha) (mul_mem hb hb)).2 ⟨hA.mul_self_mem a ha, hB.mul_self_mem b hb⟩
  · intro D hDA hDB a ha b hb hab x hx hxa hxb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hdec a (Subgroup.mem_inf.1 ha).2
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hdec b (Subgroup.mem_inf.1 hb).2
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hdec x hx
    have hmul : ∀ {a b a' b' : Y}, a ∈ A → b ∈ B → a' ∈ A → b' ∈ B →
        a * b * (a' * b') = (a * a') * (b * b') := fun {a b a' b'} ha hb ha' hb' => by
      rw [mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]; group
    have hD1 : a₁ * b₁ ≠ b₁ * a₁ := by
      intro h1
      apply hab
      set β := a₂ * b₂ * (b₂ * a₂)⁻¹ with hβ
      have hβB : β ∈ B := mul_mem (mul_mem ha₂ hb₂) (inv_mem (mul_mem hb₂ ha₂))
      have hw : a₁ * a₂ * (b₁ * b₂) * (b₁ * b₂ * (a₁ * a₂))⁻¹ = β := by
        rw [hmul ha₁ ha₂ hb₁ hb₂, hmul hb₁ hb₂ ha₁ ha₂, ← h1]
        have hc := hAB (a₁ * b₁) (mul_mem ha₁ hb₁) β hβB
        calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁ * (b₂ * a₂))⁻¹ =
            (a₁ * b₁) * β * (a₁ * b₁)⁻¹ := by rw [hβ]; group
          _ = β := by rw [hc, mul_inv_cancel_right]
      have hwD : a₁ * a₂ * (b₁ * b₂) * (b₁ * b₂ * (a₁ * a₂))⁻¹ ∈ D :=
        mul_mem (mul_mem (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)
          (inv_mem (mul_mem (Subgroup.mem_inf.1 hb).1 (Subgroup.mem_inf.1 ha).1))
      have h2 : β ∈ D ⊓ B := Subgroup.mem_inf.2 ⟨hw ▸ hwD, hβB⟩
      rw [hDB, mem_bot] at h2
      rw [← hw] at h2
      exact mul_inv_eq_one.1 h2
    have hD2 : a₂ * b₂ ≠ b₂ * a₂ := by
      intro h1
      apply hab
      set β := a₁ * b₁ * (b₁ * a₁)⁻¹ with hβ
      have hβA : β ∈ A := mul_mem (mul_mem ha₁ hb₁) (inv_mem (mul_mem hb₁ ha₁))
      have hw : a₁ * a₂ * (b₁ * b₂) * (b₁ * b₂ * (a₁ * a₂))⁻¹ = β := by
        rw [hmul ha₁ ha₂ hb₁ hb₂, hmul hb₁ hb₂ ha₁ ha₂, ← h1]
        have hc := hAB β hβA (a₂ * b₂) (mul_mem ha₂ hb₂)
        calc a₁ * b₁ * (a₂ * b₂) * (b₁ * a₁ * (a₂ * b₂))⁻¹ =
            β * (a₂ * b₂) * (a₂ * b₂)⁻¹ := by
              rw [hβ, show a₁ * b₁ * (a₂ * b₂) * (b₁ * a₁ * (a₂ * b₂))⁻¹ =
                a₁ * b₁ * ((a₂ * b₂) * (a₂ * b₂)⁻¹) * (b₁ * a₁)⁻¹ by group, mul_inv_cancel,
                mul_one]
              group
          _ = β := by rw [mul_inv_cancel_right]
      have hwD : a₁ * a₂ * (b₁ * b₂) * (b₁ * b₂ * (a₁ * a₂))⁻¹ ∈ D :=
        mul_mem (mul_mem (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)
          (inv_mem (mul_mem (Subgroup.mem_inf.1 hb).1 (Subgroup.mem_inf.1 ha).1))
      have h2 : β ∈ D ⊓ A := Subgroup.mem_inf.2 ⟨hw ▸ hwD, hβA⟩
      rw [hDA, mem_bot] at h2
      rw [← hw] at h2
      exact mul_inv_eq_one.1 h2
    obtain ⟨hxa₁, hxa₂⟩ := (hcomm hx₁ hx₂ ha₁ ha₂).1 hxa
    obtain ⟨hxb₁, hxb₂⟩ := (hcomm hx₁ hx₂ hb₁ hb₂).1 hxb
    exact (hcen hx₁ hx₂).2 ⟨hA.mem_center a₁ ha₁ b₁ hb₁ hD1 x₁ hx₁ hxa₁ hxb₁,
      hB.mem_center a₂ ha₂ b₂ hb₂ hD2 x₂ hx₂ hxa₂ hxb₂⟩

end Prod

section Package

variable {W : Type*} [Group W]

@[expose] def SylowPackage (V D : Subgroup W) (k : ℕ) : Prop :=
  Nat.card (V ⊓ centralizer (V : Set W) : Subgroup W) = k ^ 2 ∧
    (∀ z ∈ V ⊓ centralizer (V : Set W), z * z = 1) ∧
    (∀ v ∈ V, v * v ∈ V ⊓ centralizer (V : Set W)) ∧
    ∀ a ∈ D ⊓ V, ∀ b ∈ D ⊓ V, a * b ≠ b * a → ∀ x ∈ V, x * a = a * x → x * b = b * x →
      x ∈ V ⊓ centralizer (V : Set W)

theorem SylowPackage.of_map {W' : Type*} [Group W'] (φ : W →* W') {V D : Subgroup W}
    (hφ : ∀ x ∈ V, φ x = 1 → x = 1) {k : ℕ} (h : SylowPackage (V.map φ) (D.map φ) k) :
    SylowPackage V D k := by
  have hZcard := TrialityD4.card_map_of_injOn_D4 φ hφ (Y := V ⊓ centralizer (V : Set W))
    inf_le_left
  rw [TrialityD4.map_center_eq_D4 φ hφ] at hZcard
  have hcomm : ∀ {a b : W}, a ∈ V → b ∈ V → (φ a * φ b = φ b * φ a ↔ a * b = b * a) :=
    fun ha hb => by
      rw [← map_mul, ← map_mul]
      exact ⟨TrialityD4.eq_of_map_eq_D4 φ hφ (mul_mem ha hb) (mul_mem hb ha), fun h => by rw [h]⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hZcard ▸ h1, fun z hz => ?_, fun v hv => ?_, fun a ha b hb hab x hx hxa hxb => ?_⟩
  · have := h2 _ ((TrialityD4.map_mem_center_iff_D4 φ hφ hz.1).2 hz)
    rw [← map_mul] at this
    exact hφ _ (mul_mem hz.1 hz.1) this
  · have := h3 _ ⟨v, hv, rfl⟩
    rw [← map_mul] at this
    exact (TrialityD4.map_mem_center_iff_D4 φ hφ (mul_mem hv hv)).1 this
  · have := h4 (φ a) ⟨⟨a, ha.1, rfl⟩, ⟨a, ha.2, rfl⟩⟩ (φ b) ⟨⟨b, hb.1, rfl⟩, ⟨b, hb.2, rfl⟩⟩
      (fun e => hab ((hcomm ha.2 hb.2).1 e)) (φ x) ⟨x, hx, rfl⟩ ((hcomm hx ha.2).2 hxa)
      ((hcomm hx hb.2).2 hxb)
    exact (TrialityD4.map_mem_center_iff_D4 φ hφ hx).1 this

theorem SylowPackage.map {W' : Type*} [Group W'] (φ : W →* W') (hφ : Function.Injective φ)
    {V D : Subgroup W} {k : ℕ} (h : SylowPackage V D k) :
    SylowPackage (V.map φ) (D.map φ) k := by
  have hφ' : ∀ x ∈ V, φ x = 1 → x = 1 := fun x _ hx => hφ (hx.trans (map_one φ).symm)
  have hZcard := TrialityD4.card_map_of_injOn_D4 φ hφ' (Y := V ⊓ centralizer (V : Set W))
    inf_le_left
  rw [TrialityD4.map_center_eq_D4 φ hφ'] at hZcard
  have hcomm : ∀ {a b : W}, (φ a * φ b = φ b * φ a ↔ a * b = b * a) := fun {a b} => by
    rw [← map_mul, ← map_mul]
    exact ⟨fun e => hφ e, fun e => by rw [e]⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hZcard.symm ▸ h1, fun z hz => ?_, fun v hv => ?_, fun a ha b hb hab x hx hxa hxb => ?_⟩
  · obtain ⟨z₀, hz₀, rfl⟩ := hz.1
    rw [← map_mul, h2 _ ((TrialityD4.map_mem_center_iff_D4 φ hφ' hz₀).1 hz), map_one]
  · obtain ⟨v₀, hv₀, rfl⟩ := hv
    rw [← map_mul]
    exact (TrialityD4.map_mem_center_iff_D4 φ hφ' (mul_mem hv₀ hv₀)).2 (h3 _ hv₀)
  · obtain ⟨⟨a₀, ha₀D, rfl⟩, ⟨a₁, ha₁V, ha₁⟩⟩ := ha
    obtain ⟨⟨b₀, hb₀D, rfl⟩, ⟨b₁, hb₁V, hb₁⟩⟩ := hb
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain rfl := hφ ha₁
    obtain rfl := hφ hb₁
    exact (TrialityD4.map_mem_center_iff_D4 φ hφ' hx₀).2 (h4 a₁ ⟨ha₀D, ha₁V⟩ b₁ ⟨hb₀D, hb₁V⟩
      (fun e => hab (hcomm.2 e)) x₀ hx₀ (hcomm.1 hxa) (hcomm.1 hxb))

end Package

theorem sylowPackage_of_isSylowOf_sup {W : Type} [Group W] [Finite W] {Kc Kc' D : Subgroup W}
    {g : ℕ} (hg : 1 ≤ g)
    (hcase : (Kc' = Kc ∧ LieModel Kc .PSL 3 2 (2 * g)) ∨
      ((∀ x ∈ Kc, ∀ y ∈ Kc', x * y = y * x) ∧ Kc ⊓ Kc' = ⊥ ∧ LieModel Kc .PSL 3 2 g ∧
        LieModel Kc' .PSL 3 2 g ∧ D ⊓ Kc = ⊥ ∧ D ⊓ Kc' = ⊥))
    {V : Subgroup W} (hV : IsSylowOf 2 V (Kc ⊔ Kc')) : SylowPackage V D (2 ^ g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcase with ⟨rfl, hlie⟩ | ⟨hKcc, hKcinf, hlie, hlie', hDK, hDK'⟩
  · rw [sup_idem] at hV
    have hH := heisLike_of_isSylowOf_of_lieModel (by omega) hlie hV
    refine ⟨by rw [hH.card_center, ← pow_mul, mul_comm], hH.center_mul_self, hH.mul_self_mem,
      fun a ha b hb hab x hx hxa hxb => ?_⟩
    exact hH.mem_center a (Subgroup.mem_inf.1 ha).2 b (Subgroup.mem_inf.1 hb).2 hab x hx hxa hxb
  · have hNKc : Kc ⊔ Kc' ≤ normalizer (Kc : Set W) :=
      sup_le le_normalizer (fun y hy => mem_normalizer_fintype fun x hx => by
        rw [← hKcc x hx y hy, mul_inv_cancel_right]
        exact hx)
    have hNKc' : Kc ⊔ Kc' ≤ normalizer (Kc' : Set W) :=
      sup_le (fun y hy => mem_normalizer_fintype fun x hx => by
        rw [hKcc y hy x hx, mul_inv_cancel_right]
        exact hx) le_normalizer
    set A := V ⊓ Kc with hA
    set B := V ⊓ Kc' with hB
    have hAsyl : IsSylowOf 2 A Kc := hV.inf_of_le_normalizer le_sup_left hNKc
    have hBsyl : IsSylowOf 2 B Kc' := hV.inf_of_le_normalizer le_sup_right hNKc'
    have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
      hKcc x (Subgroup.mem_inf.1 hx).2 y (Subgroup.mem_inf.1 hy).2
    have hinfAB : A ⊓ B = ⊥ :=
      le_bot_iff.1 (hKcinf ▸ inf_le_inf inf_le_right inf_le_right)
    have hVAB : V = A ⊔ B := by
      symm
      refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
      have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
      rw [hinfAB, card_bot, mul_one] at h1
      have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Kc Kc' hKcc).1
      rw [hKcinf, card_bot, mul_one] at h2
      rw [h1, hV.card_eq, hAsyl.card_eq, hBsyl.card_eq, h2,
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]
    have hAh := heisLike_of_isSylowOf_of_lieModel hg hlie hAsyl
    have hBh := heisLike_of_isSylowOf_of_lieModel hg hlie' hBsyl
    obtain ⟨h1, h2, h3, h4⟩ := prod_heisLike_facts hAB hinfAB hAh hBh
    rw [hVAB]
    refine ⟨h1, h2, h3, h4 D (le_bot_iff.1 ((inf_le_inf_left D inf_le_right).trans hDK.le))
      (le_bot_iff.1 ((inf_le_inf_left D inf_le_right).trans hDK'.le))⟩

theorem sylowPackage_of_isSylowOf_of_map_eq {Y : Type} [Group Y] [Finite Y] {E V D : Subgroup Y}
    {Kc Kc' : Subgroup (Y ⧸ CFSG.oddCore Y)}
    (hE : E.map (QuotientGroup.mk' (CFSG.oddCore Y)) = Kc ⊔ Kc') {g : ℕ} (hg : 1 ≤ g)
    (hcase : (Kc' = Kc ∧ LieModel Kc .PSL 3 2 (2 * g)) ∨
      ((∀ x ∈ Kc, ∀ y ∈ Kc', x * y = y * x) ∧ Kc ⊓ Kc' = ⊥ ∧ LieModel Kc .PSL 3 2 g ∧
        LieModel Kc' .PSL 3 2 g ∧ D.map (QuotientGroup.mk' (CFSG.oddCore Y)) ⊓ Kc = ⊥ ∧
          D.map (QuotientGroup.mk' (CFSG.oddCore Y)) ⊓ Kc' = ⊥))
    (hV : IsSylowOf 2 V E) : SylowPackage V D (2 ^ g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hinj : ∀ x ∈ V, π x = 1 → x = 1 := by
    intro x hx hπx
    have hxO : x ∈ O := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
      exact hπx
    obtain ⟨k, hk⟩ := hV.isPGroup ⟨x, hx⟩
    exact TrialityD4.eq_one_of_mem_oddCore_of_pow_D4 hxO (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  have hVsyl : IsSylowOf 2 (V.map π) (Kc ⊔ Kc') := by
    refine isSylowOf_of_card (hE ▸ map_mono hV.le) ?_
    rw [TrialityD4.card_map_of_injOn_D4 π hinj le_rfl, hV.card_eq]
    have hk := Subgroup.card_ker_mul_card_range (π.domRestrict E)
    rw [MonoidHom.domRestrict_range, hE, MonoidHom.ker_domRestrict, hπ,
      QuotientGroup.ker_mk'] at hk
    have hodd : Odd (Nat.card (O.subgroupOf E)) := by
      have e : Nat.card (O.subgroupOf E) = Nat.card (O ⊓ E : Subgroup Y) := by
        rw [← subgroupOf_map_subtype, card_map_of_injective E.subtype_injective]
      rw [e]
      exact Odd.of_dvd_nat (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y)
        (card_dvd_of_le inf_le_left)
    rw [← hk, TrialityD4.factorization_two_mul_of_odd_D4 hodd Nat.card_pos.ne']
  exact SylowPackage.of_map π hinj (sylowPackage_of_isSylowOf_sup hg hcase hVsyl)

theorem isComponent_eq_of_le_sup_of_card_le_two {Q : Type*} [Group Q] [Finite Q]
    {Kc : Subgroup Q} (hKc : CFSG.IsComponent Kc) {s : Q} {D : Subgroup Q}
    (hD : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hsyl : ∀ U : Subgroup Q, IsPGroup 2 U → U ≤ centralizer (D : Set Q) → Nat.card U ≤ 2)
    {C : Subgroup Q} (hC : CFSG.IsComponent C) :
    C = Kc ∨ C = Kc.map (MulAut.conj s).toMonoidHom := by
  have hKc' : CFSG.IsComponent (Kc.map (MulAut.conj s).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hKc
  rcases CFSG.LocalCores.distinct_components_commute hC hKc with h1 | h1
  · exact Or.inl h1
  rcases CFSG.LocalCores.distinct_components_commute hC hKc' with h2 | h2
  · exact Or.inr h2
  exfalso
  have hCD : C ≤ centralizer (D : Set Q) := by
    refine le_trans ?_ (centralizer_le hD)
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h1))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h2))
  obtain ⟨U, hU, hU2⟩ := TrialityD4.exists_isPGroup_two_lt_card_of_isQuasisimple_D4 hC.1
  have h3 := hsyl (U.map C.subtype) (hU.map _) ((map_subtype_le U).trans hCD)
  rw [card_map_of_injective C.subtype_injective] at h3
  omega

theorem normalClosure_eq_sup_of_isComponent {Q : Type*} [Group Q] [Finite Q] {Kc : Subgroup Q}
    (hKc : CFSG.IsComponent Kc) (hZ : center Kc = ⊥) {s : Q}
    (hcomp : ∀ C : Subgroup Q, CFSG.IsComponent C →
      C = Kc ∨ C = Kc.map (MulAut.conj s).toMonoidHom)
    {D : Subgroup Q} (hD : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hDs : ∀ x ∈ D, s * x * s⁻¹ = x) (hDab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a) :
    normalClosure (D : Set Q) = Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom := by
  classical
  set Kc' := Kc.map (MulAut.conj s).toMonoidHom with hKc'
  have hKc'c : CFSG.IsComponent Kc' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hZ' : center Kc' = ⊥ := by
    have e := map_center_eq (Kc.equivMapOfInjective (MulAut.conj s).toMonoidHom
      (MulAut.conj s).injective)
    rw [hZ, Subgroup.map_bot] at e
    exact e.symm
  have hE : CFSG.layer Q = Kc ⊔ Kc' := by
    refine le_antisymm (sSup_le fun C hC => ?_) (sup_le (CFSG.LocalCores.component_le_layer hKc)
      (CFSG.LocalCores.component_le_layer hKc'c))
    rcases hcomp C hC with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hlayN : (CFSG.layer Q).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Q)
    exact normal_of_characteristic _
  have hnot : ¬ (D ≤ centralizer (Kc : Set Q) ∧ D ≤ centralizer (Kc' : Set Q)) := by
    rintro ⟨h1, h2⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hDab
    have h3 : Kc ⊔ Kc' ≤ centralizer (D : Set Q) :=
      sup_le (le_centralizer_iff.1 h1) (le_centralizer_iff.1 h2)
    exact hab (mem_centralizer_iff.1 ((hD.trans h3) hb) a ha)
  have hboth : D ≤ centralizer (Kc : Set Q) → D ≤ centralizer (Kc' : Set Q) := by
    intro h1 x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have h2 := mem_centralizer_iff.1 (h1 hx) c hc
    have hx' := hDs x hx
    change s * c * s⁻¹ * x = x * (s * c * s⁻¹)
    calc s * c * s⁻¹ * x = s * (c * x) * s⁻¹ := by
          rw [show s * (c * x) * s⁻¹ = (s * c * s⁻¹) * (s * x * s⁻¹) by group, hx']
      _ = s * (x * c) * s⁻¹ := by rw [h2]
      _ = x * (s * c * s⁻¹) := by
          rw [show s * (x * c) * s⁻¹ = (s * x * s⁻¹) * (s * c * s⁻¹) by group, hx']
  have hboth' : D ≤ centralizer (Kc' : Set Q) → D ≤ centralizer (Kc : Set Q) := by
    intro h1 x hx
    rw [mem_centralizer_iff]
    intro c hc
    have hc' : s * c * s⁻¹ ∈ Kc' := ⟨c, hc, rfl⟩
    have h2 := mem_centralizer_iff.1 (h1 hx) _ hc'
    have hx' := hDs x hx
    calc c * x = s⁻¹ * ((s * c * s⁻¹) * (s * x * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * c * s⁻¹) * x) * s := by rw [hx']
      _ = s⁻¹ * (x * (s * c * s⁻¹)) * s := by rw [h2]
      _ = s⁻¹ * ((s * x * s⁻¹) * (s * c * s⁻¹)) * s := by rw [hx']
      _ = x * c := by group
  set M := normalClosure (D : Set Q) with hM
  have hMle : M ≤ CFSG.layer Q :=
    normalClosure_le_normal (fun x hx => (hE.symm ▸ hD) hx)
  have hCM : ∀ C : Subgroup Q, CFSG.IsComponent C → center C = ⊥ →
      ¬ D ≤ centralizer (C : Set Q) → C ≤ M := by
    intro C hC hCZ hCK
    have hn : (M.subgroupOf C).Normal := Normal.subgroupOf inferInstance C
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC.1 hn with htop | hcen
    · intro c hc
      have : (⟨c, hc⟩ : C) ∈ M.subgroupOf C := htop ▸ mem_top _
      exact this
    · exfalso
      rw [hCZ, le_bot_iff] at hcen
      apply hCK
      intro x hx
      rw [mem_centralizer_iff]
      intro c hc
      have hxM : x ∈ M := subset_normalClosure hx
      have hxN : x ∈ normalizer (C : Set Q) :=
        CFSG.LocalCores.layer_le_normalizer hC (hMle hxM)
      have h1 : c * x * c⁻¹ * x⁻¹ ∈ M := by
        rw [show c * x * c⁻¹ * x⁻¹ = (c * x * c⁻¹) * x⁻¹ by group]
        exact mul_mem ((inferInstance : M.Normal).conj_mem x hxM c) (inv_mem hxM)
      have h2 : c * x * c⁻¹ * x⁻¹ ∈ C := by
        rw [show c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) by group]
        exact mul_mem hc ((mem_normalizer_iff.1 hxN c⁻¹).1 (inv_mem hc))
      have h3 : (⟨_, h2⟩ : C) ∈ M.subgroupOf C := h1
      rw [hcen, mem_bot] at h3
      have h4 : c * x * c⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
      calc c * x = c * x * c⁻¹ * x⁻¹ * (x * c) := by group
        _ = x * c := by rw [h4, one_mul]
  have hKcM : Kc ≤ M := hCM Kc hKc hZ fun h1 => hnot ⟨h1, hboth h1⟩
  have hKc'M : Kc' ≤ M := hCM Kc' hKc'c hZ' fun h1 => hnot ⟨hboth' h1, h1⟩
  exact le_antisymm (hMle.trans hE.le) (sup_le hKcM hKc'M)

end CFSG.LocalAnalysis.EvenBN.Common
