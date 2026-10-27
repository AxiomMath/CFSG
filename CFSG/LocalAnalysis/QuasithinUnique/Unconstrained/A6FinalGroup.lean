module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.QuasithinUnique

section Product

variable {G : Type*} [Group G]

@[expose] def ElemAb (B : Subgroup G) : Prop :=
  (∀ b ∈ B, b * b = 1) ∧ ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b

theorem ElemAb.conjugate {B : Subgroup G} (hB : ElemAb B) (g : G) :
    ElemAb (CFSG.conjugate B g) := by
  refine ⟨fun a ha => ?_, fun a ha a' ha' => ?_⟩
  · rw [BenderBranch.mem_conjugate_iff] at ha
    have h1 := hB.1 _ ha
    calc a * a = g⁻¹ * ((g * a * g⁻¹) * (g * a * g⁻¹)) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [BenderBranch.mem_conjugate_iff] at ha ha'
    have h2 := hB.2 _ ha _ ha'
    calc a * a' = g⁻¹ * ((g * a * g⁻¹) * (g * a' * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a' * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h2]
      _ = a' * a := by group

theorem exists_mul_of_mem_sup_of_commute {X Y : Subgroup G}
    (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) {g : G} (hg : g ∈ X ⊔ Y) :
    ∃ a ∈ X, ∃ b ∈ Y, g = a * b := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ X, ∃ b ∈ Y, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', X.mul_mem ha ha', b * b', Y.mul_mem hb hb', ?_⟩
        have h1 : b * a' = a' * b := (hc a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h1]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, X.one_mem, 1, Y.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, X.inv_mem ha, b⁻¹, Y.inv_mem hb, ?_⟩
        have h1 : a * b = b * a := hc a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h1]
          _ = a⁻¹ * b⁻¹ := mul_inv_rev b a }
  have hXP : X ≤ P := fun a ha => ⟨a, ha, 1, Y.one_mem, by simp⟩
  have hYP : Y ≤ P := fun b hb => ⟨1, X.one_mem, b, hb, by simp⟩
  exact sup_le hXP hYP hg

theorem eq_of_mul_eq_of_inf_eq_bot {X Y : Subgroup G} (hd : X ⊓ Y = ⊥) {a a' b b' : G} (ha : a ∈ X)
    (ha' : a' ∈ X) (hb : b ∈ Y) (hb' : b' ∈ Y) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ X ⊓ Y :=
    ⟨X.mul_mem (X.inv_mem ha') ha, h1 ▸ Y.mul_mem hb' (Y.inv_mem hb)⟩
  rw [hd, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    have := h2
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [this, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

@[expose] def projL (X Y B : Subgroup G) (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ X ∧ ∃ b ∈ Y, a * b ∈ B}
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨X.mul_mem ha ha', b * b', Y.mul_mem hb hb', ?_⟩
    have h1 := hc a' ha' b hb
    have e : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [h1]
        _ = (a * b) * (a' * b') := by group
    rw [e]
    exact B.mul_mem hab hab'
  one_mem' := ⟨X.one_mem, 1, Y.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨X.inv_mem ha, b⁻¹, Y.inv_mem hb, ?_⟩
    have h1 := hc a ha b hb
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
        _ = (a * b)⁻¹ := by rw [h1]
    rw [e]
    exact B.inv_mem hab

theorem projL_le {X Y B : Subgroup G} {hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a} :
    projL X Y B hc ≤ X := fun _ h => h.1

theorem exists_projL_projL {X Y B : Subgroup G} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hB : B ≤ X ⊔ Y) {g : G} (hg : g ∈ B) :
    ∃ a ∈ projL X Y B hc, ∃ b ∈ projL Y X B (fun b hb a ha => (hc a ha b hb).symm), g = a * b := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hc (hB hg)
  refine ⟨a, ⟨ha, b, hb, by rw [← hab]; exact hg⟩, b, ⟨hb, a, ha, ?_⟩, hab⟩
  rw [← hc a ha b hb, ← hab]
  exact hg

theorem card_le_card_projL_mul [Finite G] {X Y B : Subgroup G}
    (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) (hB : B ≤ X ⊔ Y) :
    Nat.card B ≤ Nat.card (projL X Y B hc) *
      Nat.card (projL Y X B (fun b hb a ha => (hc a ha b hb).symm)) := by
  choose a ha b hb hab using fun g : B => exists_projL_projL hc hB g.2
  let f : B → projL X Y B hc × projL Y X B (fun b hb a ha => (hc a ha b hb).symm) :=
    fun g => (⟨a g, ha g⟩, ⟨b g, hb g⟩)
  have hinj : Function.Injective f := by
    intro g g' h
    apply Subtype.ext
    have h1 : a g = a g' := congrArg (fun p => (p.1 : G)) h
    have h2 : b g = b g' := congrArg (fun p => (p.2 : G)) h
    rw [hab g, hab g', h1, h2]
  have := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_prod] at this

theorem projL_elemAb {X Y B : Subgroup G} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) (hd : X ⊓ Y = ⊥)
    (hsq : ∀ b ∈ B, b * b = 1) (hcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    (∀ a ∈ projL X Y B hc, a * a = 1) ∧
      (∀ a ∈ projL X Y B hc, ∀ a' ∈ projL X Y B hc, a * a' = a' * a) := by
  constructor
  · rintro a ⟨ha, b, hb, hab⟩
    have h1 := hsq _ hab
    have h2 := hc a ha b hb
    have h3 : a * a * (b * b) = 1 := by
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [h2]
        _ = (a * b) * (a * b) := by group
        _ = 1 := h1
    have h4 : a * a ∈ Y := by
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [this]
      exact Y.inv_mem (Y.mul_mem hb hb)
    have h5 : a * a ∈ X ⊓ Y := ⟨X.mul_mem ha ha, h4⟩
    rw [hd, Subgroup.mem_bot] at h5
    exact h5
  · rintro a ⟨ha, b, hb, hab⟩ a' ⟨ha', b', hb', hab'⟩
    have h1 := hcomm _ hab _ hab'
    have e1 := hc a' ha' b hb
    have e2 := hc a ha b' hb'
    have h2 : (a * a') * (b * b') = (a' * a) * (b' * b) := by
      calc (a * a') * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [e1]
        _ = (a * b) * (a' * b') := by group
        _ = (a' * b') * (a * b) := h1
        _ = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [e2]
        _ = (a' * a) * (b' * b) := by group
    exact (eq_of_mul_eq_of_inf_eq_bot hd (X.mul_mem ha ha') (X.mul_mem ha' ha)
      (Y.mul_mem hb hb') (Y.mul_mem hb' hb) h2).1

theorem elemAb_eq_sup [Finite G] {X Y B : Subgroup G} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hd : X ⊓ Y = ⊥) (hB : B ≤ X ⊔ Y) (hBe : ElemAb B) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hX : ∀ P : Subgroup G, P ≤ X → ElemAb P → Nat.card P ≤ m)
    (hY : ∀ P : Subgroup G, P ≤ Y → ElemAb P → Nat.card P ≤ n)
    (hcard : Nat.card B = m * n) :
    ∃ P₁ P₂ : Subgroup G, P₁ ≤ X ∧ P₂ ≤ Y ∧ ElemAb P₁ ∧ ElemAb P₂ ∧ Nat.card P₁ = m ∧
      Nat.card P₂ = n ∧ B = P₁ ⊔ P₂ := by
  have hc' : ∀ b ∈ Y, ∀ a ∈ X, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  obtain ⟨hsq1, hcomm1⟩ := projL_elemAb hc hd hBe.1 hBe.2
  have hd' : Y ⊓ X = ⊥ := by rw [inf_comm]; exact hd
  obtain ⟨hsq2, hcomm2⟩ := projL_elemAb hc' hd' hBe.1 hBe.2
  set P₁ := projL X Y B hc with hP₁
  set P₂ := projL Y X B hc' with hP₂
  have h1 : Nat.card P₁ ≤ m := hX P₁ projL_le ⟨hsq1, hcomm1⟩
  have h2 : Nat.card P₂ ≤ n := hY P₂ projL_le ⟨hsq2, hcomm2⟩
  have h3 : m * n ≤ Nat.card P₁ * Nat.card P₂ := by
    have := card_le_card_projL_mul hc hB
    rw [hcard] at this
    exact this
  have e1 : Nat.card P₁ = m := by
    by_contra hne
    have hlt : Nat.card P₁ < m := lt_of_le_of_ne h1 hne
    have : Nat.card P₁ * Nat.card P₂ < m * n :=
      calc Nat.card P₁ * Nat.card P₂ ≤ Nat.card P₁ * n := Nat.mul_le_mul_left _ h2
        _ < m * n := Nat.mul_lt_mul_of_pos_right hlt hn
    omega
  have e2 : Nat.card P₂ = n := by
    by_contra hne
    have hlt : Nat.card P₂ < n := lt_of_le_of_ne h2 hne
    have : Nat.card P₁ * Nat.card P₂ < m * n :=
      calc Nat.card P₁ * Nat.card P₂ ≤ m * Nat.card P₂ := Nat.mul_le_mul_right _ h1
        _ < m * n := Nat.mul_lt_mul_of_pos_left hlt hm
    omega
  refine ⟨P₁, P₂, projL_le, projL_le, ⟨hsq1, hcomm1⟩, ⟨hsq2, hcomm2⟩, e1, e2, ?_⟩
  have hle : B ≤ P₁ ⊔ P₂ := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_projL_projL hc hB hg
    exact (P₁ ⊔ P₂).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hcP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => hc a ha.1 b hb.1
  have hdP : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ X ⊓ Y := ⟨hg.1.1, hg.2.1⟩
    rw [hd] at this
    exact this
  have hcardsup : Nat.card ↥(P₁ ⊔ P₂) = Nat.card P₁ * Nat.card P₂ :=
    BenderBranch.card_sup_of_commute_of_inf_eq_bot hcP hdP
  have hcardB : Nat.card ↥(P₁ ⊔ P₂) ≤ Nat.card B := by rw [hcardsup, e1, e2, hcard]
  exact Subgroup.eq_of_le_of_card_ge hle hcardB

end Product

section Orbit

variable {G : Type*} [Group G]

theorem card_le_mul_card_inf_normalizer [Finite G] {W A : Subgroup G} (𝒮 : Set (Subgroup G))
    (h𝒮 : ∀ w ∈ W, CFSG.conjugate A w ∈ 𝒮) :
    Nat.card W ≤ 𝒮.ncard * Nat.card ↥(W ⊓ Subgroup.normalizer (A : Set G)) := by
  let f : W → 𝒮 := fun w => ⟨CFSG.conjugate A w, h𝒮 w w.2⟩
  let rep : 𝒮 → W := Function.invFun f
  have hrep : ∀ w : W, f (rep (f w)) = f w := fun w => Function.invFun_eq ⟨w, rfl⟩
  have hmem : ∀ w : W, (w : G) * (rep (f w) : G)⁻¹ ∈ W ⊓ Subgroup.normalizer (A : Set G) := by
    intro w
    have h1 : CFSG.conjugate A (rep (f w) : G) = CFSG.conjugate A w :=
      congrArg Subtype.val (hrep w)
    have hN : (w : G) * (rep (f w) : G)⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
      rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, ← BenderBranch.conjugate_conjugate, ← h1,
        BenderBranch.conjugate_conjugate]
      simp [BenderBranch.conjugate_one]
    exact ⟨W.mul_mem w.2 (W.inv_mem (rep (f w)).2), hN⟩
  let g : W → 𝒮 × ↥(W ⊓ Subgroup.normalizer (A : Set G)) := fun w => (f w, ⟨_, hmem w⟩)
  have hinj : Function.Injective g := by
    intro w w' h
    have h1 : f w = f w' := congrArg Prod.fst h
    have h2 : (w : G) * (rep (f w) : G)⁻¹ = (w' : G) * (rep (f w') : G)⁻¹ :=
      congrArg (fun p => ((p.2 : ↥(W ⊓ Subgroup.normalizer (A : Set G))) : G)) h
    rw [h1] at h2
    apply Subtype.ext
    exact mul_right_cancel h2
  have := Nat.card_le_card_of_injective g hinj
  rwa [Nat.card_prod, Nat.card_coe_set_eq] at this

end Orbit

section Normalizer

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_of_lt {p : ℕ} [Fact p.Prime] [Finite G] {T U : Subgroup G}
    (hT : IsPGroup p T) (hUT : U ≤ T) (hne : U ≠ T) :
    ∃ w ∈ T, w ∈ Subgroup.normalizer (U : Set G) ∧ w ∉ U := by
  let UT : Subgroup T := U.subgroupOf T
  have hUTne : UT ≠ ⊤ := by
    intro htop
    apply hne
    apply le_antisymm hUT
    intro x hx
    have : (⟨x, hx⟩ : T) ∈ UT := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.mp this)
  have hlt : UT < ⊤ := lt_of_le_of_ne le_top hUTne
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hlt' : UT < Subgroup.normalizer (UT : Set T) := hnc UT hlt
  obtain ⟨w, hwN, hwnot⟩ := IsConcreteLE.exists_of_lt hlt'
  have hwNorm : (w : G) ∈ Subgroup.normalizer (U : Set G) := by
    have hwsub : w ∈ (Subgroup.normalizer (U : Set G)).subgroupOf T := by
      rw [Subgroup.subgroupOf_normalizer_eq hUT]
      exact hwN
    exact Subgroup.mem_subgroupOf.mp hwsub
  exact ⟨w, w.2, hwNorm, fun hw => hwnot (Subgroup.mem_subgroupOf.mpr hw)⟩

theorem A6Final.two_mul_card_le_of_lt [Finite G] {Q S : Subgroup G} (hQS : Q ≤ S) (hne : Q ≠ S) :
    2 * Nat.card Q ≤ Nat.card S := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hQS
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hk1 : k ≠ 1 := by
    intro h1
    apply hne
    apply Subgroup.eq_of_le_of_card_ge hQS
    rw [hk, h1, mul_one]
  have hk0 : k ≠ 0 := by
    intro h0
    have hSpos : 0 < Nat.card S := Nat.card_pos
    rw [hk, h0, mul_zero] at hSpos
    exact lt_irrefl _ hSpos
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  nlinarith

theorem A6Final.card_le_two_mul_of_cosets [Finite G] {B B' : Subgroup G} {b : G}
    (h : ∀ g ∈ B, g ∈ B' ∨ g * b⁻¹ ∈ B') : Nat.card B ≤ 2 * Nat.card B' := by
  classical
  let f : B → B' × Bool := fun g =>
    if hg : (g : G) ∈ B' then (⟨g, hg⟩, false)
    else (⟨g * b⁻¹, (h g g.2).resolve_left hg⟩, true)
  have hinj : Function.Injective f := by
    intro g g' hgg
    by_cases h1 : (g : G) ∈ B' <;> by_cases h2 : (g' : G) ∈ B'
    · simp only [f, h1, h2, dite_true, Prod.mk.injEq, and_true] at hgg
      exact Subtype.ext (congrArg (fun p : ↥B' => (p : G)) hgg)
    · simp [f, h1, h2] at hgg
    · simp [f, h1, h2] at hgg
    · simp only [f, h1, h2, dite_false, Prod.mk.injEq, and_true] at hgg
      have := congrArg (fun p : ↥B' => (p : G)) hgg
      exact Subtype.ext (mul_right_cancel this)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem mul_inv_mem_of_card_eq_two_mul [Finite G] {S T₀ : Subgroup G} (hST : S ≤ T₀)
    (hcard : Nat.card T₀ = 2 * Nat.card S) {g x : G} (hg : g ∈ T₀) (hx : x ∈ T₀) (hgS : g ∉ S)
    (hxS : x ∉ S) : g * x⁻¹ ∈ S := by
  let S₀ : Subgroup T₀ := S.subgroupOf T₀
  have hS₀card : Nat.card S₀ = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv
  have hidx : S₀.index = 2 := by
    have h1 := Subgroup.card_mul_index S₀
    rw [hS₀card, hcard] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    nlinarith
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hg' : (⟨g, hg⟩ : T₀) ∉ S₀ := fun h => hgS h
  have hx' : (⟨x, hx⟩ : T₀) ∉ S₀ := fun h => hxS h
  have h1 : (⟨g, hg⟩ : T₀) * a ∈ S₀ := by
    rcases ha ⟨g, hg⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hg'
  have h2 : (⟨x, hx⟩ : T₀) * a ∈ S₀ := by
    rcases ha ⟨x, hx⟩ with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hx'
  have h3 : ((⟨g, hg⟩ : T₀) * a) * ((⟨x, hx⟩ : T₀) * a)⁻¹ ∈ S₀ := S₀.mul_mem h1 (S₀.inv_mem h2)
  have e : ((⟨g, hg⟩ : T₀) * a) * ((⟨x, hx⟩ : T₀) * a)⁻¹ = ⟨g * x⁻¹, T₀.mul_mem hg (T₀.inv_mem hx)⟩ := by
    apply Subtype.ext
    simp [mul_assoc]
  rw [e] at h3
  exact h3

end Normalizer

end CFSG.QuasithinUnique
