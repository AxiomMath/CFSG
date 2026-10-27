module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCData

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

structure OuterEFacts (Y : Type*) [Group Y] (S : Subgroup (MulAut Y)) (t : Y)
    (E : Subgroup (MulAut Y)) : Prop where
  t_sq : t * t = 1
  t_ne : t ≠ 1
  conj_mem : MulAut.conj t ∈ S
  center : ∀ α ∈ S, (∀ β ∈ S, β * α = α * β) ↔ (α = 1 ∨ α = MulAut.conj t)
  card_S : Nat.card S = 256
  card_aut : Nat.card (MulAut ↥E) = 1920
  E_le : E ≤ S
  E_inner : ∀ ε ∈ E, ∃ y : Y, ε = MulAut.conj y
  t_mem : MulAut.conj t ∈ E
  E_conj : ∀ ε ∈ E, ε * ε = 1 → ε ≠ 1 → ∃ c : Y, ε = MulAut.conj (c * t * c⁻¹)
  E_gen : E = closure {ε | ε ∈ E ∧ ε * ε = 1 ∧ ε ≠ 1}
  E_roots : E = closure {ε | ε ∈ E ∧ ε * ε = MulAut.conj t}
  E_roots_ge : 20 ≤ Set.ncard {ε | ε ∈ E ∧ ε * ε = MulAut.conj t}
  E_nonab : ∃ ε₁ ∈ E, ∃ ε₂ ∈ E, ε₁ * ε₂ ≠ ε₂ * ε₁
  E_comm : ∀ ε₁ ∈ E, ∀ ε₂ ∈ E,
    ε₁ * ε₂ * ε₁⁻¹ * ε₂⁻¹ = 1 ∨ ε₁ * ε₂ * ε₁⁻¹ * ε₂⁻¹ = MulAut.conj t
  E_center : ∀ ε ∈ E, (∀ f ∈ E, f * ε = ε * f) → ε = 1 ∨ ε = MulAut.conj t
  unique : ∀ P : Subgroup (MulAut Y), P ≤ S → Nonempty (↥E ≃* ↥P) → P = E
  cent : ∀ s ∈ S, (∀ ε ∈ E, s * ε = ε * s) → s = 1 ∨ s = MulAut.conj t

@[expose] def OuterEData (Y : Type*) [Group Y] : Prop :=
  ∀ S : Subgroup (MulAut Y), IsPGroup 2 S → ¬ 2 ∣ S.index →
    ∃ (t : Y) (E : Subgroup (MulAut Y)), OuterEFacts Y S t E

theorem conj_aut_apply {Y : Type*} [Group Y] (c : MulAut Y) (t : Y) :
    MulAut.conj (c t) = c * MulAut.conj t * c⁻¹ := by
  ext y
  simp [MulAut.conj_apply]

theorem OuterEFacts.map_iso {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (φ : MulAut X ≃* MulAut Y) (hφ : ∀ x : X, φ (MulAut.conj x) = MulAut.conj (e x))
    {S : Subgroup (MulAut X)} {t : X} {E : Subgroup (MulAut X)} (h : OuterEFacts X S t E) :
    OuterEFacts Y (S.map φ.toMonoidHom) (e t) (E.map φ.toMonoidHom) := by
  have hmemS : ∀ α : MulAut Y, α ∈ S.map φ.toMonoidHom ↔ φ.symm α ∈ S := by
    intro α
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hα
      exact ⟨φ.symm α, hα, by simp⟩
  have hmemE : ∀ α : MulAut Y, α ∈ E.map φ.toMonoidHom ↔ φ.symm α ∈ E := by
    intro α
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hα
      exact ⟨φ.symm α, hα, by simp⟩
  have hφs : ∀ y : Y, φ.symm (MulAut.conj y) = MulAut.conj (e.symm y) := by
    intro y
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, hφ, MulEquiv.apply_symm_apply]
  have hroots : {ε | ε ∈ E.map φ.toMonoidHom ∧ ε * ε = MulAut.conj (e t)} =
      φ.toMonoidHom '' {ε | ε ∈ E ∧ ε * ε = MulAut.conj t} := by
    ext ε
    constructor
    · rintro ⟨hε, hε2⟩
      refine ⟨φ.symm ε, ⟨(hmemE ε).1 hε, ?_⟩, by simp⟩
      apply φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hφ t]
      exact hε2
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_⟩
      show φ a * φ a = MulAut.conj (e t)
      rw [← map_mul, ha2, hφ t]
  refine
  { t_sq := by rw [← map_mul, h.t_sq, map_one]
    t_ne := fun h1 => h.t_ne (e.injective (by rw [h1, map_one]))
    conj_mem := ?_
    center := ?_
    card_S := ?_
    card_aut := ?_
    E_le := Subgroup.map_mono h.E_le
    E_inner := ?_
    t_mem := ?_
    E_conj := ?_
    E_gen := ?_
    E_roots := ?_
    E_roots_ge := ?_
    E_nonab := ?_
    E_comm := ?_
    E_center := ?_
    unique := ?_
    cent := ?_ }
  · exact ⟨_, h.conj_mem, hφ t⟩
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := hα
    have key := h.center a ha
    have hA : (∀ β ∈ S.map φ.toMonoidHom, β * φ a = φ a * β) ↔ ∀ b ∈ S, b * a = a * b := by
      constructor
      · intro hc b hb
        have h1 := hc (φ b) ⟨b, hb, rfl⟩
        change φ b * φ a = φ a * φ b at h1
        rw [← map_mul, ← map_mul] at h1
        exact φ.injective h1
      · rintro hc _ ⟨b, hb, rfl⟩
        change φ b * φ a = φ a * φ b
        rw [← map_mul, ← map_mul, hc b hb]
    have hB : (a = 1 ∨ a = MulAut.conj t) ↔ (φ.toMonoidHom a = 1 ∨ φ.toMonoidHom a =
        MulAut.conj (e t)) := by
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← hφ t]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl (by rw [h1, map_one])
        · exact Or.inr (by rw [h1])
      · rintro (h1 | h1)
        · exact Or.inl (φ.injective (h1.trans (map_one φ).symm))
        · exact Or.inr (φ.injective h1)
    exact hA.trans (key.trans hB)
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact h.card_S
  · rw [← Nat.card_congr (MulAut.congr (E.equivMapOfInjective φ.toMonoidHom φ.injective)).toEquiv]
    exact h.card_aut
  · intro ε hε
    obtain ⟨a, ha, rfl⟩ := hε
    obtain ⟨y, hy⟩ := h.E_inner a ha
    exact ⟨e y, by simp only [MulEquiv.coe_toMonoidHom]; rw [hy, hφ]⟩
  · exact ⟨_, h.t_mem, hφ t⟩
  · rintro ε ⟨a, ha, rfl⟩ hε2 hε1
    have ha2 : a * a = 1 := φ.injective (by rw [map_mul]; exact hε2.trans (map_one φ).symm)
    have ha1 : a ≠ 1 := fun h' => hε1 (by simp only [MulEquiv.coe_toMonoidHom]; rw [h', map_one])
    obtain ⟨d, hd⟩ := h.E_conj a ha ha2 ha1
    refine ⟨e d, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hd, hφ]
    simp [map_mul, map_inv]
  · apply le_antisymm
    · conv_lhs => rw [h.E_gen]
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨a, ⟨ha, ha2, ha1⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_mul, ha2, map_one]
      · intro h'
        apply ha1
        apply φ.injective
        simpa using h'
    · rw [closure_le]
      exact fun ε hε => hε.1
  · rw [hroots, ← MonoidHom.map_closure, ← h.E_roots]
  · have hinj : Function.Injective φ.toMonoidHom := φ.injective
    rw [hroots, Set.ncard_image_of_injective _ hinj]
    exact h.E_roots_ge
  · obtain ⟨ε₁, h₁, ε₂, h₂, hne⟩ := h.E_nonab
    refine ⟨φ ε₁, ⟨ε₁, h₁, rfl⟩, φ ε₂, ⟨ε₂, h₂, rfl⟩, fun h' => hne ?_⟩
    apply φ.injective
    simpa [map_mul] using h'
  · rintro _ ⟨ε₁, h₁, rfl⟩ _ ⟨ε₂, h₂, rfl⟩
    have e1 : φ.toMonoidHom ε₁ * φ.toMonoidHom ε₂ * (φ.toMonoidHom ε₁)⁻¹ *
        (φ.toMonoidHom ε₂)⁻¹ = φ.toMonoidHom (ε₁ * ε₂ * ε₁⁻¹ * ε₂⁻¹) := by
      simp [map_mul, map_inv]
    rw [e1]
    rcases h.E_comm ε₁ h₁ ε₂ h₂ with h' | h'
    · left; rw [h', map_one]
    · right
      rw [h']
      simp only [MulEquiv.coe_toMonoidHom]
      exact hφ t
  · intro ε hε hc
    obtain ⟨a, ha, rfl⟩ := hε
    have key := h.E_center a ha (fun f hf => by
      have h1 := hc (φ f) ⟨f, hf, rfl⟩
      change φ f * φ a = φ a * φ f at h1
      rw [← map_mul, ← map_mul] at h1
      exact φ.injective h1)
    rcases key with h1 | h1
    · left; simp only [MulEquiv.coe_toMonoidHom]; rw [h1, map_one]
    · right; simp only [MulEquiv.coe_toMonoidHom]; rw [h1, hφ]
  · intro P hP hiso
    obtain ⟨ε⟩ := hiso
    let P₀ : Subgroup (MulAut X) := P.map φ.symm.toMonoidHom
    have hP₀S : P₀ ≤ S := by
      rintro _ ⟨p, hp, rfl⟩
      exact (hmemS p).1 (hP hp)
    have hiso₀ : Nonempty (↥E ≃* ↥P₀) :=
      ⟨(E.equivMapOfInjective φ.toMonoidHom φ.injective).trans
        (ε.trans (P.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective))⟩
    have hP₀E : P₀ = E := h.unique P₀ hP₀S hiso₀
    ext x
    constructor
    · intro hx
      have : φ.symm x ∈ P₀ := ⟨x, hx, rfl⟩
      rw [hP₀E] at this
      exact (hmemE x).2 this
    · intro hx
      have : φ.symm x ∈ P₀ := by rw [hP₀E]; exact (hmemE x).1 hx
      obtain ⟨p, hp, hpx⟩ := this
      have : p = x := by
        have := congrArg φ hpx
        simpa using this
      rwa [← this]
  · intro s hs hc
    obtain ⟨a, ha, rfl⟩ := hs
    have key := h.cent a ha (fun ε hε => by
      have h1 := hc (φ ε) ⟨ε, hε, rfl⟩
      change φ a * φ ε = φ ε * φ a at h1
      rw [← map_mul, ← map_mul] at h1
      exact φ.injective h1)
    rcases key with h1 | h1
    · left; simp only [MulEquiv.coe_toMonoidHom]; rw [h1, map_one]
    · right; simp only [MulEquiv.coe_toMonoidHom]; rw [h1, hφ]

theorem OuterEFacts.map_conj {Y : Type*} [Group Y] {S₀ S : Subgroup (MulAut Y)} {t : Y}
    {E₀ : Subgroup (MulAut Y)} (h : OuterEFacts Y S₀ t E₀) (c : MulAut Y)
    (hmem : ∀ α : MulAut Y, α ∈ S ↔ c⁻¹ * α * c ∈ S₀) :
    ∃ E : Subgroup (MulAut Y), OuterEFacts Y S (c t) E := by
  have hSeq : S = S₀.map (MulAut.conj c).toMonoidHom := by
    ext α
    rw [hmem]
    constructor
    · intro hα
      refine ⟨c⁻¹ * α * c, hα, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨α₀, hα₀, rfl⟩
      have : c⁻¹ * ((MulAut.conj c).toMonoidHom α₀) * c = α₀ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [this]
  refine ⟨E₀.map (MulAut.conj c).toMonoidHom, ?_⟩
  rw [hSeq]
  exact h.map_iso (e := c) (MulAut.conj c)
    (fun x => by rw [MulAut.conj_apply]; exact (conj_aut_apply c x).symm)

theorem OuterEData.of_sylow {Y : Type*} [Group Y] [Finite (MulAut Y)] {S₀ : Subgroup (MulAut Y)}
    {t : Y} {E₀ : Subgroup (MulAut Y)} (hS₀p : IsPGroup 2 S₀) (hS₀idx : ¬ 2 ∣ S₀.index)
    (h : OuterEFacts Y S₀ t E₀) : OuterEData Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS hidx
  let P1 : Sylow 2 (MulAut Y) := hS₀p.toSylow hS₀idx
  let P2 : Sylow 2 (MulAut Y) := hS.toSylow hidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (MulAut Y) P1 P2
  have hmem : ∀ α : MulAut Y, α ∈ S ↔ c⁻¹ * α * c ∈ S₀ := by
    intro α
    have h1 : (P2 : Subgroup (MulAut Y)) = MulAut.conj c • (P1 : Subgroup (MulAut Y)) := by
      rw [← hc, Sylow.coe_subgroup_smul]
    have h2 : α ∈ (P2 : Subgroup (MulAut Y)) ↔
        (MulAut.conj c)⁻¹ • α ∈ (P1 : Subgroup (MulAut Y)) := by
      rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h3 : (P2 : Subgroup (MulAut Y)) = S := rfl
    have h4 : (P1 : Subgroup (MulAut Y)) = S₀ := rfl
    rw [h3, h4] at h2
    rw [h2]
    simp [MulAut.smul_def, mul_assoc]
  obtain ⟨E, hE⟩ := h.map_conj c hmem
  exact ⟨c t, E, hE⟩

theorem OuterEData.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : OuterEData X) : OuterEData Y := by
  intro S hS hidx
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  have hφ : ∀ x : X, φ (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext y
    simp [φ, MulAut.congr_apply]
  let S' : Subgroup (MulAut X) := S.map φ.symm.toMonoidHom
  have hS'p : IsPGroup 2 S' :=
    hS.of_equiv (Subgroup.equivMapOfInjective S φ.symm.toMonoidHom φ.symm.injective)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have : S'.index = S.index := Subgroup.index_map_equiv (H := S) φ.symm
    rwa [this]
  obtain ⟨t, E, hf⟩ := h S' hS'p hS'idx
  have hf' := hf.map_iso e φ hφ
  have hSeq : S'.map φ.toMonoidHom = S := by
    ext α
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      simpa using hb
    · intro hα
      exact ⟨φ.symm α, ⟨α, hα, rfl⟩, by simp⟩
  rw [hSeq] at hf'
  exact ⟨e t, _, hf'⟩

end CFSG.EvenSporadicStandard.Fin76b
