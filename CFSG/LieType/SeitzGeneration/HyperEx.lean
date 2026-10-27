module

public import CFSG.LieType.SeitzGeneration.HyperQuotient

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbedding

section HyperClosure

variable {Y : Type*} [Group Y] {p : ℕ}

@[expose] def hyperClosure (p : ℕ) (K E : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {k : Y | k ∈ K ∧ ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * k = k * f}

theorem hyperGen_iff_le {K E : Subgroup Y} : HyperGen p K E ↔ K ≤ hyperClosure p K E :=
  Iff.rfl

theorem map_hyperClosure_le (K E : Subgroup Y) [K.Normal] (g : Y) :
    (hyperClosure p K E).map (MulAut.conj g).toMonoidHom ≤
      hyperClosure p K (E.map (MulAut.conj g).toMonoidHom) := by
  rw [hyperClosure, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, ⟨hk, F, hFE, hF, hcomm⟩, rfl⟩
  refine ⟨?_, F.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hFE, ?_, ?_⟩
  · simpa using (inferInstance : K.Normal).conj_mem k hk g
  · rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hF
  · rintro _ ⟨f, hf, rfl⟩
    have h := hcomm f hf
    show g * f * g⁻¹ * (g * k * g⁻¹) = g * k * g⁻¹ * (g * f * g⁻¹)
    calc g * f * g⁻¹ * (g * k * g⁻¹) = g * (f * k) * g⁻¹ := by group
      _ = g * (k * f) * g⁻¹ := by rw [h]
      _ = g * k * g⁻¹ * (g * f * g⁻¹) := by group

theorem hyperGen_conj {K E : Subgroup Y} [K.Normal] (g : Y) (h : HyperGen p K E) :
    HyperGen p K (E.map (MulAut.conj g).toMonoidHom) := by
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by
    simpa using (inferInstance : K.Normal).conj_mem k hk g⁻¹
  have h1 : g⁻¹ * k * g ∈ hyperClosure p K E := h hk'
  have h2 := map_hyperClosure_le (p := p) K E g ⟨_, h1, rfl⟩
  have h3 : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
  rw [show (MulAut.conj g).toMonoidHom (g⁻¹ * k * g) = g * (g⁻¹ * k * g) * g⁻¹ from rfl, h3] at h2
  exact h2

end HyperClosure

section Existence

@[expose] def SeitzHyperLieEx
    (S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (Cat d) → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d →
    (∃ E₀ : Subgroup (Cat d), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3 ∧ S d p E₀) →
      ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        HyperGen p (⊤ : Subgroup (Cat d)) E

@[expose] def HyperExFor (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  SeitzHyperLieEx fun d _ _ => Fam d

theorem SeitzHyperLie.toEx
    {S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (Cat d) → Prop}
    (h : SeitzHyperLie S) : SeitzHyperLieEx S := by
  intro d p hp hp2 hpd hl ⟨E₀, hE, hc, hS⟩
  exact ⟨E₀, hE, hc, h d p hp hp2 hpd hl E₀ hE hc hS⟩

theorem SeitzHyperLieEx.of_cover
    {S S₁ S₂ : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (Cat d) → Prop}
    (hS : ∀ d p E₀, S d p E₀ → S₁ d p E₀ ∨ S₂ d p E₀)
    (h₁ : SeitzHyperLieEx S₁) (h₂ : SeitzHyperLieEx S₂) : SeitzHyperLieEx S := by
  intro d p hp hp2 hpd hl ⟨E₀, hE, hc, hs⟩
  rcases hS d p E₀ hs with h | h
  · exact h₁ d p hp hp2 hpd hl ⟨E₀, hE, hc, h⟩
  · exact h₂ d p hp hp2 hpd hl ⟨E₀, hE, hc, h⟩

end Existence

section Lift

theorem exists_lift_isElemAbelian {K L : Type*} [Group K] [Group L] [Finite K] {p : ℕ}
    (hp : p.Prime) (ρ : K →* L) (hρs : Function.Surjective ρ)
    (hker : Nat.Coprime (Nat.card ρ.ker) p) {Ē : Subgroup L} (hE : IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 3) :
    ∃ E₁ : Subgroup K, IsElemAbelian p E₁ ∧ Nat.card E₁ = p ^ 3 ∧ E₁.map ρ = Ē := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hPmap : (Ē.comap ρ).map ρ = Ē := Subgroup.map_comap_eq_self_of_surjective hρs Ē
  let P : Subgroup K := Ē.comap ρ
  obtain ⟨Q⟩ : Nonempty (Sylow p P) := inferInstance
  let E₁ : Subgroup K := (Q : Subgroup P).map P.subtype
  have hE₁p : IsPGroup p E₁ := Q.isPGroup'.map P.subtype
  have hinj : ∀ x ∈ E₁, ρ x = 1 → x = 1 := by
    intro x hx h1
    have hxk : x ∈ ρ.ker := h1
    have hord : orderOf x ∣ Nat.card ρ.ker := by
      have h := orderOf_dvd_natCard (⟨x, hxk⟩ : ρ.ker)
      rwa [Subgroup.orderOf_mk] at h
    have hcop := hE₁p.orderOf_coprime hker.symm ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hcop
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hord)
  have hmem : ∀ x ∈ E₁, ρ x ∈ Ē := by
    rintro x ⟨⟨y, hy⟩, -, rfl⟩
    exact hy
  let f : P →* Ē := (ρ.comp P.subtype).codRestrict Ē (fun y => y.2)
  have hfs : Function.Surjective f := by
    intro e
    obtain ⟨k, hk⟩ := hρs e
    exact ⟨⟨k, by simp [P, Subgroup.mem_comap, hk]⟩, Subtype.ext hk⟩
  have hĒp : IsPGroup p (⊤ : Subgroup Ē) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hE.2 ((x : Ē) : L) (x : Ē).2
  have hQtop : (Q : Subgroup P).map f = ⊤ := by
    have h := (Q.mapSurjective hfs).is_maximal' hĒp le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have himg : E₁.map ρ = Ē := by
    have h1 : E₁.map ρ = ((Q : Subgroup P).map f).map Ē.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hQtop, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    have hxy : x * y * (y * x)⁻¹ ∈ E₁ :=
      E₁.mul_mem (E₁.mul_mem hx hy) (E₁.inv_mem (E₁.mul_mem hy hx))
    have h1 : ρ (x * y * (y * x)⁻¹) = 1 := by
      have := hE.1.is_comm.comm (⟨ρ x, hmem x hx⟩ : Ē) ⟨ρ y, hmem y hy⟩
      have h2 : ρ x * ρ y = ρ y * ρ x := congrArg Subtype.val this
      rw [map_mul, map_inv, map_mul, map_mul, h2, mul_inv_cancel]
    have := hinj _ hxy h1
    rwa [mul_inv_eq_one] at this
  have hexp : ∀ x ∈ E₁, x ^ p = 1 := by
    intro x hx
    have hxp : x ^ p ∈ E₁ := E₁.pow_mem hx p
    refine hinj _ hxp ?_
    rw [map_pow]
    exact hE.2 _ (hmem x hx) |>.trans rfl
  refine ⟨E₁, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩, ?_, himg⟩
  have hinj' : Function.Injective (ρ.comp E₁.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (hinj x hx h)
  have hc : Nat.card E₁ = Nat.card (E₁.map ρ) := by
    have h := MonoidHom.range_comp ρ E₁.subtype
    rw [Subgroup.range_subtype] at h
    rw [← h]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
  rw [hc, himg, hcard]

end Lift

end CFSG.LieType.SeitzGeneration
