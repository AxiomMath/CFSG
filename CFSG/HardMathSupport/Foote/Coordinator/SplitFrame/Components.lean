module

public import CFSG.Foundations.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Plane

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open Subgroup
open scoped commutatorElement

instance normal_range_mulAutConj (M : Type*) [Group M] :
    (MulAut.conj : M →* MulAut M).range.Normal where
  conj_mem := by
    rintro _ ⟨m, rfl⟩ φ
    refine ⟨φ m, ?_⟩
    ext x
    simp [MulAut.conj_apply]

section Quasisimple

variable {M : Type*} [Group M]

theorem exists_mul_ne_of_isQuasisimple (hQ : CFSG.IsQuasisimple M) : ∃ x y : M, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul]

theorem le_center_or_eq_top_of_isQuasisimple (hQ : CFSG.IsQuasisimple M) (U : Subgroup M)
    [U.Normal] : U ≤ center M ∨ U = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (center M) with hπ
  have hn : (U.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.map π) with h | h
  · left
    intro x hx
    have : π x ∈ U.map π := ⟨x, hx, rfl⟩
    rw [h, mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  · right
    have hdec : ∀ x : M, ∃ m ∈ U, m⁻¹ * x ∈ center M := by
      intro x
      have : π x ∈ U.map π := by rw [h]; exact mem_top _
      obtain ⟨m, hm, hmx⟩ := this
      exact ⟨m, hm, (QuotientGroup.eq).1 hmx⟩
    have key1 : ∀ a b c : M, c ∈ center M → ⁅a * c, b⁆ = ⁅a, b⁆ := by
      intro a b c hc
      have hcb : c * b = b * c := (mem_center_iff.1 hc b).symm
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc a * c * b * (c⁻¹ * a⁻¹) * b⁻¹ = a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ := by group
        _ = a * (b * c) * c⁻¹ * a⁻¹ * b⁻¹ := by rw [hcb]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    have key2 : ∀ a b c : M, c ∈ center M → ⁅a, b * c⁆ = ⁅a, b⁆ := by
      intro a b c hc
      have hca : c * a⁻¹ = a⁻¹ * c := (mem_center_iff.1 hc a⁻¹).symm
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc a * (b * c) * a⁻¹ * (c⁻¹ * b⁻¹) = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [hca]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rw [eq_top_iff]
    calc (⊤ : Subgroup M) = commutator M := hperf.commutator_eq_top.symm
      _ ≤ U := by
        rw [commutator_def, commutator_le]
        intro x _ y _
        obtain ⟨m, hm, hmx⟩ := hdec x
        obtain ⟨m', hm', hmy⟩ := hdec y
        have hx : x = m * (m⁻¹ * x) := by group
        have hy : y = m' * (m'⁻¹ * y) := by group
        rw [hx, key1 _ _ _ hmx, hy, key2 _ _ _ hmy]
        exact U.mul_mem (U.mul_mem (U.mul_mem hm hm') (U.inv_mem hm)) (U.inv_mem hm')

end Quasisimple

section Conj

variable {G : Type*} [Group G]

theorem map_conj_mul (H : Subgroup G) (g h : G) :
    H.map (MulAut.conj (g * h) : G →* G) =
      (H.map (MulAut.conj h : G →* G)).map (MulAut.conj g : G →* G) := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_inv_eq {H : Subgroup G} {g : G} (h : H.map (MulAut.conj g : G →* G) = H) :
    H.map (MulAut.conj g⁻¹ : G →* G) = H := by
  conv_lhs => rw [← h]
  rw [← map_conj_mul, inv_mul_cancel, map_one]
  ext x
  simp

end Conj

section Frame

variable {G M : Type*} [Group G] [Group M]

noncomputable def frameAut [Finite M] (ψ : M →* G) (hψ : Function.Injective ψ) (g : G)
    (hg : ψ.range.map (MulAut.conj g : G →* G) = ψ.range) : MulAut M :=
  let f : M →* M := (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp
    (((MulAut.conj g : G →* G).comp ψ).codRestrict ψ.range fun m => by
      rw [← hg]
      exact ⟨ψ m, ⟨m, rfl⟩, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z => ((MonoidHom.ofInjective hψ z : ψ.range) : G)) hxy
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.codRestrict_apply] at h
    exact hψ ((MulAut.conj g).injective h)
  MulEquiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.1 hf⟩

theorem frameAut_spec [Finite M] (ψ : M →* G) (hψ : Function.Injective ψ) (g : G)
    (hg : ψ.range.map (MulAut.conj g : G →* G) = ψ.range) (m : M) :
    ψ (frameAut ψ hψ g hg m) = g * ψ m * g⁻¹ := by
  have h := MonoidHom.ofInjective_apply hψ (x := frameAut ψ hψ g hg m)
  rw [← h]
  simp [frameAut, MulAut.conj_apply]

theorem frameAut_mul [Finite M] (ψ : M →* G) (hψ : Function.Injective ψ) {g h : G}
    (hg : ψ.range.map (MulAut.conj g : G →* G) = ψ.range)
    (hh : ψ.range.map (MulAut.conj h : G →* G) = ψ.range)
    (hgh : ψ.range.map (MulAut.conj (g * h) : G →* G) = ψ.range) :
    frameAut ψ hψ (g * h) hgh = frameAut ψ hψ g hg * frameAut ψ hψ h hh := by
  ext m
  apply hψ
  rw [MulAut.mul_apply, frameAut_spec, frameAut_spec, frameAut_spec]
  group

variable {ψA ψB : M →* G}

theorem range_le_centralizer_range (hcomm : ∀ x y, Commute (ψA x) (ψB y)) :
    ψB.range ≤ centralizer (ψA.range : Set G) := by
  rintro _ ⟨y, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  exact (hcomm x y).eq

theorem sup_le_normalizer_left (hcomm : ∀ x y, Commute (ψA x) (ψB y)) :
    ψA.range ⊔ ψB.range ≤ normalizer (ψA.range : Set G) :=
  sup_le le_normalizer ((range_le_centralizer_range hcomm).trans (centralizer_le_normalizer _))

theorem sup_le_normalizer_right (hcomm : ∀ x y, Commute (ψA x) (ψB y)) :
    ψA.range ⊔ ψB.range ≤ normalizer (ψB.range : Set G) := by
  rw [sup_comm]
  exact sup_le_normalizer_left fun x y => (hcomm y x).symm

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {g x : G} (hg : g ∈ normalizer (H : Set G))
    (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (mem_normalizer_iff.1 hg x).1 hx

theorem map_conj_eq_or_eq_of_frame [Finite M] (hQ : CFSG.IsQuasisimple M)
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {g : G}
    (hg : g ∈ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G)) :
    ψA.range.map (MulAut.conj g : G →* G) = ψA.range ∨
      ψA.range.map (MulAut.conj g : G →* G) = ψB.range := by
  classical
  set A := ψA.range with hAdef
  set B := ψB.range with hBdef
  set X := A ⊔ B with hXdef
  set φ : M →* G := (MulAut.conj g : G →* G).comp ψA with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective.comp hA
  set N := A.map (MulAut.conj g : G →* G) with hNdef
  have hNφ : N = φ.range := by rw [hNdef, hφ, MonoidHom.range_comp]
  have hXg : X.map (MulAut.conj g : G →* G) = X := mem_normalizer_iff_map_conj_eq.1 hg
  have hNX : N ≤ X := by
    rw [← hXg]
    exact map_mono le_sup_left
  have hXA : X ≤ normalizer (A : Set G) := sup_le_normalizer_left hcomm
  have hXB : X ≤ normalizer (B : Set G) := sup_le_normalizer_right hcomm
  have hXN : X ≤ normalizer (N : Set G) := by
    calc X = X.map (MulAut.conj g : G →* G) := hXg.symm
      _ ≤ (normalizer (A : Set G)).map (MulAut.conj g : G →* G) := map_mono hXA
      _ ≤ normalizer (N : Set G) := le_normalizer_map _
  have hABc : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y
  have hperf : ⁅N, N⁆ = N := by
    rw [hNφ, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
      hQ.1.commutator_eq_top]
  have hNsup : N ≤ (N ⊓ A) ⊔ (N ⊓ B) := by
    calc N = ⁅N, N⁆ := hperf.symm
      _ ≤ (N ⊓ A) ⊔ (N ⊓ B) := ?_
    rw [commutator_le]
    intro n hn n' hn'
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hABc (hNX hn')
    have hnX := hNX hn
    have haX : a ∈ X := le_sup_left (a := A) ha
    have hbX : b ∈ X := le_sup_right (b := B) hb
    have h1 : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ A := by
      refine ⟨?_, A.mul_mem (conj_mem_of_mem_normalizer (hXA hnX) ha) (A.inv_mem ha)⟩
      have : a * n⁻¹ * a⁻¹ ∈ N := conj_mem_of_mem_normalizer (hXN haX) (N.inv_mem hn)
      have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
      rw [e]
      exact N.mul_mem hn this
    have h2 : n * b * n⁻¹ * b⁻¹ ∈ N ⊓ B := by
      refine ⟨?_, B.mul_mem (conj_mem_of_mem_normalizer (hXB hnX) hb) (B.inv_mem hb)⟩
      have : b * n⁻¹ * b⁻¹ ∈ N := conj_mem_of_mem_normalizer (hXN hbX) (N.inv_mem hn)
      have e : n * b * n⁻¹ * b⁻¹ = n * (b * n⁻¹ * b⁻¹) := by group
      rw [e]
      exact N.mul_mem hn this
    have h3 : a * (n * b * n⁻¹ * b⁻¹) * a⁻¹ ∈ N ⊓ B :=
      ⟨conj_mem_of_mem_normalizer (hXN haX) h2.1, conj_mem_of_mem_normalizer (hXB haX) h2.2⟩
    have e : ⁅n, a * b⁆ = (n * a * n⁻¹ * a⁻¹) * (a * (n * b * n⁻¹ * b⁻¹) * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mem_sup_left h1) (mem_sup_right h3)
  set U := (N ⊓ A).comap φ with hU
  set V := (N ⊓ B).comap φ with hV
  have hφN : ∀ m, φ m ∈ N := fun m => by rw [hNφ]; exact ⟨m, rfl⟩
  have hUn : U.Normal := ⟨fun u hu m => by
    show φ (m * u * m⁻¹) ∈ N ⊓ A
    rw [map_mul, map_mul, map_inv]
    exact ⟨conj_mem_of_mem_normalizer (hXN (hNX (hφN m))) hu.1,
      conj_mem_of_mem_normalizer (hXA (hNX (hφN m))) hu.2⟩⟩
  have hVn : V.Normal := ⟨fun v hv m => by
    show φ (m * v * m⁻¹) ∈ N ⊓ B
    rw [map_mul, map_mul, map_inv]
    exact ⟨conj_mem_of_mem_normalizer (hXN (hNX (hφN m))) hv.1,
      conj_mem_of_mem_normalizer (hXB (hNX (hφN m))) hv.2⟩⟩
  have hdec : ∀ m : M, ∃ u ∈ U, ∃ v ∈ V, m = u * v := by
    intro m
    have hc : ∀ x ∈ N ⊓ A, ∀ y ∈ N ⊓ B, Commute x y := fun x hx y hy => hABc x hx.2 y hy.2
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup_of_commute hc (hNsup (hφN m))
    have hxN : x ∈ φ.range := hNφ ▸ hx.1
    have hyN : y ∈ φ.range := hNφ ▸ hy.1
    obtain ⟨u, rfl⟩ := hxN
    obtain ⟨v, rfl⟩ := hyN
    refine ⟨u, hx, v, hy, hφinj ?_⟩
    rw [hxy, map_mul]
  have hcard : ∀ {H : Subgroup G} {ψ : M →* G}, Function.Injective ψ → H = ψ.range → N ≤ H →
      N = H := by
    intro H ψ hψ hH hNH
    have : Finite ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
    have : Finite H := hH ▸ this
    refine eq_of_le_of_card_ge hNH ?_
    rw [hH, hNφ, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
  rcases le_center_or_eq_top_of_isQuasisimple hQ U with hUc | hUt
  · rcases le_center_or_eq_top_of_isQuasisimple hQ V with hVc | hVt
    · exfalso
      obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hQ
      apply hxy
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec x
      have hz : u * v ∈ center M := mul_mem (hUc hu) (hVc hv)
      exact (mem_center_iff.1 hz y).symm
    · right
      refine hcard hB rfl ?_
      intro n hn
      rw [hNφ] at hn
      obtain ⟨m, rfl⟩ := hn
      have : m ∈ V := hVt ▸ mem_top m
      exact this.2
  · left
    refine hcard hA rfl ?_
    intro n hn
    rw [hNφ] at hn
    obtain ⟨m, rfl⟩ := hn
    have : m ∈ U := hUt ▸ mem_top m
    exact this.2

theorem range_ne_range_of_frame (hQ : CFSG.IsQuasisimple M) (hA : Function.Injective ψA)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) : ψA.range ≠ ψB.range := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hQ
  apply hxy
  have hy : ψA y ∈ ψB.range := h ▸ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hy
  apply hA
  rw [map_mul, map_mul, ← hz]
  exact (hcomm x z).eq

theorem map_conj_left_eq_iff [Finite M] (hQ : CFSG.IsQuasisimple M)
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {g : G}
    (hg : g ∈ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G)) :
    ψA.range.map (MulAut.conj g : G →* G) = ψA.range ↔
      ψB.range.map (MulAut.conj g : G →* G) = ψB.range := by
  have hcomm' : ∀ x y, Commute (ψB x) (ψA y) := fun x y => (hcomm y x).symm
  have hg' : g ∈ normalizer ((ψB.range ⊔ ψA.range : Subgroup G) : Set G) := by
    rwa [sup_comm]
  have hAB := range_ne_range_of_frame hQ hA hcomm
  have hinj : Function.Injective fun H : Subgroup G => H.map (MulAut.conj g : G →* G) :=
    map_injective (MulAut.conj g).injective
  constructor
  · intro h
    rcases map_conj_eq_or_eq_of_frame hQ hB hA hcomm' hg' with h' | h'
    · exact h'
    · exact absurd (hinj (h'.trans h.symm)) (Ne.symm hAB)
  · intro h
    rcases map_conj_eq_or_eq_of_frame hQ hA hB hcomm hg with h' | h'
    · exact h'
    · exact absurd (hinj (h'.trans h.symm)) hAB

theorem map_conj_right_eq_of_ne [Finite M] (hQ : CFSG.IsQuasisimple M)
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {g : G}
    (hg : g ∈ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G))
    (hne : ψA.range.map (MulAut.conj g : G →* G) ≠ ψA.range) :
    ψB.range.map (MulAut.conj g : G →* G) = ψA.range := by
  have hcomm' : ∀ x y, Commute (ψB x) (ψA y) := fun x y => (hcomm y x).symm
  have hg' : g ∈ normalizer ((ψB.range ⊔ ψA.range : Subgroup G) : Set G) := by
    rwa [sup_comm]
  rcases map_conj_eq_or_eq_of_frame hQ hB hA hcomm' hg' with h | h
  · exact absurd ((map_conj_left_eq_iff hQ hA hB hcomm hg).2 h) hne
  · exact h

theorem commutatorElement_mul_eq {x₁ x₂ c₁ c₂ : G} (h12 : Commute c₁ x₂) (h21 : Commute c₂ x₁)
    (hc : Commute c₁ c₂) : ⁅x₁ * c₁, x₂ * c₂⁆ = ⁅x₁, x₂⁆ := by
  have e1 : x₁ * c₁ * (x₂ * c₂) = x₁ * x₂ * (c₁ * c₂) := by
    rw [mul_assoc, ← mul_assoc c₁, h12.eq, mul_assoc, mul_assoc]
  have e2 : x₂ * c₂ * (x₁ * c₁) = x₂ * x₁ * (c₁ * c₂) := by
    rw [mul_assoc, ← mul_assoc c₂, h21.eq, mul_assoc, mul_assoc, hc.eq]
  rw [commutatorElement_def, commutatorElement_def]
  calc x₁ * c₁ * (x₂ * c₂) * (x₁ * c₁)⁻¹ * (x₂ * c₂)⁻¹
      = x₁ * c₁ * (x₂ * c₂) * (x₂ * c₂ * (x₁ * c₁))⁻¹ := by group
    _ = x₁ * x₂ * (c₁ * c₂) * (x₂ * x₁ * (c₁ * c₂))⁻¹ := by rw [e1, e2]
    _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by group

theorem isSolvable_of_le_normalizer_frame [Finite M] (hQ : CFSG.IsQuasisimple M)
    (hO : Group.IsSolvable (MulAut M ⧸ (MulAut.conj : M →* MulAut M).range))
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {Gh : Subgroup G}
    (hXG : ψA.range ⊔ ψB.range ≤ Gh)
    (hC : ∀ c ∈ centralizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) ⊓ Gh,
      ∀ d ∈ centralizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) ⊓ Gh, Commute c d)
    {P : Subgroup G} (hPG : P ≤ Gh)
    (hPN : P ≤ normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G))
    (hPX : Group.IsSolvable ↥(P ⊓ (ψA.range ⊔ ψB.range))) : Group.IsSolvable ↥P := by
  classical
  set A := ψA.range with hAdef
  set B := ψB.range with hBdef
  set X := A ⊔ B with hXdef
  set I := (MulAut.conj : M →* MulAut M).range with hIdef
  have hABc : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y
  have hAB := range_ne_range_of_frame hQ hA hcomm
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  have hσmul : ∀ p q : P,
      (if A.map (MulAut.conj ((p * q : P) : G) : G →* G) = A then (1 : ℤˣ) else -1) =
        (if A.map (MulAut.conj (p : G) : G →* G) = A then 1 else -1) *
          (if A.map (MulAut.conj (q : G) : G →* G) = A then 1 else -1) := by
    intro p q
    have hp := hPN p.2
    have hq := hPN q.2
    have e : A.map (MulAut.conj ((p * q : P) : G) : G →* G) =
        (A.map (MulAut.conj (q : G) : G →* G)).map (MulAut.conj (p : G) : G →* G) := by
      rw [Subgroup.coe_mul, map_conj_mul]
    by_cases hqA : A.map (MulAut.conj (q : G) : G →* G) = A
    · rw [ite_eq_left hqA, mul_one, e, hqA]
    · have hqB : A.map (MulAut.conj (q : G) : G →* G) = B :=
        (map_conj_eq_or_eq_of_frame hQ hA hB hcomm hq).resolve_left hqA
      rw [ite_eq_right hqA, e, hqB]
      by_cases hpA : A.map (MulAut.conj (p : G) : G →* G) = A
      · rw [ite_eq_left hpA, (map_conj_left_eq_iff hQ hA hB hcomm hp).1 hpA, ite_eq_right (Ne.symm hAB),
          one_mul]
      · rw [ite_eq_right hpA, map_conj_right_eq_of_ne hQ hA hB hcomm hp hpA, ite_eq_left rfl]
        decide
  let σ : ↥P →* ℤˣ :=
    { toFun := fun p => if A.map (MulAut.conj (p : G) : G →* G) = A then 1 else -1
      map_one' := by
        rw [ite_eq_left]
        rw [OneMemClass.coe_one, map_one]
        ext x
        simp
      map_mul' := hσmul }
  set P₀ := σ.ker with hP₀
  have hfixA : ∀ p : P₀, A.map (MulAut.conj ((p : P) : G) : G →* G) = A := by
    intro p
    by_contra h
    have hp := p.2
    rw [MonoidHom.mem_ker] at hp
    simp only [σ, MonoidHom.coe_mk, OneHom.coe_mk, ite_eq_right h] at hp
    exact hneg hp
  have hfixB : ∀ p : P₀, B.map (MulAut.conj ((p : P) : G) : G →* G) = B := fun p =>
    (map_conj_left_eq_iff hQ hA hB hcomm (hPN (p : P).2)).1 (hfixA p)
  suffices h0 : Group.IsSolvable ↥P₀ from
    Group.isSolvable_of_ker_le_range P₀.subtype σ (by rw [Subgroup.range_subtype])
  let ρA : ↥P₀ →* MulAut M :=
    { toFun := fun p => frameAut ψA hA ((p : P) : G) (hfixA p)
      map_one' := by
        ext m
        apply hA
        rw [frameAut_spec]
        simp
      map_mul' := fun p q => by
        have := frameAut_mul ψA hA (hfixA p) (hfixA q) (hfixA (p * q))
        exact this }
  let ρB : ↥P₀ →* MulAut M :=
    { toFun := fun p => frameAut ψB hB ((p : P) : G) (hfixB p)
      map_one' := by
        ext m
        apply hB
        rw [frameAut_spec]
        simp
      map_mul' := fun p q => by
        have := frameAut_mul ψB hB (hfixB p) (hfixB q) (hfixB (p * q))
        exact this }
  have : Group.IsSolvable (MulAut M ⧸ I) := hO
  let Θ : ↥P₀ →* (MulAut M ⧸ I) × (MulAut M ⧸ I) :=
    ((QuotientGroup.mk' I).comp ρA).prod ((QuotientGroup.mk' I).comp ρB)
  suffices hK : Group.IsSolvable ↥Θ.ker from
    Group.isSolvable_of_ker_le_range Θ.ker.subtype Θ (by rw [Subgroup.range_subtype])
  have hdec : ∀ k : Θ.ker, ∃ x ∈ X, ∃ c ∈ centralizer (X : Set G) ⊓ Gh,
      (((k : P₀) : P) : G) = x * c := by
    intro k
    have hk := k.2
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hk
    obtain ⟨hkA, hkB⟩ := hk
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hkA hkB
    obtain ⟨a, ha⟩ := hkA
    obtain ⟨b, hb⟩ := hkB
    set g : G := (((k : P₀) : P) : G) with hg
    have hgA : ∀ m, g * ψA m * g⁻¹ = ψA a * ψA m * (ψA a)⁻¹ := by
      intro m
      have h1 := frameAut_spec ψA hA g (hfixA k) m
      have h2 : frameAut ψA hA g (hfixA k) m = a * m * a⁻¹ := by
        have := congrArg (fun φ : MulAut M => φ m) ha
        simp only [MulAut.conj_apply] at this
        exact this.symm
      rw [← h1, h2, map_mul, map_mul, map_inv]
    have hgB : ∀ m, g * ψB m * g⁻¹ = ψB b * ψB m * (ψB b)⁻¹ := by
      intro m
      have h1 := frameAut_spec ψB hB g (hfixB k) m
      have h2 : frameAut ψB hB g (hfixB k) m = b * m * b⁻¹ := by
        have := congrArg (fun φ : MulAut M => φ m) hb
        simp only [MulAut.conj_apply] at this
        exact this.symm
      rw [← h1, h2, map_mul, map_mul, map_inv]
    set x : G := ψA a * ψB b with hx
    set c : G := x⁻¹ * g with hcdef
    have e1 : ∀ m, g * ψA m = ψA a * ψA m * (ψA a)⁻¹ * g := fun m => by
      rw [← hgA m]
      group
    have e2 : ∀ m, g * ψB m = ψB b * ψB m * (ψB b)⁻¹ * g := fun m => by
      rw [← hgB m]
      group
    have hcA : ∀ m, ψA m * c = c * ψA m := by
      intro m
      have hAB' : ψA m * (ψB b)⁻¹ = (ψB b)⁻¹ * ψA m := ((hcomm m b).inv_right).eq
      calc ψA m * c = ψA m * (ψB b)⁻¹ * (ψA a)⁻¹ * g := by rw [hcdef, hx, mul_inv_rev]; group
        _ = (ψB b)⁻¹ * ψA m * (ψA a)⁻¹ * g := by rw [hAB']
        _ = x⁻¹ * (ψA a * ψA m * (ψA a)⁻¹ * g) := by rw [hx, mul_inv_rev]; group
        _ = x⁻¹ * (g * ψA m) := by rw [← e1]
        _ = c * ψA m := by rw [hcdef]; group
    have hcB : ∀ m, ψB m * c = c * ψB m := by
      intro m
      set z : M := b * m * b⁻¹ with hz
      have hcz : ψB z * (ψA a)⁻¹ = (ψA a)⁻¹ * ψB z := ((hcomm a z).inv_left).eq.symm
      have e2' : g * ψB m = ψB z * g := by
        rw [e2, hz, map_mul, map_mul, map_inv]
      calc ψB m * c = (ψB b)⁻¹ * (ψB z * (ψA a)⁻¹) * g := by
            rw [hcdef, hx, hz, map_mul, map_mul, map_inv]; group
        _ = (ψB b)⁻¹ * ((ψA a)⁻¹ * ψB z) * g := by rw [hcz]
        _ = x⁻¹ * (ψB z * g) := by rw [hx, mul_inv_rev]; group
        _ = x⁻¹ * (g * ψB m) := by rw [e2']
        _ = c * ψB m := by rw [hcdef]; group
    refine ⟨x, mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩), c, mem_inf.2 ⟨?_, ?_⟩,
      by rw [hcdef]; group⟩
    · rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨_, ⟨m₁, rfl⟩, _, ⟨m₂, rfl⟩, rfl⟩ := exists_mul_of_mem_sup_of_commute hABc hy
      calc ψA m₁ * ψB m₂ * c = ψA m₁ * (ψB m₂ * c) := mul_assoc _ _ _
        _ = ψA m₁ * (c * ψB m₂) := by rw [hcB]
        _ = ψA m₁ * c * ψB m₂ := (mul_assoc _ _ _).symm
        _ = c * ψA m₁ * ψB m₂ := by rw [hcA]
        _ = c * (ψA m₁ * ψB m₂) := mul_assoc _ _ _
    · rw [hcdef]
      exact mul_mem (inv_mem (hXG (mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩))))
        (hPG (k : P₀).1.2)
  let ι : ↥Θ.ker →* G := P.subtype.comp (P₀.subtype.comp Θ.ker.subtype)
  have hι : Function.Injective ι :=
    P.subtype_injective.comp (P₀.subtype_injective.comp Θ.ker.subtype_injective)
  have hcommX : ⁅ι.range, ι.range⁆ ≤ P ⊓ X := by
    rw [commutator_le]
    rintro _ ⟨k₁, rfl⟩ _ ⟨k₂, rfl⟩
    refine ⟨P.mul_mem (P.mul_mem (P.mul_mem (k₁ : P₀).1.2 (k₂ : P₀).1.2)
      (P.inv_mem (k₁ : P₀).1.2)) (P.inv_mem (k₂ : P₀).1.2), ?_⟩
    obtain ⟨x₁, hx₁, c₁, hc₁, e₁⟩ := hdec k₁
    obtain ⟨x₂, hx₂, c₂, hc₂, e₂⟩ := hdec k₂
    have hι₁ : ι k₁ = x₁ * c₁ := e₁
    have hι₂ : ι k₂ = x₂ * c₂ := e₂
    rw [hι₁, hι₂, commutatorElement_mul_eq ((mem_centralizer_iff.1 hc₁.1 x₂ hx₂).symm)
      ((mem_centralizer_iff.1 hc₂.1 x₁ hx₁).symm) (hC c₁ hc₁ c₂ hc₂), commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hx₁ hx₂) (X.inv_mem hx₁)) (X.inv_mem hx₂)
  rw [← Group.isSolvable_commutator_iff]
  have hmap : ∀ y : commutator ↥Θ.ker, ι y ∈ P ⊓ X := by
    intro y
    apply hcommX
    rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def]
    exact ⟨y, y.2, rfl⟩
  let j : commutator ↥Θ.ker →* ↥(P ⊓ X) := (ι.comp (commutator ↥Θ.ker).subtype).codRestrict _ hmap
  have hj : Function.Injective j := by
    intro y z h
    have h' : ι ((commutator ↥Θ.ker).subtype y) = ι ((commutator ↥Θ.ker).subtype z) :=
      congrArg (fun w : ↥(P ⊓ X) => (w : G)) h
    exact (commutator ↥Θ.ker).subtype_injective (hι h')
  exact Group.isSolvable_of_isSolvable_injective hj

end Frame

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
