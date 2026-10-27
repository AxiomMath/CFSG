module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.LiftGen
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.HyperEichler
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.IndexGen

public section

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.Open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Quot

variable {Y : Type*} [Group Y]

@[expose] def autQuot (σ : MulAut Y) : MulAut (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ (Subgroup.map_center_eq σ)

@[simp] theorem autQuot_mk (σ : MulAut Y) (y : Y) :
    autQuot σ (QuotientGroup.mk y) = QuotientGroup.mk (σ y) := by
  simp [autQuot, QuotientGroup.congr_mk]

@[expose] def autQuotHom : MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun := autQuot
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => simp
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => simp

end Quot


section Main

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

private theorem natCast_ne_zero_zmod_two (hp : p.Prime) (hp2 : p ≠ 2) : (p : ZMod 2) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm

theorem le_centGenI_of_orthGeometry (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X}
    (hK : commutator ↥K = ⊤) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    {A : Subgroup X} (hAel : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set X))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(elementaryGroup Q))
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ p = 1 →
      ∃ y : ↥(elementaryGroup Q), σ = MulAut.conj y)
    (hcenter : ∀ z : ↥(elementaryGroup Q), (∀ x : ↥(elementaryGroup Q), z * x = x * z) → z = 1)
    (hfix : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ x ∈ E, x ^ p = 1) → ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f) :
    K ≤ GL83.CompFam.centGenI p A K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Y := ↥K with hY
  set ξ : Y →* ↥(elementaryGroup Q) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hξ
  have hξsurj : Function.Surjective ξ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hξker : ξ.ker = Subgroup.center Y := by
    ext y
    simp [hξ]
  let α : A →* MulAut Y := K.normalizerMonoidHom.comp (Subgroup.inclusion hAK)
  let ψ : A →* MulAut ↥(elementaryGroup Q) :=
    (MulAut.congr φ).toMonoidHom.comp (autQuotHom.comp α)
  have hψξ : ∀ (a : A) (y : Y), ξ (α a y) = ψ a (ξ y) := by
    intro a y
    simp [hξ, ψ, autQuotHom, MulAut.congr_apply]
    rfl
  have hψp : ∀ a : A, ψ a ^ p = 1 := by
    intro a
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hAel.2 a a.2)
    rw [this, map_one]
  choose yfun hyfun using fun a : A => hAut (ψ a) (hψp a)
  have hconj_inj : ∀ u v : ↥(elementaryGroup Q), MulAut.conj u = MulAut.conj v → u = v := by
    intro u v h
    have h1 : v⁻¹ * u = 1 := hcenter _ (fun x => by
      have := congrArg (fun f : MulAut ↥(elementaryGroup Q) => f x) h
      simp only [MulAut.conj_apply] at this
      have h2 : (v⁻¹ * u) * x = x * (v⁻¹ * u) := by
        calc (v⁻¹ * u) * x = v⁻¹ * (u * x * u⁻¹) * u := by group
          _ = v⁻¹ * (v * x * v⁻¹) * u := by rw [this]
          _ = x * (v⁻¹ * u) := by group
      exact h2)
    exact (inv_mul_eq_one.mp h1).symm
  let Yh : A →* ↥(elementaryGroup Q) :=
    { toFun := yfun
      map_one' := by
        apply hconj_inj
        rw [← hyfun, map_one, map_one]
      map_mul' := fun a b => by
        apply hconj_inj
        rw [map_mul, ← hyfun, ← hyfun, ← hyfun, map_mul] }
  have hYh_conj : ∀ a : A, MulAut.conj (Yh a) = ψ a := fun a => (hyfun a).symm
  let ρ : A →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp Yh
  have hρO : ∀ a : A, ρ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun a =>
    elementaryGroup_le_orthogonalGroup Q (Yh a).2
  have hfin : Finite (V ≃ₗ[ZMod 2] V) := by
    have : Finite V := Module.finite_of_finite (ZMod 2)
    exact Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) fun g g' h =>
      LinearEquiv.ext (congrFun h)
  set Ab : Subgroup (V ≃ₗ[ZMod 2] V) := ρ.range with hAb
  have hAbO : Ab ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, rfl⟩
    exact hρO a
  have hAbcomm : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm a b]
  have hAbexp : ∀ x ∈ Ab, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hAel.2 a a.2)
    rw [this, map_one]
  obtain ⟨P, hP⟩ := hfix Ab hAbO hAbexp
  have hpK := natCast_ne_zero_zmod_two hp hp2
  have hgen := Coordinator.elementaryGroup_le_closure_hyperEichlerSet (Q := Q) hp hpK hQ
    hAbO hAbcomm hAbexp P (fun h hh => (hP h hh).1) (fun h hh => (hP h hh).2)
  set S := Coordinator.hyperEichlerSet Q p Ab with hS
  have hSle : ∀ g ∈ S, g ∈ elementaryGroup Q := by
    rintro g ⟨F, -, -, u, w, -, -, rfl⟩
    exact eichler_mem_elementaryGroup Q u w
  have h2 : (2 : ZMod 2) = 0 := by decide
  set 𝒢 : Set Y := {y | ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) ∈ S} with h𝒢
  have hTtop : Subgroup.closure {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[ZMod 2] V) ∈ S} = ⊤ := by
    rw [eq_top_iff]
    rintro ω -
    have hω : (ω : V ≃ₗ[ZMod 2] V) ∈ Subgroup.closure S := hgen ω.2
    have key : ∀ g ∈ Subgroup.closure S, ∃ t ∈ Subgroup.closure
        {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[ZMod 2] V) ∈ S}, (t : V ≃ₗ[ZMod 2] V) = g := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        exact ⟨⟨x, hSle x hx⟩, Subgroup.subset_closure hx, rfl⟩
      | one => exact ⟨1, one_mem _, rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨t', ht', rfl⟩ := hy
        exact ⟨t * t', mul_mem ht ht', rfl⟩
      | inv x _ hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        exact ⟨t⁻¹, inv_mem ht, rfl⟩
    obtain ⟨t, ht, hte⟩ := key _ hω
    have : t = ω := Subtype.ext hte
    rwa [this] at ht
  have himage : ξ '' 𝒢 = {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[ZMod 2] V) ∈ S} := by
    ext ω
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hω
      obtain ⟨y, rfl⟩ := hξsurj ω
      exact ⟨y, hω, rfl⟩
  have hgen' : Subgroup.closure 𝒢 ⊔ Subgroup.center Y = ⊤ := by
    have hmap : (Subgroup.closure 𝒢).map ξ = ⊤ := by
      rw [MonoidHom.map_closure, himage, hTtop]
    have := Subgroup.comap_map_eq ξ (Subgroup.closure 𝒢)
    rw [hmap, Subgroup.comap_top, hξker] at this
    exact this.symm
  have hsq : ∀ y ∈ 𝒢, y ^ 2 ∈ Subgroup.center Y := by
    intro y hy
    rw [← hξker, MonoidHom.mem_ker, map_pow]
    obtain ⟨F, -, -, u, w, -, -, hg⟩ := hy
    apply Subtype.ext
    change ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) *
      ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) = 1
    rw [hg]
    exact Coordinator.eichler_mul_self_of_two_eq_zero h2 u w
  set ℰ : Set (Subgroup X) := {E | E ≤ A ∧ Nat.card A ≤ p * Nat.card E} with hℰdef
  have hℰ : ∀ E ∈ ℰ, E ≤ Subgroup.normalizer (K : Set X) := fun E hE => hE.1.trans hAK
  have hfix' : ∀ y ∈ 𝒢, ∃ E, ∃ hE : E ∈ ℰ, ∀ (a : X) (ha : a ∈ E),
      ((K.normalizerMonoidHom ⟨a, hℰ E hE ha⟩ : MulAut ↥K) y)⁻¹ * y ∈ Subgroup.center ↥K := by
    intro y hy
    have hg : ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) ∈ S := hy
    obtain ⟨F, hFAb, hF, hcomm⟩ := Coordinator.exists_commute_of_mem_hyperEichlerSet hAbO hg
    set N : Subgroup A := F.comap ρ with hN
    have hcardN : Nat.card A ≤ p * Nat.card N := by
      have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
      set F' : Subgroup Ab := F.subgroupOf Ab with hF'
      have hNeq : N = F'.comap ρ.rangeRestrict := by
        ext a
        simp [hN, hF', Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      have hidx : N.index = F'.index := by
        rw [hNeq]
        exact Subgroup.index_comap_of_surjective F' hsurj
      have hF'card : Nat.card F' = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFAb).toEquiv
      have h1 : F'.index * Nat.card F' = Nat.card Ab := F'.index_mul_card
      have h2' : N.index * Nat.card N = Nat.card A := N.index_mul_card
      have hFpos : 0 < Nat.card F := Nat.card_pos
      have hle : F'.index ≤ p := by
        by_contra hlt
        push Not at hlt
        have h3 : p * Nat.card F < F'.index * Nat.card F := Nat.mul_lt_mul_of_pos_right hlt hFpos
        have h4 : F'.index * Nat.card F = Nat.card Ab := by rw [← hF'card]; exact h1
        omega
      calc Nat.card A = N.index * Nat.card N := h2'.symm
        _ ≤ p * Nat.card N := Nat.mul_le_mul_right _ (hidx ▸ hle)
    have hE : N.map A.subtype ∈ ℰ := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩
        exact a.2
      · rw [Subgroup.card_map_of_injective A.subtype_injective]
        exact hcardN
    refine ⟨N.map A.subtype, hE, ?_⟩
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    have hcom := hcomm (ρ a') ha'
    change ((α a') y)⁻¹ * y ∈ Subgroup.center ↥K
    rw [← hξker, MonoidHom.mem_ker, map_mul, map_inv, hψξ, ← hYh_conj]
    have hfixed : MulAut.conj (Yh a') (ξ y) = ξ y := by
      apply Subtype.ext
      change (ρ a') * ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) * (ρ a')⁻¹ =
        ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V)
      rw [hcom, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfixed, inv_mul_cancel]
  have hmain := le_iSup_centralizer_of_lifts hK hZ ℰ hℰ 𝒢 hgen' hsq hfix'
  refine hmain.trans (iSup₂_le fun E hE => ?_)
  exact le_iSup (fun E : {E : Subgroup X // E ≤ A ∧ Nat.card A ≤ p * Nat.card E} =>
    K ⊓ Subgroup.centralizer (E.1 : Set X)) ⟨E, hE.1, hE.2⟩

end Main

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
