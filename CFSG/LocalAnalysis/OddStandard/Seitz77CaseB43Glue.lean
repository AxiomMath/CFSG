module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Wt
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Diag

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

namespace SwapPair

variable {G : Type} [Group G] {A B : Subgroup G} {t : G} (P : SwapPair A B t) {U : Type}
  [Group U] (e : ↥A ≃* U)

include P

theorem comm_conj {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * (t * b * t⁻¹) = (t * b * t⁻¹) * a :=
  P.comm a ha _ (P.swap₁ b hb)

@[expose] def psi : U × U →* G :=
  MonoidHom.mk' (fun p => (e.symm p.1 : G) * (t * (e.symm p.2 : G) * t⁻¹)) (by
    intro p q
    have hc := P.comm_conj (e.symm q.1).2 (e.symm p.2).2
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul]
    calc (e.symm p.1 : G) * (e.symm q.1 : G) *
          (t * ((e.symm p.2 : G) * (e.symm q.2 : G)) * t⁻¹)
        = (e.symm p.1 : G) * ((e.symm q.1 : G) * (t * (e.symm p.2 : G) * t⁻¹)) *
          (t * (e.symm q.2 : G) * t⁻¹) := by group
      _ = (e.symm p.1 : G) * ((t * (e.symm p.2 : G) * t⁻¹) * (e.symm q.1 : G)) *
          (t * (e.symm q.2 : G) * t⁻¹) := by rw [hc]
      _ = _ := by group)

theorem psi_apply (p : U × U) :
    P.psi e p = (e.symm p.1 : G) * (t * (e.symm p.2 : G) * t⁻¹) := rfl

theorem psi_inj : Function.Injective (P.psi e) := by
  intro p q h
  rw [psi_apply, psi_apply] at h
  obtain ⟨h1, h2⟩ := P.unique (e.symm p.1).2 (e.symm q.1).2 (P.swap₁ _ (e.symm p.2).2)
    (P.swap₁ _ (e.symm q.2).2) h
  have h1' : e.symm p.1 = e.symm q.1 := Subtype.ext h1
  have h2' : t * (e.symm p.2 : G) * t⁻¹ = t * (e.symm q.2 : G) * t⁻¹ := h2
  have h3 : (e.symm p.2 : G) = (e.symm q.2 : G) := by
    have := congrArg (fun z => t⁻¹ * z * t) h2'
    simpa [mul_assoc] using this
  exact Prod.ext (e.symm.injective h1') (e.symm.injective (Subtype.ext h3))

theorem exists_psi_eq {s : G} (hs : s ∈ A ⊔ B) : ∃ p : U × U, P.psi e p = s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_forall_comm (O := A) (E := B) P.comm hs
  have hb' : t * b * t⁻¹ ∈ A := P.swap₂ b hb
  refine ⟨(e ⟨a, ha⟩, e ⟨t * b * t⁻¹, hb'⟩), ?_⟩
  rw [psi_apply]
  simp only [MulEquiv.symm_apply_apply]
  rw [P.conj_conj]

theorem psi_swap (u v : U) : P.psi e (v, u) = t * P.psi e (u, v) * t⁻¹ := by
  rw [psi_apply, psi_apply]
  simp only
  have hc := P.comm_conj (e.symm v).2 (e.symm u).2
  have e1 : t * ((e.symm u : G) * (t * (e.symm v : G) * t⁻¹)) * t⁻¹ =
      (t * (e.symm u : G) * t⁻¹) * ((t * (t * (e.symm v : G) * t⁻¹) * t⁻¹)) := by group
  rw [e1, P.conj_conj, ← hc]

theorem psi_one_right (u : U) : P.psi e (u, 1) = (e.symm u : G) := by
  rw [psi_apply]
  simp

omit P in
@[expose] def torusHom {x : G} (hx : ∀ a ∈ A, x * a * x⁻¹ ∈ A) : U →* U :=
  MonoidHom.mk' (fun u => e ⟨x * (e.symm u : G) * x⁻¹, hx _ (e.symm u).2⟩) (by
    intro u v
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group)

omit P in
theorem torusHom_apply {x : G} (hx : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (u : U) :
    torusHom e hx u = e ⟨x * (e.symm u : G) * x⁻¹, hx _ (e.symm u).2⟩ := rfl

theorem psi_torus {x : G} (hx : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hxB : ∀ b ∈ B, x * b = b * x)
    (u v : U) : P.psi e (torusHom e hx u, v) = x * P.psi e (u, v) * x⁻¹ := by
  have hb : t * (e.symm v : G) * t⁻¹ ∈ B := P.swap₁ _ (e.symm v).2
  have hxb : x * (t * (e.symm v : G) * t⁻¹) * x⁻¹ = t * (e.symm v : G) * t⁻¹ := by
    rw [hxB _ hb]; group
  rw [psi_apply, psi_apply, torusHom_apply]
  simp only [MulEquiv.symm_apply_apply]
  calc x * (e.symm u : G) * x⁻¹ * (t * (e.symm v : G) * t⁻¹)
      = x * (e.symm u : G) * x⁻¹ * (x * (t * (e.symm v : G) * t⁻¹) * x⁻¹) := by rw [hxb]
    _ = _ := by group

end SwapPair

theorem SwapPair.decomp_eq {G : Type} [Group G] {A B A' B' : Subgroup G} {t : G}
    (P : SwapPair A B t) (P' : SwapPair A' B' t) {k : Type} [Field k] (hk : Nat.card k = 4)
    {e : ↥A ≃* ↥(unipAll k)} {μ : k} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) {x : G}
    (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hxB : ∀ b ∈ B, x * b = b * x)
    (hxe : ∀ a a' : ↥A, (a' : G) = x * a * x⁻¹ →
      coordA (e a') = μ * coordA (e a) ∧ coordB (e a') = μ * coordB (e a))
    (hcard : Nat.card ↥A' = 64) (hsup : A' ⊔ B' = A ⊔ B)
    (hxA' : ∀ a ∈ A', x * a * x⁻¹ ∈ A') : A' = A ∨ A' = B := by
  have hinj : Function.Injective (P.psi e) := P.psi_inj e
  have hA'S : ∀ y ∈ A', y ∈ A ⊔ B := fun y hy => hsup ▸ mem_sup_left hy
  let 𝒜 : Subgroup (↥(unipAll k) × ↥(unipAll k)) := A'.comap (P.psi e)
  have hmem : ∀ p, p ∈ 𝒜 ↔ P.psi e p ∈ A' := fun p => Iff.rfl
  have hrange : A' ≤ (P.psi e).range := by
    intro y hy
    obtain ⟨p, hp⟩ := P.exists_psi_eq e (hA'S y hy)
    exact ⟨p, hp⟩
  have hcard𝒜 : Nat.card ↥𝒜 = 64 := by
    have h1 : 𝒜.map (P.psi e) = A' := Subgroup.map_comap_eq_self hrange
    have h2 : Nat.card ↥(𝒜.map (P.psi e)) = Nat.card ↥𝒜 := Subgroup.card_map_of_injective hinj
    rw [h1] at h2
    rw [← h2, hcard]
  have H1 : ∀ g ∈ 𝒜, ∀ h ∈ 𝒜, g.1 * h.2 = h.2 * g.1 := by
    intro g hg h hh
    have hh' : P.psi e (h.2, h.1) ∈ B' := by
      rw [P.psi_swap e h.1 h.2]
      exact P'.swap₁ _ hh
    have hc := P'.comm _ hg _ hh'
    rw [← map_mul, ← map_mul] at hc
    have := congrArg Prod.fst (hinj hc)
    exact this
  have H2 : ∀ g ∈ 𝒜, (torusHom e hxA g.1, g.2) ∈ 𝒜 := by
    intro g hg
    rw [hmem, P.psi_torus e hxA hxB]
    exact hxA' _ hg
  have H3 : ∀ u : ↥(unipAll k), ∃ g ∈ 𝒜, ∃ h ∈ 𝒜, u = g.1 * h.2 := by
    intro u
    have hs : (e.symm u : G) ∈ A' ⊔ B' := hsup ▸ mem_sup_left (e.symm u).2
    obtain ⟨a', ha', b', hb', hab⟩ := mem_sup_of_forall_comm (O := A') (E := B') P'.comm hs
    have hc : t * b' * t⁻¹ ∈ A' := P'.swap₂ b' hb'
    obtain ⟨g, hg⟩ := P.exists_psi_eq e (hA'S a' ha')
    obtain ⟨h, hh⟩ := P.exists_psi_eq e (hA'S _ hc)
    refine ⟨g, (hmem g).mpr (hg ▸ ha'), h, (hmem h).mpr (hh ▸ hc), ?_⟩
    have e1 : P.psi e (u, 1) = P.psi e (g * (h.2, h.1)) := by
      rw [P.psi_one_right e, hab, map_mul, P.psi_swap e h.1 h.2, hg, hh, P.conj_conj]
    have := congrArg Prod.fst (hinj e1)
    simpa using this
  have hdA : ∀ g, coordA (torusHom e hxA g) = μ * coordA g := by
    intro g
    have := (hxe (e.symm g) ⟨x * (e.symm g : G) * x⁻¹, hxA _ (e.symm g).2⟩ rfl).1
    simpa [torusHom_apply] using this
  have hdB : ∀ g, coordB (torusHom e hxA g) = μ * coordB g := by
    intro g
    have := (hxe (e.symm g) ⟨x * (e.symm g : G) * x⁻¹, hxA _ (e.symm g).2⟩ rfl).2
    simpa [torusHom_apply] using this
  rcases weights_lemma hk hμ0 hμ1 (torusHom e hxA) hdA hdB 𝒜 hcard𝒜 H1 H2 H3 with h | h
  · left
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := P.exists_psi_eq e (hA'S y hy)
      have hg𝒜 : g ∈ 𝒜 := (hmem g).mpr (hg ▸ hy)
      have h2 : g.2 = 1 := (h g).mp hg𝒜
      have : g = (g.1, 1) := Prod.ext rfl h2
      rw [this, P.psi_one_right e] at hg
      rw [← hg]
      exact (e.symm g.1).2
    · intro hy
      have : P.psi e (e ⟨y, hy⟩, 1) = y := by rw [P.psi_one_right e]; simp
      have hmem' : (e ⟨y, hy⟩, (1 : ↥(unipAll k))) ∈ 𝒜 := (h _).mpr rfl
      rw [hmem, this] at hmem'
      exact hmem'
  · right
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := P.exists_psi_eq e (hA'S y hy)
      have hg𝒜 : g ∈ 𝒜 := (hmem g).mpr (hg ▸ hy)
      have h1 : g.1 = 1 := (h g).mp hg𝒜
      rw [← hg, P.psi_apply, h1]
      simp only [map_one, OneMemClass.coe_one, one_mul]
      exact P.swap₁ _ (e.symm g.2).2
    · intro hy
      have hc : t * y * t⁻¹ ∈ A := P.swap₂ y hy
      have : P.psi e (1, e ⟨t * y * t⁻¹, hc⟩) = y := by
        rw [P.psi_apply]
        simp only [map_one, OneMemClass.coe_one, one_mul, MulEquiv.symm_apply_apply]
        exact P.conj_conj y
      have hmem' : ((1 : ↥(unipAll k)), e ⟨t * y * t⁻¹, hc⟩) ∈ 𝒜 := (h _).mpr rfl
      rw [hmem, this] at hmem'
      exact hmem'

end CFSG.OddStandard.Seitz77
