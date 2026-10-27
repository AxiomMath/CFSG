module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Transfer

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G]

theorem eight_case {M S L : Subgroup G} {p r s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (hs : 6 ≤ s)
    (hlt : ∀ (k : ℕ)
      (ρ : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* Perm (Fin k)),
      Function.Surjective ρ → k < 2 * p)
    (D : EightBlockData M S L r s)
    {U : Subgroup G} (hUM : U ≤ M) (hUS : U ≤ Subgroup.normalizer (S : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUp : IsPGroup p U) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≤ U ∧ U₂ ≤ U ∧ U₁ ⊓ U₂ ≤ blockCentralizer M L ∧
      U₁.relIndex U ≤ p ∧ U₂.relIndex U ≤ p ∧
      ∀ y ∈ M ⊓ Subgroup.normalizer (S : Set G), y ∈ Subgroup.normalizer (L : Set G) →
        y ∈ Subgroup.normalizer (U : Set G) →
        y ∈ Subgroup.normalizer (U₁ : Set G) ∧ y ∈ Subgroup.normalizer (U₂ : Set G) := by
  obtain ⟨ψ, hB, hact⟩ := D
  have hBC : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L :=
    AGLEmbedding.barM_mono inf_le_right
  have hcard : Fintype.card (OmegaE r s) = 2 * r + s := by
    simp [OmegaE, Fintype.card_sum, Fintype.card_prod, mul_comm]
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hsurj : Function.Surjective
      ((eightAction (Fin r) (Fin s)).comp
        ((sectionEquiv hBC ψ (eightN r s) hB).trans (eightEquiv r s)).toMonoidHom) :=
    eightAction_surjective.comp ((sectionEquiv hBC ψ (eightN r s) hB).trans (eightEquiv r s)).surjective
  have hkr : r < 2 * p := hlt r ((MonoidHom.fst _ _).comp
    ((eightAction (Fin r) (Fin s)).comp
      ((sectionEquiv hBC ψ (eightN r s) hB).trans (eightEquiv r s)).toMonoidHom))
    (fun a => by
      obtain ⟨x, hx⟩ := hsurj (a, 1)
      exact ⟨x, by simpa using congrArg Prod.fst hx⟩)
  have hks : s < 2 * p := hlt s ((MonoidHom.snd _ _).comp
    ((eightAction (Fin r) (Fin s)).comp
      ((sectionEquiv hBC ψ (eightN r s) hB).trans (eightEquiv r s)).toMonoidHom))
    (fun a => by
      obtain ⟨x, hx⟩ := hsurj (1, a)
      exact ⟨x, by simpa using congrArg Prod.snd hx⟩)
  obtain ⟨π, hπ, hker⟩ := exists_block_action (by omega) (by omega) ψ hUM hUL
  have hAlt : ∀ u, π u ∈ alternatingGroup (OmegaE r s) :=
    mem_alternatingGroup_of_isPGroup hp hp2 hUp π
  have hbarU : ∀ u : ↥U, (QuotientGroup.mk (⟨u, hUM u.2⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      barM M (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)) := fun u =>
    (mem_barM _).2 ⟨⟨u, hUM u.2⟩, Subgroup.mem_inf.2 ⟨hUS u.2, hUL u.2⟩, rfl⟩
  have hπE : ∀ u : ↥U, ∃ σ₁ ∈ wStab (Fin r) Bool, ∃ σ₂ : Perm (Fin s),
      π u = Perm.sumCongr σ₁ σ₂ := by
    intro u
    obtain ⟨σ₁, hσ₁, σ₂, hσ⟩ := hact _ (hbarU u)
    refine ⟨σ₁, hσ₁, σ₂, eq_of_conjSpec (by omega) ψ
      (mk_mem_normalizer_barM (hUM u.2) (hUL u.2)) (hπ u) ?_⟩
    exact hσ
  have inj : Function.Injective (Perm.sumCongrHom (Fin r × Bool) (Fin s)) :=
    Perm.sumCongrHom_injective
  have hrange : ∀ u : ↥U, π u ∈ (Perm.sumCongrHom (Fin r × Bool) (Fin s)).range := by
    intro u
    obtain ⟨σ₁, -, σ₂, h⟩ := hπE u
    exact ⟨(σ₁, σ₂), by rw [Perm.sumCongrHom_apply]; exact h.symm⟩
  let g : ↥U →* Perm (Fin r × Bool) × Perm (Fin s) :=
    (MonoidHom.ofInjective inj).symm.toMonoidHom.comp (π.codRestrict _ hrange)
  have hg : ∀ u, Perm.sumCongr (g u).1 (g u).2 = π u := by
    intro u
    have h2 : Perm.sumCongrHom (Fin r × Bool) (Fin s) (g u) = π u :=
      congrArg Subtype.val ((MonoidHom.ofInjective inj).apply_symm_apply ⟨π u, hrange u⟩)
    rw [Perm.sumCongrHom_apply] at h2
    exact h2
  have hgu : ∀ u : ↥U, ∃ σ₁ ∈ wStab (Fin r) Bool, ∃ σ₂ : Perm (Fin s), g u = (σ₁, σ₂) := by
    intro u
    obtain ⟨σ₁, hσ₁, σ₂, h⟩ := hπE u
    refine ⟨σ₁, hσ₁, σ₂, inj ?_⟩
    rw [Perm.sumCongrHom_apply, Perm.sumCongrHom_apply, hg, h]
  have hmem : ∀ u : ↥U, g u ∈ pTilde (Fin r) (Fin s) := by
    intro u
    obtain ⟨σ₁, hσ₁, σ₂, h⟩ := hgu u
    rw [mem_pTilde, h]
    refine ⟨hσ₁, ?_⟩
    have h1 : sign (π u) = 1 := (mem_alternatingGroup).1 (hAlt u)
    rw [← hg, h, sign_sumCongr] at h1
    exact h1
  let g' : ↥U →* ↥(pTilde (Fin r) (Fin s)) := g.codRestrict _ hmem
  let A : ↥U →* Perm (Fin r) × Perm (Fin s) := (eightAction (Fin r) (Fin s)).comp g'
  let A1 : ↥U →* Perm (Fin r) := (MonoidHom.fst _ _).comp A
  let A2 : ↥U →* Perm (Fin s) := (MonoidHom.snd _ _).comp A
  have hkerA : A.ker = g'.ker :=
    ker_comp_eq_of_isPGroup hp hp2 hUp g' _ isPGroup_ker_eightAction
  have hkerπ : g'.ker ≤ π.ker := by
    intro u hu
    have h1 : g u = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hu)
    rw [MonoidHom.mem_ker, ← hg, h1]
    simp
  have hker12 : ∀ u : ↥U, A1 u = 1 → A2 u = 1 → u ∈ π.ker := by
    intro u h1 h2
    apply hkerπ
    rw [← hkerA, MonoidHom.mem_ker]
    exact Prod.ext h1 h2
  let U₁ : Subgroup G := A1.ker.map U.subtype
  let U₂ : Subgroup G := A2.ker.map U.subtype
  have hrel : ∀ K : Subgroup ↥U, (K.map U.subtype).relIndex U = K.index := by
    intro K
    have : (K.map U.subtype).subgroupOf U = K := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective K
    rw [Subgroup.relIndex, this]
  refine ⟨U₁, U₂, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨⟨u₁, hu₁, rfl⟩, ⟨u₂, hu₂, hu₂x⟩⟩
    have : u₂ = u₁ := Subtype.ext hu₂x
    subst this
    have h := hker12 u₂ hu₁ hu₂
    rw [hker, Subgroup.mem_subgroupOf] at h
    exact (Subgroup.mem_inf.1 h).2
  · rw [hrel]
    exact index_ker_le_of_perm hp hkr hUp A1
  · rw [hrel]
    exact index_ker_le_of_perm hp hks hUp A2
  · have claim : ∀ y : G, y ∈ M ⊓ Subgroup.normalizer (S : Set G) →
        y ∈ Subgroup.normalizer (L : Set G) → y ∈ Subgroup.normalizer (U : Set G) →
        (∀ h ∈ U₁, y * h * y⁻¹ ∈ U₁) ∧ (∀ h ∈ U₂, y * h * y⁻¹ ∈ U₂) := by
      intro y hyMS hyL hyU
      have hyM : y ∈ M := hyMS.1
      have hyS : y ∈ Subgroup.normalizer (S : Set G) := hyMS.2
      have hyb : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
          barM M (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)) :=
        (mem_barM _).2 ⟨⟨y, hyM⟩, Subgroup.mem_inf.2 ⟨hyS, hyL⟩, rfl⟩
      obtain ⟨τ₁, hτ₁, τ₂, hτ⟩ := hact _ hyb
      have hyN := mk_mem_normalizer_barM hyM hyL
      have key : ∀ u : ↥U, ∃ u' : ↥U, (u' : G) = y * u * y⁻¹ ∧
          A1 u' = wStabAction (Fin r) ⟨τ₁, hτ₁⟩ * A1 u * (wStabAction (Fin r) ⟨τ₁, hτ₁⟩)⁻¹ ∧
          A2 u' = τ₂ * A2 u * τ₂⁻¹ := by
        intro u
        have hmem' : y * (u : G) * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hyU u).1 u.2
        refine ⟨⟨_, hmem'⟩, rfl, ?_⟩
        have h1 := hπ ⟨_, hmem'⟩
        have h2 := conjSpec_conj ψ (mk_mem_normalizer_barM (hUM u.2) (hUL u.2)) hyN (hπ u) hτ
        have h2' : ConjSpec ψ (QuotientGroup.mk (⟨y * u * y⁻¹, hUM hmem'⟩ : ↥M) :
            ↥M ⧸ CFSG.pCore 2 ↥M) _ := h2
        have hπu' : π ⟨_, hmem'⟩ = Perm.sumCongr τ₁ τ₂ * π u * (Perm.sumCongr τ₁ τ₂)⁻¹ :=
          eq_of_conjSpec (by omega) ψ (mk_mem_normalizer_barM (hUM hmem') (hUL hmem')) h1 h2'
        have hgu' : g ⟨_, hmem'⟩ = (τ₁, τ₂) * g u * (τ₁, τ₂)⁻¹ := by
          apply inj
          simp only [map_mul, map_inv, Perm.sumCongrHom_apply]
          rw [hg, hg, ← hπu']
        have := eightAction_conj (p := g' u) (p' := g' ⟨_, hmem'⟩) hτ₁ (σ₂ := τ₂) hgu'
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      refine ⟨fun h ⟨u, hu, hux⟩ => ?_, fun h ⟨u, hu, hux⟩ => ?_⟩
      · obtain ⟨u', hu'1, hA1, -⟩ := key u
        refine ⟨u', ?_, by show (u' : G) = _; rw [hu'1]; exact congrArg (fun z => y * z * y⁻¹) hux⟩
        show A1 u' = 1
        rw [hA1, show A1 u = 1 from hu, mul_one, mul_inv_cancel]
      · obtain ⟨u', hu'1, -, hA2⟩ := key u
        refine ⟨u', ?_, by show (u' : G) = _; rw [hu'1]; exact congrArg (fun z => y * z * y⁻¹) hux⟩
        show A2 u' = 1
        rw [hA2, show A2 u = 1 from hu, mul_one, mul_inv_cancel]
    intro y hyMS hyL hyU
    obtain ⟨c1, c2⟩ := claim y hyMS hyL hyU
    obtain ⟨d1, d2⟩ := claim y⁻¹ (inv_mem hyMS) (inv_mem hyL) (inv_mem hyU)
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨c1 h, fun hh => ?_⟩
      simpa [mul_assoc] using d1 _ hh
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨c2 h, fun hh => ?_⟩
      simpa [mul_assoc] using d2 _ hh

end CFSG.HardMathSupport.RichardWeiss.Coordinator
