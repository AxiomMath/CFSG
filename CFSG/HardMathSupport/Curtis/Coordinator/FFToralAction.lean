module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFToralSetup
public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Setup
public import CFSG.HardMathSupport.Curtis.Coordinator.FFToralKey

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.Proving

open scoped Matrix

variable {G : Type} [Group G] [Finite G] {M S L Q : Subgroup G}

@[expose] noncomputable def natCoord {B K : Type} [Group B] [Group K] {F : Type} [Field F]
    (h : B →* K) (hhb : Function.Bijective h) (π : ↥(StatedSL 3 F) →* K)
    (hπb : Function.Bijective π) : B ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
  ((MulEquiv.ofBijective h hhb).trans (MulEquiv.ofBijective π hπb).symm).trans
    (specialLinearGroupEquivStatedSL 3 F).symm

theorem h_natCoord_symm {B K : Type} [Group B] [Group K] {F : Type} [Field F]
    (h : B →* K) (hhb : Function.Bijective h) (π : ↥(StatedSL 3 F) →* K)
    (hπb : Function.Bijective π) (M : Matrix.SpecialLinearGroup (Fin 3) F) :
    h ((natCoord h hhb π hπb).symm M) = π (specialLinearGroupEquivStatedSL 3 F M) := by
  simp [natCoord]

omit [Finite G] in
theorem rho_conj_h (hL : IsWeakSBlock M S L) (hQM : Q ≤ M)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    (h : ↥(barM M L) →* ↥(autOn L (blockV S L)))
    (hcompat : ∀ l : ↥L, h (toBar hL.le l) = toAut S L l) (q : ↥Q)
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M) ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (l : ↥(barM M L)) :
    (h (Subgroup.normalizerMonoidHom (barM M L)
        ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M), hx⟩ l) :
      MulAut ↥(blockV S L)) =
      Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) q * (h l : MulAut ↥(blockV S L)) *
        (Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) q)⁻¹ := by
  obtain ⟨l₁, rfl⟩ := (show Function.Surjective (toBar hL.le) from by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩) l
  have hql : (q : G) * (l₁ : G) * (q : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hQL q.2) l₁).mp l₁.2
  have hnm : Subgroup.normalizerMonoidHom (barM M L)
      ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M), hx⟩ (toBar hL.le l₁) =
      toBar hL.le ⟨(q : G) * (l₁ : G) * (q : G)⁻¹, hql⟩ := by
    refine Subtype.ext ?_
    rw [coe_normalizerMonoidHom]
    simp only [coe_toBar]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [hnm, hcompat, hcompat, coe_toAut, coe_toAut]
  exact (rho_conj_rho hQL hQS q l₁ hql).symm


omit [Finite G] in
theorem exists_matrices (hL : IsWeakSBlock M S L) (hQM : Q ≤ M)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    (h : ↥(barM M L) →* ↥(autOn L (blockV S L))) (hhb : Function.Bijective h)
    (hcompat : ∀ l : ↥L, h (toBar hL.le l) = toAut S L l) {F : Type} [Field F]
    (π : ↥(StatedSL 3 F) →* ↥(autOn L (blockV S L))) (hπb : Function.Bijective π)
    (g' : Matrix.SpecialLinearGroup (Fin 3) F) {b : Fin 3 → Fin 3 → F} (hb : LinearIndependent F b)
    (hkey : ∀ q : ↥Q, ∃ (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M) ∈
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (A' : GL (Fin 3) F)
        (a : Fin 3 → F),
        normAut ((natCoord h hhb π hπb).trans (MulAut.conj g'⁻¹))
          ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M), hx⟩ =
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A' ∧
        ∀ i, (A' : Matrix (Fin 3) (Fin 3) F) *ᵥ b i = a i • b i) :
    ∃ A : MulAut ↥(blockV S L) → GL (Fin 3) F,
      (∀ p ∈ (Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS)).range,
        ∀ γ γ' : ↥(StatedSL 3 F), (γ' : GL (Fin 3) F) = A p * (γ : GL (Fin 3) F) * (A p)⁻¹ →
          p * (π γ : MulAut ↥(blockV S L)) * p⁻¹ = (π γ' : MulAut ↥(blockV S L))) ∧
      ∀ p ∈ (Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS)).range,
        ∀ p' ∈ (Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS)).range,
          A p * A p' = A p' * A p := by
  classical
  set ψ₀ := natCoord h hhb π hπb with hψ₀
  let ĝ : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL g'
  choose hx A' a hA' hdiag using hkey
  have hQV := le_normalizer_blockV_of hQL hQS
  let Aq : ↥Q → GL (Fin 3) F := fun q => ĝ * A' q * ĝ⁻¹
  have hAqcomm : ∀ q q' : ↥Q, Aq q * Aq q' = Aq q' * Aq q := by
    intro q q'
    have := mul_comm_of_diag hb (hdiag q) (hdiag q')
    simp only [Aq]
    calc ĝ * A' q * ĝ⁻¹ * (ĝ * A' q' * ĝ⁻¹) = ĝ * (A' q * A' q') * ĝ⁻¹ := by group
      _ = ĝ * (A' q' * A' q) * ĝ⁻¹ := by rw [this]
      _ = _ := by group
  have hσ : ∀ M : Matrix.SpecialLinearGroup (Fin 3) F,
      ((specialLinearGroupEquivStatedSL 3 F M : ↥(StatedSL 3 F)) : GL (Fin 3) F) =
        Matrix.SpecialLinearGroup.toGL M := fun M => Units.ext rfl
  have hC1 : ∀ (q : ↥Q) (γ γ' : ↥(StatedSL 3 F)),
      (γ' : GL (Fin 3) F) = Aq q * (γ : GL (Fin 3) F) * (Aq q)⁻¹ →
        Setup.rho (blockV S L) Q hQV q * (π γ : MulAut ↥(blockV S L)) *
          (Setup.rho (blockV S L) Q hQV q)⁻¹ = (π γ' : MulAut ↥(blockV S L)) := by
    intro q γ γ' hγ'
    set M₀ := (specialLinearGroupEquivStatedSL 3 F).symm γ with hM₀
    set l := ψ₀.symm M₀ with hl
    have hπγ : π γ = h l := by
      rw [hl, hψ₀, h_natCoord_symm, hM₀, MulEquiv.apply_symm_apply]
    set nm := Subgroup.normalizerMonoidHom (barM M L)
      ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M), hx q⟩ with hnm
    have hconj : ∀ l' : ↥(barM M L),
        MulAut.conj g'⁻¹ (ψ₀ (nm l')) = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F (A' q) (MulAut.conj g'⁻¹ (ψ₀ l')) := by
      intro l'
      have h1 := normAut_apply (ψ₀.trans (MulAut.conj g'⁻¹))
        ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(q : G), hQM q.2⟩ : ↥M), hx q⟩ l'
      rw [(hA' q)] at h1
      exact h1.symm
    have hGL := toGL_conj_of_conj ψ₀ g' nm (A' q) hconj l
    have hψl : ψ₀ l = M₀ := by simp [hl]
    rw [hψl] at hGL
    have hγeq : γ' = specialLinearGroupEquivStatedSL 3 F (ψ₀ (nm l)) := by
      apply Subtype.ext
      have hγM : (γ : GL (Fin 3) F) = Matrix.SpecialLinearGroup.toGL M₀ := by
        have := hσ M₀
        rwa [hM₀, MulEquiv.apply_symm_apply] at this
      rw [hσ, hGL, hγ', hγM]
    have hπγ' : π γ' = h (nm l) := by
      rw [hγeq, ← h_natCoord_symm h hhb π hπb, ← hψ₀, MulEquiv.symm_apply_apply]
    rw [hπγ, hπγ']
    exact (rho_conj_h hL hQM hQL hQS h hcompat q (hx q) l).symm
  let Afun : MulAut ↥(blockV S L) → GL (Fin 3) F := fun p =>
    if hp : ∃ q : ↥Q, Setup.rho (blockV S L) Q hQV q = p then Aq (Classical.choose hp) else 1
  have hAfun : ∀ p (hex : ∃ q : ↥Q, Setup.rho (blockV S L) Q hQV q = p),
      Afun p = Aq (Classical.choose hex) := fun p hex => by
    simp only [Afun, hex, ↓reduceDIte]
  refine ⟨Afun, ?_, ?_⟩
  · intro p hp γ γ' hγ'
    obtain ⟨q₁, hq₁⟩ := hp
    have hex : ∃ q : ↥Q, Setup.rho (blockV S L) Q hQV q = p := ⟨q₁, hq₁⟩
    rw [hAfun p hex] at hγ'
    rw [← Classical.choose_spec hex]
    exact hC1 _ γ γ' hγ'
  · intro p hp p' hp'
    obtain ⟨q₁, hq₁⟩ := hp
    obtain ⟨q₂, hq₂⟩ := hp'
    have hex : ∃ q : ↥Q, Setup.rho (blockV S L) Q hQV q = p := ⟨q₁, hq₁⟩
    have hex' : ∃ q : ↥Q, Setup.rho (blockV S L) Q hQV q = p' := ⟨q₂, hq₂⟩
    rw [hAfun p hex, hAfun p' hex']
    exact hAqcomm _ _

end CFSG.HardMathSupport.Curtis.Coordinator
