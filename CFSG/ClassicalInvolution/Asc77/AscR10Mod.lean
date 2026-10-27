module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactLie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.R10

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3Typed

section Model

variable {p e : ℕ} [Fact p.Prime]


theorem aut_map_fund_g2 (hp2 : p ≠ 2) (hp3 : p ≠ 3) (he : 1 ≤ e)
    (α : MulAut ↥(adjointGroup Tag.G2 (GaloisField p e)))
    {F₁ : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hF₁ : F₁ ∈ fundamentalSubgroups StatedLieTag.G2
      (g2Datum (GaloisField p e))) :
    ∃ g : ↥(adjointGroup Tag.G2 (GaloisField p e)), conjSub g F₁ = F₁.map α.toMonoidHom := by
  classical
  set F := GaloisField p e with hF
  have hcard : Nat.card F = p ^ e := GaloisField.card p e (by omega)
  obtain ⟨hNF, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
    (p := p) (f := e) Fact.out hp2 he F hcard Tag.G2 (Or.inr ⟨rfl, hp3⟩)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  have key : ∀ δ : Fin Tag.G2.rank → ℤ, IsRoot Tag.G2 δ →
      ∀ x ∈ rootGroup (rootOperatorFamily Tag.G2) F δ,
        g⁻¹ * α x * g ∈ rootGroup (rootOperatorFamily Tag.G2) F δ := by
    intro δ hδ x hx
    rw [rootGroup_of_isRoot hδ, ← (rootOperatorFamily Tag.G2).subgroupOf_rootSubgroup_eq F ⟨δ, hδ⟩,
      Subgroup.mem_subgroupOf] at hx ⊢
    have h1 : Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.G2 F) ∈
        rootSubgroup Tag.G2 F δ := by
      have := Subgroup.mem_map_of_mem (Units.map (entrywiseHom σ.toRingHom)) hx
      rwa [map_entrywise_rootSubgroup σ δ] at this
    have h2 : ((g⁻¹ * α x * g : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.G2 F) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgσ x]
      group
    rw [h2]
    exact h1
  obtain ⟨g₀, γ, hγ, rfl⟩ := hF₁
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  set Q : Subgroup ↥(adjointGroup Tag.G2 F) :=
    rootGroup (rootOperatorFamily Tag.G2) F γ ⊔ rootGroup (rootOperatorFamily Tag.G2) F (-γ)
    with hQ
  have hγ' : IsRoot Tag.G2 (-γ) := IsRoot.neg hγroot
  set φ : ↥(adjointGroup Tag.G2 F) →* ↥(adjointGroup Tag.G2 F) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp α.toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective.comp α.injective
  have hφx : ∀ δ : Fin Tag.G2.rank → ℤ, IsRoot Tag.G2 δ →
      (rootGroup (rootOperatorFamily Tag.G2) F δ).map φ ≤
        rootGroup (rootOperatorFamily Tag.G2) F δ := by
    intro δ hδ
    rintro _ ⟨x, hx, rfl⟩
    have := key δ hδ x hx
    simpa [hφ, MulAut.conj_apply] using this
  have hφQ : Q.map φ ≤ Q := by
    rw [hQ, Subgroup.map_sup]
    exact sup_le_sup (hφx γ hγroot) (hφx (-γ) hγ')
  have hφQ' : Q.map φ = Q :=
    Subgroup.eq_of_le_of_card_ge hφQ (le_of_eq (Subgroup.card_map_of_injective hφinj).symm)
  have hαQ : Q.map α.toMonoidHom = conjSub g Q := by
    have h1 : Q.map α.toMonoidHom = (Q.map φ).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h1, hφQ']
    rfl
  refine ⟨α g₀ * g * g₀⁻¹, ?_⟩
  have e1 : (conjSub g₀ Q).map α.toMonoidHom =
      conjSub (α g₀) (Q.map α.toMonoidHom) := by
    exact map_conj_eq_conjSub_map α.toMonoidHom g₀ Q
  show conjSub (α g₀ * g * g₀⁻¹) (conjSub g₀ Q) = (conjSub g₀ Q).map α.toMonoidHom
  rw [e1, hαQ, ← conjSub_mul, ← conjSub_mul]
  congr 1
  group

theorem aut_swap_false_g2 (hp2 : p ≠ 2) (hp3 : p ≠ 3) (he : 1 ≤ e)
    (α : MulAut ↥(adjointGroup Tag.G2 (GaloisField p e)))
    {R₁ R₂ : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hR₁ : R₁ ∈ fundamentalSubgroups StatedLieTag.G2 (g2Datum (GaloisField p e)))
    {c : ↥(adjointGroup Tag.G2 (GaloisField p e))} (hc₁ : IsUniqueInvolution R₁ c)
    (hc₂ : IsUniqueInvolution R₂ c) (hα : R₁.map α.toMonoidHom = R₂) : R₂ = R₁ := by
  obtain ⟨g, hg⟩ := aut_map_fund_g2 hp2 hp3 he α hR₁
  rw [hα] at hg
  have hg' : IsUniqueInvolution (conjSub g R₁) c := hg ▸ hc₂
  have := noTwins_g2 (p := p) (e := e) hp2 he R₁ hR₁ c hc₁ g hg'
  rw [← hg]
  exact this

end Model

section Generic

theorem exists_aut_of_normalizes {M X : Type} [Group M] [Group X] [Finite X] (ψ : M →* X)
    (hψ : Function.Injective ψ) {s : X} (hs : conjSub s ψ.range = ψ.range) :
    ∃ α : MulAut M, ∀ m, ψ (α m) = s * ψ m * s⁻¹ := by
  have hmem : ∀ m, s * ψ m * s⁻¹ ∈ ψ.range := fun m => by
    have : s * ψ m * s⁻¹ ∈ conjSub s ψ.range := conj_mem_conjSub ⟨m, rfl⟩
    rwa [hs] at this
  choose f hf using hmem
  have hfmul : ∀ a b, f (a * b) = f a * f b := fun a b => by
    apply hψ
    rw [hf, map_mul, map_mul, hf, hf]
    group
  have hfone : f 1 = 1 := by
    apply hψ
    rw [hf, map_one]
    group
  let F : M →* M := { toFun := f, map_one' := hfone, map_mul' := hfmul }
  have hFinj : Function.Injective F := fun a b h => by
    apply hψ
    have h1 : ψ (f a) = ψ (f b) := congrArg ψ h
    rw [hf, hf] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have : Finite M := Finite.of_injective ψ hψ
  have hFsurj : Function.Surjective F := Finite.injective_iff_surjective.mp hFinj
  exact ⟨MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩, fun m => hf m⟩

theorem conjSub_eq_of_simple_normal {X : Type} [Group X] [Finite X] {Y C : Subgroup X}
    [IsSimpleGroup ↥C] (hCY : C ≤ Y) (hCn : ∀ g ∈ Y, ∀ x ∈ C, g * x * g⁻¹ ∈ C)
    {s : X} (hsY : ∀ y ∈ Y, s⁻¹ * y * s ∈ Y) {x : X} (hxC : x ∈ C) (hx1 : x ≠ 1)
    (hsx : s * x * s⁻¹ ∈ C) : conjSub s C = C := by
  set B : Subgroup X := conjSub s C ⊓ C with hB
  have hBc : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B := by
    intro c hc b hb
    refine Subgroup.mem_inf.mpr ⟨?_, C.mul_mem (C.mul_mem hc hb.2) (C.inv_mem hc)⟩
    rw [mem_conjSub_iff]
    have h1 : s⁻¹ * b * s ∈ C := mem_conjSub_iff.mp hb.1
    have h2 : s⁻¹ * c * s ∈ Y := hsY c (hCY hc)
    have e : s⁻¹ * (c * b * c⁻¹) * s = (s⁻¹ * c * s) * (s⁻¹ * b * s) * (s⁻¹ * c * s)⁻¹ := by
      group
    rw [e]
    exact hCn _ h2 _ h1
  have : (B.subgroupOf C).Normal := ⟨fun n hn g => by
    have : (g : X) * (n : X) * (g : X)⁻¹ ∈ B := hBc g g.2 n hn
    exact this⟩
  have hne : B.subgroupOf C ≠ ⊥ := by
    intro h
    have hy : s * x * s⁻¹ ∈ B := Subgroup.mem_inf.mpr ⟨by
      rw [mem_conjSub_iff]
      have : s⁻¹ * (s * x * s⁻¹) * s = x := by group
      rw [this]; exact hxC, hsx⟩
    have hy' : (⟨s * x * s⁻¹, hsx⟩ : ↥C) ∈ B.subgroupOf C := hy
    rw [h, Subgroup.mem_bot] at hy'
    apply hx1
    have h2 : s * x * s⁻¹ = 1 := congrArg Subtype.val hy'
    calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
      _ = 1 := by rw [h2]; group
  have htop : B.subgroupOf C = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf C) with h | h
    · exact absurd h hne
    · exact h
  have hCA : C ≤ conjSub s C := by
    intro c hc
    have : (⟨c, hc⟩ : ↥C) ∈ B.subgroupOf C := htop ▸ Subgroup.mem_top _
    exact this.1
  exact (Subgroup.eq_of_le_of_card_ge hCA (by rw [natCard_conjSub])).symm

end Generic

section Lie


theorem swap_false_aux {p e : ℕ} [Fact p.Prime] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n : ℕ} (ht : t = .G2)
    (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (α : MulAut (modelUniv t n p e Fact.out).K)
    {R₁ R₂ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {c : (modelUniv t n p e Fact.out).K} (hc₁ : IsUniqueInvolution R₁ c)
    (hc₂ : IsUniqueInvolution R₂ c) (hα : R₁.map α.toMonoidHom = R₂) : R₂ = R₁ := by
  subst ht
  have hn : n = 0 := hadm.2.2.1
  subst hn
  exact aut_swap_false_g2 hp2 hp3 hadm.2.1 α hR₁ hc₁ hc₂ hα

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

theorem false_of_twin_swap (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hΦ : HypOmegaMod p f Φ)
    (D : OmegaLie p f Φ) {i : Fin D.card} (hG2 : D.tag i = .G2)
    {R₁ R₂ : Subgroup (D.model i).K} (hR₁ : R₁ ∈ D.cls i) {c : X}
    (hc₁ : IsUniqueInvolution (R₁.map (D.hom i)) c)
    (hc₂ : IsUniqueInvolution (R₂.map (D.hom i)) c) {s : X}
    (hs : conjSub s (R₁.map (D.hom i)) = R₂.map (D.hom i)) : R₂ = R₁ := by
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inl hG2
  have hinj := hom_injective_of_g2d4 hp2 D hi
  set ψ := D.hom i with hψ
  have hsimple : IsSimpleGroup ↥(D.comp i) := by
    have := isSimpleGroup_model_of_g2d4 hp2 (D.admissible i) hi
    exact MulEquiv.isSimpleGroup (MonoidHom.ofInjective hinj).symm
  have hY : (omegaGen Φ).Normal := omegaGen_normal hΦ.conjInvariant
  have hcC : c ∈ D.comp i := by
    have := Subgroup.map_le_range ψ R₂ hc₂.mem
    exact this
  have hc1C : c ∈ D.comp i := by
    exact Subgroup.map_le_range ψ R₁ hc₁.mem
  have hscC : s * c * s⁻¹ ∈ D.comp i := by
    have h1 : s * c * s⁻¹ ∈ conjSub s (R₁.map ψ) := conj_mem_conjSub hc₁.mem
    rw [hs] at h1
    exact Subgroup.map_le_range ψ R₂ h1
  have hsC : conjSub s (D.comp i) = D.comp i :=
    conjSub_eq_of_simple_normal (Y := omegaGen Φ) (D.comp_le_omegaGen i)
      (fun g hg x hx => D.mem_comp_conj hg hx)
      (fun y hy => by
        have := hY.conj_mem y hy s⁻¹
        simpa using this) hc1C hc₁.ne_one hscC
  obtain ⟨α, hα⟩ := exists_aut_of_normalizes ψ hinj (s := s) hsC
  have hαR : R₁.map α.toMonoidHom = R₂ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_map]
    have : ψ.comp α.toMonoidHom = (MulAut.conj s).toMonoidHom.comp ψ := by
      ext m
      simp [hα, MulAut.conj_apply]
    rw [this, ← Subgroup.map_map]
    exact hs
  have hc₁' := isUniqueInvolution_of_map hinj hc₁
  have hc₂' := isUniqueInvolution_of_map hinj hc₂
  obtain ⟨c₁, hc₁e, hc₁u⟩ := hc₁'
  obtain ⟨c₂, hc₂e, hc₂u⟩ := hc₂'
  have hcc : c₂ = c₁ := hinj (hc₂e.trans hc₁e.symm)
  rw [hcc] at hc₂u
  exact swap_false_aux hG2 (D.admissible i) hp2 hp3 α hR₁.1 hc₁u hc₂u hαR

end Lie

end CFSG.ClassicalInvolution.Asc77.R10
