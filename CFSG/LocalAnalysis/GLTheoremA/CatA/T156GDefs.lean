module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType

@[expose] def FixGeomP (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) {R₀ : Type}
    [Group R₀] (I₀ : Set (MulAut R₀)) (θ₀ : ggFixDer x ≃* R₀) : Prop :=
  (∀ φ ∈ I, φ ^ p = 1 → ∀ hφ : φ * x = x * φ, ∃ φ₀ ∈ I₀, ∀ (g : R) (hg : g ∈ ggFixDer x),
      θ₀ ⟨φ g, ggFixDer_map_mem hφ hg⟩ = φ₀ (θ₀ ⟨g, hg⟩)) ∧
    ∀ φ ∈ I, φ ^ p = 1 → φ * x = x * φ → (∀ g ∈ ggFixDer x, φ g = g) → φ = 1

@[expose] def FixAlt (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) : Prop :=
  (∃ lab₀ : LargeEvenLabel, LargeEvenInLambda2 lab₀ ∧
      CFSG.Assembly.LargeEvenRawDatum lab₀ fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧
        (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer x ≃* R₀, FixGeomP p I x I₀ θ₀) ∨
    ∀ E : Subgroup (MulAut R), IsElemAbelian p E → (∀ φ ∈ E, φ ∈ I ∧ φ * x = x * φ) →
      Nat.card E ≤ p

@[expose] def GeomBody (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (¬ (lab.tag = .triD4 ∧ p = 3) → ∀ f ∈ F, orderOf f = p →
        FixAlt p I f ∨ (p = 3 ∧ catalogIs R S9.isU3eight)) ∧
      (lab.tag = .triD4 → p = 3 → ∀ x : MulAut R, x ^ 3 = 1 →
        x ∉ (MulAut.conj : R →* MulAut R).range →
          S10.twoPart (FP.fixNum x) = Nat.sqrt (S10.twoPart (Nat.card R)) → FixAlt 3 I x)

@[expose] def T156Geom : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    MI.CAll lab (GeomBody p lab)

@[expose] def RestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .A ∧ lab.rank = 1) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨
    (lab.tag = .D ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twD ∧ lab.rank ≤ 3) ∨
    lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    (lab.tag = .E6 ∧ (p = 3 ∨ ¬ p ∣ 2 ^ lab.n - 1)) ∨ lab.tag = .twE6

@[expose] def T156Rest : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → RestLabel p lab →
    MI.CAll lab (GeomBody p lab)

theorem fixGeomP_of_ggFixGeom {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {x : MulAut R}
    {R₀ : Type} [Group R₀] {I₀ : Set (MulAut R₀)} {θ₀ : ggFixDer x ≃* R₀}
    (h : GGFixGeom I x I₀ θ₀) : FixGeomP p I x I₀ θ₀ :=
  ⟨fun φ hφ _ hc => h.1 φ hφ hc, fun φ hφ _ hc htriv => h.2 φ hφ hc htriv⟩

theorem mem_ggFixDer_conj {R : Type} [Group R] (x u : MulAut R) (g : R) :
    g ∈ ggFixDer (u * x * u⁻¹) ↔ u⁻¹ g ∈ ggFixDer x := by
  have hsub : ggFixSub (u * x * u⁻¹) = (ggFixSub x).map (u : R →* R) := by
    ext y
    rw [mem_ggFixSub, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨u⁻¹ y, ?_, by simp⟩
      rw [mem_ggFixSub]
      have h1 : (u * x * u⁻¹) y = y := hy
      have h2 : u (x (u⁻¹ y)) = y := by simpa [MulAut.mul_apply] using h1
      calc x (u⁻¹ y) = u⁻¹ (u (x (u⁻¹ y))) := by simp
        _ = u⁻¹ y := by rw [h2]
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ggFixSub] at hz
      change (u * x * u⁻¹) (u z) = u z
      simp [MulAut.mul_apply, hz]
  have hder : ggFixDer (u * x * u⁻¹) = (ggFixDer x).map (u : R →* R) := by
    unfold ggFixDer
    rw [hsub, Subgroup.map_commutator]
  rw [hder, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨u⁻¹ g, h, by simp⟩

theorem fixGeomP_conj {p : ℕ} {R : Type} [Group R] {J : Subgroup (MulAut R)} {x u : MulAut R}
    (hu : u ∈ J) {R₀ : Type} [Group R₀] {I₀ : Set (MulAut R₀)} {θ₀ : ggFixDer x ≃* R₀}
    (h : FixGeomP p (J : Set (MulAut R)) x I₀ θ₀) :
    ∃ θ : ggFixDer (u * x * u⁻¹) ≃* R₀, FixGeomP p (J : Set (MulAut R)) (u * x * u⁻¹) I₀ θ := by
  let e : ggFixDer (u * x * u⁻¹) ≃* ggFixDer x :=
    { toFun := fun g => ⟨u⁻¹ (g : R), (mem_ggFixDer_conj x u (g : R)).1 g.2⟩
      invFun := fun k => ⟨u (k : R), by
        rw [mem_ggFixDer_conj]
        simpa using k.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp)
      map_mul' := fun g k => Subtype.ext (by simp) }
  have he : ∀ g : ggFixDer (u * x * u⁻¹), ((e g : ggFixDer x) : R) = u⁻¹ (g : R) := fun _ => rfl
  have hconj : ∀ φ : MulAut R, φ * (u * x * u⁻¹) = (u * x * u⁻¹) * φ →
      (u⁻¹ * φ * u) * x = x * (u⁻¹ * φ * u) := by
    intro φ hφ
    calc u⁻¹ * φ * u * x = u⁻¹ * (φ * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * x * u⁻¹) * φ) * u := by rw [hφ]
      _ = x * (u⁻¹ * φ * u) := by group
  have hpow : ∀ φ : MulAut R, φ ^ p = 1 → (u⁻¹ * φ * u) ^ p = 1 := by
    intro φ hφ
    have : (u⁻¹ * φ * u) ^ p = u⁻¹ * φ ^ p * u := by
      rw [show u⁻¹ * φ * u = (MulAut.conj u⁻¹) φ by simp [MulAut.conj_apply], ← map_pow,
        MulAut.conj_apply, inv_inv]
    rw [this, hφ]
    group
  refine ⟨e.trans θ₀, ?_, ?_⟩
  · intro φ hφJ hφp hφ
    obtain ⟨φ₀, hφ₀I₀, hφ₀⟩ := h.1 (u⁻¹ * φ * u) (J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu)
      (hpow φ hφp) (hconj φ hφ)
    refine ⟨φ₀, hφ₀I₀, fun g hg => ?_⟩
    have hmem : u⁻¹ g ∈ ggFixDer x := (mem_ggFixDer_conj x u g).1 hg
    calc (e.trans θ₀) ⟨φ g, ggFixDer_map_mem hφ hg⟩
        = θ₀ ⟨(u⁻¹ * φ * u) (u⁻¹ g), ggFixDer_map_mem (hconj φ hφ) hmem⟩ := by
          rw [MulEquiv.trans_apply]
          congr 1
          apply Subtype.ext
          rw [he]
          simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = φ₀ (θ₀ ⟨u⁻¹ g, hmem⟩) := hφ₀ (u⁻¹ g) hmem
      _ = φ₀ ((e.trans θ₀) ⟨g, hg⟩) := by
          rw [MulEquiv.trans_apply]
          have hsub : (⟨u⁻¹ g, hmem⟩ : ggFixDer x) = e ⟨g, hg⟩ := Subtype.ext (by rw [he])
          rw [hsub]
  · intro φ hφJ hφp hφ hfix
    have hfix' : ∀ g ∈ ggFixDer x, (u⁻¹ * φ * u) g = g := by
      intro g hg
      have hgx : u g ∈ ggFixDer (u * x * u⁻¹) := by
        rw [mem_ggFixDer_conj]
        simpa using hg
      have h1 : φ (u g) = u g := hfix (u g) hgx
      calc (u⁻¹ * φ * u) g = u⁻¹ (φ (u g)) := by simp [MulAut.mul_apply]
        _ = u⁻¹ (u g) := by rw [h1]
        _ = g := by simp
    have h1 : u⁻¹ * φ * u = 1 := h.2 (u⁻¹ * φ * u)
      (J.mul_mem (J.mul_mem (J.inv_mem hu) hφJ) hu) (hpow φ hφp) (hconj φ hφ) hfix'
    calc φ = u * (u⁻¹ * φ * u) * u⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem fixAlt_conj {p : ℕ} {R : Type} [Group R] {J : Subgroup (MulAut R)} {x u : MulAut R}
    (hu : u ∈ J) (h : FixAlt p (J : Set (MulAut R)) x) :
    FixAlt p (J : Set (MulAut R)) (u * x * u⁻¹) := by
  rcases h with ⟨lab₀, hlab₀, hraw⟩ | hcyc
  · refine Or.inl ⟨lab₀, hlab₀, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R₀ _ I₀ F₀ ⟨hs, hna, θ₀, hθ₀⟩
    obtain ⟨θ, hθ⟩ := fixGeomP_conj hu hθ₀
    exact ⟨hs, hna, θ, hθ⟩
  · refine Or.inr fun E hE hEx => ?_
    let E' : Subgroup (MulAut R) := E.map (MulAut.conj u⁻¹).toMonoidHom
    have hE' : IsElemAbelian p E' := CFSG.Open.IsElemAbelian.map hE _
    have hE'x : ∀ φ ∈ E', φ ∈ (J : Set (MulAut R)) ∧ φ * x = x * φ := by
      intro φ hφ
      obtain ⟨φ', hφ', rfl⟩ := Subgroup.mem_map.1 hφ
      obtain ⟨hφ'J, hφ'x⟩ := hEx φ' hφ'
      have hφe : (MulAut.conj u⁻¹).toMonoidHom φ' = u⁻¹ * φ' * u := by
        simp [MulAut.conj_apply]
      rw [hφe]
      refine ⟨J.mul_mem (J.mul_mem (J.inv_mem hu) hφ'J) hu, ?_⟩
      calc u⁻¹ * φ' * u * x = u⁻¹ * (φ' * (u * x * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * x * u⁻¹) * φ') * u := by rw [hφ'x]
        _ = x * (u⁻¹ * φ' * u) := by group
    have h1 := hcyc E' hE' hE'x
    have h2 : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective
    rwa [h2] at h1

end CFSG.LocalAnalysis.GLTheoremA.T156

end
