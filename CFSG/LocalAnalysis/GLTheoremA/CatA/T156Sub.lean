module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Quot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Sub

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_ker_subtype {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    ¬ p ∣ Nat.card (H.subtype : ↥H →* G).ker := by
  rw [Subgroup.ker_subtype, Subgroup.card_bot]
  exact hp.not_dvd_one

noncomputable def pquotIsoOf {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) : PQuot p Y ≃* PQuot p X := by
  subst h
  exact pquotMap hp H.subtype (not_dvd_card_ker_subtype hp H) Y

theorem indRel_pquotIsoOf {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) {gH : ↥H} (hg : gH ∈ Subgroup.normalizer (Y : Set ↥H))
    (q q' : PQuot p Y) :
    indRel p X (gH : G) (pquotIsoOf hp h q) (pquotIsoOf hp h q') ↔ indRel p Y gH q q' := by
  subst h
  exact indRel_pquotMap hp H.subtype (not_dvd_card_ker_subtype hp H) hg q q'

theorem inducesInnerMod_map {A Ω : Type} [Group A] [Group Ω] [Finite A] [Finite Ω] {p : ℕ} (hp : p.Prime)
    (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) {Y : Subgroup A} {g : A} (h : InducesInnerMod p Y g) :
    InducesInnerMod p (Y.map π) (π g) := by
  obtain ⟨l, hl, hall⟩ := h
  refine ⟨π l, Subgroup.mem_map_of_mem π hl, ?_⟩
  intro t ht
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ht
  have hz := hall y hy
  have hπz : π ((l⁻¹ * y * l)⁻¹ * (g⁻¹ * y * g)) ∈ GLAPPrimeCoreOf p (Y.map π) := by
    rw [← map_glaPPrimeCoreOf hp π hN Y]
    exact Subgroup.mem_map_of_mem π hz
  have e : π ((l⁻¹ * y * l)⁻¹ * (g⁻¹ * y * g)) =
      ((π l)⁻¹ * π y * π l)⁻¹ * ((π g)⁻¹ * π y * π g) := by
    simp only [map_mul, map_inv]
  rw [← e]
  exact hπz

theorem glaInduces_centerQuot {X Y R : Type} [Group X] [Group Y] [Group R] (e : X ≃* Y)
    (rel : X → X → Prop) (rel' : Y → Y → Prop) (hrel : ∀ x x', rel x x' ↔ rel' (e x) (e x'))
    (θ : Y ⧸ Subgroup.center Y ≃* R) (φ : MulAut R) :
    CFSG.Assembly.LargeEvenInduces ((CFSG.StandardType.centerQuotCongr e).trans θ) rel φ ↔
      CFSG.Assembly.LargeEvenInduces θ rel' φ := by
  unfold CFSG.Assembly.LargeEvenInduces
  simp only [MulEquiv.trans_apply, CFSG.StandardType.centerQuotCongr_mk]
  constructor
  · intro h y y' hyy'
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective y'
    exact h x x' ((hrel x x').2 hyy')
  · intro h x x' hxx'
    exact h (e x) (e x') ((hrel x x').1 hxx')

theorem glaPrimeField_marking_transfer {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ)
    (rel : X → X → Prop) (rel' : Y → Y → Prop) (hrel : ∀ x x', rel x x' ↔ rel' (e x) (e x')) :
    CFSG.Assembly.LargeEvenMarking X (fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ rel)) ↔
      CFSG.Assembly.LargeEvenMarking Y (fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ rel')) := by
  constructor
  · intro h
    refine Y10F.glaMarking_congr e.symm ?_ h
    intro lab R _ I F θ hθ
    have hrel2 : ∀ y y', rel' y y' ↔ rel (e.symm y) (e.symm y') := fun y y' => by
      have := hrel (e.symm y) (e.symm y')
      simp only [MulEquiv.apply_symm_apply] at this
      exact this.symm
    obtain ⟨h1, f, hf, u, hu, hord, hφ⟩ := hθ
    exact ⟨h1, f, hf, u, hu, hord, (glaInduces_centerQuot e.symm rel' rel hrel2 θ _).2 hφ⟩
  · intro h
    refine Y10F.glaMarking_congr e ?_ h
    intro lab R _ I F θ hθ
    obtain ⟨h1, f, hf, u, hu, hord, hφ⟩ := hθ
    exact ⟨h1, f, hf, u, hu, hord, (glaInduces_centerQuot e rel rel' hrel θ _).2 hφ⟩

end Sub

end CFSG.LocalAnalysis.GLTheoremA.T156

end
