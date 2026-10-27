module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace L3U3

section Abstract

variable {S X H : Type*} [Group S] [Group X] [Group H]

theorem exists_normal_of_param (ρ : S →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center S) (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1)
    (φ : H →* S) (hrange : φ.range = centralizer ({a} : Set S)) (T : Subgroup H)
    (hT : T.Normal) {t₀ : H} (ht₀ : t₀ ∈ T) (ht₀a : φ t₀ = a)
    (hinj : ∀ t ∈ T, ρ (φ t) = 1 → t = 1) :
    ∃ Y : Subgroup X, Y ≤ centralizer ({ρ a} : Set X) ∧
      (Y.subgroupOf (centralizer ({ρ a} : Set X))).Normal ∧ Nonempty (↥Y ≃* ↥T) ∧
      ρ a ∈ Y := by
  set Ψ : ↥T →* X := (ρ.comp φ).comp T.subtype with hΨ
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    exact Subtype.ext (hinj t t.2 ht)
  have hmem : ∀ h : H, φ h * a = a * φ h := fun h =>
    mem_centralizer_singleton_iff.mp (hrange ▸ ⟨h, rfl⟩)
  refine ⟨Ψ.range, ?_, ?_, ⟨(MonoidHom.ofInjective hΨinj).symm⟩, ⟨⟨t₀, ht₀⟩, ?_⟩⟩
  · rintro _ ⟨t, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show ρ (φ t) * ρ a = ρ a * ρ (φ t)
    rw [← map_mul, ← map_mul, hmem]
  · constructor
    rintro ⟨n, hn⟩ hnY ⟨g, hg⟩
    rw [mem_subgroupOf] at hnY ⊢
    obtain ⟨t, rfl⟩ := hnY
    obtain ⟨s, rfl⟩ := hρ g
    have hs : s * a = a * s := GH74.GLS.IVK.Proofs2.Lemma41aL3.commute_of_map_commute ρ hker h3 ha
      (mem_centralizer_singleton_iff.mp hg)
    have hs' : s ∈ φ.range := by
      rw [hrange]
      exact mem_centralizer_singleton_iff.mpr hs
    obtain ⟨h, rfl⟩ := hs'
    refine ⟨⟨h * t * h⁻¹, hT.conj_mem t t.2 h⟩, ?_⟩
    simp [hΨ]
  · simp [hΨ, ht₀a]

end Abstract

theorem transport {G X : Type*} [Group G] [Group X] (E : Subgroup G) (ι : ↥E ≃* X) {x : G}
    (hx : x ∈ E) {Y : Subgroup X} (hYC : Y ≤ centralizer ({ι ⟨x, hx⟩} : Set X))
    (hYn : (Y.subgroupOf (centralizer ({ι ⟨x, hx⟩} : Set X))).Normal) (hxY : ι ⟨x, hx⟩ ∈ Y) :
    ∃ Y' : Subgroup G, Y' ≤ E ⊓ centralizer ({x} : Set G) ∧
      (Y'.subgroupOf (E ⊓ centralizer ({x} : Set G))).Normal ∧ Nonempty (↥Y' ≃* ↥Y) ∧
      x ∈ Y' := by
  set ψ : X →* G := E.subtype.comp ι.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp ι.symm.injective
  have hcomm : ∀ y : X, y * ι ⟨x, hx⟩ = ι ⟨x, hx⟩ * y → ψ y * x = x * ψ y := by
    intro y hy
    have h1 := congrArg ι.symm hy
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h1
    exact congrArg Subtype.val h1
  have hcomm' : ∀ g : ↥E, (g : G) * x = x * g → ι g * ι ⟨x, hx⟩ = ι ⟨x, hx⟩ * ι g := by
    intro g hg
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hg
  refine ⟨Y.map ψ, ?_, ?_, ⟨(Y.equivMapOfInjective ψ hψinj).symm⟩, ⟨_, hxY, by simp [hψ]⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact mem_inf.mpr ⟨(ι.symm y).2,
      mem_centralizer_singleton_iff.mpr (hcomm y (mem_centralizer_singleton_iff.mp (hYC hy)))⟩
  · constructor
    rintro ⟨n, hn⟩ hnY ⟨g, hgE, hgC⟩
    rw [mem_subgroupOf] at hnY ⊢
    obtain ⟨y, hy, rfl⟩ := hnY
    have hg'C : ι ⟨g, hgE⟩ ∈ centralizer ({ι ⟨x, hx⟩} : Set X) :=
      mem_centralizer_singleton_iff.mpr (hcomm' ⟨g, hgE⟩ (mem_centralizer_singleton_iff.mp hgC))
    have hconj := hYn.conj_mem ⟨y, hYC hy⟩ (by rw [mem_subgroupOf]; exact hy) ⟨_, hg'C⟩
    rw [mem_subgroupOf] at hconj
    refine ⟨_, hconj, ?_⟩
    simp [hψ]

section PSL

open Assembly.LowTwoRank RankThree.CentralCover GH74.GLS.IVK.Proofs2

variable {F : Type} [Field F]

theorem scalar_two_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
  intro c d h
  have := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    at this
  exact Units.ext this

theorem det_scalar_two (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = (c : F) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_fin_two]
  simp [sq]

theorem statedSL_two_normal : (StatedSL 2 F).Normal := by
  constructor
  intro n hn g
  rw [linConj_mem_statedSL] at hn ⊢
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, hn]

variable [Finite F]

theorem psl_case (hodd : Odd (Nat.card F)) {w : StatedProj (StatedSL 3 F)} (hw : orderOf w = 2) :
    ∃ Y : Subgroup (StatedProj (StatedSL 3 F)), Y ≤ centralizer ({w} : Set _) ∧
      (Y.subgroupOf (centralizer ({w} : Set (StatedProj (StatedSL 3 F))))).Normal ∧
      Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧ w ∈ Y := by
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  obtain ⟨φ, hφ, hrange⟩ := Lemma41aL3.exists_phi h2 (StatedSL 3 F)
    (fun A => linConj_mem_statedSL A) ha ha1
  have hmem : ∀ h : GL (Fin 2) F, φ h * a = a * φ h := fun h =>
    mem_centralizer_singleton_iff.mp (hrange ▸ ⟨h, rfl⟩)
  have hcent : ∀ h : GL (Fin 2) F, (∀ B : GL (Fin 2) F, φ B * φ h = φ h * φ B) →
      ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c = h := by
    intro h hh
    have hc : h ∈ center (GL (Fin 2) F) := by
      rw [mem_center_iff]
      intro B
      apply hφ
      rw [map_mul, map_mul, hh B]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    exact hc
  obtain ⟨h₀, hh₀⟩ : a ∈ φ.range := by
    rw [hrange]
    exact mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨c, hc⟩ := hcent h₀ (fun B => by rw [hh₀, hmem])
  have hh₀2 : h₀ * h₀ = 1 := hφ (by rw [map_mul, hh₀, ha, map_one])
  have hc2 : (c : F) ^ 2 = 1 := by
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) (c * c) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : Fˣ) := by
      rw [map_mul, hc, hh₀2, map_one]
    have h3 := congrArg Units.val (scalar_two_injective h1)
    rw [Units.val_mul, Units.val_one] at h3
    rw [sq]
    exact h3
  have hh₀T : h₀ ∈ StatedSL 2 F := by
    rw [linConj_mem_statedSL, ← hc, det_scalar_two, hc2]
  have hinj : ∀ t ∈ StatedSL 2 F, statedProjMk (StatedSL 3 F) (φ t) = 1 → t = 1 := by
    intro t ht htk
    have htk' : φ t ∈ (statedProjMk (StatedSL 3 F)).ker := htk
    have htc := mem_center_iff.mp (ker_statedProjMk_le_center _ htk')
    obtain ⟨d, hd⟩ := hcent t (fun B => htc (φ B))
    have hd2 : (d : F) ^ 2 = 1 := by
      rw [← det_scalar_two, hd]
      exact (linConj_mem_statedSL t).mp ht
    have ht3 : t ^ 3 = 1 := hφ (by rw [map_pow, linConj_ker_pow_three _ htk', map_one])
    have hd3 : (d : F) ^ 3 = 1 := by
      have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) (d ^ 3) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : Fˣ) := by
        rw [map_pow, hd, ht3, map_one]
      have h3 := congrArg Units.val (scalar_two_injective h1)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h3
      exact h3
    have hd1 : d = 1 := by
      have h1 : (d : F) ^ 3 = (d : F) ^ 2 * d := by ring
      rw [hd3, hd2, one_mul] at h1
      exact Units.ext h1.symm
    rw [← hd, hd1, map_one]
  obtain ⟨Y, hYC, hYn, ⟨hYT⟩, hwY⟩ := exists_normal_of_param (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (ker_statedProjMk_le_center _)
    (fun z hz => linConj_ker_pow_three z hz) ha φ hrange (StatedSL 2 F) statedSL_two_normal
    hh₀T hh₀ hinj
  exact ⟨Y, hYC, hYn, ⟨hYT.trans (specialLinearGroupEquivStatedSL 2 F).symm⟩, hwY⟩

end PSL

end L3U3

end CFSG.ComponentClassification.HarrisLit
