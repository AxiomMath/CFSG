module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcRoot
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcJ

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

section Def

variable {C : Type*} [Group C]

@[expose] def ResCent (x : C) (Z : Subgroup C) : Prop :=
  ∀ y ∈ cent x, y * y = 1 → (∀ d ∈ CFSG.Quasithin.perfectCore (cent x), y * d = d * y) → y ∈ Z

theorem centre_inv_of_resCent {x : C} {Z : Subgroup C} (h : ResCent x Z) :
    ∀ w ∈ cent x, (∀ c ∈ cent x, w * c = c * w) → w * w = 1 → w ∈ Z :=
  fun w hw hwc hw2 => h w hw hw2 fun d hd => hwc d (CFSG.Quasithin.perfectCore_le _ hd)

end Def

theorem perfectCore_subgroupOf {G : Type*} [Group G] [Finite G] {A H : Subgroup G}
    (hHA : H ≤ A) :
    (CFSG.Quasithin.perfectCore H).subgroupOf A = CFSG.Quasithin.perfectCore (H.subgroupOf A) := by
  apply Subgroup.map_injective A.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, CFSG.Quasithin.map_perfectCore,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hHA,
    inf_of_le_left ((CFSG.Quasithin.perfectCore_le H).trans hHA)]

section Sec3

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  [Finite C] {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

theorem img_perfectCore_centralizer_eq (hZA : Odd (Nat.card (center A))) {t : G}
    (htA : t ∈ A) (ht2 : t ^ 2 = 1) {x : C} (hx : ψ ⟨t, le_normalizer htA⟩ = MulAut.conj x) :
    img ψ (CFSG.Quasithin.perfectCore (A ⊓ centralizer ({t} : Set G))) =
      CFSG.Quasithin.perfectCore (cent x) := by
  have hMA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  rw [img_eq_map hZC hψ ((CFSG.Quasithin.perfectCore_le _).trans hMA), perfectCore_subgroupOf hMA,
    CFSG.Quasithin.map_perfectCore, ← img_eq_map hZC hψ hMA,
    img_centralizer_eq hZC hψ hZA (le_normalizer htA) ht2 hx]

theorem actsIn_of_resCent (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {t : G} (ht : t ∈ T) (htA : t ∈ A) (ht1 : t ≠ 1) {x : C}
    (hx : ψ ⟨t, le_normalizer htA⟩ = MulAut.conj x) {Z : Subgroup C} (hres : ResCent x Z) :
    ActsIn ψ T Z := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hTel := hc.elemT h32
  have ht2 : t ^ 2 = 1 := hTel.2 t ht
  set M := A ⊓ centralizer ({t} : Set G) with hM
  have hPX : CFSG.Quasithin.perfectCore M ≤ oUpperTwo M ⊔ ⁅M, M⁆ :=
    (CFSG.Quasithin.perfectCore_le_derivedSeriesOf M 1).trans le_sup_right
  have hPres := RankTwoClassical.le_admResidual_of_perfect hPX
    (CFSG.Quasithin.perfectCore_perfect M)
  have h39 := Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT ht ht1 hOut
  have hPT : CFSG.Quasithin.perfectCore M ≤ centralizer (T : Set G) :=
    hPres.trans (h39.1.trans h39.2)
  have hcore := img_perfectCore_centralizer_eq hZC hψ hZA htA ht2 hx
  rw [actsIn_iff]
  intro s hs hsN y hy
  refine hres y ?_ (involution_of_conj hZC hψ hc h32 hs hsN hy).1 fun d hd => ?_
  ·
    rw [mem_centralizer_singleton_iff]
    have h1 : s * t = t * s := congrArg Subtype.val (hTel.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    have h2 : ψ ⟨s, hsN⟩ * ψ ⟨t, le_normalizer htA⟩ = ψ ⟨t, le_normalizer htA⟩ * ψ ⟨s, hsN⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h1)
    rw [hy, hx, ← map_mul, ← map_mul] at h2
    exact hinj h2
  ·
    rw [← hcore] at hd
    obtain ⟨a, ha, haN, had⟩ := mem_img.1 hd
    have h1 : s * a = a * s := mem_centralizer_iff.1 (hPT ha) s hs
    have h2 : ψ ⟨s, hsN⟩ * ψ ⟨a, haN⟩ = ψ ⟨a, haN⟩ * ψ ⟨s, hsN⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h1)
    rw [hy, had, ← map_mul, ← map_mul] at h2
    exact hinj h2

theorem card_le_of_resCent (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {t : G} (ht : t ∈ T) (htA : t ∈ A) (ht1 : t ≠ 1) {x : C}
    (hx : ψ ⟨t, le_normalizer htA⟩ = MulAut.conj x) {Z : Subgroup C} (hres : ResCent x Z) :
    Nat.card T ≤ Nat.card Z :=
  card_le_of_actsIn hZC hψ h4 h32 h34 hc
    (actsIn_of_resCent hZC hψ h4 h32 h34 hc hOut hZA ht htA ht1 hx hres)

omit [Finite C] in
theorem exists_pinned_of_inf_ne_bot (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) {reps : List C} (hcover : ClassesCover reps) (hTA : T ⊓ A ≠ ⊥) :
    ∃ y ∈ reps, ∃ a ∈ A, ∃ t ∈ T, t ∈ A ∧ t ≠ 1 ∧ Sec3 A R (rightConjugate T a⁻¹) (g * a⁻¹) ∧
      a * t * a⁻¹ ∈ rightConjugate T a⁻¹ ∧ a * t * a⁻¹ ∈ A ∧
      ∃ hN : a * t * a⁻¹ ∈ normalizer (A : Set G), ψ ⟨a * t * a⁻¹, hN⟩ = MulAut.conj y := by
  obtain ⟨⟨t, htTA⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hTA
  obtain ⟨htT, htA⟩ := mem_inf.1 htTA
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htN := le_normalizer htA
  obtain ⟨x, hx⟩ := exists_conj_of_mem hψ hc h32 h4 h34 htT htN
  obtain ⟨hx2, hx1⟩ := involution_of_conj hZC hψ hc h32 htT htN hx
  obtain ⟨y, hy, hyx⟩ := hcover x hx2 (hx1 ht1')
  obtain ⟨a, ha, hc', hmem, hN, hψa⟩ := exists_pin hψ hc htT htN hx hyx
  exact ⟨y, hy, a, ha, t, htT, htA, ht1', hc', hmem,
    mul_mem (mul_mem ha htA) (inv_mem ha), hN, hψa⟩

theorem inf_eq_bot_of_resCent_card (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ y ∈ reps, ResidualMem y ∨ ∃ Z : Subgroup C, ResCent y Z ∧ Nat.card Z < 4) :
    T ⊓ A = ⊥ := by
  by_contra hTA
  obtain ⟨y, hy, a, ha, t, -, -, ht1, hc', hmem, haA, _hN, hψa⟩ :=
    exists_pinned_of_inf_ne_bot hZC hψ h4 h32 h34 hc hcover hTA
  have hat1 : a * t * a⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  rcases hres y hy with hR | ⟨Z, hZ, hZ4⟩
  · exact hat1 (eq_one_of_residualMem hZC hψ h4 h32 h34 hc' hOut hZA hmem haA hψa hR)
  · have h1 := card_le_of_resCent hZC hψ h4 h32 h34 hc' hOut hZA hmem haA hat1 hψa hZ
    have h2 : 4 ≤ Nat.card (rightConjugate T a⁻¹) := by
      rw [hc'.card_eq]
      exact hc'.four_le
    omega

theorem actsIn_zx_of_resCent_reps (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ y ∈ reps, ResidualMem y ∨ ResCent y (zx y)) (hchar : ∀ y ∈ reps, CharTwo y)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) (ht₀N : t₀ ∈ normalizer (A : Set G)) {x₀ : C}
    (hx₀ : ψ ⟨t₀, ht₀N⟩ = MulAut.conj x₀) : ActsIn ψ T (zx x₀) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  by_cases hTA : T ⊓ A = ⊥
  · refine actsIn_zx hZC hψ h4 h32 h34 hc hZA hTA (fun t ht ht1 htN x hx => ?_) ht₀ ht₀1 ht₀N hx₀
    obtain ⟨hx2, hx1⟩ := involution_of_conj hZC hψ hc h32 ht htN hx
    exact charTwo_of_reps hcover hchar hx2 (hx1 ht1)
  obtain ⟨y, hy, a, ha, t, -, -, ht1, hc', hmem, haA, _hN, hψa⟩ :=
    exists_pinned_of_inf_ne_bot hZC hψ h4 h32 h34 hc hcover hTA
  have hat1 : a * t * a⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  rcases hres y hy with hR | hRC
  · exact absurd (eq_one_of_residualMem hZC hψ h4 h32 h34 hc' hOut hZA hmem haA hψa hR) hat1
  have hact := actsIn_of_resCent hZC hψ h4 h32 h34 hc' hOut hZA hmem haA hat1 hψa hRC
  obtain ⟨Z, u, hcd, hreg⟩ := hJ y hy
  have hzy : zx y = Z := zx_eq_of_centreData hcd
  set c := toC hZC hψ ⟨a, ha⟩ with hcdef
  have hca : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj c := (conj_toC hZC hψ ⟨a, ha⟩).symm
  have hconj : ∀ s ∈ T, ∀ (hsN : s ∈ normalizer (A : Set G)) (w : C),
      ψ ⟨s, hsN⟩ = MulAut.conj w → c * w * c⁻¹ ∈ Z := by
    intro s hs hsN w hw
    have hsN' : a * s * a⁻¹ ∈ normalizer (A : Set G) :=
      mul_mem (mul_mem (le_normalizer ha) hsN) (inv_mem (le_normalizer ha))
    have hmem' : a * s * a⁻¹ ∈ rightConjugate T a⁻¹ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hs
    have e : (⟨a * s * a⁻¹, hsN'⟩ : normalizer (A : Set G)) =
        ⟨a, le_normalizer ha⟩ * ⟨s, hsN⟩ * ⟨a, le_normalizer ha⟩⁻¹ := rfl
    have hψs : ψ ⟨a * s * a⁻¹, hsN'⟩ = MulAut.conj (c * w * c⁻¹) := by
      rw [e, map_mul, map_mul, map_inv, hca, hw, ← map_inv, ← map_mul, ← map_mul]
    rw [← hzy]
    exact (actsIn_iff.1 hact) _ hmem' hsN' _ hψs
  have hx₀Z : c * x₀ * c⁻¹ ∈ Z := hconj t₀ ht₀ ht₀N x₀ hx₀
  have hx₀1 : c * x₀ * c⁻¹ ≠ 1 := by
    intro h
    have hx₀1' := (involution_of_conj hZC hψ hc h32 ht₀ ht₀N hx₀).2 ht₀1
    apply hx₀1'
    calc x₀ = c⁻¹ * (c * x₀ * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hzx : zx (c * x₀ * c⁻¹) = Z := zx_eq_of_mem hcd hreg hx₀Z hx₀1
  rw [zx_conj] at hzx
  rw [actsIn_iff]
  intro s hs hsN w hw
  have h1 := hconj s hs hsN w hw
  rw [← hzx] at h1
  obtain ⟨w', hw', hw'e⟩ := h1
  have : w' = w := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hw'e
    have h2 : c * w' * c⁻¹ = c * w * c⁻¹ := hw'e
    simpa using h2
  rw [← this]
  exact hw'

end Sec3

end CFSG.ComponentClassification.RankTwoExceptional.Exc
