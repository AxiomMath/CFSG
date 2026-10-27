module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem commutatorElement_mul_center {H : Type*} [Group H] {z w : H} (hz : z ∈ Subgroup.center H)
    (hw : w ∈ Subgroup.center H) (a b : H) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hw' : ∀ g, w * g = g * w := fun g => (Subgroup.mem_center_iff.mp hw g).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
      = z * (a * w * b * a⁻¹) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = a * w * b * a⁻¹ * (b⁻¹ * w⁻¹) := by rw [hz']; group
    _ = a * (w * (b * a⁻¹ * b⁻¹)) * w⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hw']; group

theorem mulAut_eq_one_of_mul_inv_mem_center {H : Type*} [Group H] (hH : commutator H = ⊤)
    (γ : MulAut H) (h : ∀ g, γ g * g⁻¹ ∈ Subgroup.center H) : γ = 1 := by
  let F : Subgroup H :=
    { carrier := {g | γ g = g}
      mul_mem' := fun {a b} ha hb => by
        change γ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one γ
      inv_mem' := fun {a} ha => by
        change γ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hle : commutator H ≤ F := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change γ ⁅a, b⁆ = ⁅a, b⁆
    have hγa : γ a = (γ a * a⁻¹) * a := by group
    have hγb : γ b = (γ b * b⁻¹) * b := by group
    rw [map_commutatorElement, hγa, hγb]
    exact commutatorElement_mul_center (h a) (h b) a b
  ext g
  have hg : g ∈ F := hle (hH ▸ Subgroup.mem_top g)
  exact hg

variable {K : Type} [Field K]

theorem card_coordImage {n : ℕ} (σ : K ≃+* K) (U : Submodule K (Fin n → K)) :
    Nat.card (LinearFlag.coordImage σ U) = Nat.card U := by
  refine Nat.card_congr
    { toFun := fun v => ⟨fun i => σ.symm ((v : Fin n → K) i), LinearFlag.mem_coordImage.mp v.2⟩
      invFun := fun u => ⟨fun i => σ ((u : Fin n → K) i), LinearFlag.coord_mem_coordImage u.2⟩
      left_inv := fun v => Subtype.ext (funext fun i => by simp)
      right_inv := fun u => Subtype.ext (funext fun i => by simp) }

theorem card_submodule_eq_pow [Finite K] {n : ℕ} (U : Submodule K (Fin n → K)) :
    Nat.card U = Nat.card K ^ finrank K U := by
  classical
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_fintype (Module.finBasis K U), Fintype.card_fin]

theorem card_map_mulVecLin {n : ℕ} (A : GL (Fin n) K) (U : Submodule K (Fin n → K)) :
    Nat.card (U.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) = Nat.card U := by
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) := by
    intro x y hxy
    have h := congrArg (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hxy
    simp only [mulVecLin_apply, mulVec_mulVec] at h
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec] at h
  calc Nat.card (U.map (mulVecLin (A : Matrix (Fin n) (Fin n) K)))
      = Nat.card ((mulVecLin (A : Matrix (Fin n) (Fin n) K)) '' (U : Set (Fin n → K))) := rfl
    _ = Nat.card (U : Set (Fin n → K)) := Nat.card_image_of_injective hinj _
    _ = Nat.card U := rfl

theorem exists_conj_of_slThree [Finite K] (hK : Nat.card K = 4) {i : ℕ} (hi : i = 1 ∨ i = 2)
    (α : MulAut (SpecialLinearGroup (Fin 3) K)) (hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hαZ : ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), α z = z)
    (hαQ : (LinearFlag.flagStabilizer 3 K {i}).map α.toMonoidHom =
      LinearFlag.flagStabilizer 3 K {i}) :
    ∃ g : SpecialLinearGroup (Fin 3) K, ∀ x, α x = g * x * g⁻¹ := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hu3 : ∀ u : Kˣ, u ^ 3 = 1 := fun u => by
    have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    rw [← h3]
    exact pow_card_eq_one'
  set β := LinearFlag.descendAut 3 K α with hβ
  obtain ⟨A, σ, ε, hε, hβeq⟩ :=
    (LinearFlag.automorphism_generation (n := 3) (K := K) (by norm_num)).2 β
  obtain ⟨-, -, -, hδδ, -, -, h7, h8, h9, -⟩ :=
    LinearFlag.standard_automorphism_transport (K := K) (n := 3)
  set W := LinearFlag.flagSpace 3 K i with hW
  have hWr : finrank K W = i := LinearFlag.finrank_flagSpace (by omega)
  have hβW : (LinearFlag.projStabilizer W).map (β : _ →* _) = LinearFlag.projStabilizer W := by
    rw [hβ, LinearFlag.map_projStabilizer_descendAut, ← LinearFlag.flagStabilizer_singleton]
    change ((LinearFlag.flagStabilizer 3 K {i}).map α.toMonoidHom).map (LinearFlag.proj 3 K) = _
    rw [hαQ, LinearFlag.flagStabilizer_singleton]
    rfl
  have hcardK : ∀ U : Submodule K (Fin 3 → K), Nat.card U = 4 ^ finrank K U := fun U => by
    rw [card_submodule_eq_pow, hK]
  have hproper : ∀ U : Submodule K (Fin 3 → K), (finrank K U = 1 ∨ finrank K U = 2) →
      ⊥ < U ∧ U < ⊤ := by
    intro U hU
    refine ⟨bot_lt_iff_ne_bot.mpr fun h => ?_, lt_top_iff_ne_top.mpr fun h => ?_⟩
    · have := hcardK U
      rw [h, finrank_bot] at this
      simp at this
      rcases hU with hU | hU <;> rw [h, finrank_bot] at hU <;> omega
    · have h3 : finrank K U = 3 := by
        rw [h, finrank_top, Module.finrank_fin_fun]
      omega
  have hε0 : ε = 0 := by
    by_contra hne
    obtain rfl : ε = 1 := by omega
    rw [hβeq, pow_one] at hβW
    have hmap : (LinearFlag.projStabilizer W).map ((LinearFlag.conjAut 3 K A *
        LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K : MulAut _) : _ →* _) =
        LinearFlag.projStabilizer ((LinearFlag.coordImage σ (LinearFlag.dotOrth W)).map
          (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) := by
      rw [← h7 A _, ← h8 σ _, ← h9 W, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [hmap] at hβW
    set W' := (LinearFlag.coordImage σ (LinearFlag.dotOrth W)).map
      (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) with hW'
    have hW'card : Nat.card W' = 4 ^ (3 - i) := by
      rw [hW', card_map_mulVecLin, card_coordImage, hcardK, LinearFlag.finrank_dotOrth, hWr]
    have hW'r : finrank K W' = 3 - i := by
      have h1 := hcardK W'
      rw [hW'card] at h1
      have h2 : 3 - i = finrank K W' := Nat.pow_right_injective (by norm_num : 2 ≤ 4) h1
      omega
    obtain ⟨-, hinj, -⟩ := LinearFlag.maximal_parabolics (K := K) p (by norm_num : 1 ≤ 3)
    have hWW : W' = W := hinj (hproper W' (by omega)) (hproper W (by omega)) hβW
    have : finrank K W' = finrank K W := by rw [hWW]
    omega
  subst hε0
  rw [pow_zero, mul_one] at hβeq
  set α₀ : MulAut (SpecialLinearGroup (Fin 3) K) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ with hα₀
  have hdesc : LinearFlag.descendAut 3 K α₀ = β := by
    rw [hβeq, hα₀, map_mul]
    rfl
  have hperf : commutator (SpecialLinearGroup (Fin 3) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 3) (by norm_num)
      (Or.inl le_rfl)).commutator_eq_top
  have hαα₀ : α = α₀ := by
    have h1 : α₀⁻¹ * α = 1 := by
      refine mulAut_eq_one_of_mul_inv_mem_center hperf _ fun g => ?_
      rw [← LinearFlag.scalars_eq_center, ← LinearFlag.ker_proj, MonoidHom.mem_ker, map_mul,
        map_inv, ← LinearFlag.descendAut_proj, map_mul, map_inv, hdesc, hβ]
      change (β⁻¹ * β) (LinearFlag.proj 3 K g) * _ = 1
      rw [inv_mul_cancel, MulAut.one_apply, mul_inv_cancel]
    calc α = α₀ * (α₀⁻¹ * α) := by group
      _ = α₀ := by rw [h1, mul_one]
  have hsc : ∀ c : Kˣ, σ (c : K) = c := by
    intro c
    have hdet : ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Units.val_pow_eq_pow_val,
        hu3, Units.val_one]
    set z : SpecialLinearGroup (Fin 3) K := ⟨_, hdet⟩ with hz
    have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      change (g : Matrix (Fin 3) (Fin 3) K) * ((c : K) • 1) = ((c : K) • 1) * (g : Matrix _ _ K)
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have h1 := hαZ z hzc
    rw [hαα₀] at h1
    have h2 := congrArg (fun w : SpecialLinearGroup (Fin 3) K =>
      (w : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [hα₀, MulAut.mul_apply] at h2
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix] at h2
    change (A.val * ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv
      (Fin 3) σ z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (A⁻¹).val) 0 0 = ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) 0 0 at h2
    have h3 : ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv
        (Fin 3) σ z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        σ (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext a b
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry]
      change σ (((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) a b) = _
      by_cases hab : a = b
      · subst hab
        simp
      · simp [Matrix.one_apply_ne hab]
    rw [h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one] at h2
    simpa using h2
  have hσ : σ = 1 := by
    ext x
    by_cases hx : x = 0
    · rw [hx, map_zero, map_zero]
    · exact hsc (Units.mk0 x hx)
  rw [hσ, map_one, mul_one] at hα₀
  obtain ⟨k, hk⟩ := hα2
  have hdet3 : ((A ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_pow, hu3, Units.val_one]
  set g₁ : SpecialLinearGroup (Fin 3) K := ⟨_, hdet3⟩ with hg₁
  have hc3 : α ^ 3 = MulAut.conj g₁ := by
    rw [hαα₀, hα₀, ← map_pow]
    refine MulEquiv.ext fun x => ?_
    apply SpecialLinearGroup.toGL_injective
    have hg₁ : SpecialLinearGroup.toGL g₁ = A ^ 3 := Units.ext rfl
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      MulAut.conj_apply, map_mul, map_mul, map_inv, hg₁]
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hbez : (1 : ℤ) =
      ((3 : ℕ) : ℤ) * Nat.gcdA 3 (2 ^ k) + ((2 ^ k : ℕ) : ℤ) * Nat.gcdB 3 (2 ^ k) := by
    have h := Nat.gcd_eq_gcd_ab 3 (2 ^ k)
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h
  have hαg : α = MulAut.conj (g₁ ^ Nat.gcdA 3 (2 ^ k)) := by
    rw [map_zpow, ← hc3]
    calc α = α ^ (1 : ℤ) := (zpow_one _).symm
      _ = α ^ (((3 : ℕ) : ℤ) * Nat.gcdA 3 (2 ^ k) + ((2 ^ k : ℕ) : ℤ) * Nat.gcdB 3 (2 ^ k)) := by
          rw [← hbez]
      _ = (α ^ 3) ^ Nat.gcdA 3 (2 ^ k) := by
          rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hk,
            _root_.one_zpow, mul_one]
  exact ⟨_, fun x => by rw [hαg, MulAut.conj_apply]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
