module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalInvolution.Q3.Q3T6LinFin
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.OrthQ8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

section SL2

@[expose] def sl2I : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_sl2I : ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

@[expose] def sl2J (h3 : (3 : K) = 0) : SL(2, K) :=
  ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; linear_combination -h3⟩

theorem coe_sl2J (h3 : (3 : K) = 0) :
    ((sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, -1] := rfl

theorem sl2I_sq : (sl2I : SL(2, K)) ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, coe_sl2I, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2J_sq (h3 : (3 : K) = 0) : sl2J h3 ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, coe_sl2J, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h3

theorem sl2I_pow_four : (sl2I : SL(2, K)) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, sl2I_sq, neg_one_sq]

theorem sl2J_pow_four (h3 : (3 : K) = 0) : sl2J h3 ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, sl2J_sq h3, neg_one_sq]

variable [Finite K]

theorem three_eq_zero (hK : Nat.card K = 3) : (3 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h := Nat.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact_mod_cast h

theorem two_ne_zero' (hK : Nat.card K = 3) : (2 : K) ≠ 0 := fun h =>
  one_ne_zero (by linear_combination three_eq_zero hK - h : (1 : K) = 0)

omit [Finite K] in
private theorem map_commutator_eq (e : SL(2, K) ≃* SL(2, ZMod 3)) :
    (commutator SL(2, K)).map e.toMonoidHom = commutator SL(2, ZMod 3) := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem mem_commutator_sl2_iff (hK : Nat.card K = 3) {g : SL(2, K)} :
    g ∈ commutator SL(2, K) ↔ g ^ 4 = 1 := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hK
  have hmap := map_commutator_eq e
  constructor
  · intro hg
    have h1 : e g ∈ commutator SL(2, ZMod 3) := hmap ▸ Subgroup.mem_map_of_mem _ hg
    rw [Q3T6.sl2Three_mem_commutator_iff] at h1
    exact e.injective (by rw [map_pow, h1, map_one])
  · intro hg
    have h1 : e g ∈ commutator SL(2, ZMod 3) := by
      rw [Q3T6.sl2Three_mem_commutator_iff, ← map_pow, hg, map_one]
    rw [← hmap] at h1
    obtain ⟨g', hg', he⟩ := h1
    rwa [e.injective he] at hg'

theorem natCard_commutator_sl2 (hK : Nat.card K = 3) :
    Nat.card ↥(commutator SL(2, K)) = 8 := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hK
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, map_commutator_eq e]
  exact Q3T6.sl2Three_card_commutator

private theorem sq_eq_one_cases_three :
    ∀ y : SL(2, ZMod 3), y ^ 2 = 1 → y = 1 ∨ y = -1 := by
  decide +kernel

theorem eq_one_or_neg_one (hK : Nat.card K = 3) {g : SL(2, K)} (hg : g ^ 2 = 1) :
    g = 1 ∨ g = -1 := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hK
  have hneg : e (-1) = -1 := by
    rcases sq_eq_one_cases_three (e (-1)) (by rw [← map_pow, neg_one_sq, map_one]) with h | h
    · exact absurd (e.injective (h.trans (map_one e).symm)) (by
        intro h1
        have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
        simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
          Matrix.neg_apply, Matrix.one_apply_eq] at this
        exact two_ne_zero' hK (by linear_combination -this))
    · exact h
  rcases sq_eq_one_cases_three (e g) (by rw [← map_pow, hg, map_one]) with h | h
  · exact Or.inl (e.injective (h.trans (map_one e).symm))
  · exact Or.inr (e.injective (h.trans hneg.symm))

end SL2

variable {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {S : Type} [Group S]

@[expose] noncomputable def frameQ8 (F : Frame Q) : Subgroup (V ≃ₗ[K] V) :=
  (commutator SL(2, K)).map F.La

theorem La_mem_frameQ8 (F : Frame Q) {g : SL(2, K)} (hg : g ∈ commutator SL(2, K)) :
    F.La g ∈ frameQ8 F :=
  ⟨g, hg, rfl⟩

theorem frameQ8_eq (F : Frame Q) : frameQ8 F = ⁅F.La.range, F.La.range⁆ := by
  rw [frameQ8, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]

theorem frameQ8_le (F : Frame Q) : frameQ8 F ≤ orthDerived Q := by
  rw [frameQ8_eq]
  have hle : F.La.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨A, rfl⟩
    exact F.La_mem_orthogonalGroup A
  exact Subgroup.commutator_mono hle hle

section NegOne

private def dMat : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

private theorem dMat_mul_dMat : (dMat : Matrix (Fin 2) (Fin 2) K) * dMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, Matrix.mul_apply, Fin.sum_univ_two]

private def dConj : Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun X := dMat * X * dMat
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

private theorem dConj_apply (X : Matrix (Fin 2) (Fin 2) K) : dConj X = dMat * X * dMat := rfl

private theorem dConj_mul_dConj :
    (dConj : Module.End K (Matrix (Fin 2) (Fin 2) K)) * dConj = 1 := by
  refine LinearMap.ext fun X => ?_
  rw [Module.End.mul_apply, dConj_apply, dConj_apply, Module.End.one_apply,
    show dMat * (dMat * X * dMat) * dMat = (dMat * dMat) * X * (dMat * dMat) by
      simp only [Matrix.mul_assoc], dMat_mul_dMat, Matrix.one_mul, Matrix.mul_one]

private theorem det_dConj (X : Matrix (Fin 2) (Fin 2) K) : (dConj X).det = X.det := by
  rw [dConj_apply, Matrix.det_mul, Matrix.det_mul]
  have : (dMat : Matrix (Fin 2) (Fin 2) K).det = -1 := by simp [dMat, Matrix.det_fin_two]
  rw [this]
  ring

private noncomputable def dEquiv (F : Frame Q) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (F.embLin dConj) (F.embLin dConj)
    (by rw [← Module.End.mul_eq_comp, ← Frame.embLin_mul, dConj_mul_dConj, Frame.embLin_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← Frame.embLin_mul, dConj_mul_dConj, Frame.embLin_one]; rfl)

private theorem dEquiv_apply (F : Frame Q) (x : V) : dEquiv F x = F.embLin dConj x := rfl

private theorem dEquiv_mem (F : Frame Q) :
    dEquiv F ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => F.Q_embLin det_dConj x

private theorem dEquiv_mul_self (F : Frame Q) : dEquiv F * dEquiv F = 1 :=
  LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, dEquiv_apply, dEquiv_apply, ← Module.End.mul_apply,
      ← Frame.embLin_mul, dConj_mul_dConj, Frame.embLin_one]
    rfl

private theorem La_apply_embLin (F : Frame Q) (A : SL(2, K)) (x : V) :
    F.La A x = F.embLin (Frame.rhoL A) x := rfl

private theorem dConj_rhoL :
    dConj * Frame.rhoL (sl2I : SL(2, K)) * dConj * Frame.rhoL (sl2I⁻¹ : SL(2, K)) =
      Frame.rhoL (-1 : SL(2, K)) := by
  have hM : dMat * ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * dMat *
      Matrix.adjugate ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dMat, coe_sl2I, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  refine LinearMap.ext fun X => ?_
  simp only [Module.End.mul_apply, dConj_apply, Frame.rhoL, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.mulLeft_apply, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  calc dMat * (((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (dMat * (Matrix.adjugate
          ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * X) * dMat)) * dMat =
        (dMat * ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * dMat *
          Matrix.adjugate ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) * X *
            (dMat * dMat) := by simp only [Matrix.mul_assoc]
    _ = -1 * X := by rw [hM, dMat_mul_dMat, Matrix.mul_one]

theorem La_neg_one_mem_orthDerived (F : Frame Q) : F.La (-1) ∈ orthDerived Q := by
  have key : ⁅dEquiv F, F.La sl2I⁆ = F.La (-1) := by
    refine LinearEquiv.ext fun x => ?_
    have hinv : (dEquiv F)⁻¹ = dEquiv F := inv_eq_of_mul_eq_one_right (dEquiv_mul_self F)
    rw [commutatorElement_def, hinv, ← map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, dEquiv_apply, dEquiv_apply, La_apply_embLin, La_apply_embLin,
      La_apply_embLin, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
      ← Frame.embLin_mul, ← Frame.embLin_mul, ← Frame.embLin_mul, dConj_rhoL]
  rw [← key]
  exact Subgroup.commutator_mem_commutator (dEquiv_mem F) (F.La_mem_orthogonalGroup _)

end NegOne

@[expose] noncomputable def frameMember (θ : ↥(orthDerived Q) →* S) (F : Frame Q) : Subgroup S :=
  ((frameQ8 F).subgroupOf (orthDerived Q)).map θ

@[expose] noncomputable def frameInv (θ : ↥(orthDerived Q) →* S) (F : Frame Q) : S :=
  θ ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩

theorem La_mem_frameMember (θ : ↥(orthDerived Q) →* S) (F : Frame Q) {g : SL(2, K)}
    (hg : g ∈ commutator SL(2, K)) :
    θ ⟨F.La g, frameQ8_le F (La_mem_frameQ8 F hg)⟩ ∈ frameMember θ F :=
  ⟨_, Subgroup.mem_subgroupOf.mpr (La_mem_frameQ8 F hg), rfl⟩

theorem mem_frameMember_iff (θ : ↥(orthDerived Q) →* S) (F : Frame Q) {y : S} :
    y ∈ frameMember θ F ↔ ∃ g, ∃ hg : g ∈ commutator SL(2, K),
      θ ⟨F.La g, frameQ8_le F (La_mem_frameQ8 F hg)⟩ = y := by
  constructor
  · rintro ⟨⟨x, hxΩ⟩, hx, rfl⟩
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_subgroupOf.mp hx
    refine ⟨g, hg, ?_⟩
    congr 1
    exact Subtype.ext hgx
  · rintro ⟨g, hg, rfl⟩
    exact La_mem_frameMember θ F hg

theorem frameQ8_eq_conjSub {F F' : Frame Q} {g : V ≃ₗ[K] V}
    (h : ∀ A : SL(2, K), F'.La A = g * F.La A * g⁻¹) : frameQ8 F' = conjSub g (frameQ8 F) := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [h]
    exact ⟨F.La A, ⟨A, hA, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A, hA, by rw [h]; rfl⟩

theorem frameMember_eq_conjSub (θ : ↥(orthDerived Q) →* S) {F F' : Frame Q} {g : V ≃ₗ[K] V}
    (hgΩ : g ∈ orthDerived Q) (h : ∀ A : SL(2, K), F'.La A = g * F.La A * g⁻¹) :
    frameMember θ F' = conjSub (θ ⟨g, hgΩ⟩) (frameMember θ F) := by
  ext y
  rw [frameMember, frameMember, frameQ8_eq_conjSub h, mem_conjSub_iff]
  constructor
  · rintro ⟨⟨x, hxΩ⟩, hx, rfl⟩
    have hx' : x ∈ conjSub g (frameQ8 F) := Subgroup.mem_subgroupOf.mp hx
    rw [mem_conjSub_iff] at hx'
    refine ⟨⟨g⁻¹ * x * g, (orthDerived Q).mul_mem ((orthDerived Q).mul_mem
      ((orthDerived Q).inv_mem hgΩ) hxΩ) hgΩ⟩, Subgroup.mem_subgroupOf.mpr hx', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · rintro ⟨⟨z, hzΩ⟩, hz, hzy⟩
    refine ⟨⟨g * z * g⁻¹, (orthDerived Q).mul_mem ((orthDerived Q).mul_mem hgΩ hzΩ)
      ((orthDerived Q).inv_mem hgΩ)⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [mem_conjSub_iff]
      simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp hz
    · have h1 : (⟨g * z * g⁻¹, (orthDerived Q).mul_mem ((orthDerived Q).mul_mem hgΩ hzΩ)
          ((orthDerived Q).inv_mem hgΩ)⟩ : ↥(orthDerived Q)) =
          ⟨g, hgΩ⟩ * ⟨z, hzΩ⟩ * (⟨g, hgΩ⟩ : ↥(orthDerived Q))⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv, hzy]
      group

theorem frameMember_map (θ : ↥(orthDerived Q) →* S) (F : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgΩ : g ∈ orthDerived Q) :
    frameMember θ (F.map hg) = conjSub (θ ⟨g, hgΩ⟩) (frameMember θ F) :=
  frameMember_eq_conjSub θ hgΩ (Frame.map_La F hg)

theorem natCard_frameMember_le [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (θ : ↥(orthDerived Q) →* S) (F : Frame Q) : Nat.card ↥(frameMember θ F) ≤ 8 := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  have h1 : Nat.card ↥(frameMember θ F) ≤ Nat.card ↥((frameQ8 F).subgroupOf (orthDerived Q)) :=
    Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective θ _)
  have h2 : Nat.card ↥((frameQ8 F).subgroupOf (orthDerived Q)) = Nat.card ↥(frameQ8 F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (frameQ8_le F)).toEquiv
  have h3 : Nat.card ↥(frameQ8 F) ≤ Nat.card ↥(commutator SL(2, K)) :=
    Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective F.La _)
  rw [natCard_commutator_sl2 hK] at h3
  omega

end CFSG.ClassicalInvolution.Q3.TL4.OrthQ8
