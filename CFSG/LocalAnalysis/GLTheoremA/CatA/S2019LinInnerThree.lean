module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeCore
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section LastCol

variable {E : Type*} [Field E] {m : ℕ} (last : Fin m)

@[expose] def lastColVecs : AddSubgroup (Fin m → E) where
  carrier := {c | c last = 0}
  add_mem' {a b} ha hb := by
    change a last + b last = 0
    rw [show a last = 0 from ha, show b last = 0 from hb, add_zero]
  zero_mem' := rfl
  neg_mem' {a} ha := by
    change -(a last) = 0
    rw [show a last = 0 from ha, neg_zero]

theorem vecMulVec_single_mul {c c' : Fin m → E} (hc' : c' last = 0) :
    Matrix.vecMulVec c (Pi.single last 1) * Matrix.vecMulVec c' (Pi.single last 1) = 0 := by
  classical
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have h : (Pi.single last (1 : E) ⬝ᵥ c') = 0 := by
    rw [single_dotProduct, one_mul, hc']
  rw [h, zero_smul]
  ext i j
  simp [Matrix.vecMulVec_apply]

theorem det_one_add_vecMulVec_single {c : Fin m → E} (hc : c last = 0) :
    (1 + Matrix.vecMulVec c (Pi.single last 1)).det = 1 := by
  classical
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow,
    single_dotProduct, one_mul, hc, add_zero]

@[expose] noncomputable def lastColHom :
    Multiplicative (lastColVecs (E := E) last) →* Matrix.SpecialLinearGroup (Fin m) E where
  toFun c := ⟨1 + Matrix.vecMulVec ((Multiplicative.toAdd c : lastColVecs (E := E) last) : Fin m → E) (Pi.single last 1),
    det_one_add_vecMulVec_single last (Multiplicative.toAdd c).2⟩
  map_one' := by
    apply Subtype.ext
    change 1 + Matrix.vecMulVec (((Multiplicative.toAdd (1 : Multiplicative (lastColVecs (E := E)
      last)) : lastColVecs (E := E) last)) : Fin m → E) (Pi.single last 1) = 1
    rw [toAdd_one, AddSubgroup.coe_zero]
    ext i j
    simp [Matrix.vecMulVec_apply]
  map_mul' c c' := by
    apply Subtype.ext
    change 1 + Matrix.vecMulVec (((Multiplicative.toAdd (c * c') : lastColVecs (E := E) last)) :
        Fin m → E) (Pi.single last 1) =
      (1 + Matrix.vecMulVec (((Multiplicative.toAdd c : lastColVecs (E := E) last)) : Fin m → E)
        (Pi.single last 1)) *
      (1 + Matrix.vecMulVec (((Multiplicative.toAdd c' : lastColVecs (E := E) last)) : Fin m → E)
        (Pi.single last 1))
    rw [toAdd_mul, AddSubgroup.coe_add, Matrix.add_vecMulVec, add_mul, one_mul, mul_add, mul_one,
      vecMulVec_single_mul last (Multiplicative.toAdd c').2, add_zero]
    abel

theorem coe_lastColHom (c : Multiplicative (lastColVecs (E := E) last)) :
    ((lastColHom last c : Matrix.SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      1 + Matrix.vecMulVec ((Multiplicative.toAdd c : lastColVecs (E := E) last) : Fin m → E) (Pi.single last 1) := rfl

theorem lastColHom_apply_ne (c : Multiplicative (lastColVecs (E := E) last)) {a : Fin m}
    (ha : a ≠ last) :
    ((lastColHom last c : Matrix.SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) a last =
      ((Multiplicative.toAdd c : lastColVecs (E := E) last) : Fin m → E) a := by
  classical
  rw [coe_lastColHom, Matrix.add_apply, Matrix.one_apply_ne ha, zero_add, Matrix.vecMulVec_apply,
    Pi.single_eq_same, mul_one]

theorem lastColHom_injective : Function.Injective (lastColHom (E := E) last) := by
  classical
  rw [injective_iff_map_eq_one]
  intro c hc
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext a
  by_cases ha : a = last
  · rw [ha]
    exact (Multiplicative.toAdd c).2
  · have h1 := lastColHom_apply_ne last c ha
    rw [hc, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne ha] at h1
    exact h1.symm

theorem eq_one_of_lastColHom_mem_center (c : Multiplicative (lastColVecs (E := E) last))
    (hc : lastColHom last c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) :
    c = 1 := by
  classical
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext a
  by_cases ha : a = last
  · rw [ha]
    exact (Multiplicative.toAdd c).2
  · have h1 := lastColHom_apply_ne last c ha
    rw [← hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ ha] at h1
    exact h1.symm

theorem lastColHom_pow_three [CharP E 3] (c : Multiplicative (lastColVecs (E := E) last)) :
    c ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext a
  simp only [toAdd_pow, AddSubgroup.coe_nsmul, Pi.smul_apply, toAdd_one, AddSubgroup.coe_zero,
    Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [show (3 : E) = ((3 : ℕ) : E) by norm_num, CharP.cast_eq_zero, zero_mul]

end LastCol

section Factor

variable {n : ℕ} {k : Type} [Field k] [Finite k]

theorem nine_le_card_lastColVecs {E : Type*} [Field E] [Finite E] [CharP E 3] {m : ℕ}
    (last : Fin m) (hlast : (last : ℕ) = m - 1) (hm : 3 ≤ m ∨ (2 ≤ m ∧ 4 ≤ Nat.card E)) :
    9 ≤ Nat.card (lastColVecs (E := E) last) := by
  classical
  haveI := Fintype.ofFinite E
  obtain ⟨d, -, hd⟩ := FiniteField.card E 3
  have hE3 : 3 ≤ Nat.card E := by
    rw [Nat.card_eq_fintype_card, hd]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) d.pos)
  rcases hm with h3 | ⟨h2, h4⟩
  ·
    let i0 : Fin m := ⟨0, by omega⟩
    let i1 : Fin m := ⟨1, by omega⟩
    have h0 : i0 ≠ last := fun h => by
      have := congrArg Fin.val h
      simp only [i0] at this
      omega
    have h1 : i1 ≠ last := fun h => by
      have := congrArg Fin.val h
      simp only [i1] at this
      omega
    have h01 : i0 ≠ i1 := fun h => by
      have := congrArg Fin.val h
      simp [i0, i1] at this
    let f : E × E → lastColVecs (E := E) last := fun st =>
      ⟨Pi.single i0 st.1 + Pi.single i1 st.2, by
        change (Pi.single i0 st.1 + Pi.single i1 st.2 : Fin m → E) last = 0
        rw [Pi.add_apply, Pi.single_eq_of_ne h0.symm, Pi.single_eq_of_ne h1.symm, add_zero]⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e := congrArg Subtype.val hab
      have e0 := congrFun e i0
      have e1 := congrFun e i1
      simp only [f, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h01,
        Pi.single_eq_of_ne h01.symm, add_zero, zero_add] at e0 e1
      exact Prod.ext e0 e1
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at this
    nlinarith
  ·
    have hE9 : 9 ≤ Nat.card E := by
      rw [Nat.card_eq_fintype_card, hd] at h4 ⊢
      have hd2 : 2 ≤ (d : ℕ) := by
        by_contra hlt
        have : (d : ℕ) = 1 := by have := d.pos; omega
        rw [this] at h4
        omega
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (d : ℕ) := Nat.pow_le_pow_right (by norm_num) hd2
    let i0 : Fin m := ⟨0, by omega⟩
    have h0 : i0 ≠ last := fun h => by
      have := congrArg Fin.val h
      simp only [i0] at this
      omega
    let f : E → lastColVecs (E := E) last := fun t =>
      ⟨Pi.single i0 t, by
        change (Pi.single i0 t : Fin m → E) last = 0
        rw [Pi.single_eq_of_ne h0.symm]⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e := congrFun (congrArg Subtype.val hab) i0
      simpa [f] using e
    exact hE9.trans (Nat.card_le_card_of_injective f hf)

theorem exists_pGroup_specialFactor [CharP k 3] {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) {h : k[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End k (Fin n → k))) (hgood : IsGoodFactor A h) :
    ∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin n) k), P ≤ specialFactor A h ∧
      IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ j ∈ specialFactor A h, u * j = j * u) → u = 1) ∧
      ∀ u ∈ P, (((slGL n k u : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)) - 1) ^ 2 = 0 := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite k
  haveI : CharP (AdjoinRoot h) 3 :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot h)).injective 3
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h := by
    rcases hgood with h3 | ⟨h2, -⟩ <;> omega
  set W := primaryComponent (glA A : Module.End k (Fin n → k)) h with hW
  let b : Module.Basis (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h))
      (AdjoinRoot h) W := Module.finBasisOfFinrankEq _ _ rfl
  let last : Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h) :=
    ⟨primaryMultiplicity (glA A : Module.End k (Fin n → k)) h - 1, by omega⟩
  let e₁ : linearSpecialBlock (glA A) h ≃* _root_.SpecialLinearGroup (AdjoinRoot h) W :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (glA A) h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n k).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  have hmap : (specialFactor A h).map (slGL n k) = linearSpecialBlock (glA A) h := by
    rw [specialFactor, Subgroup.map_comap_eq, inf_eq_right]
    exact hle
  let e₂ : specialFactor A h ≃* linearSpecialBlock (glA A) h :=
    (Subgroup.equivMapOfInjective _ (slGL n k) slGL_injective).trans (MulEquiv.subgroupCongr hmap)
  let ψ : Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h))
      (AdjoinRoot h) ≃* specialFactor A h :=
    ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm).trans e₂.symm
  have hψ : ∀ g, slGL n k (ψ g : Matrix.SpecialLinearGroup (Fin n) k) =
      ((e₁.symm (Matrix.SpecialLinearGroup.toLin_equiv b g) : linearSpecialBlock (glA A) h) :
        LinearMap.GeneralLinearGroup k (Fin n → k)) := by
    intro g
    have := congrArg (fun x : linearSpecialBlock (glA A) h =>
      (x : LinearMap.GeneralLinearGroup k (Fin n → k)))
      (e₂.apply_symm_apply (e₁.symm (Matrix.SpecialLinearGroup.toLin_equiv b g)))
    exact this
  have hψW : ∀ g (w : W), ((slGL n k (ψ g : Matrix.SpecialLinearGroup (Fin n) k) :
      LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) (w : Fin n → k) =
      ((Matrix.toLin b b (g : Matrix _ _ (AdjoinRoot h)) w : W) : Fin n → k) := by
    intro g w
    rw [hψ g]
    have h1 := coe_linearSpecialBlockRestrict (e₁.symm (Matrix.SpecialLinearGroup.toLin_equiv b g)) w
    have h2 : linearSpecialBlockRestrict (glA A) h
        (e₁.symm (Matrix.SpecialLinearGroup.toLin_equiv b g)) =
        Matrix.SpecialLinearGroup.toLin_equiv b g := e₁.apply_symm_apply _
    rw [h2] at h1
    rw [← h1]
    exact congrArg Subtype.val
      (LinearMap.congr_fun (Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b g) w)
  have hψO : ∀ g, ∀ j ∈ primaryFactors (glA A : Module.End k (Fin n → k)), j ≠ h →
      ∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) j,
        ((slGL n k (ψ g : Matrix.SpecialLinearGroup (Fin n) k) :
          LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) v = v := by
    intro g j hj hjh v hv
    rw [hψ g]
    exact (mem_linearSpecialBlock.1 (e₁.symm (Matrix.SpecialLinearGroup.toLin_equiv b g)).2).2.1
      j hj hjh v hv
  set P : Subgroup (Matrix.SpecialLinearGroup (Fin n) k) :=
    (((lastColHom last).range.map ψ.toMonoidHom).map (specialFactor A h).subtype) with hP
  have hmemP : ∀ u ∈ P, ∃ c, u = (ψ (lastColHom last c) : Matrix.SpecialLinearGroup (Fin n) k) := by
    rintro _ ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  refine ⟨P, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨c, hc⟩ := hmemP _ x.2
    rw [pow_one, Subgroup.coe_pow, hc, ← Subgroup.coe_pow, ← map_pow, ← map_pow,
      lastColHom_pow_three, map_one, map_one]
    rfl
  ·
    rw [hP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective ψ.injective,
      ← Nat.card_congr (MonoidHom.ofInjective (lastColHom_injective last)).toEquiv,
      ← Nat.card_congr (Multiplicative.toAdd : Multiplicative _ ≃ _)]
    exact nine_le_card_lastColVecs last rfl (by
      rcases hgood with h3 | h2
      · exact Or.inl h3
      · exact Or.inr h2)
  ·
    intro u hu hcent
    obtain ⟨c, rfl⟩ := hmemP u hu
    have hc : lastColHom last c ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply ψ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact (hcent _ (ψ g).2).symm
    rw [eq_one_of_lastColHom_mem_center last c hc, map_one, map_one]
    rfl
  ·
    intro u hu
    obtain ⟨c, rfl⟩ := hmemP u hu
    set N : W →ₗ[AdjoinRoot h] W := Matrix.toLin b b
      (Matrix.vecMulVec ((Multiplicative.toAdd c : lastColVecs last) : Fin _ → AdjoinRoot h)
        (Pi.single last 1)) with hNdef
    have hNN : ∀ w : W, N (N w) = 0 := by
      intro w
      have e1 : N.comp N = 0 := by
        rw [hNdef, ← Matrix.toLin_mul, vecMulVec_single_mul last (Multiplicative.toAdd c).2,
          map_zero]
      exact LinearMap.congr_fun e1 w
    have hact : ∀ w : W, ((slGL n k (ψ (lastColHom last c) : Matrix.SpecialLinearGroup (Fin n) k) :
        LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) (w : Fin n → k) =
        (w : Fin n → k) + ((N w : W) : Fin n → k) := by
      intro w
      rw [hψW, coe_lastColHom, map_add, Matrix.toLin_one, LinearMap.add_apply, LinearMap.id_apply,
        Submodule.coe_add]
    refine ext_primaryComponent hsq fun j hj v hv => ?_
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    by_cases hjh : j = h
    · subst hjh
      set w : W := ⟨v, hv⟩
      have e1 := hact w
      have e2 := hact (N w)
      change _ = (w : Fin n → k) + _ at e1
      rw [e1, add_sub_cancel_left, e2, hNN, Submodule.coe_zero, add_zero, sub_self]
    · rw [hψO _ j hj hjh v hv, sub_self, map_zero, sub_self]

end Factor

theorem s2019LinInner_three : S2019LinInner (· = 3) := by
  intro p q hp hp2 hq hq2 hqp hq3 F _ _ _ n A c hA L hL T hT2 hLT
  classical
  change q = 3 at hq3
  subst hq3
  have hpk : (p : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F 3]
    intro hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hdvd)
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hle := perfectInLayer_conjAut hpk hA L hL.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hL hle
  obtain ⟨⟨⟨h, hh⟩, hgood⟩, hLeq⟩ := LieComp.linear_inner_components hpk hA L hcomp
  have hsq := squarefree_minpoly_glA hpk hA
  obtain ⟨P, hPJ, hP3, hP9, hPZ, hPq⟩ := exists_pGroup_specialFactor hsq hh hgood
  exact commutator_eq_bot_of_quadratic_lift_three hcomp.2.2 hLT hT2 (LinearFlag.proj n F)
    (LinearFlag.proj_surjective n F)
    (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_center n F) (slGL n F)
    slGL_injective (Subgroup.isPerfect_iff.mp (isQuasisimple_specialFactor hsq hh hgood).1)
    hLeq.symm hPJ hP3 hP9 hPZ (fun u hu _ _ => hPq u hu)

end CFSG.LocalAnalysis.GLTheoremA.S2019
