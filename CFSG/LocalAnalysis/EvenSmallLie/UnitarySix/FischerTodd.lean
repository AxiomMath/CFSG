module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerPoints
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExtTodd
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import Certificates.Certificate3001
public import Certificates.Certificate1003
public import Certificates.Certificate2035
public import Certificates.Certificate2195
public import Certificates.Certificate3029
public import Certificates.Certificate3180
public import Certificates.Certificate1002
public import Certificates.Certificate1009
public import Certificates.Certificate3010
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer Subgroup CFSG.ComponentClassification.WittDesign
  CFSG.EvenSmallLie.UnitarySix.MathieuExt
open CFSG.EvenSmallLie.UnitarySix.ToddOrbit (orb orb_subset conj_mem_orb_iff')
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem m22Count_fpf :
    m22Count (fun g => (∀ x, g (g x) = x) ∧ ∀ x, g x ≠ x) = 0 :=
  Certificates.certificate3001

theorem exists_fixed_of_mul_self
    {σ : Equiv.Perm (Fin 22)} (hσ : σ ∈ M22) (h2 : σ * σ = 1) :
    ∃ i, σ i = i := by
  by_contra hno
  push Not at hno
  have h0 := m22Count_fpf
  rw [← card_m22_subtype] at h0
  have hne : Nonempty {x : M22 // (∀ y, (x : Equiv.Perm (Fin 22)) ((x : Equiv.Perm (Fin 22)) y) =
      y) ∧ ∀ y, (x : Equiv.Perm (Fin 22)) y ≠ y} :=
    ⟨⟨⟨σ, hσ⟩, fun y => by rw [← Equiv.Perm.mul_apply, h2]; rfl, hno⟩⟩
  exact (Nat.card_pos_iff.2 ⟨hne, inferInstance⟩).ne' h0

section Orb

variable {t : G} {E : Subgroup G}

@[expose] def orbConj (n : normalizer (E : Set G)) : Equiv.Perm (orb E t) where
  toFun s := ⟨n * s * (n : G)⁻¹, (conj_mem_orb_iff' n.2).2 s.2⟩
  invFun s := ⟨(n : G)⁻¹ * s * n, by
    have := (conj_mem_orb_iff' (inv_mem n.2) (s := (s : G))).2 s.2
    rwa [inv_inv] at this⟩
  left_inv s := Subtype.ext (by show (n : G)⁻¹ * (n * s * (n : G)⁻¹) * n = s; group)
  right_inv s := Subtype.ext (by show (n : G) * ((n : G)⁻¹ * s * n) * (n : G)⁻¹ = s; group)

theorem orbConj_val (n : normalizer (E : Set G)) (s : orb E t) :
    (orbConj n s : G) = n * s * (n : G)⁻¹ := rfl

@[expose] def labelPerm (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) :
    Equiv.Perm (Fin 22) :=
  (f.symm.trans (orbConj n)).trans f

theorem labelPerm_apply (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) (i : Fin 22) :
    labelPerm f n i = f (orbConj n (f.symm i)) := rfl

theorem labelPerm_symm (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) (s : orb E t) :
    (f.symm (labelPerm f n (f s)) : G) = n * s * (n : G)⁻¹ := by
  rw [labelPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, orbConj_val]

theorem labelPerm_mul (f : orb E t ≃ Fin 22) (n m : normalizer (E : Set G)) :
    labelPerm f (n * m) = labelPerm f n * labelPerm f m := by
  ext i
  simp only [labelPerm_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  congr 2
  exact Subtype.ext (by simp only [orbConj_val, Subgroup.coe_mul]; group)

theorem labelPerm_one (f : orb E t ≃ Fin 22) : labelPerm f 1 = 1 := by
  ext i
  simp only [labelPerm_apply, Equiv.Perm.one_apply]
  rw [show orbConj (1 : normalizer (E : Set G)) (f.symm i) = f.symm i from
    Subtype.ext (by simp [orbConj_val]), Equiv.apply_symm_apply]

theorem labelPerm_pow (f : orb E t ≃ Fin 22) (n : normalizer (E : Set G)) (k : ℕ) :
    labelPerm f (n ^ k) = labelPerm f n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, labelPerm_one]
  | succ k ih => rw [pow_succ, pow_succ, labelPerm_mul, ih]

end Orb

section Module

variable {E : Subgroup G}

@[reducible] def eModuleF [IsMulCommutative E] (hsq : ∀ e ∈ E, e ^ 2 = 1) :
    Module (ZMod 2) (Additive E) :=
  AddCommMonoid.zmodModule (n := 2) fun x : Additive E => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hsq _ (Additive.toMul x).2)

@[expose] def eConj (n : normalizer (E : Set G)) (e : E) : E :=
  ⟨n * e * (n : G)⁻¹, (mem_normalizer_iff.1 n.2 e).1 e.2⟩

@[expose] def eConjAdd (n : normalizer (E : Set G)) :
    Additive E →+ Additive E where
  toFun v := Additive.ofMul (eConj n (Additive.toMul v))
  map_zero' := by
    change Additive.ofMul (eConj n 1) = Additive.ofMul 1
    congr 1
    exact Subtype.ext (by simp [eConj])
  map_add' u v := by
    change Additive.ofMul (eConj n (Additive.toMul u * Additive.toMul v)) =
      Additive.ofMul (eConj n (Additive.toMul u) * eConj n (Additive.toMul v))
    congr 1
    exact Subtype.ext (by simp only [eConj, Subgroup.coe_mul]; group)

theorem coe_eConjAdd (n : normalizer (E : Set G)) (v : Additive E) :
    ((Additive.toMul (eConjAdd n v) : E) : G) = n * (Additive.toMul v : E) * (n : G)⁻¹ := rfl

end Module

namespace FischerHyp

variable {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

theorem isMulCommutative_E
    (h : FischerHyp t L E p) : IsMulCommutative E :=
  ⟨⟨fun a b => Subtype.ext (h.E_comm a a.2 b b.2)⟩⟩

theorem orb_subset_E
    (h : FischerHyp t L E p) : orb E t ⊆ E := orb_subset h.todd.t_mem_E

@[expose] def ePt
    (h : FischerHyp t L E p) (f : orb E t ≃ Fin 22) (i : Fin 22) : Additive E :=
  Additive.ofMul ⟨f.symm i, h.orb_subset_E (f.symm i).2⟩

theorem coe_ePt
    (h : FischerHyp t L E p) (f : orb E t ≃ Fin 22) (i : Fin 22) :
    ((Additive.toMul (h.ePt f i) : E) : G) = f.symm i := rfl

theorem ePt_injective
    (h : FischerHyp t L E p) (f : orb E t ≃ Fin 22) :
    Function.Injective (h.ePt f) := fun _ _ he =>
  f.symm.injective (Subtype.ext (congrArg (fun v : Additive E => ((Additive.toMul v : E) : G)) he))

theorem card_additive_E
    [Finite G]
    (h : FischerHyp t L E p) : Nat.card (Additive E) = 2 ^ 10 :=
  (Nat.card_congr (Additive.ofMul (α := E))).symm.trans h.todd.card_E

theorem labelPerm_mem (f : orb E t ≃ Fin 22)
    (hf : ∀ σ : Equiv.Perm (Fin 22), σ ∈ M22 ↔ ∃ n ∈ normalizer (E : Set G),
      ∀ s : orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹) (n : normalizer (E : Set G)) :
    labelPerm f n ∈ M22 :=
  (hf _).2 ⟨n, n.2, labelPerm_symm f n⟩

theorem exists_eConjAdd
    (h : FischerHyp t L E p) (f : orb E t ≃ Fin 22)
    (hf : ∀ σ : Equiv.Perm (Fin 22), σ ∈ M22 ↔ ∃ n ∈ normalizer (E : Set G),
      ∀ s : orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹) {g : Equiv.Perm (Fin 22)}
    (hg : g ∈ M22) : ∃ ρ : Additive E →+ Additive E, ∀ i, ρ (h.ePt f i) = h.ePt f (g i) := by
  obtain ⟨n, hn, hns⟩ := (hf g).1 hg
  refine ⟨eConjAdd ⟨n, hn⟩, fun i => ?_⟩
  apply Additive.toMul.injective
  refine Subtype.ext ?_
  rw [coe_eConjAdd, coe_ePt, coe_ePt]
  have := hns (f.symm i)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm


theorem toddBasis_zero_apply (i : Fin 22) :
    toddBasis 0 i = if i ∈ ({0, 1, 2, 4, 6, 7, 10} : Finset (Fin 22)) then 1 else 0 := by
  have hb : ∀ j : Fin 22,
      Nat.testBit 1239 j = true ↔ j ∈ ({0, 1, 2, 4, 6, 7, 10} : Finset (Fin 22)) := by
    decide
  show bvec 1239 i = _
  unfold bvec
  simp only [hb]

theorem coe_toMul_add {E : Subgroup G} (u v : Additive E) :
    ((Additive.toMul (u + v) : E) : G) = (Additive.toMul u : E) * (Additive.toMul v : E) := rfl

theorem eq_of_coe_toMul {E : Subgroup G} {u v : Additive E}
    (huv : ((Additive.toMul u : E) : G) = (Additive.toMul v : E)) : u = v :=
  Additive.toMul.injective (Subtype.ext huv)

theorem coe_ePt_apply
    (h : FischerHyp t L E p) (f : orb E t ≃ Fin 22) {s : G}
    (hs : s ∈ orb E t) : ((Additive.toMul (h.ePt f (f ⟨s, hs⟩)) : E) : G) = s := by
  rw [coe_ePt, Equiv.symm_apply_apply]

theorem label_ne (f : orb E t ≃ Fin 22) {s s' : G} (hs : s ∈ orb E t) (hs' : s' ∈ orb E t)
    (hne : s ≠ s') : f ⟨s, hs⟩ ≠ f ⟨s', hs'⟩ := fun e =>
  hne (congrArg Subtype.val (f.injective e))

section Todd

variable
  [Finite G]
  (h : FischerHyp t L E p) (f : orb E t ≃ Fin 22)
  (hf : ∀ σ : Equiv.Perm (Fin 22), σ ∈ M22 ↔ ∃ n ∈ normalizer (E : Set G),
    ∀ s : orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹)
include h hf

theorem pair_inj :
    ∀
    a ∈ orb E t, ∀ b ∈ orb E t, ∀ a' ∈ orb E t, ∀ b' ∈ orb E t,
    a ≠ b → a' ≠ b' → a * b = a' * b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  intro a ha b hb a' ha' b' hb' hab hab' he
  have := h.isMulCommutative_E
  let _ := eModuleF h.todd.E_sq
  have hrel := todd_relations (V := Additive E) h.card_additive_E (h.ePt_injective f)
    (fun _ hg => h.exists_eConjAdd f hf hg)
  have hsum : h.ePt f (f ⟨a, ha⟩) + h.ePt f (f ⟨b, hb⟩) =
      h.ePt f (f ⟨a', ha'⟩) + h.ePt f (f ⟨b', hb'⟩) := eq_of_coe_toMul (by
    rw [coe_toMul_add, coe_toMul_add, h.coe_ePt_apply, h.coe_ePt_apply, h.coe_ePt_apply,
      h.coe_ePt_apply, he])
  rcases hrel.2.2.1 _ _ _ _ (label_ne f ha hb hab) (label_ne f ha' hb' hab') hsum with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨congrArg Subtype.val (f.injective h1), congrArg Subtype.val (f.injective h2)⟩
  · exact Or.inr ⟨congrArg Subtype.val (f.injective h1), congrArg Subtype.val (f.injective h2)⟩

theorem mul_notMem_orb
    {a b : G} (ha : a ∈ orb E t) (hb : b ∈ orb E t) (hab : a ≠ b) :
    a * b ∉ orb E t := by
  intro hc
  have := h.isMulCommutative_E
  let _ := eModuleF h.todd.E_sq
  have hrel := todd_relations (V := Additive E) h.card_additive_E (h.ePt_injective f)
    (fun _ hg => h.exists_eConjAdd f hf hg)
  exact hrel.2.2.2 _ _ (f ⟨a * b, hc⟩) (label_ne f ha hb hab) (eq_of_coe_toMul (by
    rw [coe_toMul_add, h.coe_ePt_apply, h.coe_ePt_apply, h.coe_ePt_apply]))

theorem closure_orb :
    closure (orb E t) = E := by
  have := h.isMulCommutative_E
  let _ := eModuleF h.todd.E_sq
  have hspan := (todd_module_unique (V := Additive E) h.card_additive_E (h.ePt_injective f)
    (fun _ hg => h.exists_eConjAdd f hf hg)).1
  refine le_antisymm ((closure_le E).2 h.orb_subset_E) fun e he => ?_
  have key : ∀ v ∈ Submodule.span (ZMod 2) (Set.range (h.ePt f)),
      ((Additive.toMul v : E) : G) ∈ closure (orb E t) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact subset_closure (f.symm i).2
    | zero => exact one_mem _
    | add x y _ _ hx hy => exact mul_mem hx hy
    | smul c x _ hx =>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul]
        exact one_mem _
      · rwa [one_smul]
  exact key (Additive.ofMul ⟨e, he⟩) (by rw [hspan]; exact Submodule.mem_top)


theorem odd_relation :
    (f.symm 0 : G) * (f.symm 1 * (f.symm 2 * (f.symm 4 * (f.symm 6 * (f.symm 7 *
      (f.symm 10 : G)))))) = 1 := by
  have := h.isMulCommutative_E
  let _ := eModuleF h.todd.E_sq
  have hu := (todd_module_unique (V := Additive E) h.card_additive_E (h.ePt_injective f)
    (fun _ hg => h.exists_eConjAdd f hf hg)).2 (toddBasis 0)
  have h0 := hu.2 (Submodule.subset_span ⟨0, rfl⟩)
  rw [evalW_apply] at h0
  simp only [toddBasis_zero_apply, ite_smul, one_smul, zero_smul] at h0
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h0
  have h1 := congrArg (fun v : Additive E => ((Additive.toMul v : E) : G)) h0
  simpa only [coe_toMul_add, coe_ePt, toMul_zero, OneMemClass.coe_one] using h1

theorem orb_subset_closure_mul :
    orb E t ⊆ closure {x | ∃ a ∈ orb E t, ∃ b ∈ orb E t, a * b = x} := by
  set P := {x | ∃ a ∈ orb E t, ∃ b ∈ orb E t, a * b = x}
  have hP : ∀ i j : Fin 22, (f.symm i : G) * f.symm j ∈ closure P := fun i j =>
    subset_closure ⟨_, (f.symm i).2, _, (f.symm j).2, rfl⟩
  have hsq : ∀ s : orb E t, (s : G) * s = 1 := fun s => by
    rw [← sq]; exact h.todd.E_sq _ (h.orb_subset_E s.2)
  have h0 : (f.symm 0 : G) ∈ closure P := by
    have e : (f.symm 0 : G) = f.symm 1 * f.symm 2 * (f.symm 4 * f.symm 6 *
        (f.symm 7 * (f.symm 10 : G))) := by
      calc (f.symm 0 : G) = f.symm 0 * ((f.symm 0 : G) * (f.symm 1 * (f.symm 2 * (f.symm 4 *
            (f.symm 6 * (f.symm 7 * (f.symm 10 : G))))))) := by rw [h.odd_relation f hf, mul_one]
        _ = f.symm 1 * f.symm 2 * (f.symm 4 * f.symm 6 * (f.symm 7 * (f.symm 10 : G))) := by
          rw [← mul_assoc, hsq, one_mul]; simp only [mul_assoc]
    rw [e]
    exact mul_mem (hP 1 2) (mul_mem (hP 4 6) (hP 7 10))
  intro s hs
  have e : s = s * f.symm 0 * f.symm 0 := by rw [mul_assoc, hsq, mul_one]
  rw [e]
  exact mul_mem (subset_closure ⟨s, hs, _, (f.symm 0).2, rfl⟩) h0

theorem eq_one_of_orderOf_eleven
    {g : G} (hg : g ∈ normalizer (E : Set G))
    (hg11 : orderOf g = 11) {y : G} (hy : y ∈ E) (hgy : g * y = y * g) : y = 1 := by
  have := h.isMulCommutative_E
  let _ := eModuleF h.todd.E_sq
  have hp11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set n : normalizer (E : Set G) := ⟨g, hg⟩
  set σ := labelPerm f n
  have hσ11 : σ ^ 11 = 1 := by
    rw [← labelPerm_pow, show n ^ 11 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, ← hg11]; exact pow_orderOf_eq_one g), labelPerm_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ
    have hfix : ∀ s ∈ orb E t, g * s * g⁻¹ = s := by
      intro s hs
      have := labelPerm_symm f n ⟨s, hs⟩
      rw [show labelPerm f n = 1 from hσ, Equiv.Perm.one_apply, Equiv.symm_apply_apply] at this
      exact this.symm
    have hgE := h.ker g hg hfix
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (h.todd.E_sq g hgE)
    rw [hg11] at h2
    norm_num at h2
  have hρg : ∀ i, eConjAdd n (h.ePt f i) = h.ePt f (σ i) := by
    intro i
    apply eq_of_coe_toMul
    rw [coe_eConjAdd, coe_ePt, coe_ePt, labelPerm_apply, Equiv.symm_apply_apply, orbConj_val]
  have hv : eConjAdd n (Additive.ofMul ⟨y, hy⟩) = Additive.ofMul ⟨y, hy⟩ := by
    apply eq_of_coe_toMul
    rw [coe_eConjAdd]
    show g * y * g⁻¹ = y
    rw [hgy, mul_inv_cancel_right]
  have h0 := todd_fixedPointFree (V := Additive E) h.card_additive_E (h.ePt_injective f)
    (fun _ hg' => h.exists_eConjAdd f hf hg') (orderOf_eq_prime hσ11 hσ1) hρg hv
  have := congrArg (fun v : Additive E => ((Additive.toMul v : E) : G)) h0
  simpa using this

end Todd

end FischerHyp

end CFSG.EvenSmallLie.UnitarySix.Fischer
