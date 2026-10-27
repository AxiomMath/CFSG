module

public import CFSG.LieType.Steinberg.Adjoint.Comm
public import CFSG.LieType.Steinberg.Extras
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

section Raises

variable {R : Type} [CommRing R] (φ : (Fin τ.rank → ℤ) →+ ℤ)

@[expose] def Raises (m : ℤ) (A : Module.End R (RootModule τ R)) : Prop :=
  ∀ a b : Label τ, A (Finsupp.single b 1) a ≠ 0 →
    φ (labelWt τ b) + m ≤ φ (labelWt τ a)

variable {φ}

namespace Raises

theorem zero (m : ℤ) : Raises (R := R) (τ := τ) φ m 0 := fun _ _ h => absurd rfl h

theorem mono {m n : ℤ} {A : Module.End R (RootModule τ R)} (h : Raises φ m A) (hnm : n ≤ m) :
    Raises φ n A := fun a b hab => by
  have := h a b hab
  omega

theorem add {m : ℤ} {A B : Module.End R (RootModule τ R)} (hA : Raises φ m A)
    (hB : Raises φ m B) : Raises φ m (A + B) := fun a b hab => by
  rw [LinearMap.add_apply, Finsupp.add_apply] at hab
  by_cases h : A (Finsupp.single b 1) a = 0
  · rw [h, zero_add] at hab
    exact hB a b hab
  · exact hA a b h

theorem neg {m : ℤ} {A : Module.End R (RootModule τ R)} (hA : Raises φ m A) :
    Raises φ m (-A) := fun a b hab => hA a b (by simpa using hab)

theorem sub {m : ℤ} {A B : Module.End R (RootModule τ R)} (hA : Raises φ m A)
    (hB : Raises φ m B) : Raises φ m (A - B) := by
  rw [sub_eq_add_neg]
  exact hA.add hB.neg

theorem smul {m : ℤ} {A : Module.End R (RootModule τ R)} (hA : Raises φ m A) (r : R) :
    Raises φ m (r • A) := fun a b hab => by
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] at hab
  exact hA a b (right_ne_zero_of_mul hab)

theorem sum {ι : Type*} (s : Finset ι) {m : ℤ} {A : ι → Module.End R (RootModule τ R)}
    (h : ∀ i ∈ s, Raises φ m (A i)) : Raises φ m (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (R := R) (τ := τ) (φ := φ) m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mul {m n : ℤ} {A B : Module.End R (RootModule τ R)} (hA : Raises φ m A)
    (hB : Raises φ n B) : Raises φ (m + n) (A * B) := fun a b hab => by
  rw [Module.End.mul_apply, ← Finsupp.sum_single (B (Finsupp.single b 1)), Finsupp.sum,
    map_sum, Finsupp.finsetSum_apply] at hab
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  have h1 := hA a c (right_ne_zero_of_mul hc')
  have h2 := hB c b (Finsupp.mem_support_iff.mp hc)
  omega

theorem of_mapsLabelWt {A : Module.End R (RootModule τ R)} {v : Fin τ.rank → ℤ}
    (h : MapsLabelWt A (· + v)) : Raises φ (φ v) A := fun a b hab => by
  rw [h a b hab, map_add]

theorem apply_eq_zero {m : ℤ} {A : Module.End R (RootModule τ R)} (h : Raises φ m A)
    {a b : Label τ} (hab : φ (labelWt τ a) < φ (labelWt τ b) + m) :
    A (Finsupp.single b 1) a = 0 := by
  by_contra hne
  have := h a b hne
  omega

end Raises

end Raises

namespace RootOperatorFamily'

variable (F : RootOperatorFamily τ) {R : Type} [CommRing R] {φ : (Fin τ.rank → ℤ) →+ ℤ}

theorem D_raises (α : Root τ) {k : ℕ} (hk : 1 ≤ k) :
    Raises φ (k * φ α.1) (F.D R α k) := by
  have := Raises.of_mapsLabelWt (φ := φ) (F.mapsLabelWt_D (R := R) α hk)
  rwa [map_nsmul, nsmul_eq_mul] at this

theorem elt_sub_one (α : Root τ) (c : R) :
    F.elt R α c - 1 = ∑ k ∈ Finset.Ico 1 4, c ^ k • F.D R α k := by
  rw [RootOperatorFamily.elt, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num),
    pow_zero, one_smul, F.D_zero, add_sub_cancel_left]

theorem elt_sub_one_raises (α : Root τ) (hα : 0 ≤ φ α.1) (c : R) :
    Raises φ (φ α.1) (F.elt R α c - 1) := by
  rw [elt_sub_one]
  refine Raises.sum _ fun k hk => ((D_raises F α (Finset.mem_Ico.1 hk).1).smul _).mono ?_
  have : (1 : ℤ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
  nlinarith

theorem elt_neg_sub_one_raises (α : Root τ) (hα : 0 ≤ φ α.1) (c : R) :
    Raises φ (φ α.1) (F.elt R α (-c) - 1) :=
  elt_sub_one_raises F α hα (-c)

theorem D_apply_eq_zero_of_shift (α : Root τ) {k : ℕ} (hk : k ≠ 1) {a b : Label τ}
    (hab : labelWt τ a = labelWt τ b + α.1) : F.D R α k (Finsupp.single b 1) a = 0 := by
  by_contra hne
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [F.D_zero, Module.End.one_apply, Finsupp.single_apply] at hne
    split_ifs at hne with hba
    · subst hba
      have : α.1 = 0 := by simpa using hab
      exact α.2.ne_zero this
    · exact hne rfl
  · have h := F.mapsLabelWt_D (R := R) α hk0 a b hne
    rw [hab] at h
    have h' : (k - 1 : ℤ) • α.1 = 0 := by
      have := congrArg (· - labelWt τ b) h
      simp only [add_sub_cancel_left] at this
      rw [sub_smul, one_smul, natCast_zsmul, ← this, sub_self]
    rcases smul_eq_zero.1 h' with h0 | h0
    · omega
    · exact α.2.ne_zero h0

theorem elt_apply_of_shift (α : Root τ) (c : R) {a b : Label τ}
    (hab : labelWt τ a = labelWt τ b + α.1) :
    F.elt R α c (Finsupp.single b 1) a = c * F.D R α 1 (Finsupp.single b 1) a := by
  rw [RootOperatorFamily.elt, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_eq_single 1]
  · rw [pow_one, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  · intro k _ hk
    rw [LinearMap.smul_apply, Finsupp.smul_apply, D_apply_eq_zero_of_shift F α hk hab,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by norm_num)) h

theorem eltOr_sub_one_raises {γ : Fin τ.rank → ℤ} (hγ : 0 ≤ φ γ) (c : R) :
    Raises φ (φ γ) (eltOr F R γ c - 1) := by
  by_cases h : IsRoot τ γ
  · rw [eltOr_of_isRoot F R h]
    exact elt_sub_one_raises F ⟨γ, h⟩ hγ c
  · rw [eltOr_of_not_isRoot F R h, sub_self]
    exact Raises.zero _

theorem mul_sub_one (X P : Module.End R (RootModule τ R)) :
    X * P - 1 = (X - 1) + (P - 1) + (X - 1) * (P - 1) := by
  simp only [mul_sub, sub_mul, one_mul, mul_one]
  abel

theorem prod_sub_one_raises {s : ℤ} (hs : 0 ≤ s) (c : (Fin τ.rank → ℤ) → R) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ γ ∈ L, s ≤ φ γ) →
      Raises φ s ((L.map fun γ => eltOr F R γ (c γ)).prod - 1)
  | [], _ => by simpa using Raises.zero (R := R) (τ := τ) (φ := φ) s
  | γ :: L, hL => by
    rw [List.map_cons, List.prod_cons, mul_sub_one]
    have h1 := (eltOr_sub_one_raises F (le_trans hs (hL γ (List.mem_cons_self))) (c γ)).mono
      (hL γ List.mem_cons_self)
    have h2 := prod_sub_one_raises hs c L fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ)
    exact (h1.add h2).add ((h1.mul h2).mono (by omega))

theorem prod_sub_one_apply_eq_zero {γ₀ : Fin τ.rank → ℤ} (h₀ : IsRoot τ γ₀) (h₀φ : 1 ≤ φ γ₀)
    (c : (Fin τ.rank → ℤ) → R) {a b : Label τ} (hab : labelWt τ a = labelWt τ b + γ₀) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ γ ∈ L, γ ≠ γ₀ ∧ φ γ₀ ≤ φ γ) →
      ((L.map fun γ => eltOr F R γ (c γ)).prod - 1) (Finsupp.single b 1) a = 0
  | [], _ => by simp
  | γ :: L, hL => by
    have hφab : φ (labelWt τ a) = φ (labelWt τ b) + φ γ₀ := by rw [hab, map_add]
    rw [List.map_cons, List.prod_cons, mul_sub_one, LinearMap.add_apply, LinearMap.add_apply,
      Finsupp.add_apply, Finsupp.add_apply,
      prod_sub_one_apply_eq_zero h₀ h₀φ c hab L fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ),
      add_zero]
    obtain ⟨hγne, hγφ⟩ := hL γ List.mem_cons_self
    have h2 := prod_sub_one_raises F (by omega : (0 : ℤ) ≤ φ γ₀) c L
      fun δ hδ => (hL δ (List.mem_cons_of_mem _ hδ)).2
    have h1 := (eltOr_sub_one_raises F (by omega : 0 ≤ φ γ) (c γ)).mono hγφ
    rw [Raises.apply_eq_zero (h1.mul h2) (by omega), add_zero]
    by_cases hγ : IsRoot τ γ
    · rw [eltOr_of_isRoot F R hγ, elt_sub_one, LinearMap.sum_apply, Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      obtain ⟨hk1, hk4⟩ := Finset.mem_Ico.1 hk
      rw [LinearMap.smul_apply, Finsupp.smul_apply]
      by_contra hne
      have hD := F.mapsLabelWt_D (R := R) ⟨γ, hγ⟩ hk1 a b (right_ne_zero_of_smul hne)
      rw [hab] at hD
      have hv : γ₀ = k • γ := add_left_cancel hD
      have hφv : φ γ₀ = k * φ γ := by rw [hv, map_nsmul, nsmul_eq_mul]
      have hk1' : k = 1 := by
        have : (k : ℤ) * φ γ ≤ φ γ := by rw [← hφv]; exact hγφ
        have hk : (k : ℤ) ≤ 1 := by nlinarith
        omega
      subst hk1'
      exact hγne (by rw [hv, one_nsmul])
    · rw [eltOr_of_not_isRoot F R hγ, sub_self, LinearMap.zero_apply, Finsupp.zero_apply]

theorem prod_apply_of_shift {γ₀ : Fin τ.rank → ℤ} (h₀ : IsRoot τ γ₀) (h₀φ : 1 ≤ φ γ₀)
    (c : (Fin τ.rank → ℤ) → R) {a b : Label τ} (hab : labelWt τ a = labelWt τ b + γ₀)
    (L : List (Fin τ.rank → ℤ)) (hL : ∀ γ ∈ L, γ ≠ γ₀ ∧ φ γ₀ ≤ φ γ) :
    ((γ₀ :: L).map fun γ => eltOr F R γ (c γ)).prod (Finsupp.single b 1) a =
      c γ₀ * F.D R ⟨γ₀, h₀⟩ 1 (Finsupp.single b 1) a := by
  rw [List.map_cons, List.prod_cons]
  have hXP : ∀ X P : Module.End R (RootModule τ R), X * P = X + (P - 1) + (X - 1) * (P - 1) := by
    intro X P
    simp only [mul_sub, sub_mul, one_mul, mul_one]
    abel
  have hφab : φ (labelWt τ a) = φ (labelWt τ b) + φ γ₀ := by rw [hab, map_add]
  have h2 := prod_sub_one_raises F (by omega : (0 : ℤ) ≤ φ γ₀) c L fun δ hδ => (hL δ hδ).2
  have h1 := eltOr_sub_one_raises F (by omega : 0 ≤ φ γ₀) (c γ₀)
  rw [hXP, LinearMap.add_apply, LinearMap.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    prod_sub_one_apply_eq_zero F h₀ h₀φ c hab L hL,
    Raises.apply_eq_zero (h1.mul h2) (by omega), add_zero, add_zero,
    eltOr_of_isRoot F R h₀, elt_apply_of_shift F ⟨γ₀, h₀⟩ (c γ₀) hab]

omit φ in
theorem exists_D_one_apply_ne_zero [Nontrivial R] (α : Root τ) :
    ∃ a b : Label τ, F.D R α 1 (Finsupp.single b 1) a ≠ 0 := by
  by_contra h
  push Not at h
  have hD0 : F.D R α 1 = 0 :=
    Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => by simpa using h a b)
  obtain ⟨j, ε, w, hε, hw⟩ := RootOperatorFamily'.exists_D_eq_word F α
  set W := (w.map fun i => weylElt τ R i 1).prod
  have h1 : (W : Module.End R (RootModule τ R)) * xCoeff τ R j 1 *
      ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) = 0 := by
    have := hw R 1
    rw [hD0, pow_one] at this
    have h2 := congrArg (((ε : ℤ) : R) • ·) this
    simp only [smul_zero, smul_smul, ← Int.cast_mul, show ε * ε = 1 by
      rcases hε with rfl | rfl <;> norm_num, Int.cast_one, one_smul] at h2
    exact h2.symm
  have h3 : xCoeff τ R j 1 = 0 := by
    have := congrArg (fun A => ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) * A * (W : Module.End R (RootModule τ R))) h1
    simpa [mul_assoc] using this
  have h4 := congrArg (fun A : Module.End R (RootModule τ R) =>
    A (rootVec τ R (-Pi.single j 1)) (Sum.inl j)) h3
  simp [xCoeff_one, infE_rootVec_neg_single, hVec] at h4

theorem prod_eltOr_injective {K : Type} [Field K] :
    ∀ L : List (Fin τ.rank → ℤ), L.Nodup → (∀ γ ∈ L, IsRoot τ γ ∧ 0 < φ γ) →
      L.Pairwise (fun γ δ => φ γ ≤ φ δ) → ∀ c c' : (Fin τ.rank → ℤ) → K,
        (L.map fun γ => eltOr F K γ (c γ)).prod = (L.map fun γ => eltOr F K γ (c' γ)).prod →
          ∀ γ ∈ L, c γ = c' γ
  | [], _, _, _, _, _, _ => by simp
  | γ₀ :: L, hnd, hL, hsort, c, c', heq => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hsort₀, hsort'⟩ := List.pairwise_cons.1 hsort
    obtain ⟨h₀, h₀φ⟩ := hL γ₀ List.mem_cons_self
    have hL' : ∀ γ ∈ L, γ ≠ γ₀ ∧ φ γ₀ ≤ φ γ := fun γ hγ =>
      ⟨fun h => hnot (h ▸ hγ), hsort₀ γ hγ⟩
    obtain ⟨a, b, hab⟩ := exists_D_one_apply_ne_zero F (R := K) ⟨γ₀, h₀⟩
    have hshift : labelWt τ a = labelWt τ b + γ₀ := by
      have := F.mapsLabelWt_D (R := K) ⟨γ₀, h₀⟩ le_rfl a b hab
      rwa [one_nsmul] at this
    have hc₀ : c γ₀ = c' γ₀ := by
      have := congrArg (fun A : Module.End K (RootModule τ K) => A (Finsupp.single b 1) a) heq
      rw [prod_apply_of_shift F h₀ h₀φ c hshift L hL',
        prod_apply_of_shift F h₀ h₀φ c' hshift L hL'] at this
      exact mul_right_cancel₀ hab this
    have heq' : (L.map fun γ => eltOr F K γ (c γ)).prod =
        (L.map fun γ => eltOr F K γ (c' γ)).prod := by
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hc₀] at heq
      have := congrArg (fun A => F.elt K ⟨γ₀, h₀⟩ (-c' γ₀) * A) heq
      simp only [eltOr_of_isRoot F K h₀, ← mul_assoc, F.elt_neg_mul_elt, one_mul] at this
      exact this
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact hc₀
    · exact prod_eltOr_injective L hnd' (fun δ hδ => hL δ (List.mem_cons_of_mem _ hδ)) hsort' c
        c' heq' γ hγ

end RootOperatorFamily'

section Groups

variable (F : RootOperatorFamily τ) (K : Type) [Field K]

@[expose] def endHom : adjointGroup τ K →* Module.End K (RootModule τ K) :=
  (Units.coeHom (Module.End K (RootModule τ K))).comp (adjointGroup τ K).subtype

variable {K}

@[simp] theorem endHom_apply (g : adjointGroup τ K) :
    endHom K g = ((g : ModGL τ K) : Module.End K (RootModule τ K)) := rfl

theorem endHom_injective : Function.Injective (endHom (τ := τ) K) := fun _ _ hgh =>
  Subtype.ext (Units.ext hgh)

theorem endHom_eq_one {g : adjointGroup τ K} (h : endHom K g = 1) : g = 1 :=
  endHom_injective (h.trans (map_one _).symm)

variable (K)

open _root_.Classical in
@[expose] def rootGroup (γ : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  if h : IsRoot τ γ then F.rootSubgroup K ⟨γ, h⟩ else ⊥

@[expose] def torusHom (i : Fin τ.rank) : Kˣ →* adjointGroup τ K where
  toFun t := torusElement τ K i t
  map_one' := Subtype.ext (torusElt_one i)
  map_mul' t u := Subtype.ext (torusElt_mul i t u)

@[expose] def torus (i : Fin τ.rank) : Subgroup (adjointGroup τ K) := (torusHom K i).range

variable {F K}

theorem rootGroup_of_isRoot {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    rootGroup F K γ = F.rootSubgroup K ⟨γ, h⟩ := by
  classical
  exact dite_eq_left h

theorem rootGroup_of_not_isRoot {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ) : rootGroup F K γ = ⊥ := by
  classical
  exact dite_eq_right h

theorem endHom_eltElement (α : Root τ) (c : K) : endHom K (F.eltElement α c) = F.elt K α c :=
  rfl

theorem exists_of_mem_rootGroup {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) {g : adjointGroup τ K}
    (hg : g ∈ rootGroup F K γ) : ∃ c : K, g = F.eltElement ⟨γ, h⟩ c := by
  rw [rootGroup_of_isRoot h] at hg
  obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hg
  exact ⟨c, rfl⟩

theorem mem_torus {i : Fin τ.rank} {g : adjointGroup τ K} :
    g ∈ torus K i ↔ ∃ t : Kˣ, torusElement τ K i t = g :=
  Iff.rfl

variable (φ : (Fin τ.rank → ℤ) →+ ℤ)

@[expose] def IsDiag (A : Module.End K (RootModule τ K)) : Prop :=
  ∀ b : Label τ, ∃ μ : K, A (Finsupp.single b 1) = μ • Finsupp.single b 1

theorem IsDiag.mul {A B : Module.End K (RootModule τ K)} (hA : IsDiag A) (hB : IsDiag B) :
    IsDiag (A * B) := fun b => by
  obtain ⟨μ, hμ⟩ := hB b
  obtain ⟨ν, hν⟩ := hA b
  exact ⟨μ * ν, by rw [Module.End.mul_apply, hμ, map_smul, hν, smul_smul]⟩

theorem IsDiag.raises {A : Module.End K (RootModule τ K)} (hA : IsDiag A) : Raises φ 0 A :=
  fun a b hab => by
    obtain ⟨μ, hμ⟩ := hA b
    rw [hμ, Finsupp.smul_apply, Finsupp.single_apply] at hab
    split_ifs at hab with h
    · subst h
      omega
    · simp at hab

@[expose] def unip : Subgroup (adjointGroup τ K) where
  carrier := {g | Raises φ 1 (endHom K g - 1) ∧ Raises φ 1 (endHom K g⁻¹ - 1)}
  mul_mem' {_ _} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, RootOperatorFamily'.mul_sub_one]
      exact (hg.1.add hh.1).add ((hg.1.mul hh.1).mono (by omega))
    · rw [mul_inv_rev, map_mul, RootOperatorFamily'.mul_sub_one]
      exact (hh.2.add hg.2).add ((hh.2.mul hg.2).mono (by omega))
  one_mem' := ⟨by simpa using Raises.zero (R := K) (τ := τ) (φ := φ) 1,
    by simpa using Raises.zero (R := K) (τ := τ) (φ := φ) 1⟩
  inv_mem' {_} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

@[expose] def tri : Subgroup (adjointGroup τ K) where
  carrier := {g | Raises φ 0 (endHom K g) ∧ Raises φ 0 (endHom K g⁻¹)}
  mul_mem' {_ _} hg hh :=
    ⟨by rw [map_mul]; exact (hg.1.mul hh.1).mono (by omega),
      by rw [mul_inv_rev, map_mul]; exact (hh.2.mul hg.2).mono (by omega)⟩
  one_mem' := ⟨by rw [map_one]; exact (IsDiag.raises φ fun b => ⟨1, by simp⟩),
    by rw [inv_one, map_one]; exact (IsDiag.raises φ fun b => ⟨1, by simp⟩)⟩
  inv_mem' {_} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

variable (K) in
@[expose] def diag : Subgroup (adjointGroup τ K) where
  carrier := {g | IsDiag (endHom K g) ∧ IsDiag (endHom K g⁻¹)}
  mul_mem' {_ _} hg hh :=
    ⟨by rw [map_mul]; exact hg.1.mul hh.1, by rw [mul_inv_rev, map_mul]; exact hh.2.mul hg.2⟩
  one_mem' := ⟨fun _ => ⟨1, by simp⟩, fun _ => ⟨1, by simp⟩⟩
  inv_mem' {_} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem one_raises_zero : Raises φ 0 (1 : Module.End K (RootModule τ K)) :=
  IsDiag.raises φ fun b => ⟨1, by simp⟩

theorem unip_le_tri : unip (K := K) φ ≤ tri φ := fun g hg => by
  have h1 : endHom K g = 1 + (endHom K g - 1) := by abel
  have h2 : endHom K g⁻¹ = 1 + (endHom K g⁻¹ - 1) := by abel
  exact ⟨by rw [h1]; exact (one_raises_zero φ).add (hg.1.mono (by omega)),
    by rw [h2]; exact (one_raises_zero φ).add (hg.2.mono (by omega))⟩

theorem diag_le_tri : diag K ≤ tri (K := K) φ := fun _ hg => ⟨hg.1.raises φ, hg.2.raises φ⟩

theorem torus_le_diag (i : Fin τ.rank) : torus K i ≤ diag K := by
  rintro _ ⟨t, rfl⟩
  refine ⟨fun b => ⟨_, torusElt_single i t b⟩, fun b => ?_⟩
  have : (torusHom K i t)⁻¹ = torusHom K i t⁻¹ := (map_inv _ t).symm
  rw [this]
  exact ⟨_, torusElt_single i t⁻¹ b⟩

theorem rootGroup_le_unip {γ : Fin τ.rank → ℤ} (hγ : 0 < φ γ) : rootGroup F K γ ≤ unip φ := by
  by_cases h : IsRoot τ γ
  · intro g hg
    obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup h hg
    have hinv : (F.eltElement ⟨γ, h⟩ c)⁻¹ = F.eltElement ⟨γ, h⟩ (-c) := by
      rw [eq_comm, eq_inv_iff_mul_eq_one, ← F.eltElement_add, neg_add_cancel, F.eltElement_zero]
    refine ⟨?_, ?_⟩
    · exact (RootOperatorFamily'.elt_sub_one_raises F ⟨γ, h⟩ hγ.le c).mono
        (show (1 : ℤ) ≤ φ γ by omega)
    · rw [hinv]
      exact (RootOperatorFamily'.elt_sub_one_raises F ⟨γ, h⟩ hγ.le (-c)).mono
        (show (1 : ℤ) ≤ φ γ by omega)
  · rw [rootGroup_of_not_isRoot h]
    exact bot_le

theorem tri_inf_unip_neg : tri (K := K) φ ⊓ unip (-φ) = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨h1, -⟩, h2, -⟩ := hg
  refine Subgroup.mem_bot.2 (endHom_eq_one ?_)
  refine sub_eq_zero.1 (Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_))
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    Finsupp.zero_apply]
  by_contra hne
  have h3 := h2 a b hne
  simp only [AddMonoidHom.neg_apply] at h3
  by_cases hab : a = b
  · subst hab
    omega
  · have hne' : endHom K g (Finsupp.single b 1) a ≠ 0 := by
      rwa [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne hab, sub_zero] at hne
    have := h1 a b hne'
    omega

theorem unip_inf_unip_neg : unip (K := K) φ ⊓ unip (-φ) = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ (unip_le_tri φ)).trans (tri_inf_unip_neg φ).le)

theorem diag_inf_unip : diag K ⊓ unip φ = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨h1, -⟩, h2, -⟩ := hg
  refine Subgroup.mem_bot.2 (endHom_eq_one ?_)
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  obtain ⟨μ, hμ⟩ := h1 b
  rw [hμ]
  by_cases hμ1 : μ = 1
  · rw [hμ1, one_smul]
  · exfalso
    have h3 := h2 b b (by
      rw [LinearMap.sub_apply, hμ, Module.End.one_apply, Finsupp.sub_apply, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
      exact sub_ne_zero.2 hμ1)
    omega

end Groups

end CFSG.LieType.Steinberg.Adjoint
