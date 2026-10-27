module

public import CFSG.ClassicalGroups.Alternating.I4SpDefs
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

@[expose] def Gsp.lin (g : Gsp BN) : N →ₗ[K] N :=
  ((g : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N)

theorem Gsp.lin_apply (g : Gsp BN) (x : N) : g.lin x = g.app x := rfl

@[expose] def IsLine (BN : BilinForm K N) (ℓ : Submodule K N) : Prop :=
  (∀ x ∈ ℓ, ∀ y ∈ ℓ, BN x y = 0) ∧ finrank K ℓ = 2

@[expose] def IsPlane (BN : BilinForm K N) (π : Submodule K N) : Prop :=
  (∀ x ∈ π, ∀ y ∈ π, BN x y = 0) ∧ finrank K π = 3

@[expose] def commSp (H : Subgroup (Gsp BN)) : Submodule K N :=
  Submodule.span K {w | ∃ g ∈ H, ∃ x, w = g.app x - x}

theorem exists_apply_eq_of_linearIndependent [FiniteDimensional K N] (hBNnd : BN.Nondegenerate)
    {ι : Type*} [Fintype ι] {v : ι → N} (hv : LinearIndependent K v) (a : ι → K) :
    ∃ x, ∀ i, BN x (v i) = a i := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr K a)
  refine ⟨(BN.toDual hBNnd).symm g, fun i => ?_⟩
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  have h1 := LinearMap.congr_fun hg (Module.Basis.span hv i)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.constr_basis] at h1
  exact h1

section Calculus

variable (hBN : BN.IsAlt) {σ : Submodule K N} (hσ : ∀ x ∈ σ, ∀ y ∈ σ, BN x y = 0)

include hBN hσ in
theorem lineElt_mul_lineElt_app {a c a' c' : N} (ha : a ∈ σ) (hc : c ∈ σ) (ha' : a' ∈ σ)
    (hc' : c' ∈ σ) (x : N) :
    (lineElt hBN a c * lineElt hBN a' c').app x =
      x + (BN x a • c + BN x c • a) + (BN x a' • c' + BN x c' • a') := by
  have hac : BN a c = 0 := hσ a ha c hc
  have hac' : BN a' c' = 0 := hσ a' ha' c' hc'
  have h1 : BN a' a = 0 := hσ a' ha' a ha
  have h2 : BN c' a = 0 := hσ c' hc' a ha
  have h3 : BN a' c = 0 := hσ a' ha' c hc
  have h4 : BN c' c = 0 := hσ c' hc' c hc
  rw [Gsp.app_mul, lineElt_app hBN hac', lineElt_app hBN hac]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
    h3, h4, mul_zero, add_zero]
  module

include hBN hσ in
theorem lineElt_mul_right {a c c' : N} (ha : a ∈ σ) (hc : c ∈ σ) (hc' : c' ∈ σ) :
    lineElt hBN a c * lineElt hBN a c' = lineElt hBN a (c + c') := by
  have hacc : BN a (c + c') = 0 := by rw [map_add, hσ a ha c hc, hσ a ha c' hc', add_zero]
  refine Gsp.ext' fun x => ?_
  rw [lineElt_mul_lineElt_app hBN hσ ha hc ha hc', lineElt_app hBN hacc]
  simp only [map_add, add_smul, smul_add]
  abel

theorem lineElt_zero_right (a : N) : lineElt hBN a 0 = 1 := by
  refine Gsp.ext' fun x => ?_
  rw [lineElt_app hBN (map_zero (BN a))]
  simp [Gsp.app_one]

theorem lineElt_smul_left {a c : N} (hac : BN a c = 0) (l : K) :
    lineElt hBN (l • a) c = lineElt hBN a (l • c) := by
  have h1 : BN (l • a) c = 0 := by rw [map_smul, LinearMap.smul_apply, hac, smul_zero]
  have h2 : BN a (l • c) = 0 := by rw [map_smul, hac, smul_zero]
  refine Gsp.ext' fun x => ?_
  rw [lineElt_app hBN h1, lineElt_app hBN h2]
  simp only [map_smul, smul_eq_mul]
  module

end Calculus

theorem mul_app_sub_eq {σ : Submodule K N} (hσ : ∀ x ∈ σ, ∀ y ∈ σ, BN x y = 0) {g h : Gsp BN}
    (g2 : ∀ y, (∀ p ∈ σ, BN p y = 0) → g.app y = y) (h1 : ∀ x, h.app x - x ∈ σ) (x : N) :
    (g * h).app x - x = (g.app x - x) + (h.app x - x) := by
  have he : g.app (h.app x - x) = h.app x - x := g2 _ (fun p hp => hσ p hp _ (h1 x))
  have key : g.app (h.app x) = g.app x + (h.app x - x) := by
    have := Gsp.map_add g x (h.app x - x)
    rw [add_sub_cancel, he] at this
    exact this
  rw [Gsp.app_mul, key]
  abel

@[expose] def planeSub (hBN : BN.IsAlt) {σ : Submodule K N}
    (hσ : ∀ x ∈ σ, ∀ y ∈ σ, BN x y = 0) : Subgroup (Gsp BN) where
  carrier := {g | (∀ x, g.app x - x ∈ σ) ∧ (∀ y, (∀ p ∈ σ, BN p y = 0) → g.app y = y) ∧
    ∀ x, BN x (g.app x - x) = 0}
  one_mem' := ⟨fun x => by simp [Gsp.app_one], fun y _ => Gsp.app_one y,
    fun x => by simp [Gsp.app_one]⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    have hadd : ∀ x, (g * h).app x - x = (g.app x - x) + (h.app x - x) :=
      mul_app_sub_eq hσ g2 h1
    refine ⟨fun x => ?_, fun y hy => ?_, fun x => ?_⟩
    · rw [hadd]; exact σ.add_mem (g1 x) (h1 x)
    · rw [Gsp.app_mul, h2 y hy, g2 y hy]
    · rw [hadd, map_add, g3, h3, add_zero]
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    have hsurj : ∀ x, ∃ y, x = g.app y := fun x => ⟨g⁻¹.app x, (Gsp.app_app_inv g x).symm⟩
    refine ⟨fun x => ?_, fun y hy' => ?_, fun x => ?_⟩
    · obtain ⟨y, rfl⟩ := hsurj x
      rw [Gsp.app_inv_app, ← neg_sub]
      exact σ.neg_mem (g1 y)
    · calc g⁻¹.app y = g⁻¹.app (g.app y) := by rw [g2 y hy']
        _ = y := Gsp.app_inv_app g y
    · obtain ⟨y, rfl⟩ := hsurj x
      have hx' : BN (g.app y) (g.app y - y) = 0 := by
        have e1 : g.app y = (g.app y - y) + y := by abel
        calc BN (g.app y) (g.app y - y) = BN ((g.app y - y) + y) (g.app y - y) := by rw [← e1]
          _ = BN (g.app y - y) (g.app y - y) + BN y (g.app y - y) := by
            rw [map_add, LinearMap.add_apply]
          _ = 0 := by rw [hBN.self_eq_zero, g3 y, add_zero]
      rw [Gsp.app_inv_app, ← neg_sub, map_neg, hx', neg_zero]

section PlaneGroup

variable (hBN : BN.IsAlt) {σ : Submodule K N} (hσ : ∀ x ∈ σ, ∀ y ∈ σ, BN x y = 0)

theorem lineElt_mem_planeGroup {a c : N} (ha : a ∈ σ) (hc : c ∈ σ) :
    lineElt hBN a c ∈ planeGroup hBN σ :=
  Subgroup.subset_closure ⟨a, ha, c, hc, rfl⟩

theorem planeGroup_mono {σ σ' : Submodule K N} (h : σ ≤ σ') :
    planeGroup hBN σ ≤ planeGroup hBN σ' := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨a, ha, c, hc, rfl⟩
  exact ⟨a, h ha, c, h hc, rfl⟩

include hBN hσ in
theorem planeGroup_le_planeSub [CharP K 2] : planeGroup hBN σ ≤ planeSub hBN hσ := by
  rw [planeGroup, Subgroup.closure_le]
  rintro _ ⟨a, ha, c, hc, rfl⟩
  have hac : BN a c = 0 := hσ a ha c hc
  refine ⟨fun x => ?_, fun y hy => ?_, fun x => ?_⟩
  · rw [lineElt_app hBN hac, add_assoc, add_sub_cancel_left]
    exact σ.add_mem (σ.smul_mem _ hc) (σ.smul_mem _ ha)
  · have h1 : BN y a = 0 := by rw [← hBN.neg_eq a y, hy a ha, neg_zero]
    have h2 : BN y c = 0 := by rw [← hBN.neg_eq c y, hy c hc, neg_zero]
    rw [lineElt_app hBN hac, h1, h2, zero_smul, zero_smul, add_zero, add_zero]
  · rw [lineElt_app hBN hac, add_assoc, add_sub_cancel_left]
    simp only [map_add, map_smul, smul_eq_mul]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (BN x a * BN x c) * h2

include hBN hσ in
theorem mul_comm_of_mem_planeGroup [CharP K 2] {g h : Gsp BN} (hg : g ∈ planeGroup hBN σ)
    (hh : h ∈ planeGroup hBN σ) : g * h = h * g := by
  obtain ⟨g1, g2, -⟩ := planeGroup_le_planeSub hBN hσ hg
  obtain ⟨h1, h2, -⟩ := planeGroup_le_planeSub hBN hσ hh
  refine Gsp.ext' fun x => ?_
  have e1 := mul_app_sub_eq hσ g2 h1 x
  have e2 := mul_app_sub_eq hσ h2 g1 x
  rw [add_comm] at e2
  have := e1.trans e2.symm
  exact sub_left_injective this

end PlaneGroup

structure PlaneFrame (BN : BilinForm K N) (π : Submodule K N) where
  e : Fin 3 → N
  f : Fin 3 → N
  mem : ∀ i, e i ∈ π
  span : ∀ w ∈ π, ∃ a b c : K, w = a • e 0 + b • e 1 + c • e 2
  dual : ∀ i j, BN (f i) (e j) = if i = j then 1 else 0

theorem exists_planeFrame [FiniteDimensional K N] (hBNnd : BN.Nondegenerate) {π : Submodule K N}
    (hπ : IsPlane BN π) : Nonempty (PlaneFrame BN π) := by
  have : Module.Finite K π := Module.finite_of_finrank_pos (by rw [hπ.2]; norm_num)
  let b : Module.Basis (Fin 3) K π := Module.finBasisOfFinrankEq K π hπ.2
  have hli : LinearIndependent K (fun i => (b i : N)) :=
    b.linearIndependent.map' π.subtype (Submodule.ker_subtype π)
  have hf : ∀ i : Fin 3, ∃ x : N, ∀ j : Fin 3, BN x (b j : N) = if i = j then 1 else 0 :=
    fun i => exists_apply_eq_of_linearIndependent hBNnd hli _
  choose f hf using hf
  refine ⟨⟨fun i => (b i : N), f, fun i => (b i).2, fun w hw => ?_, hf⟩⟩
  refine ⟨b.repr ⟨w, hw⟩ 0, b.repr ⟨w, hw⟩ 1, b.repr ⟨w, hw⟩ 2, ?_⟩
  have h := b.sum_repr ⟨w, hw⟩
  rw [Fin.sum_univ_three] at h
  have h' := congrArg (fun x : π => (x : N)) h
  simpa using h'.symm

namespace PlaneFrame

variable {π : Submodule K N} (F : PlaneFrame BN π)

theorem eq_zero_of_add_eq_zero {a b c : K} (h : a • F.e 0 + b • F.e 1 + c • F.e 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ j, a * BN (F.f j) (F.e 0) + b * BN (F.f j) (F.e 1) + c * BN (F.f j) (F.e 2) = 0 :=
    fun j => by
      have := congrArg (BN (F.f j)) h
      simpa only [map_add, map_smul, smul_eq_mul, map_zero] using this
  refine ⟨?_, ?_, ?_⟩
  · simpa [F.dual] using key 0
  · simpa [F.dual] using key 1
  · simpa [F.dual] using key 2

theorem coord {w : N} (hw : w ∈ π) :
    w = BN (F.f 0) w • F.e 0 + BN (F.f 1) w • F.e 1 + BN (F.f 2) w • F.e 2 := by
  obtain ⟨a, b, c, rfl⟩ := F.span w hw
  simp only [map_add, map_smul, smul_eq_mul, F.dual]
  simp

variable (hBN : BN.IsAlt)

include hBN in
theorem decomp (x : N) : ∃ z : N, (∀ p ∈ π, BN p z = 0) ∧
    x = BN x (F.e 0) • F.f 0 + BN x (F.e 1) • F.f 1 + BN x (F.e 2) • F.f 2 + z := by
  refine ⟨x - (BN x (F.e 0) • F.f 0 + BN x (F.e 1) • F.f 1 + BN x (F.e 2) • F.f 2), ?_, by abel⟩
  have hz : ∀ j, BN (x - (BN x (F.e 0) • F.f 0 + BN x (F.e 1) • F.f 1 + BN x (F.e 2) • F.f 2))
      (F.e j) = 0 := by
    intro j
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, F.dual]
    fin_cases j <;> simp
  intro p hp
  obtain ⟨a, b, c, rfl⟩ := F.span p hp
  have hz' : ∀ j, BN (F.e j) (x - (BN x (F.e 0) • F.f 0 + BN x (F.e 1) • F.f 1 +
      BN x (F.e 2) • F.f 2)) = 0 := fun j => by
    rw [← hBN.neg_eq, hz j, neg_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hz']
  simp

@[expose] noncomputable def phi (hBN : BN.IsAlt) (a b c : K) : Gsp BN :=
  lineElt hBN (F.e 0) (a • F.e 1 + b • F.e 2) * lineElt hBN (F.e 1) (c • F.e 2)

variable (hπ : ∀ x ∈ π, ∀ y ∈ π, BN x y = 0)

include hBN hπ in
theorem phi_app (a b c : K) (x : N) :
    (F.phi hBN a b c).app x = x + a • (BN x (F.e 0) • F.e 1 + BN x (F.e 1) • F.e 0) +
      b • (BN x (F.e 0) • F.e 2 + BN x (F.e 2) • F.e 0) +
        c • (BN x (F.e 1) • F.e 2 + BN x (F.e 2) • F.e 1) := by
  have h1 : a • F.e 1 + b • F.e 2 ∈ π :=
    π.add_mem (π.smul_mem _ (F.mem 1)) (π.smul_mem _ (F.mem 2))
  rw [phi, lineElt_mul_lineElt_app hBN hπ (F.mem 0) h1 (F.mem 1) (π.smul_mem c (F.mem 2)) x]
  simp only [map_add, map_smul, smul_eq_mul]
  module

include hBN hπ in
theorem phi_form_app (a b c : K) (x : N) (j : Fin 3) :
    BN ((F.phi hBN a b c).app x) (F.e j) = BN x (F.e j) := by
  have h : ∀ i, BN (F.e i) (F.e j) = 0 := fun i => hπ _ (F.mem i) _ (F.mem j)
  rw [phi_app F hBN hπ]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h,
    mul_zero, add_zero]

include hBN hπ in
theorem phi_mul (a b c a' b' c' : K) :
    F.phi hBN a b c * F.phi hBN a' b' c' = F.phi hBN (a + a') (b + b') (c + c') := by
  refine Gsp.ext' fun x => ?_
  rw [Gsp.app_mul, phi_app F hBN hπ a b c ((F.phi hBN a' b' c').app x)]
  simp only [phi_form_app F hBN hπ]
  rw [phi_app F hBN hπ a' b' c' x, phi_app F hBN hπ (a + a') (b + b') (c + c') x]
  module

include hBN hπ in
theorem phi_zero : F.phi hBN 0 0 0 = 1 := by
  refine Gsp.ext' fun x => ?_
  rw [phi_app F hBN hπ, Gsp.app_one]
  simp

include hBN hπ in
theorem phi_eq_one_iff {a b c : K} : F.phi hBN a b c = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  refine ⟨fun h => ?_, fun ⟨ha, hb, hc⟩ => by rw [ha, hb, hc, phi_zero F hBN hπ]⟩
  have h0 := congrArg (fun g : Gsp BN => g.app (F.f 0)) h
  have h1 := congrArg (fun g : Gsp BN => g.app (F.f 1)) h
  simp only [phi_app F hBN hπ, Gsp.app_one, F.dual] at h0 h1
  simp at h0 h1
  have e0 : a • F.e 1 + b • F.e 2 = 0 := by simpa [add_assoc] using h0
  have hab := F.eq_zero_of_add_eq_zero (a := 0) (b := a) (c := b) (by simpa using e0)
  have e1 : c • F.e 2 = 0 := by
    have := h1
    rw [hab.2.1] at this
    simpa using this
  have hc := F.eq_zero_of_add_eq_zero (a := 0) (b := 0) (c := c) (by simpa using e1)
  exact ⟨hab.2.1, hab.2.2, hc.2.2⟩

include hBN in
theorem phi_mem_planeGroup (a b c : K) : F.phi hBN a b c ∈ planeGroup hBN π :=
  mul_mem (lineElt_mem_planeGroup hBN (F.mem 0)
    (π.add_mem (π.smul_mem _ (F.mem 1)) (π.smul_mem _ (F.mem 2))))
    (lineElt_mem_planeGroup hBN (F.mem 1) (π.smul_mem _ (F.mem 2)))

include hBN hπ in
theorem exists_phi_eq [CharP K 2] {g : Gsp BN} (hg : g ∈ planeSub hBN hπ) :
    ∃ a b c : K, g = F.phi hBN a b c := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨m, hm⟩ : ∃ m : Fin 3 → Fin 3 → K,
      ∀ i j, BN (F.f j) (g.app (F.f i) - F.f i) = m i j :=
    ⟨fun i j => BN (F.f j) (g.app (F.f i) - F.f i), fun _ _ => rfl⟩
  have hE : ∀ i, g.app (F.f i) = F.f i + (m i 0 • F.e 0 + m i 1 • F.e 1 + m i 2 • F.e 2) := by
    intro i
    have := F.coord (g1 (F.f i))
    rw [hm i 0, hm i 1, hm i 2] at this
    rw [← this]
    abel
  have hdiag : ∀ i, m i i = 0 := fun i => by rw [← hm i i]; exact g3 (F.f i)
  have hsym : ∀ i j, m i j = m j i := by
    intro i j
    have h := g3 (F.f i + F.f j)
    have hd : g.app (F.f i + F.f j) - (F.f i + F.f j) =
        (g.app (F.f i) - F.f i) + (g.app (F.f j) - F.f j) := by
      rw [Gsp.map_add]; abel
    rw [hd] at h
    simp only [map_add, LinearMap.add_apply] at h
    rw [g3 (F.f i), g3 (F.f j), hm j i, hm i j] at h
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h - (m j i) * h2
  refine ⟨m 0 1, m 0 2, m 1 2, Gsp.ext' fun x => ?_⟩
  obtain ⟨z, hz, hx⟩ := F.decomp hBN x
  rw [phi_app F hBN hπ]
  generalize BN x (F.e 0) = p0 at hx ⊢
  generalize BN x (F.e 1) = p1 at hx ⊢
  generalize BN x (F.e 2) = p2 at hx ⊢
  subst hx
  simp only [Gsp.map_add, Gsp.map_smul, g2 z hz, hE]
  rw [hdiag 0, hdiag 1, hdiag 2, hsym 1 0, hsym 2 0, hsym 2 1]
  module

@[expose] noncomputable def phiHom (hBN : BN.IsAlt) (hπ : ∀ x ∈ π, ∀ y ∈ π, BN x y = 0) :
    Multiplicative (K × K × K) →* Gsp BN where
  toFun t := F.phi hBN t.toAdd.1 t.toAdd.2.1 t.toAdd.2.2
  map_one' := by simpa using phi_zero F hBN hπ
  map_mul' s t := by
    simpa using (phi_mul F hBN hπ s.toAdd.1 s.toAdd.2.1 s.toAdd.2.2 t.toAdd.1 t.toAdd.2.1
      t.toAdd.2.2).symm

theorem phiHom_injective (hBN : BN.IsAlt) (hπ : ∀ x ∈ π, ∀ y ∈ π, BN x y = 0) :
    Function.Injective (F.phiHom hBN hπ) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  obtain ⟨a, b, c⟩ := t.toAdd
  have : F.phi hBN t.toAdd.1 t.toAdd.2.1 t.toAdd.2.2 = 1 := ht
  have h := (phi_eq_one_iff F hBN hπ).mp this
  apply Multiplicative.toAdd.injective
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem range_phiHom [CharP K 2] (hBN : BN.IsAlt) (hπ : ∀ x ∈ π, ∀ y ∈ π, BN x y = 0) :
    (F.phiHom hBN hπ).range = planeGroup hBN π := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact phi_mem_planeGroup F hBN _ _ _
  · intro g hg
    obtain ⟨a, b, c, rfl⟩ := exists_phi_eq F hBN hπ (planeGroup_le_planeSub hBN hπ hg)
    exact ⟨Multiplicative.ofAdd (a, b, c), rfl⟩

include hBN hπ in
theorem exists_lineElt_eq_phi [CharP K 2] {a b c : K} (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    ∃ u ∈ π, ∃ v ∈ π, LinearIndependent K ![u, v] ∧ F.phi hBN a b c = lineElt hBN u v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hc : c = 0
  · subst hc
    have hab : ¬ (a = 0 ∧ b = 0) := fun h => hne ⟨h.1, h.2, rfl⟩
    have hv : a • F.e 1 + b • F.e 2 ∈ π :=
      π.add_mem (π.smul_mem _ (F.mem 1)) (π.smul_mem _ (F.mem 2))
    refine ⟨F.e 0, F.mem 0, _, hv, ?_, ?_⟩
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have h := F.eq_zero_of_add_eq_zero (a := s) (b := t * a) (c := t * b)
        (by rw [← hst]; module)
      refine ⟨h.1, ?_⟩
      by_contra ht
      exact hab ⟨(mul_eq_zero.mp h.2.1).resolve_left ht, (mul_eq_zero.mp h.2.2).resolve_left ht⟩
    · refine Gsp.ext' fun x => ?_
      rw [phi_app F hBN hπ, lineElt_app hBN (hπ _ (F.mem 0) _ hv)]
      simp only [map_add, map_smul, smul_eq_mul]
      module
  · obtain ⟨r, rfl⟩ : ∃ r, b = c * r := ⟨b / c, (mul_div_cancel₀ b hc).symm⟩
    have hu : r • F.e 0 + F.e 1 ∈ π := π.add_mem (π.smul_mem _ (F.mem 0)) (F.mem 1)
    have hv : a • F.e 0 + c • F.e 2 ∈ π :=
      π.add_mem (π.smul_mem _ (F.mem 0)) (π.smul_mem _ (F.mem 2))
    refine ⟨_, hu, _, hv, ?_, ?_⟩
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have h := F.eq_zero_of_add_eq_zero (a := s * r + t * a) (b := s) (c := t * c)
        (by rw [← hst]; module)
      have hs : s = 0 := h.2.1
      exact ⟨hs, (mul_eq_zero.mp h.2.2).resolve_right hc⟩
    · refine Gsp.ext' fun x => ?_
      rw [phi_app F hBN hπ, lineElt_app hBN (hπ _ hu _ hv)]
      simp only [map_add, map_smul, smul_eq_mul]
      linear_combination (norm := module) (-(a * r * BN x (F.e 0))) • (h2 • F.e 0)

end PlaneFrame

section Plane

variable [CharP K 2] [FiniteDimensional K N] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
  {π : Submodule K N} (hπ : IsPlane BN π)

include hBN hBNnd hπ in
theorem card_planeGroup_of_isPlane : Nat.card (planeGroup hBN π) = Nat.card K ^ 3 := by
  obtain ⟨F⟩ := exists_planeFrame hBNnd hπ
  rw [← F.range_phiHom hBN hπ.1,
    Nat.card_congr (MonoidHom.ofInjective (F.phiHom_injective hBN hπ.1)).toEquiv.symm,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod]
  ring

include hBN hBNnd hπ in
theorem eq_lineElt_of_mem_planeGroup {g : Gsp BN} (hg : g ∈ planeGroup hBN π) (hg1 : g ≠ 1) :
    ∃ a ∈ π, ∃ c ∈ π, LinearIndependent K ![a, c] ∧ g = lineElt hBN a c := by
  obtain ⟨F⟩ := exists_planeFrame hBNnd hπ
  obtain ⟨a, b, c, rfl⟩ := F.exists_phi_eq hBN hπ.1 (planeGroup_le_planeSub hBN hπ.1 hg)
  refine F.exists_lineElt_eq_phi hBN hπ.1 fun h => hg1 ?_
  rw [h.1, h.2.1, h.2.2, F.phi_zero hBN hπ.1]

end Plane

section Line

variable (hBN : BN.IsAlt)

include hBN in
theorem isotropic_span_pair {a c : N} (hac : BN a c = 0) :
    ∀ x ∈ Submodule.span K {a, c}, ∀ y ∈ Submodule.span K {a, c}, BN x y = 0 := by
  have hca : BN c a = 0 := by rw [← hBN.neg_eq a c, hac, neg_zero]
  intro x hx y hy
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp [hac, hca, hBN.self_eq_zero]

@[expose] noncomputable def lineHom {a c : N} (hac : BN a c = 0) : Multiplicative K →* Gsp BN where
  toFun l := lineElt hBN a (l.toAdd • c)
  map_one' := by simpa using lineElt_zero_right hBN a
  map_mul' s t := by
    have hσ := isotropic_span_pair hBN hac
    have ha : a ∈ Submodule.span K {a, c} := Submodule.subset_span (by simp)
    have hc : c ∈ Submodule.span K {a, c} := Submodule.subset_span (by simp)
    have := lineElt_mul_right hBN hσ ha ((Submodule.span K {a, c}).smul_mem s.toAdd hc)
      ((Submodule.span K {a, c}).smul_mem t.toAdd hc)
    simp only [toAdd_mul, add_smul]
    exact this.symm

theorem lineGroup_eq_range {a c : N} (hac : BN a c = 0) :
    lineGroup hBN a c = (lineHom hBN hac).range := by
  refine le_antisymm ?_ ?_
  · rw [lineGroup, Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨Multiplicative.ofAdd l, rfl⟩
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨t.toAdd, rfl⟩

theorem mem_lineGroup_iff {a c : N} (hac : BN a c = 0) {g : Gsp BN} :
    g ∈ lineGroup hBN a c ↔ ∃ l : K, g = lineElt hBN a (l • c) := by
  rw [lineGroup_eq_range hBN hac]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨Multiplicative.ofAdd l, rfl⟩

theorem lineHom_injective [FiniteDimensional K N] (hBNnd : BN.Nondegenerate) {a c : N}
    (hac : BN a c = 0) (hind : LinearIndependent K ![a, c]) :
    Function.Injective (lineHom hBN hac) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  obtain ⟨x, hx⟩ := exists_apply_eq_of_linearIndependent hBNnd hind ![1, 0]
  have hxa : BN x a = 1 := by simpa using hx 0
  have hxc : BN x c = 0 := by simpa using hx 1
  have hc0 : c ≠ 0 := by simpa using hind.ne_zero (1 : Fin 2)
  have h1 : lineElt hBN a (t.toAdd • c) = 1 := ht
  have h2 := congrArg (fun g : Gsp BN => g.app x) h1
  simp only [lineElt_app hBN (show BN a (t.toAdd • c) = 0 by rw [map_smul, hac, smul_zero]),
    Gsp.app_one, map_smul, hxa, hxc, smul_eq_mul, mul_zero, zero_smul, add_zero, one_smul] at h2
  have h3 : t.toAdd • c = 0 := by
    have := h2
    simpa [add_eq_left] using this
  exact Multiplicative.toAdd.injective ((smul_eq_zero.mp h3).resolve_right hc0)

theorem card_lineGroup [FiniteDimensional K N] (hBNnd : BN.Nondegenerate) {a c : N}
    (hac : BN a c = 0) (hind : LinearIndependent K ![a, c]) :
    Nat.card (lineGroup hBN a c) = Nat.card K := by
  rw [lineGroup_eq_range hBN hac,
    Nat.card_congr (MonoidHom.ofInjective (lineHom_injective hBN hBNnd hac hind)).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

include hBN in
theorem planeGroup_span_pair [CharP K 2] {a c : N} (hac : BN a c = 0) :
    planeGroup hBN (Submodule.span K {a, c}) = lineGroup hBN a c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha : a ∈ Submodule.span K {a, c} := Submodule.subset_span (by simp)
  have hc : c ∈ Submodule.span K {a, c} := Submodule.subset_span (by simp)
  have hσ := isotropic_span_pair hBN hac
  refine le_antisymm ?_ ?_
  · rw [planeGroup, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
    refine (mem_lineGroup_iff hBN hac).mpr ⟨α * δ + β * γ, Gsp.ext' fun v => ?_⟩
    rw [lineElt_app hBN (hσ _ hx _ hy), lineElt_app hBN (by rw [map_smul, hac, smul_zero])]
    simp only [map_add, map_smul, smul_eq_mul]
    linear_combination (norm := module) (α * γ * BN v a) • (h2 • a) +
      (β * δ * BN v c) • (h2 • c)
  · rw [lineGroup, Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact lineElt_mem_planeGroup hBN ha ((Submodule.span K {a, c}).smul_mem l hc)

include hBN in
theorem lineGroup_eq_of_span_eq [CharP K 2] {a c a' c' : N} (hac : BN a c = 0)
    (hac' : BN a' c' = 0) (h : Submodule.span K {a, c} = Submodule.span K {a', c'}) :
    lineGroup hBN a c = lineGroup hBN a' c' := by
  rw [← planeGroup_span_pair hBN hac, ← planeGroup_span_pair hBN hac', h]

theorem IsLine.exists_pair {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    ∃ a c : N, BN a c = 0 ∧ LinearIndependent K ![a, c] ∧ ℓ = Submodule.span K {a, c} := by
  have : Module.Finite K ℓ := Module.finite_of_finrank_pos (by rw [hℓ.2]; norm_num)
  let b : Module.Basis (Fin 2) K ℓ := Module.finBasisOfFinrankEq K ℓ hℓ.2
  have hli : LinearIndependent K (fun i => (b i : N)) :=
    b.linearIndependent.map' ℓ.subtype (Submodule.ker_subtype ℓ)
  refine ⟨b 0, b 1, hℓ.1 _ (b 0).2 _ (b 1).2, ?_, ?_⟩
  · convert hli using 1
    ext i
    fin_cases i <;> rfl
  · apply le_antisymm
    · intro w hw
      have h := b.sum_repr ⟨w, hw⟩
      rw [Fin.sum_univ_two] at h
      have h' := congrArg (fun x : ℓ => (x : N)) h
      simp only [Submodule.coe_add, Submodule.coe_smul] at h'
      rw [← h']
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact (b 0).2
      · exact (b 1).2

end Line

section Comm

variable [CharP K 2] [FiniteDimensional K N] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)

include hBN hBNnd in
theorem card_planeGroup_of_isLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    Nat.card (planeGroup hBN ℓ) = Nat.card K := by
  obtain ⟨a, c, hac, hind, rfl⟩ := hℓ.exists_pair
  rw [planeGroup_span_pair hBN hac, card_lineGroup hBN hBNnd hac hind]

omit [CharP K 2] [FiniteDimensional K N] in
theorem exists_mem_linearIndependent_pair {σ : Submodule K N} (h2 : 2 ≤ finrank K σ) {a : N}
    (ha : a ∈ σ) (ha0 : a ≠ 0) : ∃ c ∈ σ, LinearIndependent K ![a, c] := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (M := σ)
    (by omega) (x := ⟨a, ha⟩) (by simpa using ha0)
  refine ⟨y, y.2, ?_⟩
  rw [LinearIndependent.pair_iff] at hy ⊢
  intro s t hst
  exact hy s t (Subtype.ext (by simpa using hst))

include hBN hBNnd in
theorem commSp_planeGroup {σ : Submodule K N} (hσ : ∀ x ∈ σ, ∀ y ∈ σ, BN x y = 0)
    (h2 : 2 ≤ finrank K σ) : commSp (planeGroup hBN σ) = σ := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun a ha => ?_
  · rintro _ ⟨g, hg, x, rfl⟩
    exact (planeGroup_le_planeSub hBN hσ hg).1 x
  · by_cases ha0 : a = 0
    · rw [ha0]; exact Submodule.zero_mem _
    · obtain ⟨c, hcσ, hind⟩ := exists_mem_linearIndependent_pair h2 ha ha0
      obtain ⟨x, hx⟩ := exists_apply_eq_of_linearIndependent hBNnd hind ![0, 1]
      have hxa : BN x a = 0 := by simpa using hx 0
      have hxc : BN x c = 1 := by simpa using hx 1
      refine Submodule.subset_span ⟨lineElt hBN a c, lineElt_mem_planeGroup hBN ha hcσ, x, ?_⟩
      rw [lineElt_app hBN (hσ a ha c hcσ), hxa, hxc]
      simp

include hBN hBNnd in
theorem eq_of_planeGroup_eq {σ σ' : Submodule K N} (hσ : IsLine BN σ ∨ IsPlane BN σ)
    (hσ' : IsLine BN σ' ∨ IsPlane BN σ') (h : planeGroup hBN σ = planeGroup hBN σ') :
    σ = σ' := by
  have iso : ∀ {τ : Submodule K N}, (IsLine BN τ ∨ IsPlane BN τ) →
      (∀ x ∈ τ, ∀ y ∈ τ, BN x y = 0) ∧ 2 ≤ finrank K τ := fun {τ} hτ =>
    hτ.elim (fun h => ⟨h.1, h.2.ge⟩) (fun h => ⟨h.1, by rw [h.2]; norm_num⟩)
  rw [← commSp_planeGroup hBN hBNnd (iso hσ).1 (iso hσ).2, h,
    commSp_planeGroup hBN hBNnd (iso hσ').1 (iso hσ').2]

include hBN hBNnd in
theorem exists_isLine_of_mem_planeGroup {π : Submodule K N} (hπ : IsPlane BN π) {g : Gsp BN}
    (hg : g ∈ planeGroup hBN π) (hg1 : g ≠ 1) :
    ∃ ℓ ≤ π, IsLine BN ℓ ∧ g ∈ planeGroup hBN ℓ := by
  obtain ⟨a, ha, c, hc, hind, rfl⟩ := eq_lineElt_of_mem_planeGroup hBN hBNnd hπ hg hg1
  have hac : BN a c = 0 := hπ.1 a ha c hc
  refine ⟨Submodule.span K {a, c}, Submodule.span_le.mpr ?_, ⟨isotropic_span_pair hBN hac, ?_⟩,
    lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))⟩
  · rintro _ (rfl | rfl)
    · exact ha
    · exact hc
  · rw [← Matrix.range_cons_cons_empty a c ![], finrank_span_eq_card hind, Fintype.card_fin]

end Comm

end CFSG.ClassicalGroups.Alternating
