module

public import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.LieType.Chevalley.RootOps.Groups
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

abbrev PEntry : Type := (ℕ × ℕ) × Entry

variable {τ : Tag}

section Ring

variable {R : Type*} [CommRing R]

variable (τ R) in
@[expose] noncomputable def pOp (L : List PEntry) (s t : R) : Module.End R (RootModule τ R) :=
  (L.map fun x => (s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2]).sum

@[simp] theorem pOp_nil (s t : R) : pOp τ R [] s t = 0 :=
  rfl

theorem pOp_cons (x : PEntry) (L : List PEntry) (s t : R) :
    pOp τ R (x :: L) s t = (s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2] + pOp τ R L s t :=
  rfl

theorem pOp_append (L L' : List PEntry) (s t : R) :
    pOp τ R (L ++ L') s t = pOp τ R L s t + pOp τ R L' s t := by
  simp [pOp]

theorem pOp_flatMap {α : Type*} (l : List α) (f : α → List PEntry) (s t : R) :
    pOp τ R (l.flatMap f) s t = (l.map fun a => pOp τ R (f a) s t).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, pOp_append, ih, List.map_cons, List.sum_cons]

@[expose] def ValidP (τ : Tag) (L : List PEntry) : Prop :=
  ∀ x ∈ L, x.2.1 < dim τ ∧ x.2.2.1 < dim τ

theorem ValidP.append {L L' : List PEntry} (h : ValidP τ L) (h' : ValidP τ L') :
    ValidP τ (L ++ L') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem entriesOp_single_mul_single (e f : Entry) (hf : f.2.1 < dim τ) :
    entriesOp τ R [e] * entriesOp τ R [f] =
      if e.1 = f.2.1 then entriesOp τ R [(f.1, e.2.1, e.2.2 * f.2.2)] else 0 := by
  refine LinearMap.ext fun v => ?_
  simp only [entriesOp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
    posCoord_posVec hf]
  split_ifs with h
  · simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, Int.cast_mul]
    module
  · simp

@[expose] def pmul (L L' : List PEntry) : List PEntry :=
  L'.flatMap fun y => (L.filter fun x => Nat.beq x.2.1 y.2.2.1).map fun x =>
    ((x.1.1 + y.1.1, x.1.2 + y.1.2), (y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2))

theorem pOp_mul_single (L : List PEntry) (y : PEntry) (hy : y.2.2.1 < dim τ) (s t : R) :
    pOp τ R L s t * ((s ^ y.1.1 * t ^ y.1.2) • entriesOp τ R [y.2]) =
      pOp τ R ((L.filter fun x => Nat.beq x.2.1 y.2.2.1).map fun x =>
        ((x.1.1 + y.1.1, x.1.2 + y.1.2), (y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2))) s t := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have key : ((s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2]) *
        ((s ^ y.1.1 * t ^ y.1.2) • entriesOp τ R [y.2]) =
        if x.2.1 = y.2.2.1 then
          (s ^ (x.1.1 + y.1.1) * t ^ (x.1.2 + y.1.2)) •
            entriesOp τ R [(y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2)]
        else 0 := by
      rw [smul_mul_smul_comm, entriesOp_single_mul_single _ _ hy]
      split_ifs
      · congr 1
        ring
      · rw [smul_zero]
    rw [pOp_cons, add_mul, ih, key, List.filter_cons]
    cases hb : Nat.beq x.2.1 y.2.2.1
    · have h : x.2.1 ≠ y.2.2.1 := fun h => by rw [h, Nat.beq_refl] at hb; cases hb
      simp only [h, ↓reduceIte, zero_add, Bool.false_eq_true]
    · have h : x.2.1 = y.2.2.1 := Nat.eq_of_beq_eq_true hb
      simp only [h, ↓reduceIte, List.map_cons, pOp_cons]

theorem pOp_pmul (L : List PEntry) {L' : List PEntry} (hL' : ValidP τ L') (s t : R) :
    pOp τ R (pmul L L') s t = pOp τ R L s t * pOp τ R L' s t := by
  induction L' with
  | nil => simp [pmul]
  | cons y L' ih =>
    have hy := (hL' y (List.mem_cons_self ..)).2
    rw [pmul, List.flatMap_cons, pOp_append, ← pmul, ih fun x hx => hL' x (List.mem_cons_of_mem _ hx),
      pOp_cons, mul_add, pOp_mul_single L y hy]

theorem validP_pmul {L L' : List PEntry} (hL : ValidP τ L) (hL' : ValidP τ L') :
    ValidP τ (pmul L L') := by
  intro z hz
  simp only [pmul, List.mem_flatMap, List.mem_map, List.mem_filter] at hz
  obtain ⟨y, hy, x, ⟨hx, -⟩, rfl⟩ := hz
  exact ⟨(hL' y hy).1, (hL x hx).2⟩

@[expose] def mul1 (A B : List PEntry) : List PEntry :=
  A ++ B ++ pmul A B

theorem one_add_pOp_mul1 (A : List PEntry) {B : List PEntry} (hB : ValidP τ B) (s t : R) :
    1 + pOp τ R (mul1 A B) s t = (1 + pOp τ R A s t) * (1 + pOp τ R B s t) := by
  rw [mul1, pOp_append, pOp_append, pOp_pmul A hB]
  noncomm_ring

theorem validP_mul1 {A B : List PEntry} (hA : ValidP τ A) (hB : ValidP τ B) :
    ValidP τ (mul1 A B) :=
  (hA.append hB).append (validP_pmul hA hB)

@[expose] def coeffAt (L : List PEntry) (δ : ℕ × ℕ) : List Entry :=
  (L.filter fun x => Nat.beq x.1.1 δ.1 && Nat.beq x.1.2 δ.2).map Prod.snd

theorem pOp_eq_sum (L : List PEntry) (S : Finset (ℕ × ℕ)) (hS : ∀ x ∈ L, x.1 ∈ S) (s t : R) :
    pOp τ R L s t = ∑ δ ∈ S, (s ^ δ.1 * t ^ δ.2) • entriesOp τ R (coeffAt L δ) := by
  induction L with
  | nil => simp [coeffAt]
  | cons x L ih =>
    rw [pOp_cons, ih fun y hy => hS y (List.mem_cons_of_mem _ hy)]
    have hx := hS x (List.mem_cons_self ..)
    have hc : ∀ δ : ℕ × ℕ, coeffAt (x :: L) δ =
        if x.1 = δ then x.2 :: coeffAt L δ else coeffAt L δ := by
      intro δ
      simp only [coeffAt, List.filter_cons]
      by_cases h : x.1 = δ
      · subst h
        simp [Nat.beq_refl]
      · have : ¬(Nat.beq x.1.1 δ.1 && Nat.beq x.1.2 δ.2) = true := by
          simp only [Bool.and_eq_true]
          exact fun ⟨h1, h2⟩ => h (Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2))
        simp [h, this]
    have hc' : ∀ δ : ℕ × ℕ, entriesOp τ R (coeffAt (x :: L) δ) =
        (if x.1 = δ then entriesOp τ R [x.2] else 0) + entriesOp τ R (coeffAt L δ) := by
      intro δ
      rw [hc δ]
      split_ifs
      · rw [show x.2 :: coeffAt L δ = [x.2] ++ coeffAt L δ from rfl, entriesOp_append]
      · rw [zero_add]
    simp only [hc', smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, hx,
      ↓reduceIte]

@[expose] def pEqCheck (L L' : List PEntry) : Bool :=
  (L ++ L').all fun x => summaryEq (summary (coeffAt L x.1)) (summary (coeffAt L' x.1))

theorem pOp_eq_of_pEqCheck {L L' : List PEntry} (h : pEqCheck L L' = true) (s t : R) :
    pOp τ R L s t = pOp τ R L' s t := by
  classical
  set S : Finset (ℕ × ℕ) := ((L ++ L').map Prod.fst).toFinset
  have hS : ∀ x ∈ L ++ L', x.1 ∈ S := fun x hx =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [pOp_eq_sum L S (fun x hx => hS x (List.mem_append_left _ hx)),
    pOp_eq_sum L' S (fun x hx => hS x (List.mem_append_right _ hx))]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hδ)
  simp only [pEqCheck, List.all_eq_true] at h
  rw [entriesOp_eq_of_summaryEq (h x hx)]

end Ring

@[expose] def rootAt (τ : Tag) (a : ℕ) (ha : a < τ.rootCertificate.roots.length) : Root τ :=
  ⟨τ.rootCertificate.root a, isRoot_rootCertificate_root ha⟩

theorem rootPos_rootAt {a : ℕ} (ha : a < τ.rootCertificate.roots.length) :
    rootPos (rootAt τ a ha) = a :=
  rootPos_eq ha rfl

@[expose] def nilpE (τ : Tag) (g : ℕ) (C : ℤ) (ea eb : ℕ) : List PEntry :=
  [1, 2, 3].flatMap fun k => (entries τ g k).map fun e =>
    ((k * ea, k * eb), (e.1, e.2.1, C ^ k * e.2.2))

theorem validP_nilpE (h : allValid τ = true) {g : ℕ} (hg : g < τ.rootCertificate.roots.length)
    (C : ℤ) (ea eb : ℕ) : ValidP τ (nilpE τ g C ea eb) := by
  intro x hx
  simp only [nilpE, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨k, hk, e, he, rfl⟩ := hx
  exact validEntries_of_validB (validB_of_allValid h hg hk) e he

section Family

variable {R : Type} [CommRing R]

theorem pOp_map_deg (δ : ℕ × ℕ) (L : List Entry) (s t : R) :
    pOp τ R (L.map fun e => (δ, e)) s t = (s ^ δ.1 * t ^ δ.2) • entriesOp τ R L := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [List.map_cons, pOp_cons, ih, show e :: L = [e] ++ L from rfl, entriesOp_append,
      smul_add]

theorem one_add_pOp_nilpE (γ : Root τ) (C : ℤ) (ea eb : ℕ) (s t : R) :
    1 + pOp τ R (nilpE τ (rootPos γ) C ea eb) s t =
      (rootOperatorFamily τ).elt R γ ((C : R) * s ^ ea * t ^ eb) := by
  have hmap : ∀ k : ℕ, ((entries τ (rootPos γ) k).map fun e =>
      ((k * ea, k * eb), (e.1, e.2.1, C ^ k * e.2.2))) =
      ((entries τ (rootPos γ) k).map fun e => (e.1, e.2.1, C ^ k * e.2.2)).map
        fun e => ((k * ea, k * eb), e) := by
    intro k
    rw [List.map_map]
    rfl
  simp only [nilpE, pOp_flatMap, hmap, pOp_map_deg, entriesOp_map_smul, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [RootOperatorFamily.elt, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change _ = (((C : R) * s ^ ea * t ^ eb) ^ 0) • dataD τ R γ 0 +
    (((C : R) * s ^ ea * t ^ eb) ^ 1) • dataD τ R γ 1 +
    (((C : R) * s ^ ea * t ^ eb) ^ 2) • dataD τ R γ 2 +
    (((C : R) * s ^ ea * t ^ eb) ^ 3) • dataD τ R γ 3
  simp only [dataD, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
    show (3 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≤ 3 by omega, show (2 : ℕ) ≤ 3 by omega,
    le_refl, ↓reduceIte, pow_zero, one_smul, smul_smul]
  have e1 : (s ^ (1 * ea) * t ^ (1 * eb)) * ((C ^ 1 : ℤ) : R) = ((C : R) * s ^ ea * t ^ eb) ^ 1 := by
    push_cast; ring
  have e2 : (s ^ (2 * ea) * t ^ (2 * eb)) * ((C ^ 2 : ℤ) : R) = ((C : R) * s ^ ea * t ^ eb) ^ 2 := by
    push_cast; ring
  have e3 : (s ^ (3 * ea) * t ^ (3 * eb)) * ((C ^ 3 : ℤ) : R) = ((C : R) * s ^ ea * t ^ eb) ^ 3 := by
    push_cast; ring
  rw [e1, e2, e3]
  abel

end Family

abbrev Factor : Type := ℕ × ℕ × ℕ × ℤ

@[expose] def factorsN (τ : Tag) : List PEntry → List Factor → List PEntry
  | acc, [] => acc
  | acc, f :: fs => factorsN τ (mul1 acc (nilpE τ f.2.2.1 f.2.2.2 f.1 f.2.1)) fs

@[expose] def coneOk (τ : Tag) (a b : ℕ) (f : Factor) : Bool :=
  Nat.blt f.2.2.1 τ.rootCertificate.roots.length && Nat.ble 1 f.1 && Nat.ble 1 f.2.1 &&
    CFSG.LieType.Ree.vecBEq (τ.rootCertificate.root f.2.2.1)
      (f.1 • τ.rootCertificate.root a + f.2.1 • τ.rootCertificate.root b)

@[expose] def repCheck (τ : Tag) (a b : ℕ) (fs : List Factor) : Bool :=
  Nat.blt a τ.rootCertificate.roots.length && Nat.blt b τ.rootCertificate.roots.length &&
    fs.all (coneOk τ a b) &&
    pEqCheck (mul1 (nilpE τ a 1 1 0) (nilpE τ b 1 0 1))
      (mul1 (mul1 (factorsN τ [] fs) (nilpE τ b 1 0 1)) (nilpE τ a 1 1 0))

section Family

variable {R : Type} [CommRing R]

@[expose] noncomputable def factorsProd (τ : Tag) (R : Type) [CommRing R] (fs : List Factor)
    (s t : R) : Module.End R (RootModule τ R) :=
  (fs.map fun f => if h : f.2.2.1 < τ.rootCertificate.roots.length then
    (rootOperatorFamily τ).elt R (rootAt τ f.2.2.1 h) ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1)
    else 1).prod

theorem factorsProd_cons (f : Factor) (fs : List Factor) (s t : R) :
    factorsProd τ R (f :: fs) s t = (if h : f.2.2.1 < τ.rootCertificate.roots.length then
      (rootOperatorFamily τ).elt R (rootAt τ f.2.2.1 h) ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1)
      else 1) * factorsProd τ R fs s t := by
  simp [factorsProd]

theorem one_add_pOp_factorsN (hv : allValid τ = true) (fs : List Factor)
    (hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length) (acc : List PEntry)
    (hacc : ValidP τ acc) (s t : R) :
    1 + pOp τ R (factorsN τ acc fs) s t = (1 + pOp τ R acc s t) * factorsProd τ R fs s t := by
  induction fs generalizing acc with
  | nil => simp [factorsN, factorsProd]
  | cons f fs ih =>
    have hf := hfs f (List.mem_cons_self ..)
    have hn := validP_nilpE hv hf f.2.2.2 f.1 f.2.1
    rw [factorsN, ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _ (validP_mul1 hacc hn),
      one_add_pOp_mul1 acc hn, factorsProd_cons, mul_assoc]
    simp only [hf, ↓reduceDIte]
    congr 2
    have := one_add_pOp_nilpE (R := R) (rootAt τ f.2.2.1 hf) f.2.2.2 f.1 f.2.1 s t
    rwa [rootPos_rootAt] at this

theorem validP_factorsN (hv : allValid τ = true) (fs : List Factor)
    (hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length) (acc : List PEntry)
    (hacc : ValidP τ acc) : ValidP τ (factorsN τ acc fs) := by
  induction fs generalizing acc with
  | nil => exact hacc
  | cons f fs ih =>
    exact ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _
      (validP_mul1 hacc (validP_nilpE hv (hfs f (List.mem_cons_self ..)) _ _ _))

theorem elt_mul_elt_of_repCheck (hv : allValid τ = true) {a b : ℕ} {fs : List Factor}
    (h : repCheck τ a b fs = true) (α β : Root τ) (ha : rootPos α = a) (hb : rootPos β = b)
    (s t : R) :
    (rootOperatorFamily τ).elt R α s * (rootOperatorFamily τ).elt R β t =
      factorsProd τ R fs s t * (rootOperatorFamily τ).elt R β t *
        (rootOperatorFamily τ).elt R α s := by
  simp only [repCheck, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨ha', hb'⟩, hcone⟩, hpeq⟩ := h
  have hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length := fun f hf => by
    have := hcone f hf
    simp only [coneOk, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.1.1
  have hA := validP_nilpE hv ha' 1 1 0
  have hB := validP_nilpE hv hb' 1 0 1
  have hP := validP_factorsN hv fs hfs [] (fun x hx => absurd hx (List.not_mem_nil))
  have heq := congrArg (fun X => 1 + X) (pOp_eq_of_pEqCheck (τ := τ) (R := R) hpeq s t)
  rw [one_add_pOp_mul1 _ hB, one_add_pOp_mul1 _ hA, one_add_pOp_mul1 _ hB,
    one_add_pOp_factorsN hv fs hfs [] (fun x hx => absurd hx (List.not_mem_nil))] at heq
  rw [← ha, ← hb] at heq
  simp only [one_add_pOp_nilpE, Int.cast_one, one_mul, pow_one, pow_zero, mul_one, pOp_nil,
    add_zero, one_mul] at heq
  exact heq

end Family

section Field

variable (K : Type) [Field K]

@[expose] noncomputable def factorsElement (fs : List Factor) (c d : K) : adjointGroup τ K :=
  (fs.map fun f => if h : f.2.2.1 < τ.rootCertificate.roots.length then
    (rootOperatorFamily τ).eltElement (rootAt τ f.2.2.1 h) ((f.2.2.2 : K) * c ^ f.1 * d ^ f.2.1)
    else 1).prod

theorem coe_factorsElement (fs : List Factor) (c d : K) :
    (((factorsElement K fs c d : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K)) =
      factorsProd τ K fs c d := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [factorsElement, List.map_cons, List.prod_cons, ← factorsElement, factorsProd_cons,
      Subgroup.coe_mul, Units.val_mul, ih]
    split_ifs <;> rfl

theorem commContained_of_repCheck (hv : allValid τ = true) {a b : ℕ} {fs : List Factor}
    (h : repCheck τ a b fs = true) (α β : Root τ) (ha : rootPos α = a) (hb : rootPos β = b) :
    (rootOperatorFamily τ).CommContained K α β := by
  have hcone : ∀ f ∈ fs, coneOk τ a b f = true := by
    simp only [repCheck, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1.2
  rw [RootOperatorFamily.commContained_iff]
  intro c d
  set F := rootOperatorFamily τ
  have hop := elt_mul_elt_of_repCheck (R := K) hv h α β ha hb c d
  have hgrp : F.eltElement α c * F.eltElement β d * (F.eltElement α c)⁻¹ *
      (F.eltElement β d)⁻¹ = factorsElement K fs c d := by
    have : F.eltElement α c * F.eltElement β d =
        factorsElement K fs c d * F.eltElement β d * F.eltElement α c := by
      refine Subtype.ext (Units.ext ?_)
      simp only [Subgroup.coe_mul, Units.val_mul, RootOperatorFamily.coe_eltElement,
        RootOperatorFamily.coe_eltUnit, coe_factorsElement]
      exact hop
    rw [this]
    group
  rw [hgrp]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
  have hc := hcone f hf
  simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  obtain ⟨⟨⟨hg, hp⟩, hq⟩, hv'⟩ := hc
  simp only [hg, ↓reduceDIte]
  refine (le_iSup₂ (f := fun (γ : Root τ)
    (_ : ∃ a' b' : ℕ, 1 ≤ a' ∧ 1 ≤ b' ∧ γ.1 = a' • α.1 + b' • β.1) => F.rootSubgroup K γ)
    (rootAt τ f.2.2.1 hg) ⟨f.1, f.2.1, hp, hq, ?_⟩) (F.eltElement_mem_rootSubgroup _ _)
  rw [CFSG.LieType.Ree.vecBEq_iff] at hv'
  rw [← root_rootPos α, ← root_rootPos β, ha, hb]
  exact hv'

end Field

end CFSG.LieType.Chevalley.RootOps
