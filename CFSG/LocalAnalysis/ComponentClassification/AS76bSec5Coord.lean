module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Defs
public import Mathlib.Tactic.Abel

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

variable {V : Type} [AddCommGroup V] {R U W : AddSubgroup V}

@[expose] def sumHom (R U W : AddSubgroup V) : R × U × W →+ V where
  toFun p := (p.1 : V) + p.2.1 + p.2.2
  map_zero' := by simp
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add]
    abel

@[simp] theorem sumHom_apply (p : R × U × W) :
    sumHom R U W p = (p.1 : V) + p.2.1 + p.2.2 := rfl

theorem card_sup_eq_mul {H K : AddSubgroup V} (h : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : H × K → ↥(H ⊔ K) := fun p => ⟨p.1 + p.2, AddSubgroup.add_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ he
      simp only [f, Subtype.mk.injEq] at he
      have hab : a - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      have hmem : a - a' ∈ H ⊓ K :=
        AddSubgroup.mem_inf.2 ⟨H.sub_mem ha ha', hab ▸ K.sub_mem hb' hb⟩
      rw [h, AddSubgroup.mem_bot, sub_eq_zero] at hmem
      subst hmem
      have : b = b' := by simpa using he
      subst this
      rfl
    · rintro ⟨v, hv⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hv
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

@[expose] noncomputable def nz {H : Type} [Zero H] (x : H) : Bool :=
  @decide (x ≠ 0) (Classical.propDecidable _)

theorem nz_eq_true {H : Type} [Zero H] {x : H} : nz x = true ↔ x ≠ 0 := by
  simp [nz]

theorem nz_eq_false {H : Type} [Zero H] {x : H} : nz x = false ↔ x = 0 := by
  simp [nz]

@[simp] theorem nz_zero {H : Type} [Zero H] : nz (0 : H) = false := nz_eq_false.2 rfl

theorem nz_of_ne {H : Type} [Zero H] {x : H} (hx : x ≠ 0) : nz x = true := nz_eq_true.2 hx

theorem nz_eq_nz {H H' : Type} [Zero H] [Zero H'] {x : H} {y : H'} :
    nz x = nz y ↔ (x = 0 ↔ y = 0) := by
  simp only [nz, decide_eq_decide, ne_eq, not_iff_not]

namespace Decomp

variable (hd : Decomp R U W)
include hd

theorem eq_zero_of_add_eq_zero {r u w : V} (hr : r ∈ R) (hu : u ∈ U) (hw : w ∈ W)
    (h : r + u + w = 0) : r = 0 ∧ u = 0 ∧ w = 0 := by
  have h1 : r + (u + w) = 0 := by rw [← add_assoc]; exact h
  have hr0 : r = 0 := by
    have hmem : r ∈ R ⊓ (U ⊔ W) := AddSubgroup.mem_inf.2 ⟨hr, by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact neg_mem (AddSubgroup.add_mem_sup hu hw)⟩
    rw [hd.inf_R] at hmem
    exact AddSubgroup.mem_bot.1 hmem
  subst hr0
  rw [zero_add] at h1
  have hu0 : u = 0 := by
    have hmem : u ∈ U ⊓ W :=
      AddSubgroup.mem_inf.2 ⟨hu, by rw [eq_neg_of_add_eq_zero_left h1]; exact neg_mem hw⟩
    rw [hd.inf_U] at hmem
    exact AddSubgroup.mem_bot.1 hmem
  subst hu0
  exact ⟨rfl, rfl, by simpa using h1⟩

theorem injective : Function.Injective (sumHom R U W) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨r, hr⟩, ⟨u, hu⟩, ⟨w, hw⟩⟩ h
  obtain ⟨rfl, rfl, rfl⟩ := hd.eq_zero_of_add_eq_zero hr hu hw h
  rfl

theorem surjective : Function.Surjective (sumHom R U W) := by
  intro v
  have hv : v ∈ R ⊔ U ⊔ W := by rw [hd.sup_eq]; trivial
  obtain ⟨y, hy, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hv
  obtain ⟨r, hr, u, hu, rfl⟩ := AddSubgroup.mem_sup.1 hy
  exact ⟨(⟨r, hr⟩, ⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

omit hd in
@[expose] noncomputable def equiv (hd : Decomp R U W) : R × U × W ≃+ V :=
  AddEquiv.ofBijective (sumHom R U W) ⟨hd.injective, hd.surjective⟩

omit hd in
@[expose] noncomputable def cR (hd : Decomp R U W) (v : V) : R := (hd.equiv.symm v).1

omit hd in
@[expose] noncomputable def cU (hd : Decomp R U W) (v : V) : U := (hd.equiv.symm v).2.1

omit hd in
@[expose] noncomputable def cW (hd : Decomp R U W) (v : V) : W := (hd.equiv.symm v).2.2

theorem equiv_apply (p : R × U × W) : hd.equiv p = (p.1 : V) + p.2.1 + p.2.2 := rfl

theorem coord_sum (v : V) : (hd.cR v : V) + hd.cU v + hd.cW v = v :=
  hd.equiv.apply_symm_apply v

theorem symm_apply (r : R) (u : U) (w : W) : hd.equiv.symm ((r : V) + u + w) = (r, u, w) :=
  hd.equiv.symm_apply_eq.2 rfl

theorem cR_sum {r u w : V} (hr : r ∈ R) (hu : u ∈ U) (hw : w ∈ W) :
    (hd.cR (r + u + w) : V) = r :=
  congrArg (fun p : R × U × W => (p.1 : V)) (hd.symm_apply ⟨r, hr⟩ ⟨u, hu⟩ ⟨w, hw⟩)

theorem cU_sum {r u w : V} (hr : r ∈ R) (hu : u ∈ U) (hw : w ∈ W) :
    (hd.cU (r + u + w) : V) = u :=
  congrArg (fun p : R × U × W => (p.2.1 : V)) (hd.symm_apply ⟨r, hr⟩ ⟨u, hu⟩ ⟨w, hw⟩)

theorem cW_sum {r u w : V} (hr : r ∈ R) (hu : u ∈ U) (hw : w ∈ W) :
    (hd.cW (r + u + w) : V) = w :=
  congrArg (fun p : R × U × W => (p.2.2 : V)) (hd.symm_apply ⟨r, hr⟩ ⟨u, hu⟩ ⟨w, hw⟩)

theorem cR_add (v v' : V) : hd.cR (v + v') = hd.cR v + hd.cR v' := by
  simp only [cR, map_add, Prod.fst_add]

theorem cU_add (v v' : V) : hd.cU (v + v') = hd.cU v + hd.cU v' := by
  simp only [cU, map_add, Prod.fst_add, Prod.snd_add]

theorem cW_add (v v' : V) : hd.cW (v + v') = hd.cW v + hd.cW v' := by
  simp only [cW, map_add, Prod.snd_add]

theorem ext_coord {v v' : V} (h1 : hd.cR v = hd.cR v') (h2 : hd.cU v = hd.cU v')
    (h3 : hd.cW v = hd.cW v') : v = v' := by
  rw [← hd.coord_sum v, ← hd.coord_sum v', h1, h2, h3]

theorem cW_eq_zero_iff (v : V) : hd.cW v = 0 ↔ v ∈ R ⊔ U := by
  constructor
  · intro h
    rw [← hd.coord_sum v, h, ZeroMemClass.coe_zero, add_zero]
    exact AddSubgroup.add_mem_sup (hd.cR v).2 (hd.cU v).2
  · intro hv
    obtain ⟨r, hr, u, hu, rfl⟩ := AddSubgroup.mem_sup.1 hv
    exact Subtype.ext (by simpa using hd.cW_sum hr hu (zero_mem W))

theorem cU_eq_zero_iff (v : V) : hd.cU v = 0 ↔ v ∈ R ⊔ W := by
  constructor
  · intro h
    rw [← hd.coord_sum v, h, ZeroMemClass.coe_zero, add_zero]
    exact AddSubgroup.add_mem_sup (hd.cR v).2 (hd.cW v).2
  · intro hv
    obtain ⟨r, hr, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hv
    exact Subtype.ext (by simpa using hd.cU_sum hr (zero_mem U) hw)

theorem cR_eq_zero_iff (v : V) : hd.cR v = 0 ↔ v ∈ U ⊔ W := by
  constructor
  · intro h
    rw [← hd.coord_sum v, h, ZeroMemClass.coe_zero, zero_add]
    exact AddSubgroup.add_mem_sup (hd.cU v).2 (hd.cW v).2
  · intro hv
    obtain ⟨u, hu, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hv
    exact Subtype.ext (by simpa [add_assoc] using hd.cR_sum (zero_mem R) hu hw)

theorem mem_R_iff (v : V) : v ∈ R ↔ hd.cU v = 0 ∧ hd.cW v = 0 := by
  constructor
  · intro hv
    exact ⟨Subtype.ext (by simpa using hd.cU_sum hv (zero_mem U) (zero_mem W)),
      Subtype.ext (by simpa using hd.cW_sum hv (zero_mem U) (zero_mem W))⟩
  · rintro ⟨h2, h3⟩
    rw [← hd.coord_sum v, h2, h3]
    simp

theorem mem_U_iff (v : V) : v ∈ U ↔ hd.cR v = 0 ∧ hd.cW v = 0 := by
  constructor
  · intro hv
    exact ⟨Subtype.ext (by simpa using hd.cR_sum (zero_mem R) hv (zero_mem W)),
      Subtype.ext (by simpa using hd.cW_sum (zero_mem R) hv (zero_mem W))⟩
  · rintro ⟨h1, h3⟩
    rw [← hd.coord_sum v, h1, h3]
    simp

theorem mem_W_iff (v : V) : v ∈ W ↔ hd.cR v = 0 ∧ hd.cU v = 0 := by
  constructor
  · intro hv
    exact ⟨Subtype.ext (by simpa using hd.cR_sum (zero_mem R) (zero_mem U) hv),
      Subtype.ext (by simpa using hd.cU_sum (zero_mem R) (zero_mem U) hv)⟩
  · rintro ⟨h1, h2⟩
    rw [← hd.coord_sum v, h1, h2]
    simp

theorem inf_RU : R ⊓ U = ⊥ := eq_bot_mono (inf_le_inf_left R le_sup_left) hd.inf_R

theorem inf_RW : R ⊓ W = ⊥ := eq_bot_mono (inf_le_inf_left R le_sup_right) hd.inf_R

theorem card_eq : Nat.card V = Nat.card R * (Nat.card U * Nat.card W) := by
  rw [← Nat.card_congr hd.equiv.toEquiv, Nat.card_prod, Nat.card_prod]

theorem card_RU : Nat.card ↥(R ⊔ U) = Nat.card R * Nat.card U := card_sup_eq_mul hd.inf_RU

theorem card_RW : Nat.card ↥(R ⊔ W) = Nat.card R * Nat.card W := card_sup_eq_mul hd.inf_RW

theorem card_UW : Nat.card ↥(U ⊔ W) = Nat.card U * Nat.card W := card_sup_eq_mul hd.inf_U

omit hd in
@[expose] noncomputable def pat (hd : Decomp R U W) (v : V) : Bool × Bool × Bool :=
  (nz (hd.cR v), nz (hd.cU v), nz (hd.cW v))

theorem pat_fst (v : V) : (hd.pat v).1 = true ↔ hd.cR v ≠ 0 := nz_eq_true

theorem pat_snd_fst (v : V) : (hd.pat v).2.1 = true ↔ hd.cU v ≠ 0 := nz_eq_true

theorem pat_snd_snd (v : V) : (hd.pat v).2.2 = true ↔ hd.cW v ≠ 0 := nz_eq_true

theorem pat_eq_iff (v v' : V) : hd.pat v = hd.pat v' ↔
    ((hd.cR v = 0 ↔ hd.cR v' = 0) ∧ (hd.cU v = 0 ↔ hd.cU v' = 0) ∧
      (hd.cW v = 0 ↔ hd.cW v' = 0)) := by
  simp only [pat, Prod.mk.injEq, nz_eq_nz]

theorem cR_zero : hd.cR 0 = 0 := by simp [cR]

theorem cU_zero : hd.cU 0 = 0 := by simp [cU]

theorem cW_zero : hd.cW 0 = 0 := by simp [cW]

theorem pat_eq_zero_iff (v : V) : hd.pat v = (false, false, false) ↔ v = 0 := by
  constructor
  · intro h
    simp only [pat, Prod.mk.injEq, nz_eq_false] at h
    rw [← hd.coord_sum v, h.1, h.2.1, h.2.2]
    simp
  · rintro rfl
    simp [pat, hd.cR_zero, hd.cU_zero, hd.cW_zero]

omit hd in
theorem pat_equiv (hd : Decomp R U W) (p : R × U × W) :
    hd.pat (hd.equiv p) = (nz p.1, nz p.2.1, nz p.2.2) := by
  simp only [pat, cR, cU, cW, AddEquiv.symm_apply_apply]

omit hd in
theorem pat_equiv_add (hd : Decomp R U W) (p : R × U × W) (v : V) :
    hd.pat (hd.equiv p + v) = (nz (p.1 + hd.cR v), nz (p.2.1 + hd.cU v), nz (p.2.2 + hd.cW v)) := by
  have he : hd.equiv p + v = hd.equiv (p + hd.equiv.symm v) := by
    rw [map_add, AddEquiv.apply_symm_apply]
  rw [he, pat_equiv]
  rfl

end Decomp

end CFSG.ComponentClassification.AS76b.Sec5
